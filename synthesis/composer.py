"""The Composer — core Synthesis engine.

Takes a bundle of discoveries + proofs and produces a publication-quality paper draft.
Stages: boundary detection → section composition → assembly → review → REVISION → output.
"""

from __future__ import annotations

import json
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path

from synthesis.api import ClaudeAPI
from synthesis.models import (
    PaperDraft, PaperBundle, ReviewRequest, SectionDraft,
    Citation, BoundaryDecision, PaperConfidence,
)
from synthesis.prompts.compose import (
    SECTION_SYSTEM,
    ABSTRACT_PROMPT, INTRODUCTION_PROMPT, METHODS_PROMPT,
    RESULTS_PROMPT, DISCUSSION_PROMPT, HONEST_SCOPE_PROMPT,
    CONCLUSION_PROMPT, REFERENCES_PROMPT,
)
from synthesis.prompts.boundary import BOUNDARY_PROMPT
from synthesis.prompts.review import REVIEW_PROMPT, REVISION_PROMPT


class Composer:
    """Core paper composition engine."""

    def __init__(self, api: ClaudeAPI, corpus_papers_dir: Path | None = None):
        self.api = api
        self.corpus_papers_dir = corpus_papers_dir

    def detect_boundaries(
        self, convergences: list[dict], proofs: list[dict], findings: list[dict]
    ) -> list[PaperBundle]:
        """Deterministic paper boundary detection by domain pair.

        Groups convergences by their domain pair (e.g. "Topology × Quantum Mechanics").
        This is fully reproducible, semantically coherent, and avoids the risk of
        Claude hallucinating convergence IDs (which it was never given in the old approach).

        Rules:
        - Each domain pair with ≥3 convergences = one paper (split at 10 if large)
        - Small domain pairs (1-2 convergences) sharing a domain are merged
        - Any remaining singletons get a catch-all paper
        - Every convergence is assigned to exactly one paper (completeness guaranteed)
        """
        if len(convergences) <= 10:
            bundle = PaperBundle(
                convergences=convergences,
                proofs=proofs,
                findings=findings,
            )
            return [bundle]

        # Build proof lookup
        proof_by_conv = {}
        for p in proofs:
            proof_by_conv[p.get("convergence_id", "")] = p

        # Group convergences by domain pair
        pair_groups: dict[str, list[dict]] = {}
        for c in convergences:
            domains = tuple(sorted(c.get("domain_names", c.get("domains", []))))
            key = " × ".join(domains) if domains else "Unknown"
            pair_groups.setdefault(key, []).append(c)

        bundles = []
        small_groups: list[tuple[str, list[dict]]] = []  # pairs with <3 convergences

        for pair_key, convs in sorted(pair_groups.items(), key=lambda x: -len(x[1])):
            if len(convs) < 3:
                small_groups.append((pair_key, convs))
                continue

            # Split large groups into papers of ~8
            max_per_paper = 10
            for i in range(0, len(convs), max_per_paper):
                chunk = convs[i:i + max_per_paper]
                chunk_proofs = [proof_by_conv[c.get("id", "")]
                                for c in chunk if c.get("id", "") in proof_by_conv]
                suffix = f" (Part {i // max_per_paper + 1})" if len(convs) > max_per_paper else ""
                bundles.append(PaperBundle(
                    convergences=chunk,
                    proofs=chunk_proofs,
                    findings=[],
                    theme=pair_key,
                    target_structure=f"Structural Convergences in {pair_key}{suffix}",
                ))

        # Merge small groups by shared domain
        if small_groups:
            # Group small pairs by their first domain
            domain_buckets: dict[str, list[dict]] = {}
            for pair_key, convs in small_groups:
                first_domain = pair_key.split(" × ")[0] if " × " in pair_key else pair_key
                domain_buckets.setdefault(first_domain, []).extend(convs)

            for domain, convs in domain_buckets.items():
                if not convs:
                    continue
                # Split into papers of ~8 if bucket got large
                for i in range(0, len(convs), 10):
                    chunk = convs[i:i + 10]
                    chunk_proofs = [proof_by_conv[c.get("id", "")]
                                    for c in chunk if c.get("id", "") in proof_by_conv]
                    pair_names = set()
                    for c in chunk:
                        for d in c.get("domain_names", c.get("domains", [])):
                            pair_names.add(d)
                    bundles.append(PaperBundle(
                        convergences=chunk,
                        proofs=chunk_proofs,
                        findings=[],
                        theme=f"Cross-domain convergences involving {domain}",
                        target_structure=f"Cross-Domain Convergences: {', '.join(sorted(pair_names)[:4])}",
                    ))

        # Assign findings to the most relevant paper
        if findings:
            self._assign_findings_to_bundles(findings, bundles)

        if not bundles:
            return [PaperBundle(convergences=convergences, proofs=proofs, findings=findings)]

        return bundles

    def _assign_findings_to_bundles(
        self, findings: list[dict], bundles: list[PaperBundle]
    ):
        """Assign each finding to the bundle whose convergences it most references."""
        for f in findings:
            # Findings may reference convergence IDs or domain pairs
            f_domains = set(f.get("domains", []))
            f_conv_ids = set(f.get("convergence_ids", []))

            best_bundle = None
            best_score = -1

            for bundle in bundles:
                score = 0
                bundle_conv_ids = {c.get("id", "") for c in bundle.convergences}
                score += len(f_conv_ids & bundle_conv_ids) * 10  # Strong signal

                bundle_domains = set()
                for c in bundle.convergences:
                    for d in c.get("domain_names", c.get("domains", [])):
                        bundle_domains.add(d)
                score += len(f_domains & bundle_domains)

                if score > best_score:
                    best_score = score
                    best_bundle = bundle

            if best_bundle is not None:
                best_bundle.findings.append(f)

    def compose(self, bundle: PaperBundle) -> tuple[PaperDraft, ReviewRequest]:
        """Compose a complete paper from a bundle."""

        paper = PaperDraft()
        paper.source_bundle = asdict(bundle)
        paper.convergence_ids = [c.get("id", "") for c in bundle.convergences]
        paper.proof_ids = [p.get("id", "") for p in bundle.proofs]
        paper.finding_ids = [f.get("id", "") for f in bundle.findings]

        review = ReviewRequest(paper_id=paper.id)

        # Determine title and theme
        paper.title = bundle.target_structure or self._generate_title(bundle)

        # Build context
        discoveries_summary = self._build_discoveries_summary(bundle)
        proofs_summary = self._build_proofs_summary(bundle)
        corpus_context = self._load_corpus_context()

        # Compose each section
        sections = []

        # Abstract
        abstract_text = self._compose_abstract(paper.title, bundle.theme, discoveries_summary, proofs_summary)
        paper.abstract = abstract_text
        sections.append({"section": "abstract", "title": "Abstract", "content": abstract_text,
                        "word_count": len(abstract_text.split()), "confidence": 0.8, "flags": []})

        # Introduction
        intro_text = self._compose_introduction(paper.title, abstract_text, bundle.theme,
                                                 discoveries_summary, corpus_context)
        sections.append({"section": "introduction", "title": "1. Introduction", "content": intro_text,
                        "word_count": len(intro_text.split()), "confidence": 0.7, "flags": []})

        # Methods
        methods_text = self._compose_methods(bundle)
        sections.append({"section": "methods", "title": "2. Methods", "content": methods_text,
                        "word_count": len(methods_text.split()), "confidence": 0.9, "flags": []})

        # Results
        results_text = self._compose_results(bundle)
        sections.append({"section": "results", "title": "3. Results", "content": results_text,
                        "word_count": len(results_text.split()), "confidence": 0.7, "flags": []})

        # Discussion
        discussion_text = self._compose_discussion(paper.title, bundle)
        sections.append({"section": "discussion", "title": "4. Discussion", "content": discussion_text,
                        "word_count": len(discussion_text.split()), "confidence": 0.6, "flags": []})

        # Honest Scope
        scope_text = self._compose_honest_scope(bundle)
        sections.append({"section": "honest_scope", "title": "5. Honest Scope", "content": scope_text,
                        "word_count": len(scope_text.split()), "confidence": 0.9, "flags": []})

        # Conclusion
        conclusion_text = self._compose_conclusion(paper.title, bundle)
        sections.append({"section": "conclusion", "title": "6. Conclusion", "content": conclusion_text,
                        "word_count": len(conclusion_text.split()), "confidence": 0.8, "flags": []})

        # References
        references_text = self._compose_references(bundle)
        sections.append({"section": "references", "title": "References", "content": references_text,
                        "word_count": len(references_text.split()), "confidence": 0.7, "flags": []})

        # Appendices — complete data from Gnosis + Logos (no data loss)
        appendix_a = self._build_appendix_discoveries(bundle)
        sections.append({"section": "appendix_a", "title": "Appendix A: Complete Discovery Data",
                        "content": appendix_a, "word_count": len(appendix_a.split()),
                        "confidence": 1.0, "flags": []})

        appendix_b = self._build_appendix_formalisations(bundle)
        sections.append({"section": "appendix_b", "title": "Appendix B: Complete Formalisation Data",
                        "content": appendix_b, "word_count": len(appendix_b.split()),
                        "confidence": 1.0, "flags": []})

        appendix_c = self._build_appendix_validation(bundle)
        sections.append({"section": "appendix_c", "title": "Appendix C: Validation and Methodology Log",
                        "content": appendix_c, "word_count": len(appendix_c.split()),
                        "confidence": 1.0, "flags": []})

        paper.sections = sections
        paper.total_word_count = sum(s["word_count"] for s in sections)

        # Assemble full markdown
        paper.full_markdown = self._assemble_markdown(paper)

        # Generate keywords
        paper.keywords = self._extract_keywords(bundle)

        # Store metadata
        paper.run_metadata = {
            "model_deep": self.api.config.model_deep,
            "api_calls": self.api.stats.calls,
            "cost_usd": self.api.stats.cost_usd,
        }

        return paper, review

    def review_paper(self, paper: PaperDraft) -> dict:
        """Run adversarial review on a paper draft.

        Reviews the FULL paper body (not truncated). Appendices are summarised
        to keep within context limits while still being assessed.
        """
        # Build review text: full body + appendix summary (not truncated body)
        body_sections = [s for s in paper.sections
                         if not s.get("section", "").startswith("appendix")]
        body_text = "\n\n".join(
            f"## {s.get('title', '')}\n\n{s.get('content', '')}"
            for s in body_sections
        )

        # Appendix summary — enough to assess quality without full data dump
        appendix_summary = "\n\n[APPENDICES PRESENT — summarised for review]\n"
        for s in paper.sections:
            if s.get("section", "").startswith("appendix"):
                title = s.get("title", "")
                wc = s.get("word_count", 0)
                # Include just the "How to Read" section (first ~500 chars)
                content_preview = s.get("content", "")[:500]
                appendix_summary += f"\n### {title} ({wc} words)\n{content_preview}...\n"

        review_text = body_text + appendix_summary

        prompt = REVIEW_PROMPT.format(
            title=paper.title,
            full_text=review_text,
        )

        data = self.api.query_deep_json(prompt, system=SECTION_SYSTEM, max_tokens=4096)

        # Update paper confidence from review
        overall = data.get("overall_quality", 0.5)
        paper.confidence_score = overall
        paper.confidence_category = PaperConfidence.from_score(overall).value

        return data

    def revise_paper(self, paper: PaperDraft, review_result: dict, bundle: PaperBundle) -> PaperDraft:
        """Revise a paper based on review feedback.

        Takes the review issues, rewrites affected sections, and reassembles.
        Only rewrites sections with critical or major issues.
        """
        issues = review_result.get("issues", [])
        if not issues:
            return paper

        # Identify sections needing revision
        sections_to_revise = set()
        for issue in issues:
            severity = issue.get("severity", "minor")
            if severity in ("critical", "major"):
                sections_to_revise.add(issue.get("section", ""))

        if not sections_to_revise:
            return paper

        # Build revision context
        issues_text = "\n".join(
            f"- [{issue.get('severity', 'unknown')}] {issue.get('section', '?')}: "
            f"{issue.get('issue', '')} → Fix: {issue.get('suggested_fix', '')}"
            for issue in issues
            if issue.get("severity") in ("critical", "major")
        )

        # Revise each flagged section
        for i, section in enumerate(paper.sections):
            section_name = section.get("section", "")
            if section_name not in sections_to_revise:
                continue
            if section_name.startswith("appendix"):
                continue  # Appendices are structured data, not AI-revised

            original_content = section.get("content", "")

            prompt = REVISION_PROMPT.format(
                section_title=section.get("title", ""),
                section_content=original_content,
                review_issues=issues_text,
                paper_title=paper.title,
            )

            revised = self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=4096).strip()
            if revised and len(revised) > 100:  # Sanity check — don't replace with garbage
                paper.sections[i]["content"] = revised
                paper.sections[i]["word_count"] = len(revised.split())

        # Reassemble markdown
        paper.total_word_count = sum(s["word_count"] for s in paper.sections)
        paper.full_markdown = self._assemble_markdown(paper)

        return paper

    def verify_completeness(self, bundles: list[PaperBundle],
                            all_convergences: list[dict],
                            all_proofs: list[dict]) -> dict:
        """Verify that ALL convergences and proofs are covered across all bundles.

        Returns a manifest showing coverage. Raises no exceptions — just reports.
        """
        all_conv_ids = {c.get("id", "") for c in all_convergences}
        all_proof_conv_ids = {p.get("convergence_id", "") for p in all_proofs}

        covered_conv_ids = set()
        covered_proof_ids = set()
        paper_assignments = []

        for i, bundle in enumerate(bundles):
            bundle_conv_ids = {c.get("id", "") for c in bundle.convergences}
            bundle_proof_ids = {p.get("id", "") for p in bundle.proofs}
            covered_conv_ids |= bundle_conv_ids
            covered_proof_ids |= bundle_proof_ids

            paper_assignments.append({
                "paper_index": i,
                "theme": bundle.theme,
                "convergences": len(bundle.convergences),
                "proofs": len(bundle.proofs),
                "convergence_ids": sorted(bundle_conv_ids),
            })

        missed_convs = all_conv_ids - covered_conv_ids
        orphan_proofs = all_proof_conv_ids - covered_conv_ids

        manifest = {
            "total_convergences": len(all_conv_ids),
            "covered_convergences": len(covered_conv_ids),
            "missed_convergences": sorted(missed_convs),
            "total_proofs": len(all_proofs),
            "covered_proofs": len(covered_proof_ids),
            "orphan_proof_convergences": sorted(orphan_proofs),
            "total_papers": len(bundles),
            "paper_assignments": paper_assignments,
            "complete": len(missed_convs) == 0,
        }

        return manifest

    # ─── Private composition methods ───

    def _generate_title(self, bundle: PaperBundle) -> str:
        """Generate a paper title from the bundle content."""
        domains = set()
        for c in bundle.convergences:
            for d in c.get("domain_names", c.get("domains", [])):
                domains.add(d)

        domain_str = ", ".join(sorted(domains)[:4])
        n = len(bundle.convergences)
        return f"Cross-Domain Structural Convergences: {domain_str} ({n} Discoveries)"

    def _compose_abstract(self, title: str, theme: str, discoveries: str, proofs: str) -> str:
        prompt = ABSTRACT_PROMPT.format(
            title=title, theme=theme,
            discoveries_summary=discoveries, proofs_summary=proofs,
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=1024).strip()

    def _compose_introduction(self, title: str, abstract: str, theme: str,
                               discoveries: str, corpus_context: str) -> str:
        prompt = INTRODUCTION_PROMPT.format(
            title=title, abstract=abstract, theme=theme,
            discoveries_text=discoveries, corpus_context=corpus_context,
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_methods(self, bundle: PaperBundle) -> str:
        formalisation_types = set()
        apparatus = set()
        for p in bundle.proofs:
            formalisation_types.add(p.get("formalisation_type", "unknown"))
            for a in p.get("mathematical_apparatus", []):
                apparatus.add(a)

        verification_stats = {"verified": 0, "partial": 0, "unverified": 0}
        for p in bundle.proofs:
            if p.get("lean_verified"):
                verification_stats["verified"] += 1
            elif p.get("lean_partial"):
                verification_stats["partial"] += 1
            else:
                verification_stats["unverified"] += 1

        details = (
            f"Formalisation types used: {', '.join(formalisation_types)}\n"
            f"Mathematical apparatus: {', '.join(apparatus)}\n"
            f"Proofs generated: {len(bundle.proofs)}\n"
            f"Lean 4 verification: {verification_stats['verified']} verified, "
            f"{verification_stats['partial']} partial, {verification_stats['unverified']} unverified"
        )

        prompt = METHODS_PROMPT.format(
            discovery_method="Convergent Descent (pairwise structural comparison with EA validation)",
            formalisation_details=details,
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_results(self, bundle: PaperBundle) -> str:
        # Build proof lookup
        proof_by_conv = {}
        for p in bundle.proofs:
            proof_by_conv[p.get("convergence_id", "")] = p

        results_parts = []
        for i, c in enumerate(bundle.convergences):
            claim = c.get("structural_claim", "")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            ea = c.get("ea_scores", {})

            # Full EA scores — all 5 dimensions (not just category)
            ea_text = f"  EA confidence: {ea.get('confidence_category', 'unknown')} ({ea.get('confidence', 'N/A')})"
            for dim in ["strength", "independence", "adversarial", "reproducibility", "depth_consistency"]:
                score = ea.get(dim)
                if isinstance(score, (int, float)):
                    ea_text += f"\n    {dim}: {score:.2f}"

            # Full proof data — proposition, key steps, confidence
            proof_text = "  [No formalisation available — Logos did not produce a proof for this convergence]"
            cid = c.get("id", "")
            p = proof_by_conv.get(cid)
            if p:
                proof_text = (
                    f"  Formalisation type: {p.get('formalisation_type', 'N/A')}\n"
                    f"  Apparatus: {', '.join(p.get('mathematical_apparatus', []))}\n"
                    f"  Verification: {p.get('verification_status', 'N/A')}\n"
                    f"  Proof confidence: {p.get('confidence_score', 'N/A')} ({p.get('confidence_category', 'N/A')})"
                )
                if p.get("proposition_natural"):
                    proof_text += f"\n  Proposition: {p['proposition_natural']}"
                if p.get("proof_natural"):
                    # Include key proof narrative (cap at 500 chars to keep prompt manageable)
                    pn = p["proof_natural"]
                    proof_text += f"\n  Proof narrative: {pn[:500]}{'...' if len(pn) > 500 else ''}"

            # Supporting results summary
            supporting = c.get("supporting_results", [])
            sr_text = ""
            if supporting:
                sr_text = f"\n  Supporting results ({len(supporting)}):"
                for sr in supporting[:4]:  # First 4 for prompt size
                    sr_text += f"\n    - [{sr.get('domain_name', '?')}] {sr.get('result_name', '?')}: {sr.get('structural_conclusion', '')[:100]}"

            results_parts.append(
                f"### Convergence {i+1}: {domains}\n"
                f"**Claim:** {claim}\n"
                f"{ea_text}\n"
                f"{proof_text}"
                f"{sr_text}"
            )

        # Scale target words with convergence count — no arbitrary cap
        target_words = max(500 * len(bundle.convergences), 2000)
        prompt = RESULTS_PROMPT.format(
            results_text="\n\n".join(results_parts),
            target_words=target_words,
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=16384).strip()

    def _compose_discussion(self, title: str, bundle: PaperBundle) -> str:
        # Full claims for ALL convergences (not truncated, not limited)
        results_summary = "\n".join(
            f"- [{', '.join(c.get('domain_names', c.get('domains', [])))}] "
            f"{c.get('structural_claim', '')} "
            f"(confidence: {c.get('ea_scores', {}).get('confidence_category', '?')})"
            for c in bundle.convergences
        )
        themes = set()
        for c in bundle.convergences:
            for cat in c.get("source_categories", []):
                themes.add(cat)

        prompt = DISCUSSION_PROMPT.format(
            title=title,
            results_summary=results_summary,
            themes=", ".join(themes) or bundle.theme or "cross-domain structural convergence",
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=4096).strip()

    def _compose_honest_scope(self, bundle: PaperBundle) -> str:
        # Full claims with confidence — NOT truncated
        results_confidence = []
        for c in bundle.convergences:
            ea = c.get("ea_scores", {})
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            results_confidence.append(
                f"- [{domains}] {c.get('structural_claim', '')} → "
                f"{ea.get('confidence_category', 'unknown')} ({ea.get('confidence', 'N/A')})"
            )

        # ALL limitations (not capped at 3 per proof)
        limitations = []
        verification_status = []
        for p in bundle.proofs:
            if p.get("limitations"):
                for lim in p["limitations"]:
                    if isinstance(lim, dict):
                        limitations.append(f"[{lim.get('severity', '?')}] {lim.get('description', str(lim))}")
                    else:
                        limitations.append(str(lim))
            v_status = p.get("verification_status", "N/A")
            lean_status = "machine-verified" if p.get("lean_verified") else \
                          "partial (contains sorry)" if p.get("lean_partial") else \
                          "natural-language only"
            verification_status.append(
                f"- {p.get('formalisation_type', 'N/A')}: {v_status} (Lean 4: {lean_status})"
            )

        # Count proofless convergences
        proof_conv_ids = {p.get("convergence_id", "") for p in bundle.proofs}
        proofless = [c for c in bundle.convergences if c.get("id", "") not in proof_conv_ids]
        if proofless:
            limitations.append(
                f"{len(proofless)} convergence(s) have no formal proof — "
                f"formalisation was not completed for these discoveries"
            )

        prompt = HONEST_SCOPE_PROMPT.format(
            results_confidence="\n".join(results_confidence),
            limitations="\n".join(f"- {l}" for l in limitations) or "- None identified",
            verification_status="\n".join(verification_status) or "- No proofs included",
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_conclusion(self, title: str, bundle: PaperBundle) -> str:
        # ALL convergences with full claims and confidence
        key_results = "\n".join(
            f"- [{', '.join(c.get('domain_names', c.get('domains', [])))}] "
            f"{c.get('structural_claim', '')} "
            f"({c.get('ea_scores', {}).get('confidence_category', '?')})"
            for c in bundle.convergences
        )
        prompt = CONCLUSION_PROMPT.format(title=title, key_results=key_results)
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_references(self, bundle: PaperBundle) -> str:
        # Collect all citations from proofs
        citations = []
        for p in bundle.proofs:
            for dep in p.get("dependencies_literature", []):
                citations.append(
                    f"  {dep.get('name', '')}, {dep.get('authors', '')}, "
                    f"{dep.get('year', '')} ({dep.get('field', '')})"
                )

        prompt = REFERENCES_PROMPT.format(
            citations_used="\n".join(citations) or "No external citations used.",
        )
        return self.api.query(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _assemble_markdown(self, paper: PaperDraft) -> str:
        """Assemble the full paper markdown from sections."""
        parts = [
            f"---",
            f"title: \"{paper.title}\"",
            f"author: \"{', '.join(paper.authors)}\"",
            f"date: \"{paper.date}\"",
            f"keywords: [{', '.join(paper.keywords)}]",
            f"---",
            f"",
            f"# {paper.title}",
            f"",
            f"**{', '.join(paper.authors)}**",
            f"",
            f"*{paper.date}*",
            f"",
        ]

        for section in paper.sections:
            parts.append(f"## {section.get('title', '')}")
            parts.append("")
            parts.append(section.get("content", ""))
            parts.append("")

        return "\n".join(parts)

    def _build_discoveries_summary(self, bundle: PaperBundle) -> str:
        lines = []
        for c in bundle.convergences:
            claim = c.get("structural_claim", "")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            ea = c.get("ea_scores", {})
            lines.append(f"- [{domains}] {claim[:100]} (confidence: {ea.get('confidence_category', 'N/A')})")
        return "\n".join(lines)

    def _build_proofs_summary(self, bundle: PaperBundle) -> str:
        lines = []
        for p in bundle.proofs:
            lines.append(
                f"- Type: {p.get('formalisation_type', 'N/A')}, "
                f"Apparatus: {', '.join(p.get('mathematical_apparatus', []))}, "
                f"Verification: {p.get('verification_status', 'N/A')}, "
                f"Confidence: {p.get('confidence_category', 'N/A')}"
            )
        return "\n".join(lines) or "No proofs available."

    def _load_corpus_context(self) -> str:
        """Load summaries of existing corpus papers for context.

        Reads both pre-existing corpus papers AND papers generated earlier in
        this same run, so each new paper is aware of what came before it.
        """
        if not self.corpus_papers_dir or not self.corpus_papers_dir.exists():
            return "No prior corpus papers available."

        papers = []
        for path in sorted(self.corpus_papers_dir.glob("*.md")):
            content = path.read_text()
            # Extract title (first H1) and abstract
            title = ""
            abstract = ""
            in_abstract = False
            for line in content.split("\n"):
                if line.startswith("# ") and not title:
                    title = line[2:].strip()
                elif "abstract" in line.lower() and line.startswith("##"):
                    in_abstract = True
                elif in_abstract and line.startswith("##"):
                    in_abstract = False
                elif in_abstract:
                    abstract += line + " "

            summary = abstract.strip()[:300] if abstract.strip() else " ".join(content.split("\n")[:5])[:300]
            papers.append(f"- **{title or path.stem}**: {summary}")

        return "\n".join(papers) if papers else "No prior corpus papers available."

    def _extract_keywords(self, bundle: PaperBundle) -> list[str]:
        """Extract keywords from the bundle."""
        keywords = set()
        for c in bundle.convergences:
            for d in c.get("domain_names", c.get("domains", [])):
                keywords.add(d)
            ctype = c.get("convergence_type", "")
            if ctype:
                keywords.add(ctype)
        keywords.add("cross-domain convergence")
        keywords.add("Convergence Codex")
        return sorted(keywords)[:10]

    # ─── Appendix builders (structured data, not AI-generated) ───

    def _build_appendix_discoveries(self, bundle: PaperBundle) -> str:
        """Appendix A: Complete Gnosis discovery data — nothing truncated."""
        parts = [
            "*This appendix contains the complete discovery data from Gnosis AI for every "
            "convergence in this paper. No data has been truncated or summarised.*\n",
            "## How to Read This Appendix\n",
            "Each convergence entry below contains:\n",
            "- **Structural Claim**: The specific structural parallel discovered between two or more domains. "
            "This is the core finding — the claim that domain A and domain B share a common mathematical structure.\n",
            "- **EA Validation Scores**: The Epistemic Assurance (EA) engine tests every discovery across 5 independent "
            "dimensions before it enters the pipeline. Scores range from 0.0 (no evidence) to 1.0 (overwhelming evidence):\n",
            "  - *Strength*: How strong is the structural parallel? (Do the mathematical structures genuinely correspond, "
            "or is the similarity superficial?)\n",
            "  - *Independence*: Could this parallel arise by coincidence? (A low score means it might be a mathematical "
            "artefact; a high score means the parallel is unlikely to be coincidental.)\n",
            "  - *Adversarial*: Does the convergence survive deliberate attack? (The EA engine tries to disprove it.)\n",
            "  - *Reproducibility*: Would a different analysis find the same result? (Tests robustness to methodological "
            "variation.)\n",
            "  - *Depth-consistency*: Does the parallel hold at deeper levels of analysis, or only at the surface?\n",
            "  - *Overall confidence*: Weighted aggregate. Categories: **high** (>0.7), **medium** (0.4-0.7), "
            "**preliminary** (0.2-0.4), **speculative** (<0.2).\n",
            "- **Supporting Results**: The specific results from each domain that underpin the convergence. "
            "Each shows the domain, the specific result, its structural conclusion, and its epistemic status "
            "(how well-established it is within its own field).\n",
            "---\n",
        ]

        for i, c in enumerate(bundle.convergences):
            cid = c.get("id", "unknown")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            ea = c.get("ea_scores", {})

            parts.append(f"### A.{i+1} Convergence `{cid}`\n")
            parts.append(f"**Domains:** {domains}")
            parts.append(f"**Type:** {c.get('convergence_type', 'N/A')}")
            parts.append(f"**Discovery level:** {c.get('discovered_at_level', 'N/A')}")
            parts.append(f"**Discovered in run:** {c.get('discovered_in_run', 'N/A')}")
            parts.append(f"**Timestamp:** {c.get('timestamp', 'N/A')}\n")

            # Full structural claim — NOT truncated
            parts.append(f"**Structural Claim:**\n> {c.get('structural_claim', 'N/A')}\n")

            # Full EA scores — all 5 dimensions
            if ea:
                parts.append("**EA Validation Scores:**")
                parts.append(f"| Dimension | Score |")
                parts.append(f"|-----------|-------|")
                for dim in ["strength", "independence", "adversarial", "reproducibility", "depth_consistency"]:
                    score = ea.get(dim, "N/A")
                    if isinstance(score, float):
                        parts.append(f"| {dim} | {score:.3f} |")
                    else:
                        parts.append(f"| {dim} | {score} |")
                parts.append(f"| **Overall confidence** | **{ea.get('confidence', 'N/A')}** ({ea.get('confidence_category', 'N/A')}) |")
                parts.append("")

            # Full supporting results — every one, not truncated
            results = c.get("supporting_results", [])
            if results:
                parts.append(f"**Supporting Results ({len(results)}):**\n")
                for j, r in enumerate(results):
                    domain = r.get("domain_name", r.get("domain_id", "unknown"))
                    parts.append(f"**{j+1}. [{domain}] {r.get('result_name', 'unnamed')}**")
                    parts.append(f"- Conclusion: {r.get('structural_conclusion', 'N/A')}")
                    parts.append(f"- Epistemic status: {r.get('epistemic_status', 'N/A')}")
                    if r.get("mathematical_structure"):
                        parts.append(f"- Mathematical structure: {r.get('mathematical_structure')}")
                    parts.append("")

            parts.append("---\n")

        return "\n".join(parts)

    def _build_appendix_formalisations(self, bundle: PaperBundle) -> str:
        """Appendix B: Complete Logos formalisation data — proofs, Lean code, everything."""
        parts = [
            "*This appendix contains the complete formalisation data from Logos AI for every "
            "proof in this paper, including formal propositions, proof steps, Lean 4 code, "
            "assumptions, limitations, and literature dependencies.*\n",
            "## How to Read This Appendix\n",
            "Each proof entry below takes a discovery from Appendix A and attempts to establish it formally. "
            "The formalisation process involves:\n",
            "1. **Type detection**: What kind of mathematical relationship is this? (e.g. categorical equivalence, "
            "topological homeomorphism, algebraic isomorphism, information-theoretic bound)\n",
            "2. **Apparatus selection**: What mathematical tools are needed? (e.g. category theory, differential "
            "geometry, spectral theory) — with justification for why this apparatus was chosen\n",
            "3. **Proof generation**: A formal proposition is stated, then proved in natural language "
            "(step-by-step with justifications) and, where possible, in Lean 4 (a machine-verifiable proof language)\n",
            "4. **Verification**: Each proof step is checked for logical soundness\n",
            "\n**Reading the Lean 4 code**: Lean 4 is a formal proof assistant. Code beginning with `theorem` or "
            "`lemma` states what is being proved. Lines beginning with `sorry` indicate steps that the system could "
            "not yet formalise — this is honest incompleteness, not an error. If a proof compiles without `sorry`, "
            "it has been machine-verified to be logically sound.\n",
            "\n**Confidence levels**: Each proof carries a confidence score (0.0-1.0) reflecting the strength of "
            "the formalisation. A high score means the proof is logically sound and well-supported; a lower score "
            "means the proof has gaps or relies on assumptions that need further justification.\n",
            "---\n",
        ]

        for i, p in enumerate(bundle.proofs):
            pid = p.get("id", "unknown")
            cid = p.get("convergence_id", "unknown")

            parts.append(f"### B.{i+1} Proof `{pid}` (Convergence `{cid}`)\n")
            parts.append(f"**Formalisation type:** {p.get('formalisation_type', 'N/A')}")
            parts.append(f"**Mathematical apparatus:** {', '.join(p.get('mathematical_apparatus', []))}")
            parts.append(f"**Apparatus justification:** {p.get('apparatus_justification', 'N/A')}")
            parts.append(f"**Verification status:** {p.get('verification_status', 'N/A')}")
            parts.append(f"**Confidence:** {p.get('confidence_score', 'N/A')} ({p.get('confidence_category', 'N/A')})")
            parts.append(f"**Within standard mathematics:** {p.get('within_standard_mathematics', 'N/A')}\n")

            if p.get("new_mathematics_needed"):
                parts.append(f"**New mathematics needed:** {p['new_mathematics_needed']}\n")

            # Formal proposition
            if p.get("proposition"):
                parts.append(f"**Formal Proposition:**\n```\n{p['proposition']}\n```\n")

            # Natural language proposition
            if p.get("proposition_natural"):
                parts.append(f"**Natural Language Proposition:**\n> {p['proposition_natural']}\n")

            # Assumptions
            assumptions = p.get("assumptions", [])
            if assumptions:
                parts.append(f"**Assumptions ({len(assumptions)}):**")
                for a in assumptions:
                    parts.append(f"- {a}")
                parts.append("")

            # Full proof steps
            steps = p.get("proof_steps", [])
            if steps:
                parts.append(f"**Proof Steps ({len(steps)}):**\n")
                for s in steps:
                    num = s.get("step_number", "?")
                    parts.append(f"**Step {num}:** {s.get('statement', '')}")
                    if s.get("justification"):
                        parts.append(f"  *Justification:* {s['justification']}")
                    if s.get("dependencies"):
                        deps = s["dependencies"]
                        if isinstance(deps, list):
                            parts.append(f"  *Dependencies:* {', '.join(str(d) for d in deps)}")
                    parts.append("")

            # Natural language proof
            if p.get("proof_natural"):
                parts.append(f"**Natural Language Proof:**\n\n{p['proof_natural']}\n")

            # Lean 4 code
            if p.get("proof_lean"):
                parts.append(f"**Lean 4 Code:**\n```lean\n{p['proof_lean']}\n```\n")
                if p.get("lean_verified"):
                    parts.append("*Status: Machine-verified*\n")
                elif p.get("lean_partial"):
                    parts.append("*Status: Partially verified (contains sorry)*\n")
                else:
                    reason = p.get("lean_failure_reason", "Lean 4 not available for verification")
                    parts.append(f"*Status: Unverified — {reason}*\n")

            # Literature dependencies
            deps = p.get("dependencies_literature", [])
            if deps:
                parts.append(f"**Literature Dependencies ({len(deps)}):**")
                for d in deps:
                    parts.append(f"- {d.get('name', 'unnamed')}: {d.get('statement', '')}")
                    if d.get("authors"):
                        parts.append(f"  Authors: {d['authors']}, {d.get('year', '')}")
                parts.append("")

            # Limitations and gaps
            limitations = p.get("limitations", [])
            if limitations:
                parts.append(f"**Limitations and Gaps ({len(limitations)}):**")
                for lim in limitations:
                    if isinstance(lim, dict):
                        parts.append(f"- [{lim.get('severity', 'unknown')}] {lim.get('description', str(lim))}")
                    else:
                        parts.append(f"- {lim}")
                parts.append("")

            parts.append("---\n")

        return "\n".join(parts)

    def _build_appendix_validation(self, bundle: PaperBundle) -> str:
        """Appendix C: Validation results and methodology reasoning log."""
        parts = [
            "*This appendix contains the complete adversarial validation results and "
            "the Logos AI reasoning log showing how each formalisation decision was made. "
            "This provides full methodological transparency.*\n",
            "## How to Read This Appendix\n",
            "This appendix serves two purposes: **validation evidence** and **methodological transparency**.\n",
            "### Validation Evidence\n",
            "Each proof undergoes a 5-layer validation pipeline. The layers are independent and weighted:\n",
            "| Layer | Weight | What It Tests |\n",
            "|-------|--------|---------------|\n",
            "| Mechanical (Layer 1) | 30% | Does each proof step follow logically from the previous? Are there gaps in reasoning? |\n",
            "| Adversarial (Layer 2) | 25% | A separate AI deliberately tries to break the proof. What attacks succeed? |\n",
            "| Internal consistency (Layer 3) | 20% | Does the proof actually prove what it claims to prove? |\n",
            "| Cross-proof consistency (Layer 4) | 15% | Do multiple proofs in the same paper contradict each other? |\n",
            "| Calibration (Layer 5) | 10% | Are the confidence scores well-calibrated against the actual evidence? |\n",
            "\nThe overall confidence score is the weighted sum. **High** (>0.7) means the proof is robust; "
            "**medium** (0.4-0.7) means it is plausible but has identifiable gaps; **low** (<0.4) means "
            "significant issues remain.\n",
            "### Methodological Transparency\n",
            "The **Formaliser Reasoning Logs** show every decision the AI made during formalisation — what "
            "type of proof to attempt, which mathematical apparatus to use, which proof strategy to follow — "
            "along with the alternatives it considered and why they were rejected. This allows human reviewers "
            "to audit not just the final proof but the entire reasoning process that produced it.\n",
            "### Human Review Flags\n",
            "Some proofs are automatically flagged for human review. Reasons include: low confidence, novel "
            "mathematical claims, high complexity, or adversarial review concerns. Each flag includes the "
            "specific reason and suggested domain expertise for the reviewer.\n",
            "---\n",
        ]

        for i, p in enumerate(bundle.proofs):
            pid = p.get("id", "unknown")
            cid = p.get("convergence_id", "unknown")

            parts.append(f"### C.{i+1} Validation for Proof `{pid}` (Convergence `{cid}`)\n")

            # 5-layer confidence breakdown
            breakdown = p.get("confidence_breakdown", {})
            if breakdown:
                parts.append("**5-Layer Confidence Breakdown:**")
                parts.append("| Layer | Weight | Score |")
                parts.append("|-------|--------|-------|")
                weights = {"mechanical": 0.30, "adversarial": 0.25, "internal": 0.20,
                          "cross_proof": 0.15, "calibration": 0.10}
                for layer in ["mechanical", "adversarial", "internal", "cross_proof", "calibration"]:
                    score = breakdown.get(layer, "N/A")
                    w = weights.get(layer, "?")
                    if isinstance(score, float):
                        parts.append(f"| {layer} | {w} | {score:.3f} |")
                    else:
                        parts.append(f"| {layer} | {w} | {score} |")
                parts.append(f"| **Overall** | **1.00** | **{p.get('confidence_score', 'N/A')}** |")
                parts.append("")

            # Adversarial attack results
            adv = p.get("adversarial_result", {})
            if adv:
                parts.append("**Adversarial Review (Layer 2):**")
                parts.append(f"- Proof soundness: {adv.get('proof_soundness', 'N/A')}")
                parts.append(f"- Overall assessment: {adv.get('overall_assessment', 'N/A')}")
                parts.append(f"- Verdict: {adv.get('verdict', 'N/A')}")
                gaps = adv.get("gaps", [])
                if gaps:
                    parts.append(f"- Gaps found ({len(gaps)}):")
                    for g in gaps:
                        if isinstance(g, dict):
                            parts.append(f"  - [{g.get('severity', '?')}] {g.get('description', str(g))}")
                        else:
                            parts.append(f"  - {g}")
                strengths = adv.get("strengths", [])
                if strengths:
                    parts.append(f"- Strengths noted ({len(strengths)}):")
                    for s in strengths:
                        parts.append(f"  - {s}")
                parts.append("")

            # Internal consistency
            internal = p.get("internal_consistency", {})
            if internal:
                parts.append("**Internal Consistency (Layer 3):**")
                parts.append(f"- Score: {internal.get('internal_score', 'N/A')}")
                parts.append(f"- Proves stated proposition: {internal.get('proves_stated_proposition', 'N/A')}")
                if internal.get("issues"):
                    parts.append(f"- Issues: {internal['issues']}")
                parts.append("")

            # Cross-proof consistency
            cross = p.get("cross_proof_consistency", {})
            if cross:
                parts.append("**Cross-Proof Consistency (Layer 4):**")
                parts.append(f"- Score: {cross.get('consistency_score', 'N/A')}")
                parts.append(f"- Contradictions found: {cross.get('contradictions_found', 'N/A')}")
                if cross.get("notes"):
                    parts.append(f"- Notes: {cross['notes']}")
                parts.append("")

            parts.append("---\n")

        # Reasoning logs (from Logos formaliser — how/why each decision was made)
        has_logs = any(p.get("_reasoning_log") for p in bundle.proofs)
        if has_logs:
            parts.append("## Formaliser Reasoning Logs\n")
            parts.append("*Complete decision log from Logos AI showing how each formalisation "
                        "decision was made, including alternatives considered and reasons for rejection.*\n")

            for i, p in enumerate(bundle.proofs):
                rlog = p.get("_reasoning_log", {})
                decisions = rlog.get("decisions", [])
                if not decisions:
                    continue

                pid = p.get("id", "unknown")
                parts.append(f"### Proof `{pid}` — {len(decisions)} decisions\n")

                for d in decisions:
                    parts.append(f"**{d.get('step', 'unknown')}**")
                    parts.append(f"- Choice: {d.get('choice', 'N/A')}")
                    if d.get("reasoning"):
                        parts.append(f"- Reasoning: {d['reasoning']}")
                    alts = d.get("alternatives_considered", [])
                    if alts:
                        parts.append(f"- Alternatives considered:")
                        for alt in alts:
                            if alt:
                                parts.append(f"  - {alt}")
                    parts.append("")

                parts.append("---\n")

        # Flag data (human review requirements)
        has_flags = any(p.get("_flag_data") for p in bundle.proofs)
        if has_flags:
            parts.append("## Human Review Flags\n")
            for i, p in enumerate(bundle.proofs):
                flag = p.get("_flag_data", {})
                if not flag or not flag.get("requires_human_review"):
                    continue

                pid = p.get("id", "unknown")
                parts.append(f"**Proof `{pid}`:** Review priority: {flag.get('review_priority', 'N/A')}")
                for reason in flag.get("review_reasons", []):
                    parts.append(f"- {reason}")
                expertise = flag.get("suggested_expertise", [])
                if expertise:
                    parts.append(f"- Suggested expertise: {', '.join(expertise)}")
                parts.append("")

        # Methodology notes
        parts.append("## Methodology Notes\n")
        parts.append("**Discovery Pipeline:** Gnosis AI (Convergence Intelligence engine + "
                     "Epistemic Assurance engine) → Logos AI (formalisation + 5-layer validation) "
                     "→ Synthesis AI (paper composition + adversarial review)\n")
        parts.append("**Models used:** Claude Opus 4 for deep reasoning (type detection, proof "
                     "generation, adversarial review), Claude Sonnet 4 for supporting operations\n")

        for p in bundle.proofs[:1]:  # Show metadata from first proof
            meta = p.get("run_metadata", {})
            if meta:
                parts.append(f"**Run metadata (sample):** Model deep: {meta.get('model_deep', 'N/A')}, "
                           f"Model fast: {meta.get('model_fast', 'N/A')}, "
                           f"API calls: {meta.get('api_calls', 'N/A')}, "
                           f"Cost: ${meta.get('cost_usd', 0):.2f}")

        return "\n".join(parts)
