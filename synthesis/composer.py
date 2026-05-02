"""The Composer — core Synthesis engine.

Takes a bundle of discoveries + proofs and produces a publication-quality paper draft.
Stages: boundary detection → section composition → assembly → review → output.
"""

from __future__ import annotations

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
from synthesis.prompts.review import REVIEW_PROMPT


class Composer:
    """Core paper composition engine."""

    def __init__(self, api: ClaudeAPI, corpus_papers_dir: Path | None = None):
        self.api = api
        self.corpus_papers_dir = corpus_papers_dir

    def detect_boundaries(
        self, convergences: list[dict], proofs: list[dict], findings: list[dict]
    ) -> list[PaperBundle]:
        """Auto-detect appropriate paper boundaries.

        Groups convergences/proofs into bundles, each becoming one paper.
        """
        if len(convergences) <= 10:
            # Small enough for a single paper
            bundle = PaperBundle(
                convergences=convergences,
                proofs=proofs,
                findings=findings,
            )
            return [bundle]

        # Use Claude to determine groupings
        domain_pairs = {}
        for c in convergences:
            domains = tuple(sorted(c.get("domain_names", c.get("domains", []))))
            key = " × ".join(domains)
            domain_pairs[key] = domain_pairs.get(key, 0) + 1

        proof_types = {}
        for p in proofs:
            t = p.get("formalisation_type", "unknown")
            proof_types[t] = proof_types.get(t, 0) + 1

        finding_levels = {}
        for f in findings:
            lvl = f.get("level", 0)
            finding_levels[str(lvl)] = finding_levels.get(str(lvl), 0) + 1

        prompt = BOUNDARY_PROMPT.format(
            n_convergences=len(convergences),
            domain_pairs_text="\n".join(f"  {k}: {v}" for k, v in sorted(domain_pairs.items(), key=lambda x: -x[1])),
            n_proofs=len(proofs),
            proof_types_text="\n".join(f"  {k}: {v}" for k, v in proof_types.items()),
            n_findings=len(findings),
            findings_levels_text="\n".join(f"  Level {k}: {v}" for k, v in finding_levels.items()),
            min_words=self.api.config.target_word_count_min,
            max_words=self.api.config.target_word_count_max,
        )

        data = self.api.query_deep_json(prompt, system=SECTION_SYSTEM)

        # Build bundles from boundary decision
        conv_by_id = {c.get("id", ""): c for c in convergences}
        proof_by_id = {p.get("id", ""): p for p in proofs}
        finding_by_id = {f.get("id", ""): f for f in findings}

        bundles = []
        for paper_spec in data.get("papers", []):
            bundle = PaperBundle(
                convergences=[conv_by_id[cid] for cid in paper_spec.get("convergence_ids", []) if cid in conv_by_id],
                proofs=[proof_by_id[pid] for pid in paper_spec.get("proof_ids", []) if pid in proof_by_id],
                findings=[finding_by_id[fid] for fid in paper_spec.get("finding_ids", []) if fid in finding_by_id],
                theme=paper_spec.get("theme", ""),
                target_structure=paper_spec.get("title_suggestion", ""),
            )
            if bundle.convergences:
                bundles.append(bundle)

        return bundles if bundles else [PaperBundle(convergences=convergences, proofs=proofs, findings=findings)]

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
        """Run adversarial review on a paper draft."""

        prompt = REVIEW_PROMPT.format(
            title=paper.title,
            full_text=paper.full_markdown[:15000],  # Limit for context
        )

        data = self.api.query_deep_json(prompt, system=SECTION_SYSTEM, max_tokens=4096)

        # Update paper confidence from review
        overall = data.get("overall_quality", 0.5)
        paper.confidence_score = overall
        paper.confidence_category = PaperConfidence.from_score(overall).value

        return data

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

        details = (
            f"Formalisation types used: {', '.join(formalisation_types)}\n"
            f"Mathematical apparatus: {', '.join(apparatus)}\n"
            f"Proofs generated: {len(bundle.proofs)}"
        )

        prompt = METHODS_PROMPT.format(
            discovery_method="Convergent Descent (pairwise structural comparison with EA validation)",
            formalisation_details=details,
        )
        return self.api.query(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_results(self, bundle: PaperBundle) -> str:
        results_parts = []
        for i, c in enumerate(bundle.convergences):
            claim = c.get("structural_claim", "")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            ea = c.get("ea_scores", {})
            conf = ea.get("confidence_category", "unknown")

            proof_text = ""
            cid = c.get("id", "")
            for p in bundle.proofs:
                if p.get("convergence_id") == cid:
                    proof_text = (
                        f"  Formalisation: {p.get('formalisation_type', 'N/A')}\n"
                        f"  Apparatus: {', '.join(p.get('mathematical_apparatus', []))}\n"
                        f"  Verification: {p.get('verification_status', 'N/A')}\n"
                        f"  Proof confidence: {p.get('confidence_category', 'N/A')}"
                    )
                    break

            results_parts.append(
                f"### Convergence {i+1}: {domains}\n"
                f"**Claim:** {claim}\n"
                f"**EA confidence:** {conf}\n"
                f"{proof_text}"
            )

        target_words = min(400 * len(bundle.convergences), 3000)
        prompt = RESULTS_PROMPT.format(
            results_text="\n\n".join(results_parts),
            target_words=target_words,
        )
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=8192).strip()

    def _compose_discussion(self, title: str, bundle: PaperBundle) -> str:
        results_summary = "\n".join(
            f"- {c.get('structural_claim', '')[:100]}"
            for c in bundle.convergences[:10]
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
        return self.api.query_deep(prompt, system=SECTION_SYSTEM, max_tokens=2048).strip()

    def _compose_honest_scope(self, bundle: PaperBundle) -> str:
        # Build confidence and limitation summaries
        results_confidence = []
        for c in bundle.convergences:
            ea = c.get("ea_scores", {})
            results_confidence.append(
                f"- {c.get('structural_claim', '')[:60]}... → {ea.get('confidence_category', 'unknown')}"
            )

        limitations = []
        verification_status = []
        for p in bundle.proofs:
            if p.get("limitations"):
                limitations.extend(p["limitations"][:3])
            verification_status.append(
                f"- {p.get('formalisation_type', 'N/A')}: {p.get('verification_status', 'N/A')}"
            )

        prompt = HONEST_SCOPE_PROMPT.format(
            results_confidence="\n".join(results_confidence),
            limitations="\n".join(f"- {l}" for l in limitations) or "- None identified",
            verification_status="\n".join(verification_status) or "- No proofs included",
        )
        return self.api.query(prompt, system=SECTION_SYSTEM, max_tokens=1024).strip()

    def _compose_conclusion(self, title: str, bundle: PaperBundle) -> str:
        key_results = "\n".join(
            f"- {c.get('structural_claim', '')[:80]}"
            for c in bundle.convergences[:5]
        )
        prompt = CONCLUSION_PROMPT.format(title=title, key_results=key_results)
        return self.api.query(prompt, system=SECTION_SYSTEM, max_tokens=1024).strip()

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
        """Load summaries of existing corpus papers for context."""
        if not self.corpus_papers_dir or not self.corpus_papers_dir.exists():
            return "No prior corpus papers available."

        papers = []
        for path in sorted(self.corpus_papers_dir.glob("*.md")):
            content = path.read_text()
            # Extract first few lines as summary
            lines = content.split("\n")[:5]
            papers.append(f"- {path.stem}: {' '.join(lines)[:150]}")

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
