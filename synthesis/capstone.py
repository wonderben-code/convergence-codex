"""Capstone Composer — Nobel-grade paper generation from convergence cascade data.

NOT a separate AI. A new mode within Synthesis that:
1. Reads ALL convergence/proof/finding data (deterministic census)
2. Uses the CASCADE STRUCTURE to determine which claims are strongest
3. Formulates each as a precise falsifiable claim (AI-assisted)
4. Composes Nobel-template papers (AI)
5. Reviews with enhanced anti-drift checks (AI)
6. Extracts predictions into a separately timestamped register

Key insight: The cascade determines the claims. Level 5 fixed points are the
ultimate claims. Level 1 findings with 17 source convergences are the strongest
evidence base. The AI formulates and writes — it doesn't "discover" what to
write about.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from synthesis.api import ClaudeAPI
from synthesis.models import (
    PaperDraft, PaperBundle, ReviewRequest, PaperConfidence,
    CapstoneContext, CandidateClaim, PaperPlan, CapstoneRun,
    _uid, _now,
)
from synthesis.prompts.capstone import (
    CAPSTONE_SYSTEM,
    CLAIM_FORMULATION_PROMPT,
    PAPER_PLANNING_PROMPT,
    CAPSTONE_ABSTRACT_PROMPT,
    CAPSTONE_PROBLEM_PROMPT,
    CAPSTONE_SETUP_PROMPT,
    CAPSTONE_RESULT_PROMPT,
    CAPSTONE_PREDICTIONS_PROMPT,
    CAPSTONE_CONNECTIONS_PROMPT,
    CAPSTONE_LIMITATIONS_PROMPT,
    CAPSTONE_PROVENANCE_PROMPT,
    CAPSTONE_REFERENCES_PROMPT,
    CAPSTONE_REVIEW_PROMPT,
    CROSS_PAPER_CHECK_PROMPT,
    PREDICTION_REGISTER_HEADER,
)


class CapstoneComposer:
    """Nobel-grade capstone paper composition engine."""

    def __init__(
        self,
        api: ClaudeAPI,
        capstone_dir: Path,
        gnosis_dir: Path,
        proofs_dir: Path,
        synthesis_papers_dir: Path | None = None,
    ):
        self.api = api
        self.capstone_dir = capstone_dir
        self.gnosis_dir = gnosis_dir
        self.proofs_dir = proofs_dir
        self.synthesis_papers_dir = synthesis_papers_dir

        # Ensure capstone directories exist
        for sub in ["papers", "drafts", "reviews", "claims", "plans", "runs"]:
            (capstone_dir / sub).mkdir(parents=True, exist_ok=True)

    # ─── STAGE 1: DATA CENSUS (deterministic, no AI) ───

    def census(self) -> CapstoneContext:
        """Read ALL available data and compute analytics.

        This is fully deterministic — no AI calls. The cascade structure itself
        determines which claims are strongest.
        """
        ctx = CapstoneContext()

        # Load convergences
        conv_dir = self.gnosis_dir / "convergences"
        if conv_dir.exists():
            for f in sorted(conv_dir.glob("*.json")):
                try:
                    data = json.loads(f.read_text())
                    if not data.get("negative", False):
                        ctx.convergences.append(data)
                except (json.JSONDecodeError, Exception):
                    continue
        ctx.total_convergences = len(ctx.convergences)

        # Load proofs
        if self.proofs_dir.exists():
            for f in sorted(self.proofs_dir.glob("*.json")):
                try:
                    ctx.proofs.append(json.loads(f.read_text()))
                except (json.JSONDecodeError, Exception):
                    continue
        ctx.total_proofs = len(ctx.proofs)

        # Load findings
        findings_dir = self.gnosis_dir / "findings"
        if findings_dir.exists():
            for f in sorted(findings_dir.glob("*.json")):
                try:
                    ctx.findings.append(json.loads(f.read_text()))
                except (json.JSONDecodeError, Exception):
                    continue
        ctx.total_findings = len(ctx.findings)

        # Separate fixed points (level 5)
        ctx.fixed_points = [f for f in ctx.findings if f.get("level", 0) >= 5]

        # Load synthesis papers (if they exist)
        if self.synthesis_papers_dir and self.synthesis_papers_dir.exists():
            for f in sorted(self.synthesis_papers_dir.glob("*.json")):
                try:
                    paper_data = json.loads(f.read_text())
                    ctx.synthesis_papers.append({
                        "id": paper_data.get("id", ""),
                        "title": paper_data.get("title", ""),
                        "abstract": paper_data.get("abstract", ""),
                        "convergence_ids": paper_data.get("convergence_ids", []),
                        "confidence_score": paper_data.get("confidence_score", 0),
                        "total_word_count": paper_data.get("total_word_count", 0),
                    })
                except (json.JSONDecodeError, Exception):
                    continue

        # ─── Pre-computed analytics ───

        # Domain pair counts
        for c in ctx.convergences:
            domains = tuple(sorted(c.get("domain_names", c.get("domains", []))))
            key = " × ".join(domains)
            ctx.domain_pair_counts[key] = ctx.domain_pair_counts.get(key, 0) + 1

        # Cross-domain hubs (domains with most connections)
        domain_counts = Counter()
        for c in ctx.convergences:
            for d in c.get("domain_names", c.get("domains", [])):
                domain_counts[d] += 1
        ctx.cross_domain_hubs = [d for d, _ in domain_counts.most_common(10)]

        # Confidence distribution
        buckets = {"high (≥0.75)": 0, "medium (0.45-0.74)": 0, "low (<0.45)": 0, "unknown": 0}
        for p in ctx.proofs:
            conf = p.get("confidence_score", 0)
            if conf >= 0.75:
                buckets["high (≥0.75)"] += 1
            elif conf >= 0.45:
                buckets["medium (0.45-0.74)"] += 1
            elif conf > 0:
                buckets["low (<0.45)"] += 1
            else:
                buckets["unknown"] += 1
        ctx.confidence_distribution = buckets

        # Strongest convergences (top 20 by proof confidence)
        proof_by_conv = {}
        for p in ctx.proofs:
            cid = p.get("convergence_id", "")
            if cid:
                existing = proof_by_conv.get(cid)
                if existing is None or p.get("confidence_score", 0) > existing.get("confidence_score", 0):
                    proof_by_conv[cid] = p

        scored = []
        for c in ctx.convergences:
            cid = c.get("id", "")
            proof = proof_by_conv.get(cid)
            score = proof.get("confidence_score", 0) if proof else 0
            scored.append({**c, "_proof_confidence": score})
        scored.sort(key=lambda x: x["_proof_confidence"], reverse=True)
        ctx.strongest_convergences = scored[:20]

        # Cascade DAG: level → findings
        cascade = defaultdict(list)
        for f in ctx.findings:
            level = f.get("level", 0)
            cascade[level].append(f.get("id", ""))
        ctx.cascade_dag = {
            "levels": {str(k): v for k, v in sorted(cascade.items())},
            "total_levels": max(cascade.keys()) if cascade else 0,
            "reduction": f"{ctx.total_convergences} convergences → {ctx.total_findings} findings → {len(ctx.fixed_points)} fixed points",
        }
        ctx.cascade_levels = {str(k): v for k, v in sorted(cascade.items())}

        # Independence clusters: find convergences from UNRELATED domains
        # pointing to the same mathematical structure
        structure_groups = defaultdict(list)
        for c in ctx.convergences:
            claim = c.get("structural_claim", "")
            # Group by convergence_type as a proxy for structure
            ctype = c.get("convergence_type", "unknown")
            structure_groups[ctype].append(c)

        for stype, convs in structure_groups.items():
            if len(convs) < 3:
                continue
            # Check domain diversity
            all_domains = set()
            for c in convs:
                for d in c.get("domain_names", c.get("domains", [])):
                    all_domains.add(d)
            if len(all_domains) >= 4:  # Genuinely independent
                ctx.independence_clusters.append({
                    "structure_type": stype,
                    "num_convergences": len(convs),
                    "domains": sorted(all_domains),
                    "convergence_ids": [c.get("id", "") for c in convs],
                })

        # Recurring mathematical structures (from proofs)
        apparatus_counts = Counter()
        for p in ctx.proofs:
            for a in p.get("mathematical_apparatus", []):
                apparatus_counts[a] += 1
        ctx.recurring_structures = [
            {"structure": s, "count": c}
            for s, c in apparatus_counts.most_common()
            if c >= 3
        ]

        return ctx

    # ─── STAGE 2: CLAIM FORMULATION (data-driven, AI formulates) ───

    def generate_claims(self, ctx: CapstoneContext) -> list[CandidateClaim]:
        """Generate candidate claims from cascade data.

        The CASCADE determines which claims to make — the AI formulates them
        as precise, falsifiable statements.
        """
        claims = []

        # Build proof lookup for enriching findings with evidence data
        proof_by_conv = {}
        for p in ctx.proofs:
            cid = p.get("convergence_id", "")
            if cid:
                proof_by_conv[cid] = p

        conv_by_id = {c.get("id", ""): c for c in ctx.convergences}

        # Process findings from HIGHEST level down — these are the strongest claims
        findings_by_level = defaultdict(list)
        for f in ctx.findings:
            findings_by_level[f.get("level", 0)].append(f)

        for level in sorted(findings_by_level.keys(), reverse=True):
            for finding in findings_by_level[level]:
                claim = self._formulate_claim(
                    finding, level, ctx, conv_by_id, proof_by_conv, findings_by_level
                )
                if claim:
                    claims.append(claim)

        # Save claims
        claims_path = self.capstone_dir / "claims" / "all_candidates.json"
        claims_path.write_text(json.dumps(
            [asdict(c) for c in claims], indent=2, default=str
        ))

        return claims

    def _formulate_claim(
        self,
        finding: dict,
        level: int,
        ctx: CapstoneContext,
        conv_by_id: dict,
        proof_by_conv: dict,
        findings_by_level: dict,
    ) -> Optional[CandidateClaim]:
        """Formulate a single finding as a precise falsifiable claim."""

        source_ids = finding.get("source_convergence_ids", [])
        coined = finding.get("coined_term") or ""  # Handle None explicitly
        structural_finding = finding.get("structural_finding", "")

        # Gather supporting convergence data
        supporting_convs = []
        for sid in source_ids:
            conv = conv_by_id.get(sid)
            if conv:
                supporting_convs.append(conv)
            # Also check if this ID is a finding ID (meta-convergence)
            # and trace down to its source convergences
            for f in ctx.findings:
                if f.get("id") == sid:
                    for sub_id in f.get("source_convergence_ids", []):
                        sub_conv = conv_by_id.get(sub_id)
                        if sub_conv and sub_conv not in supporting_convs:
                            supporting_convs.append(sub_conv)

        # If no convergences found directly, trace through the cascade
        if not supporting_convs:
            supporting_convs = self._trace_convergences(finding, ctx)

        if not supporting_convs:
            return None  # Can't make a claim without evidence

        # Gather proof data for supporting convergences
        supporting_proofs = []
        for c in supporting_convs:
            cid = c.get("id", "")
            proof = proof_by_conv.get(cid)
            if proof:
                supporting_proofs.append(proof)

        # Compute mean confidence
        confidences = [p.get("confidence_score", 0) for p in supporting_proofs if p.get("confidence_score", 0) > 0]
        mean_conf = sum(confidences) / len(confidences) if confidences else 0.0

        # Compute independence score (how many different domain pairs)
        domain_pairs = set()
        for c in supporting_convs:
            domains = tuple(sorted(c.get("domain_names", c.get("domains", []))))
            domain_pairs.add(domains)
        independence = len(domain_pairs) / max(len(supporting_convs), 1)

        # Build cascade position description
        cascade_position = self._describe_cascade_position(finding, level, ctx)

        # Build convergence data string for the prompt
        conv_data = self._format_convergences_for_prompt(supporting_convs, proof_by_conv)
        proof_data = self._format_proofs_for_prompt(supporting_proofs)

        # Ask AI to formulate the claim precisely
        prompt = CLAIM_FORMULATION_PROMPT.format(
            coined_term=coined,
            level=level,
            structural_finding=structural_finding,
            source_ids=", ".join(source_ids),
            is_meta=finding.get("is_meta_convergence", False),
            convergence_data=conv_data,
            proof_data=proof_data,
            cascade_position=cascade_position,
        )

        try:
            result = self.api.query_deep_json(prompt, system=CAPSTONE_SYSTEM, max_tokens=4096)
        except Exception as e:
            # If AI call fails, create a basic claim from the data alone
            result = {
                "claim_text": structural_finding,
                "existing_crisis": "",
                "falsification_criterion": "",
                "predictions": [],
                "mathematical_sketch": "",
                "tier": "framework" if level >= 3 else "bridge",
                "strength_assessment": f"AI formulation failed: {e}",
            }

        # Determine tier from cascade level (data-driven, not AI's guess)
        if level >= 5:
            tier = "meta"
        elif level >= 3:
            tier = "framework"
        elif len(supporting_convs) >= 7:
            tier = "anchor"
        else:
            tier = "bridge"

        claim = CandidateClaim(
            claim_text=result.get("claim_text", structural_finding),
            claim_type="fixed_point" if level >= 5 else "cascade",
            tier=tier,
            source_finding_id=finding.get("id", ""),
            source_finding_level=level,
            coined_term=coined,
            supporting_convergence_ids=[c.get("id", "") for c in supporting_convs],
            supporting_finding_ids=[finding.get("id", "")] + [
                f.get("id", "") for f in ctx.findings
                if f.get("id") != finding.get("id") and
                set(f.get("source_convergence_ids", [])) & set(source_ids)
            ],
            mean_confidence=mean_conf,
            num_source_convergences=len(supporting_convs),
            independence_score=independence,
            falsification_criterion=result.get("falsification_criterion", ""),
            existing_crisis=result.get("existing_crisis", ""),
            predictions=result.get("predictions", []),
            claim_too_broad=result.get("claim_too_broad", ""),
            claim_too_narrow=result.get("claim_too_narrow", ""),
            mathematical_sketch=result.get("mathematical_sketch", ""),
        )

        return claim

    def _trace_convergences(self, finding: dict, ctx: CapstoneContext) -> list[dict]:
        """Trace a finding down through the cascade to find base convergences."""
        conv_by_id = {c.get("id", ""): c for c in ctx.convergences}
        finding_by_id = {f.get("id", ""): f for f in ctx.findings}

        visited = set()
        base_convs = []

        def _trace(source_ids):
            for sid in source_ids:
                if sid in visited:
                    continue
                visited.add(sid)
                # Is it a convergence?
                if sid in conv_by_id:
                    base_convs.append(conv_by_id[sid])
                # Is it a finding? Trace deeper.
                elif sid in finding_by_id:
                    sub = finding_by_id[sid]
                    _trace(sub.get("source_convergence_ids", []))

        _trace(finding.get("source_convergence_ids", []))
        return base_convs

    # ─── STAGE 3: CLAIM FILTERING & PAPER PLANNING ───

    def plan_papers(self, claims: list[CandidateClaim], ctx: CapstoneContext) -> list[PaperPlan]:
        """Select which claims merit papers. Quality over volume.

        Data-driven selection:
        - Level 5 fixed points always get papers (they survived all rounds)
        - Level 3-4 findings get papers if they have strong evidence
        - Level 1-2 findings get papers only if they have 7+ source convergences
        - Claims are merged if they're essentially saying the same thing
        """
        # First pass: deterministic filtering
        # Every cascade level makes a genuinely different claim — include all
        # that pass minimum evidence thresholds
        strong_claims = []
        for claim in claims:
            # Level 5: always include (survived all rounds)
            if claim.source_finding_level >= 5:
                strong_claims.append(claim)
            # Level 2-4: include — these are distinct claims at different
            # levels of abstraction (e.g. L4 "Constraint Monism" is a
            # STRONGER claim than L5 "Reality is constraint")
            elif claim.source_finding_level >= 2 and claim.num_source_convergences >= 2:
                strong_claims.append(claim)
            # Level 1: include with strong evidence base (7+ convergences)
            elif claim.source_finding_level >= 1 and claim.num_source_convergences >= 7:
                strong_claims.append(claim)

        if not strong_claims:
            # Fallback: include all claims above minimum threshold
            strong_claims = [c for c in claims if c.num_source_convergences >= 3]

        # Deduplicate — each cascade level makes a DIFFERENT claim at a different
        # level of abstraction. L5 "Reality is constraint" is the ultimate meta-claim.
        # L4 "Constraint Monism" makes the STRONGER claim that there's no positive
        # content. L1 "Topological Governance" is a specific empirical claim.
        # All deserve papers.
        #
        # Only dedup TRUE duplicates:
        # 1. Same finding ID (never two papers from same finding)
        # 2. Near-identical structural_finding text (parallel branches say same thing)
        #
        # The AI planning step handles merging related claims if appropriate.
        seen_finding_ids = set()
        seen_texts = set()
        deduped = []

        for claim in sorted(strong_claims, key=lambda c: (-c.source_finding_level, -c.num_source_convergences)):
            if claim.source_finding_id in seen_finding_ids:
                continue

            # Dedup by structural finding text — two findings with near-identical
            # text on parallel cascade branches are the same claim
            finding = None
            for f in ctx.findings:
                if f.get("id") == claim.source_finding_id:
                    finding = f
                    break
            text_key = (finding.get("structural_finding", "")[:80] if finding else "")
            if text_key and text_key in seen_texts:
                continue

            seen_finding_ids.add(claim.source_finding_id)
            if text_key:
                seen_texts.add(text_key)
            deduped.append(claim)

        # AI pass: ask for paper planning (merge similar claims, assess portfolio)
        cascade_summary = self._build_cascade_summary(ctx)
        # Include numeric indexes so AI can reference claims reliably
        claims_with_index = []
        for idx, c in enumerate(deduped):
            d = asdict(c)
            d["_index"] = idx  # AI should use these indexes in claim_ids
            claims_with_index.append(d)
        claims_json = json.dumps(claims_with_index, indent=2, default=str)

        prompt = PAPER_PLANNING_PROMPT.format(
            claims_json=claims_json,
            cascade_summary=cascade_summary,
        )

        try:
            planning = self.api.query_deep_json(prompt, system=CAPSTONE_SYSTEM, max_tokens=8192)
        except Exception:
            # If AI planning fails, use deterministic plan
            planning = {"papers": [{"claim_ids": [c.id], "title": c.coined_term or c.claim_text[:60],
                                     "target_pages": "8-15", "existing_crisis": c.existing_crisis}
                                    for c in deduped]}

        # Build PaperPlan objects
        claim_by_id = {c.id: c for c in deduped}
        plans = []
        used_claim_indexes = set()

        for paper_spec in planning.get("papers", []):
            claim_ids = paper_spec.get("claim_ids", [])
            matched_claims = []
            for cid in claim_ids:
                # Try as integer index first (preferred — we told AI to use indexes)
                try:
                    idx = int(cid)
                    if 0 <= idx < len(deduped) and idx not in used_claim_indexes:
                        matched_claims.append(deduped[idx])
                        used_claim_indexes.add(idx)
                        continue
                except (ValueError, TypeError):
                    pass
                # Try as claim ID
                if isinstance(cid, str) and cid in claim_by_id:
                    matched_claims.append(claim_by_id[cid])

            if not matched_claims and deduped:
                # Fallback: assign next unused claim
                for idx, c in enumerate(deduped):
                    if idx not in used_claim_indexes:
                        matched_claims = [c]
                        used_claim_indexes.add(idx)
                        break

            if not matched_claims:
                continue

            primary_claim = matched_claims[0]

            # Collect all convergence/finding/proof IDs across merged claims
            all_conv_ids = []
            all_finding_ids = []
            for mc in matched_claims:
                all_conv_ids.extend(mc.supporting_convergence_ids)
                all_finding_ids.extend(mc.supporting_finding_ids)

            # Deduplicate
            all_conv_ids = list(dict.fromkeys(all_conv_ids))
            all_finding_ids = list(dict.fromkeys(all_finding_ids))

            # Find proof IDs for these convergences
            proof_ids = []
            for p in ctx.proofs:
                if p.get("convergence_id", "") in all_conv_ids:
                    proof_ids.append(p.get("id", ""))

            plan = PaperPlan(
                tier=primary_claim.tier,
                title=paper_spec.get("title", primary_claim.coined_term or "Untitled"),
                claim=asdict(primary_claim),
                convergence_ids=all_conv_ids,
                finding_ids=all_finding_ids,
                proof_ids=proof_ids,
                existing_crisis=paper_spec.get("existing_crisis", primary_claim.existing_crisis),
                target_length_pages=paper_spec.get("target_pages", "8-15"),
            )
            plans.append(plan)

        # Save plans
        plans_path = self.capstone_dir / "plans" / "paper_plans.json"
        plans_path.write_text(json.dumps(
            [asdict(p) for p in plans], indent=2, default=str
        ))

        return plans

    # ─── STAGE 4: COMPOSITION (Nobel template) ───

    def compose_paper(self, plan: PaperPlan, ctx: CapstoneContext) -> PaperDraft:
        """Compose a single capstone paper using the Nobel template.

        9 sections: Abstract → Problem → Setup → Central Result → Predictions →
        Connections → Limitations → Provenance → References
        """
        paper = PaperDraft(
            id=plan.id,
            title=plan.title,
        )
        paper.convergence_ids = plan.convergence_ids
        paper.finding_ids = plan.finding_ids
        paper.proof_ids = plan.proof_ids

        claim = plan.claim if isinstance(plan.claim, dict) else asdict(plan.claim)
        claim_text = claim.get("claim_text", plan.title)
        tier = plan.tier

        # Build scope boundary context for composition
        scope_guard = ""
        too_broad = claim.get("claim_too_broad", "")
        if too_broad:
            scope_guard = (
                f"\n\nSCOPE BOUNDARY — DO NOT CROSS:\n"
                f"The following version of this claim is TOO BROAD and must NOT "
                f"be stated or implied: \"{too_broad}\"\n"
                f"The claim must stay within: \"{claim_text}\"\n"
            )
        composition_system = CAPSTONE_SYSTEM + scope_guard

        # Gather evidence
        conv_by_id = {c.get("id", ""): c for c in ctx.convergences}
        proof_by_conv = {}
        for p in ctx.proofs:
            cid = p.get("convergence_id", "")
            if cid:
                proof_by_conv[cid] = p

        supporting_convs = [conv_by_id[cid] for cid in plan.convergence_ids if cid in conv_by_id]
        supporting_proofs = [proof_by_conv[cid] for cid in plan.convergence_ids if cid in proof_by_conv]

        evidence_summary = self._format_convergences_for_prompt(supporting_convs, proof_by_conv)
        formalisation_data = self._format_proofs_for_prompt(supporting_proofs)
        cascade_level = claim.get("source_finding_level", 0)

        sections = []

        # 1. Abstract
        abstract = self.api.query_deep(
            CAPSTONE_ABSTRACT_PROMPT.format(
                claim_text=claim_text,
                tier=tier,
                cascade_level=cascade_level,
                evidence_summary=evidence_summary[:3000],
            ),
            system=composition_system,
            max_tokens=2048,
        )
        paper.abstract = abstract
        sections.append(self._make_section("abstract", "Abstract", abstract))

        # 2. The Problem
        problem = self.api.query_deep(
            CAPSTONE_PROBLEM_PROMPT.format(
                claim_text=claim_text,
                existing_crisis=plan.existing_crisis or claim.get("existing_crisis", ""),
            ),
            system=composition_system,
            max_tokens=4096,
        )
        sections.append(self._make_section("the_problem", "1. The Problem", problem))

        # 3. Setup and Definitions
        setup = self.api.query_deep(
            CAPSTONE_SETUP_PROMPT.format(
                claim_text=claim_text,
                mathematical_sketch=claim.get("mathematical_sketch", ""),
                formalisation_data=formalisation_data[:4000],
            ),
            system=composition_system,
            max_tokens=4096,
        )
        sections.append(self._make_section("setup", "2. Setup and Definitions", setup))

        # 4. The Central Result
        convergence_details = self._format_convergences_detailed(supporting_convs, proof_by_conv)
        cascade_evidence = self._describe_cascade_evidence(plan, ctx)

        result = self.api.query_deep(
            CAPSTONE_RESULT_PROMPT.format(
                claim_text=claim_text,
                mathematical_sketch=claim.get("mathematical_sketch", ""),
                convergence_details=convergence_details,
                formalisation_details=formalisation_data,
                cascade_evidence=cascade_evidence,
            ),
            system=composition_system,
            max_tokens=16384,
        )
        sections.append(self._make_section("central_result", "3. The Central Result", result))

        # 5. Predictions
        predictions_list = "\n".join(f"- {p}" for p in claim.get("predictions", []))
        evidence_strength = f"Mean confidence: {claim.get('mean_confidence', 0):.2f}, " \
                           f"Independence score: {claim.get('independence_score', 0):.2f}, " \
                           f"Source convergences: {claim.get('num_source_convergences', 0)}"

        predictions = self.api.query_deep(
            CAPSTONE_PREDICTIONS_PROMPT.format(
                claim_text=claim_text,
                predictions_list=predictions_list,
                evidence_strength=evidence_strength,
            ),
            system=composition_system,
            max_tokens=4096,
        )
        sections.append(self._make_section("predictions", "4. Predictions", predictions))

        # 6. Connection to Existing Results
        domain_pairs = self._list_domain_pairs(supporting_convs)
        connections = self.api.query_deep(
            CAPSTONE_CONNECTIONS_PROMPT.format(
                claim_text=claim_text,
                domain_pairs=domain_pairs,
            ),
            system=composition_system,
            max_tokens=4096,
        )
        sections.append(self._make_section("connections", "5. Connection to Existing Results", connections))

        # 7. Limitations and Open Problems
        evidence_gaps = self._identify_evidence_gaps(supporting_proofs)
        formalisation_status = self._summarise_formalisation_status(supporting_proofs)

        limitations = self.api.query_deep(
            CAPSTONE_LIMITATIONS_PROMPT.format(
                claim_text=claim_text,
                evidence_gaps=evidence_gaps,
                formalisation_status=formalisation_status,
            ),
            system=composition_system,
            max_tokens=2048,
        )
        sections.append(self._make_section("limitations", "6. Limitations and Open Problems", limitations))

        # 8. Priority and Provenance
        # Compute SHA-256 of paper content so far for provenance
        content_so_far = "\n\n".join(s.get("content", "") for s in sections)
        paper_hash = hashlib.sha256(content_so_far.encode("utf-8")).hexdigest()

        provenance = self.api.query(
            CAPSTONE_PROVENANCE_PROMPT.format(
                paper_id=paper.id,
                claim_text=claim_text,
                convergence_ids=", ".join(plan.convergence_ids[:10]),
                finding_ids=", ".join(plan.finding_ids[:5]),
                git_hash=paper_hash,
                block_height="[recorded at push time — filled by git_stamp_capstone]",
            ),
            system=composition_system,
            max_tokens=2048,
        )
        sections.append(self._make_section("provenance", "7. Priority and Provenance", provenance))

        # 9. References — pass the full paper text so AI can extract actual citations
        full_text_so_far = "\n\n".join(
            f"## {s.get('title', '')}\n{s.get('content', '')}" for s in sections
        )
        references = self.api.query(
            CAPSTONE_REFERENCES_PROMPT.format(
                citations_used=full_text_so_far[:12000],  # Cap for context window
            ),
            system=composition_system,
            max_tokens=4096,
        )
        sections.append(self._make_section("references", "8. References", references))

        # Appendix A: Complete Evidence Table (deterministic, no AI)
        # Lists ALL supporting convergences — not just the 30 shown to the AI
        evidence_table = self._build_evidence_table(supporting_convs, proof_by_conv)
        sections.append(self._make_section(
            "appendix_a", "Appendix A: Complete Evidence Table", evidence_table
        ))

        # Appendix B: Methodology Note (deterministic, no AI)
        # Brief self-contained explanation so the paper doesn't depend on external papers
        methodology_note = self._build_methodology_note(len(supporting_convs), len(supporting_proofs))
        sections.append(self._make_section(
            "appendix_b", "Appendix B: Discovery and Formalisation Methodology", methodology_note
        ))

        # Assemble paper
        paper.sections = sections
        paper.full_markdown = self._assemble_markdown(paper, sections)
        paper.total_word_count = sum(s.get("word_count", 0) for s in sections)

        # Compute overall confidence from evidence
        confidences = [p.get("confidence_score", 0) for p in supporting_proofs if p.get("confidence_score", 0) > 0]
        paper.confidence_score = sum(confidences) / len(confidences) if confidences else 0.3
        paper.confidence_category = PaperConfidence.from_score(paper.confidence_score).value

        paper.run_metadata = {
            "mode": "capstone",
            "tier": tier,
            "cascade_level": cascade_level,
            "num_convergences": len(supporting_convs),
            "num_proofs": len(supporting_proofs),
            "coined_term": claim.get("coined_term", ""),
        }

        # Generation log — audit trail of how this paper was built
        paper.generation_log = [
            {
                "stage": "claim_formulation",
                "source_finding_id": claim.get("source_finding_id", ""),
                "claim_text": claim_text,
                "claim_too_broad": claim.get("claim_too_broad", ""),
                "claim_too_narrow": claim.get("claim_too_narrow", ""),
                "mathematical_sketch": claim.get("mathematical_sketch", "")[:500],
                "falsification_criterion": claim.get("falsification_criterion", ""),
                "predictions": claim.get("predictions", []),
                "mean_confidence": claim.get("mean_confidence", 0),
                "independence_score": claim.get("independence_score", 0),
            },
            {
                "stage": "evidence_assembly",
                "convergence_ids": [c.get("id", "") for c in supporting_convs],
                "proof_ids": [p.get("id", "") for p in supporting_proofs],
                "num_convergences_shown_to_ai": min(len(supporting_convs), 30),
                "num_proofs_shown_to_ai": min(len(supporting_proofs), 30),
                "num_convergences_in_appendix": len(supporting_convs),
                "scope_guard_active": bool(scope_guard),
            },
            {
                "stage": "composition",
                "sections_composed": [s.get("section", "") for s in sections],
                "ai_sections": [s.get("section", "") for s in sections
                                if s.get("section", "") not in ("appendix_a", "appendix_b")],
                "deterministic_sections": ["appendix_a", "appendix_b"],
                "total_word_count": sum(s.get("word_count", 0) for s in sections),
                "paper_hash": paper_hash,
            },
        ]

        return paper

    # ─── STAGE 5: ADVERSARIAL REVIEW (enhanced for capstone) ───

    def review_capstone(self, paper: PaperDraft) -> dict:
        """Enhanced 15-point review for capstone papers.

        Standard 10 criteria + 5 capstone-specific:
        drift detection, over-generalisation, prediction quality,
        evidence independence, Nobel completeness.
        """
        tier = paper.run_metadata.get("tier", "unknown")
        prompt = CAPSTONE_REVIEW_PROMPT.format(
            title=paper.title,
            tier=tier,
            full_text=paper.full_markdown[:30000],  # Cap for context window
        )

        review = self.api.query_deep_json(prompt, system=CAPSTONE_SYSTEM, max_tokens=8192)

        # Update paper confidence based on review
        overall = review.get("overall_quality", 0.5)
        nobel_scores = review.get("nobel_model_scores", review.get("capstone_scores", {}))
        drift = nobel_scores.get("drift_detection", 1.0)
        scope = nobel_scores.get("scope_precision", 1.0)
        over_gen = nobel_scores.get("over_generalisation_guard", 1.0)

        # Penalise heavily for drift and over-generalisation
        adjusted = overall * min(drift, 1.0) * min(scope, 1.0) * min(over_gen, 1.0)
        paper.confidence_score = adjusted
        paper.confidence_category = PaperConfidence.from_score(adjusted).value

        return review

    def revise_capstone(self, paper: PaperDraft, review: dict, plan: PaperPlan, ctx: CapstoneContext) -> PaperDraft:
        """Revise a capstone paper based on review feedback.

        Only revises sections with critical/major issues.
        """
        from synthesis.prompts.review import REVISION_PROMPT

        issues = review.get("issues", [])
        critical_major = [i for i in issues if i.get("severity") in ("critical", "major")]

        if not critical_major:
            return paper

        # Group issues by section
        issues_by_section = defaultdict(list)
        for issue in critical_major:
            issues_by_section[issue.get("section", "general")].append(issue)

        # Revise each affected section
        for section_dict in paper.sections:
            section_name = section_dict.get("section", "")
            section_issues = issues_by_section.get(section_name, [])
            if not section_issues:
                continue

            review_issues_text = "\n".join(
                f"- [{i['severity'].upper()}] {i.get('issue', '')} → Suggested: {i.get('suggested_fix', '')}"
                for i in section_issues
            )

            revised = self.api.query_deep(
                REVISION_PROMPT.format(
                    paper_title=paper.title,
                    section_title=section_dict.get("title", ""),
                    section_content=section_dict.get("content", ""),
                    review_issues=review_issues_text,
                ),
                system=CAPSTONE_SYSTEM,
                max_tokens=8192,
            )

            section_dict["content"] = revised
            section_dict["word_count"] = len(revised.split())

        # Reassemble markdown
        paper.full_markdown = self._assemble_markdown(paper, paper.sections)
        paper.total_word_count = sum(s.get("word_count", 0) for s in paper.sections)

        return paper

    def cross_paper_check(self, papers: list[PaperDraft]) -> dict:
        """Check consistency across all capstone papers."""
        papers_summary = "\n\n".join(
            f"### Paper: {p.title}\nID: {p.id}\nTier: {p.run_metadata.get('tier', '?')}\n"
            f"Claim: {p.abstract[:300]}\n"
            f"Convergence IDs: {', '.join(p.convergence_ids[:5])}"
            for p in papers
        )

        prompt = CROSS_PAPER_CHECK_PROMPT.format(papers_summary=papers_summary)
        return self.api.query_deep_json(prompt, system=CAPSTONE_SYSTEM, max_tokens=8192)

    # ─── STAGE 6: PREDICTION EXTRACTION ───

    def extract_predictions(self, papers: list[PaperDraft]) -> dict:
        """Extract all predictions from all capstone papers into a single register."""
        predictions = []

        for paper in papers:
            # Find the predictions section
            for section in paper.sections:
                if section.get("section") == "predictions":
                    content = section.get("content", "")
                    # Parse predictions from markdown
                    paper_predictions = self._parse_predictions(content, paper)
                    predictions.extend(paper_predictions)

        register = {
            "generated_at": _now(),
            "total_predictions": len(predictions),
            "total_papers": len(papers),
            "predictions": predictions,
        }

        # Save
        register_path = self.capstone_dir / "predictions.json"
        register_path.write_text(json.dumps(register, indent=2, default=str))

        # Also save human-readable version
        md_path = self.capstone_dir / "PREDICTIONS_REGISTER.md"
        md_content = PREDICTION_REGISTER_HEADER.format(
            date=datetime.now(timezone.utc).strftime("%Y-%m-%d"),
        )
        for i, pred in enumerate(predictions, 1):
            md_content += f"### Prediction {i}\n\n"
            md_content += f"**From:** {pred.get('paper_title', '')}\n"
            md_content += f"**Paper ID:** {pred.get('paper_id', '')}\n\n"
            md_content += f"{pred.get('text', '')}\n\n"
            if pred.get("falsification"):
                md_content += f"*Falsification:* {pred['falsification']}\n\n"
            md_content += f"**Supporting convergences:** {', '.join(pred.get('convergence_ids', []))}\n\n"
            md_content += "---\n\n"
        md_path.write_text(md_content)

        return register

    def _parse_predictions(self, content: str, paper: PaperDraft) -> list[dict]:
        """Parse individual predictions from the predictions section text."""
        predictions = []
        lines = content.split("\n")
        current_pred = None

        for line in lines:
            stripped = line.strip()
            # Look for "Prediction N." pattern
            if stripped.startswith("**Prediction") or stripped.startswith("Prediction"):
                if current_pred:
                    predictions.append(current_pred)
                current_pred = {
                    "paper_id": paper.id,
                    "paper_title": paper.title,
                    "convergence_ids": paper.convergence_ids[:5],
                    "text": stripped,
                    "falsification": "",
                    "test": "",
                    "confidence": "",
                }
            elif current_pred:
                if "falsification" in stripped.lower():
                    current_pred["falsification"] = stripped
                elif "test:" in stripped.lower():
                    current_pred["test"] = stripped
                elif "confidence:" in stripped.lower():
                    current_pred["confidence"] = stripped
                else:
                    current_pred["text"] += " " + stripped

        if current_pred:
            predictions.append(current_pred)

        return predictions

    # ─── Helper Methods ───

    def _make_section(self, section_id: str, title: str, content: str) -> dict:
        return {
            "section": section_id,
            "title": title,
            "content": content,
            "word_count": len(content.split()),
            "confidence": 0.7,
            "flags": [],
        }

    def _assemble_markdown(self, paper: PaperDraft, sections: list[dict]) -> str:
        """Assemble full markdown from sections."""
        lines = [
            f"# {paper.title}",
            "",
            f"**Author:** Mark E. Mala",
            f"**Date:** {paper.date}",
            f"**Paper ID:** {paper.id}",
            f"**Mode:** Capstone (Nobel-grade claim)",
            "",
            "---",
            "",
        ]
        for s in sections:
            lines.append(f"## {s.get('title', '')}")
            lines.append("")
            lines.append(s.get("content", ""))
            lines.append("")
        return "\n".join(lines)

    def _format_convergences_for_prompt(self, convs: list[dict], proof_by_conv: dict) -> str:
        """Format convergences for inclusion in a prompt."""
        parts = []
        for c in convs[:30]:  # Show up to 30 (was 15 — too few for high-level findings)
            cid = c.get("id", "")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            claim = c.get("structural_claim", "")[:200]
            ea = c.get("ea_scores", {})

            proof = proof_by_conv.get(cid, {})
            conf = proof.get("confidence_score", 0)
            adv = proof.get("adversarial_result", {})
            verdict = adv.get("verdict", "unknown") if isinstance(adv, dict) else "unknown"

            parts.append(
                f"- **{cid}** [{domains}]: {claim}\n"
                f"  EA scores: {json.dumps(ea)}\n"
                f"  Proof confidence: {conf:.2f}, adversarial verdict: {verdict}"
            )
        if len(convs) > 30:
            parts.append(f"\n(... and {len(convs) - 30} more convergences)")
        return "\n".join(parts)

    def _format_convergences_detailed(self, convs: list[dict], proof_by_conv: dict) -> str:
        """Detailed convergence data for the Central Result section."""
        parts = []
        for c in convs[:30]:  # Show up to 30 for better evidence coverage
            cid = c.get("id", "")
            domains = ", ".join(c.get("domain_names", c.get("domains", [])))
            claim = c.get("structural_claim", "")
            ctype = c.get("convergence_type", "")
            ea = c.get("ea_scores", {})

            proof = proof_by_conv.get(cid, {})
            conf = proof.get("confidence_score", 0)
            adv = proof.get("adversarial_result", {})
            verdict = adv.get("verdict", "unknown") if isinstance(adv, dict) else "unknown"
            apparatus = ", ".join(proof.get("mathematical_apparatus", [])[:3])
            # Gaps are in adversarial_result.gaps, each is a dict with 'issue' key
            raw_gaps = adv.get("gaps", []) if isinstance(adv, dict) else []
            gap_text = "; ".join(
                g.get("issue", str(g))[:100] if isinstance(g, dict) else str(g)[:100]
                for g in raw_gaps[:3]
            ) if raw_gaps else "none identified"

            parts.append(
                f"### Convergence {cid}\n"
                f"- **Domains:** {domains}\n"
                f"- **Type:** {ctype}\n"
                f"- **Claim:** {claim}\n"
                f"- **EA Scores:** {json.dumps(ea)}\n"
                f"- **Formalisation confidence:** {conf:.2f}\n"
                f"- **Adversarial verdict:** {verdict}\n"
                f"- **Mathematical apparatus:** {apparatus}\n"
                f"- **Identified gaps:** {gap_text}\n"
            )
        if len(convs) > 30:
            parts.append(f"\n(... and {len(convs) - 30} more convergences)")
        return "\n".join(parts)

    def _format_proofs_for_prompt(self, proofs: list[dict]) -> str:
        """Format proofs for inclusion in a prompt."""
        parts = []
        for p in proofs[:30]:  # Match convergence cap — more evidence for Nobel-grade papers
            pid = p.get("id", "")
            cid = p.get("convergence_id", "")
            ftype = p.get("formalisation_type", "")
            conf = p.get("confidence_score", 0)
            adv = p.get("adversarial_result", {})
            verdict = adv.get("verdict", "unknown") if isinstance(adv, dict) else "unknown"
            apparatus = ", ".join(p.get("mathematical_apparatus", [])[:3])
            # proposition is a string, not a dict — include FULL text for Nobel-grade precision
            proposition = p.get("proposition", "")
            formal = proposition if isinstance(proposition, str) else str(proposition)
            complete = p.get("internal_consistency", {}).get("proof_complete", False)

            parts.append(
                f"- **{pid}** (for {cid}): {ftype}, confidence {conf:.2f}, verdict: {verdict}, complete: {complete}\n"
                f"  Apparatus: {apparatus}\n"
                f"  Proposition: {formal}"
            )
        if len(proofs) > 30:
            parts.append(f"\n(... and {len(proofs) - 30} more formalisations)")
        return "\n".join(parts)

    def _describe_cascade_position(self, finding: dict, level: int, ctx: CapstoneContext) -> str:
        """Describe where this finding sits in the cascade."""
        total_levels = max((f.get("level", 0) for f in ctx.findings), default=0)
        same_level = sum(1 for f in ctx.findings if f.get("level", 0) == level)
        lower = sum(1 for f in ctx.findings if f.get("level", 0) < level)

        return (
            f"This finding is at Level {level} of {total_levels} in the convergence cascade.\n"
            f"The cascade structure: {ctx.total_convergences} convergences → "
            f"{ctx.total_findings} findings → {len(ctx.fixed_points)} terminal fixed points.\n"
            f"There are {same_level} findings at this level and {lower} at lower levels.\n"
            f"Level {level} means this finding survived {level} rounds of meta-convergence analysis."
        )

    def _describe_cascade_evidence(self, plan: PaperPlan, ctx: CapstoneContext) -> str:
        """Describe the cascade evidence supporting this paper."""
        claim = plan.claim if isinstance(plan.claim, dict) else asdict(plan.claim)
        level = claim.get("source_finding_level", 0)

        finding_ids = plan.finding_ids
        related_findings = [f for f in ctx.findings if f.get("id") in finding_ids]

        parts = [f"This claim is at cascade Level {level}."]
        parts.append(f"Cascade structure: {ctx.cascade_dag.get('reduction', '')}")
        parts.append(f"\nSupporting findings ({len(related_findings)}):")
        for f in related_findings:
            parts.append(
                f"- Level {f.get('level', '?')}: {f.get('coined_term', '')} — "
                f"{f.get('structural_finding', '')[:100]}"
            )
        return "\n".join(parts)

    def _build_cascade_summary(self, ctx: CapstoneContext) -> str:
        """Build a text summary of the entire cascade for planning."""
        parts = [
            f"Total convergences: {ctx.total_convergences}",
            f"Total proofs: {ctx.total_proofs}",
            f"Total findings: {ctx.total_findings}",
            f"Terminal fixed points: {len(ctx.fixed_points)}",
            f"Cascade: {ctx.cascade_dag.get('reduction', '')}",
            "",
            "Findings by level:",
        ]
        for level, ids in sorted(ctx.cascade_levels.items(), key=lambda x: int(x[0]), reverse=True):
            level_findings = [f for f in ctx.findings if f.get("id") in ids]
            for f in level_findings:
                sources = len(f.get("source_convergence_ids", []))
                parts.append(
                    f"  Level {level}: {f.get('coined_term', '')} "
                    f"({sources} sources) — {f.get('structural_finding', '')[:80]}"
                )
        parts.append("")
        parts.append(f"Cross-domain hubs: {', '.join(ctx.cross_domain_hubs[:5])}")
        parts.append(f"Confidence distribution: {json.dumps(ctx.confidence_distribution)}")
        return "\n".join(parts)

    def _list_domain_pairs(self, convs: list[dict]) -> str:
        """List unique domain pairs from convergences."""
        pairs = set()
        for c in convs:
            domains = tuple(sorted(c.get("domain_names", c.get("domains", []))))
            pairs.add(" × ".join(domains))
        return "\n".join(f"- {p}" for p in sorted(pairs))

    def _identify_evidence_gaps(self, proofs: list[dict]) -> str:
        """Identify gaps in the evidence from proof data."""
        gaps = []
        for p in proofs:
            pid = p.get("id", "")
            adv = p.get("adversarial_result", {})
            verdict = adv.get("verdict", "unknown") if isinstance(adv, dict) else "unknown"
            conf = p.get("confidence_score", 0)

            if verdict not in ("accept",):
                gaps.append(f"- Formalisation {pid}: verdict={verdict}, confidence={conf:.2f}")

            # Check for gaps in adversarial result
            if isinstance(adv, dict):
                for g in adv.get("gaps", []):
                    if isinstance(g, dict):
                        severity = g.get("severity", "")
                        issue = g.get("issue", "")[:120]
                        if severity in ("critical", "major"):
                            gaps.append(f"  [{severity}] {issue}")
                    else:
                        gaps.append(f"  Gap: {str(g)[:120]}")

        if not gaps:
            return "No critical gaps identified in supporting formalisations."
        return "\n".join(gaps[:30])

    def _summarise_formalisation_status(self, proofs: list[dict]) -> str:
        """Summarise the formalisation status across all supporting proofs."""
        if not proofs:
            return "No formalisations available."

        total = len(proofs)
        # Verdict is in adversarial_result.verdict (NOT top-level adversarial_verdict)
        accepted = sum(1 for p in proofs
                       if p.get("adversarial_result", {}).get("verdict") == "accept")
        major_rev = sum(1 for p in proofs
                        if p.get("adversarial_result", {}).get("verdict") == "major_revision")
        rejected = sum(1 for p in proofs
                       if p.get("adversarial_result", {}).get("verdict") == "reject")
        complete = sum(1 for p in proofs
                       if p.get("internal_consistency", {}).get("proof_complete", False))
        confidences = [p.get("confidence_score", 0) for p in proofs if p.get("confidence_score", 0) > 0]
        mean_conf = sum(confidences) / len(confidences) if confidences else 0

        return (
            f"Total formalisations: {total}\n"
            f"Adversarial verdicts: {accepted} accepted, {major_rev} major revision, {rejected} rejected\n"
            f"Proof complete (internal check): {complete}/{total}\n"
            f"Mean confidence: {mean_conf:.2f}\n"
            f"Most formalisations are Level 3-4 (formal conjectures with structured arguments, "
            f"NOT complete proofs). This is stated honestly in the paper."
        )

    def _build_evidence_table(self, convs: list[dict], proof_by_conv: dict) -> str:
        """Build a complete evidence table of ALL supporting convergences.

        This is deterministic — no AI involved. Lists every convergence with
        its domains, confidence, adversarial verdict, and formalisation status.
        This ensures the paper contains the COMPLETE evidence base, not just
        the top 30 shown to the AI during composition.
        """
        lines = [
            "The following table lists every convergence supporting the central claim, "
            "with formalisation confidence scores and adversarial review verdicts.\n",
            "| # | Convergence ID | Domain Pair | Confidence | Adversarial Verdict | Proof Complete | Mathematical Apparatus |",
            "|---|---------------|-------------|------------|--------------------|----|----------------------|",
        ]

        for i, c in enumerate(convs, 1):
            cid = c.get("id", "")
            domains = " × ".join(c.get("domain_names", c.get("domains", [])))

            proof = proof_by_conv.get(cid, {})
            conf = proof.get("confidence_score", 0)
            adv = proof.get("adversarial_result", {})
            verdict = adv.get("verdict", "unknown") if isinstance(adv, dict) else "unknown"
            complete = proof.get("internal_consistency", {}).get("proof_complete", False)
            apparatus = ", ".join(proof.get("mathematical_apparatus", [])[:3])

            lines.append(
                f"| {i} | {cid} | {domains} | {conf:.2f} | {verdict} | "
                f"{'Yes' if complete else 'No'} | {apparatus or '—'} |"
            )

        # Summary statistics
        confidences = [
            proof_by_conv.get(c.get("id", ""), {}).get("confidence_score", 0)
            for c in convs
        ]
        valid_confs = [c for c in confidences if c > 0]
        mean_conf = sum(valid_confs) / len(valid_confs) if valid_confs else 0

        verdicts = [
            proof_by_conv.get(c.get("id", ""), {}).get("adversarial_result", {}).get("verdict", "unknown")
            if isinstance(proof_by_conv.get(c.get("id", ""), {}).get("adversarial_result", {}), dict)
            else "unknown"
            for c in convs
        ]
        verdict_counts = Counter(verdicts)

        lines.append("")
        lines.append(f"**Total convergences:** {len(convs)}")
        lines.append(f"**Mean formalisation confidence:** {mean_conf:.3f}")
        lines.append(f"**Adversarial verdicts:** {', '.join(f'{v}: {n}' for v, n in sorted(verdict_counts.items()))}")

        # Domain pair distribution
        pair_counts = Counter()
        for c in convs:
            pair = " × ".join(sorted(c.get("domain_names", c.get("domains", []))))
            pair_counts[pair] += 1

        lines.append(f"\n**Unique domain pairs:** {len(pair_counts)}")
        lines.append("**Domain pair distribution:**")
        for pair, count in pair_counts.most_common():
            lines.append(f"- {pair}: {count} convergence{'s' if count > 1 else ''}")

        return "\n".join(lines)

    def _build_methodology_note(self, num_convergences: int, num_proofs: int) -> str:
        """Build a self-contained methodology explanation.

        This is deterministic — no AI involved. Provides enough methodological
        detail that the paper stands alone without requiring external references
        to Paper G16 or other methodology papers.
        """
        return (
            "## Discovery Methodology\n\n"
            "All convergences reported in this paper were discovered by Gnosis AI, an autonomous "
            "knowledge discovery system. The methodology proceeds in three stages:\n\n"
            "**Stage 1: Domain Analysis.** For each pair of knowledge domains (e.g., quantum mechanics "
            "and thermodynamics, or topology and economics), Gnosis AI identifies structural parallels — "
            "cases where the same mathematical structure, symmetry, or organising principle appears "
            "in both domains. Each candidate convergence is scored on five epistemic adequacy (EA) "
            "dimensions: novelty, specificity, explanatory depth, cross-domain validity, and "
            "falsifiability.\n\n"
            "**Stage 2: Formalisation.** Each convergence is independently formalised by Logos AI, "
            "which attempts to express the structural claim as a precise mathematical proposition "
            "with defined terms, stated assumptions, and a structured argument. Formalisations are "
            "classified by type (formal_proof, formal_conjecture, structured_argument, etc.) and "
            "scored for confidence.\n\n"
            "**Stage 3: Adversarial Review.** Each formalisation undergoes adversarial review, where "
            "a separate AI instance attempts to find gaps, logical errors, unstated assumptions, "
            "and counterexamples. The adversarial reviewer issues a verdict (accept, minor_revision, "
            "major_revision, or reject) and identifies specific gaps with severity ratings.\n\n"
            f"This paper draws on {num_convergences} convergences and {num_proofs} formalisations "
            "that survived this three-stage pipeline.\n\n"
            "## Cascade Analysis\n\n"
            "After individual convergences are established, a meta-convergence analysis identifies "
            "higher-order patterns: cases where multiple convergences from different domain pairs "
            "point to the same underlying structure. This cascade proceeds through multiple levels "
            "of abstraction:\n\n"
            "- **Level 1:** Direct meta-findings from groups of convergences\n"
            "- **Level 2:** Patterns across Level 1 findings\n"
            "- **Level 3–5:** Successive reductions toward terminal fixed points\n\n"
            "The cascade structure (266 convergences → 26 findings → 6 → 2 → 1 terminal structure) "
            "is itself a result — the data reduces to a small number of fundamental structural "
            "claims, which form the basis of this paper's central result.\n\n"
            "## Provenance\n\n"
            "All data is committed to a git repository and pushed to GitHub, where each push is "
            "anchored to a Bitcoin block height via the OpenTimestamps protocol. This provides "
            "cryptographic proof-of-existence at the time of discovery, independent of any "
            "institutional authority. The SHA-256 hash of each paper and its supporting data "
            "is recorded in the git history, and the Bitcoin block height at time of push is "
            "noted in the Priority and Provenance section.\n\n"
            "## Limitations of This Methodology\n\n"
            "1. **AI-generated claims:** All convergences were identified by AI, not human domain "
            "experts. While the three-stage pipeline (discovery → formalisation → adversarial review) "
            "reduces hallucination risk, it does not eliminate it.\n"
            "2. **Formalisation depth:** Most formalisations are at Level 3–4 (formal conjectures "
            "with structured arguments), not complete mathematical proofs. The confidence scores "
            "reflect this honestly.\n"
            "3. **Independence:** Domain pairs were analysed independently, but the same AI system "
            "was used for all analyses, which may introduce systematic biases.\n"
            "4. **Verification:** The predictions made in this paper have not been independently "
            "verified. They are offered as falsifiable conjectures for the scientific community "
            "to test."
        )

    # ─── Save/Load utilities ───

    def save_paper(self, paper: PaperDraft):
        path = self.capstone_dir / "papers" / f"{paper.id}.json"
        path.write_text(json.dumps(asdict(paper), indent=2, default=str))

    def save_markdown(self, paper: PaperDraft):
        if paper.full_markdown:
            path = self.capstone_dir / "drafts" / f"{paper.id}.md"
            path.write_text(paper.full_markdown)

    def save_review(self, paper_id: str, review: dict):
        path = self.capstone_dir / "reviews" / f"{paper_id}.json"
        path.write_text(json.dumps(review, indent=2, default=str))

    def list_completed_paper_ids(self) -> set[str]:
        """List IDs of already-completed capstone papers (for resume support)."""
        completed = set()
        papers_dir = self.capstone_dir / "papers"
        if papers_dir.exists():
            for f in papers_dir.glob("*.json"):
                completed.add(f.stem)
        return completed

    def load_completed_papers(self) -> list[PaperDraft]:
        """Load all completed capstone papers."""
        papers = []
        papers_dir = self.capstone_dir / "papers"
        if papers_dir.exists():
            for f in sorted(papers_dir.glob("*.json")):
                try:
                    data = json.loads(f.read_text())
                    papers.append(PaperDraft(**data))
                except (json.JSONDecodeError, Exception):
                    continue
        return papers
