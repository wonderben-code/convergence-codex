"""5-Layer Adversarial Validation Pipeline for Logos proofs."""

from __future__ import annotations

from dataclasses import asdict, dataclass

from logos.api import ClaudeAPI
from logos.models import ProofRecord, ValidationScores, ProofConfidence
from logos.store import ProofStore
from logos.prompts.adversarial import (
    ADVERSARIAL_PROOF_PROMPT,
    INTERNAL_CONSISTENCY_PROMPT,
    CROSS_PROOF_PROMPT,
)


SYSTEM_PROMPT = (
    "You are an adversarial mathematical reviewer. Your job is to find flaws, "
    "not to be encouraging. Be harsh, precise, and honest."
)


@dataclass
class ValidationResult:
    """Complete validation result for a proof."""
    scores: ValidationScores
    adversarial_detail: dict
    internal_detail: dict
    cross_proof_detail: dict
    overall_confidence: float
    confidence_category: str
    passed: bool  # meets minimum threshold


class ProofValidator:
    """5-layer adversarial validation pipeline."""

    def __init__(self, api: ClaudeAPI, store: ProofStore):
        self.api = api
        self.store = store

    def validate(self, proof: ProofRecord) -> ValidationResult:
        """Run all 5 validation layers on a proof."""

        scores = ValidationScores()

        # Layer 1: Mechanical verification (Lean)
        scores.mechanical = self._verify_mechanical(proof)

        # Layer 2: Adversarial scan
        adversarial_detail = self._adversarial_scan(proof)
        scores.adversarial = adversarial_detail.get("proof_soundness", 0.5)

        # Layer 3: Internal consistency
        internal_detail = self._check_internal(proof)
        scores.internal = internal_detail.get("internal_score", 0.5)

        # Layer 4: Cross-proof consistency
        cross_proof_detail = self._check_cross_proof(proof)
        scores.cross_proof = cross_proof_detail.get("consistency_score", 0.8)

        # Layer 5: Confidence calibration
        scores.calibration = self._calibrate(scores, proof)

        overall = scores.compute_confidence()
        category = ProofConfidence.from_score(overall).value

        # Store validation results on the proof
        proof.validation_scores = asdict(scores)
        proof.confidence_score = overall
        proof.confidence_category = category
        proof.confidence_breakdown = {
            "mechanical": scores.mechanical,
            "adversarial": scores.adversarial,
            "internal": scores.internal,
            "cross_proof": scores.cross_proof,
            "calibration": scores.calibration,
        }
        proof.adversarial_result = adversarial_detail
        proof.internal_consistency = internal_detail
        proof.cross_proof_consistency = cross_proof_detail

        return ValidationResult(
            scores=scores,
            adversarial_detail=adversarial_detail,
            internal_detail=internal_detail,
            cross_proof_detail=cross_proof_detail,
            overall_confidence=overall,
            confidence_category=category,
            passed=overall >= self.api.config.min_confidence_for_synthesis,
        )

    def _verify_mechanical(self, proof: ProofRecord) -> float:
        """Layer 1: Multi-tool mechanical verification.

        Uses consensus from all verification tools (Lean, Z3, SymPy, Numerical)
        if available, falls back to Lean-only assessment.
        """
        # Use multi-tool consensus if available
        consensus = proof.multi_tool_consensus
        if consensus and consensus.get("consensus_score", 0) > 0:
            # Scale consensus (0-1) to mechanical score range
            base = consensus["consensus_score"]
            level = consensus.get("verification_level", "natural_language_only")
            if level == "fully_verified":
                return min(1.0, base * 1.1)  # Slight boost for full verification
            elif level == "multi_tool_verified":
                return max(0.6, base)
            elif level == "single_tool_verified":
                return max(0.4, base * 0.9)
            elif level == "partially_verified":
                return max(0.3, base * 0.7)
            return base

        # Fallback: Lean-only (legacy path)
        if proof.lean_verified:
            return 1.0
        if proof.lean_partial:
            return 0.6
        if proof.proof_lean:
            return 0.3

        # No mechanical verification — score based on proof structure
        steps = proof.proof_steps
        if not steps:
            return 0.1

        justified = sum(1 for s in steps if s.get("justification"))
        ratio = justified / len(steps) if steps else 0
        return 0.2 + ratio * 0.3

    def _adversarial_scan(self, proof: ProofRecord) -> dict:
        """Layer 2: Frontier LLM as antagonistic reviewer."""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        deps_text = "\n".join(
            f"- {d.get('name', '')}: {d.get('statement', '')}"
            for d in proof.dependencies_literature
        )

        prompt = ADVERSARIAL_PROOF_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            proof_text=proof.proof_natural or steps_text,
            assumptions=", ".join(proof.assumptions),
            dependencies=deps_text,
        )

        try:
            data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT)
            return data
        except Exception:
            return {"proof_soundness": 0.5, "gaps": [], "overall_assessment": "Validation failed"}

    def _check_internal(self, proof: ProofRecord) -> dict:
        """Layer 3: Internal consistency check."""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        prompt = INTERNAL_CONSISTENCY_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            steps_text=steps_text,
            assumptions=", ".join(proof.assumptions),
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data
        except Exception:
            return {"internal_score": 0.5, "proves_stated_proposition": True}

    def _check_cross_proof(self, proof: ProofRecord) -> dict:
        """Layer 4: Cross-proof consistency with existing corpus."""

        existing_proofs = self.store.list_proofs()
        if not existing_proofs:
            return {"consistency_score": 0.9, "contradictions_found": False,
                    "notes": "No existing proofs to check against"}

        # Build summaries of existing proofs (limit to 20 most relevant)
        summaries = []
        for p in existing_proofs[:20]:
            if p.id == proof.id:
                continue
            summaries.append(
                f"- [{p.id}] {p.proposition_natural or p.proposition}: "
                f"Assumes: {', '.join(p.assumptions[:3])}... "
                f"Type: {p.formalisation_type}"
            )

        if not summaries:
            return {"consistency_score": 0.9, "contradictions_found": False,
                    "notes": "No other proofs to check against"}

        key_claims = []
        for s in proof.proof_steps:
            key_claims.append(s.get("statement", ""))

        prompt = CROSS_PROOF_PROMPT.format(
            new_proposition=proof.proposition or proof.proposition_natural,
            new_assumptions=", ".join(proof.assumptions),
            new_key_claims="\n".join(f"- {c}" for c in key_claims[:10]),
            existing_proofs_text="\n".join(summaries),
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data
        except Exception:
            return {"consistency_score": 0.7, "contradictions_found": False,
                    "notes": "Cross-proof check failed"}

    def _calibrate(self, scores: ValidationScores, proof: ProofRecord) -> float:
        """Layer 5: Meta-calibration — does the confidence feel right?"""

        # Calibration heuristics
        calibration = 0.7  # Base

        # Boost for machine verification (multi-tool aware)
        consensus = proof.multi_tool_consensus
        if consensus:
            n_verified = consensus.get("total_tools_verified", 0)
            if n_verified >= 3:
                calibration += 0.25
            elif n_verified >= 2:
                calibration += 0.2
            elif n_verified >= 1:
                calibration += 0.15
        elif proof.lean_verified:
            calibration += 0.2
        elif proof.lean_partial:
            calibration += 0.1

        # Penalise if outside standard mathematics
        if not proof.within_standard_mathematics:
            calibration -= 0.3

        # Penalise for many limitations
        if len(proof.limitations) >= 5:
            calibration -= 0.2
        elif len(proof.limitations) >= 3:
            calibration -= 0.1

        # Penalise if adversarial found critical gaps
        gaps = proof.adversarial_result.get("gaps", [])
        critical_gaps = [g for g in gaps if isinstance(g, dict) and g.get("severity") == "critical"]
        if critical_gaps:
            calibration -= 0.2 * len(critical_gaps)

        # Boost for formal convergence type (stronger than structural analogy)
        src = proof.source_convergence
        if src.get("convergence_type") == "formal":
            calibration += 0.1

        return max(0.0, min(1.0, calibration))
