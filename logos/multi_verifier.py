"""Lean Verifier — Lean 4 is the sole verification tool.

Simplified from the original 4-tool stack (Lean + Z3 + SymPy + Numerical).
Z3/SymPy/Numerical added massive time cost (5-10 min per proof, multiple Claude
calls each) with minimal value for novel cross-domain formalisations. Lean runs
locally in seconds and is the gold standard.

The MultiVerifier class name is preserved so all existing callers work unchanged.
"""

from __future__ import annotations

from logos.api import ClaudeAPI
from logos.config import LogosConfig
from logos.lean_bridge import LeanBridge
from logos.models import ProofRecord, LogRecord, VerificationTier


class MultiVerifier:
    """Lean-only verification. Generates Lean 4 code, verifies locally, fills sorry gaps.

    Usage:
        mv = MultiVerifier(api, config)
        mv.verify(proof, log)
    """

    def __init__(self, api: ClaudeAPI, config: LogosConfig):
        self.api = api
        self.config = config
        self.lean = LeanBridge(api, config)

    def verify(self, proof: ProofRecord, log: LogRecord) -> dict:
        """Run Lean verification and set tier/status on the proof.

        Modifies proof in place. Returns consensus dict for compatibility.
        """
        tools_run = []
        tools_verified = []
        tools_partial = []
        tools_failed = []

        log.add_decision(
            step="verify_lean",
            choice="starting",
            alternatives=[],
            reasoning="Lean 4 interactive theorem prover (sole verification tool)",
        )

        try:
            self.lean.process(proof, log)
            tools_run.append("lean")
            if proof.lean_verified:
                tools_verified.append("lean")
            elif proof.lean_partial:
                tools_partial.append("lean")
            else:
                tools_failed.append("lean")
        except Exception as e:
            log.add_decision(
                step="verify_lean",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # Determine tier
        tier = VerificationTier.from_proof(proof)
        proof.verification_tier = tier.value
        proof.verification_tier_reason = self._tier_reason(proof, tier)

        # Determine verification level
        if proof.lean_verified:
            verification_level = "fully_verified"
            proof.verification_status = "machine_verified"
        elif proof.lean_partial:
            verification_level = "partially_verified"
            if proof.verification_status == "natural_language_only":
                proof.verification_status = "partially_verified"
        else:
            verification_level = "natural_language_only"

        # Coverage
        total_steps = len(proof.proof_steps) or 1
        if proof.lean_verified:
            steps_covered = total_steps
        elif proof.lean_partial:
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            steps_covered = max(0, total_steps - sorrys)
        else:
            steps_covered = 0

        coverage_pct = round(100 * steps_covered / total_steps, 1)
        coverage = {
            "coverage_percentage": coverage_pct,
            "steps_total": total_steps,
            "steps_machine_verified": steps_covered,
        }
        proof.coverage_percentage = coverage_pct
        proof.coverage_detail = coverage

        consensus = {
            "tools_run": tools_run,
            "tools_verified": tools_verified,
            "tools_partial": tools_partial,
            "tools_failed": tools_failed,
            "tools_skipped": [],
            "tool_scores": {"lean": 1.0 if proof.lean_verified else 0.5 if proof.lean_partial else 0.0},
            "consensus_score": 1.0 if proof.lean_verified else 0.5 if proof.lean_partial else 0.0,
            "verification_level": verification_level,
            "verification_tier": tier.value,
            "total_tools_attempted": len(tools_run),
            "total_tools_verified": len(tools_verified),
            "coverage": coverage,
        }

        proof.multi_tool_consensus = consensus

        log.add_decision(
            step="verify_result",
            choice=f"tier={tier.value}, level={verification_level}, coverage={coverage_pct:.0f}%",
            alternatives=[],
            reasoning=proof.verification_tier_reason,
        )

        return consensus

    def _tier_reason(self, proof: ProofRecord, tier: VerificationTier) -> str:
        if tier == VerificationTier.PROVEN:
            return "Full Lean 4 proof with 0 sorry gaps — machine verified"
        if tier == VerificationTier.PROOF_WITH_GAPS:
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            return f"Lean type-checks, {sorrys} sorry gap(s) remain"
        if tier == VerificationTier.RIGOROUS_ARGUMENT:
            if proof.lean_failure_reason:
                return f"Lean failed: {proof.lean_failure_reason[:100]}"
            return "Structured proof generated but Lean could not verify"
        return "No proof generated"
