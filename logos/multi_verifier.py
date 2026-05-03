"""Multi-Tool Verifier — orchestrates Lean, Z3, SymPy, and Numerical verification.

4-tier verification stack:
  1. Lean 4 (full interactive theorem proving — strongest)
  2. Z3 SMT (automated logical verification)
  3. SymPy (algebraic/symbolic verification)
  4. Numerical (NumPy/SciPy sanity checks — weakest but broadest)

Consensus scoring across all tools. A proof verified by multiple independent
external tools has much higher confidence than one verified by none.
"""

from __future__ import annotations

from logos.api import ClaudeAPI
from logos.config import LogosConfig
from logos.lean_bridge import LeanBridge
from logos.z3_bridge import Z3Bridge
from logos.sympy_bridge import SymPyBridge
from logos.numerical_bridge import NumericalBridge
from logos.back_translation import BackTranslator
from logos.models import ProofRecord, LogRecord, VerificationTier


# Tool weights for consensus scoring
TOOL_WEIGHTS = {
    "lean": 0.40,       # Strongest — full interactive theorem prover
    "z3": 0.25,         # Strong — automated SMT solving
    "sympy": 0.20,      # Good — algebraic verification
    "numerical": 0.15,  # Weakest — sanity check only
}


class MultiVerifier:
    """Orchestrates all 4 verification tools with consensus scoring.

    Usage:
        mv = MultiVerifier(api, config)
        mv.verify(proof, log)
        # proof.multi_tool_consensus now contains:
        # {
        #   "tools_run": ["lean", "z3", "sympy", "numerical"],
        #   "tools_verified": ["z3", "sympy"],
        #   "consensus_score": 0.72,
        #   "verification_level": "multi_tool_verified",
        # }
    """

    def __init__(self, api: ClaudeAPI, config: LogosConfig):
        self.api = api
        self.config = config
        self.lean = LeanBridge(api, config)
        self.z3 = Z3Bridge(api)
        self.sympy = SymPyBridge(api)
        self.numerical = NumericalBridge(api)
        self.back_translator = BackTranslator(api)

    def verify(self, proof: ProofRecord, log: LogRecord) -> dict:
        """Run all applicable verification tools and compute consensus.

        Modifies proof in place with results from each tool.

        Returns:
            Consensus dict with scores and verification level.
        """
        tools_run = []
        tools_verified = []
        tools_partial = []
        tools_failed = []
        tools_skipped = []
        tool_scores = {}

        # ─── TIER 1: LEAN 4 ───
        log.add_decision(
            step="multi_verify_lean",
            choice="starting",
            alternatives=[],
            reasoning="Tier 1: Lean 4 interactive theorem prover",
        )
        try:
            self.lean.process(proof, log)
            tools_run.append("lean")
            if proof.lean_verified:
                tools_verified.append("lean")
                tool_scores["lean"] = 1.0
            elif proof.lean_partial:
                tools_partial.append("lean")
                tool_scores["lean"] = 0.5
            else:
                tools_failed.append("lean")
                tool_scores["lean"] = 0.0
        except Exception as e:
            tools_skipped.append("lean")
            tool_scores["lean"] = 0.0
            log.add_decision(
                step="multi_verify_lean",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # ─── TIER 2: Z3 SMT ───
        log.add_decision(
            step="multi_verify_z3",
            choice="starting",
            alternatives=[],
            reasoning="Tier 2: Z3 SMT solver",
        )
        try:
            self.z3.process(proof, log)
            tools_run.append("z3")
            if proof.z3_verified:
                tools_verified.append("z3")
                tool_scores["z3"] = 1.0
            elif proof.z3_result.get("partial"):
                tools_partial.append("z3")
                tool_scores["z3"] = 0.5
            else:
                tools_failed.append("z3")
                tool_scores["z3"] = 0.0
        except Exception as e:
            tools_skipped.append("z3")
            tool_scores["z3"] = 0.0
            log.add_decision(
                step="multi_verify_z3",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # ─── TIER 3: SYMPY ───
        log.add_decision(
            step="multi_verify_sympy",
            choice="starting",
            alternatives=[],
            reasoning="Tier 3: SymPy algebraic verification",
        )
        try:
            self.sympy.process(proof, log)
            tools_run.append("sympy")
            if proof.sympy_verified:
                tools_verified.append("sympy")
                tool_scores["sympy"] = 1.0
            elif proof.sympy_result.get("partial"):
                tools_partial.append("sympy")
                tool_scores["sympy"] = 0.5
            else:
                tools_failed.append("sympy")
                tool_scores["sympy"] = 0.0
        except Exception as e:
            tools_skipped.append("sympy")
            tool_scores["sympy"] = 0.0
            log.add_decision(
                step="multi_verify_sympy",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # ─── TIER 4: NUMERICAL ───
        log.add_decision(
            step="multi_verify_numerical",
            choice="starting",
            alternatives=[],
            reasoning="Tier 4: Numerical sanity checks (NumPy/SciPy)",
        )
        try:
            self.numerical.process(proof, log)
            tools_run.append("numerical")
            if proof.numerical_consistent:
                if proof.numerical_result.get("applicable", True):
                    tools_verified.append("numerical")
                    tool_scores["numerical"] = 1.0
                else:
                    # Not applicable — don't count
                    tools_skipped.append("numerical")
                    tool_scores["numerical"] = 0.0
            elif proof.numerical_result.get("partial"):
                tools_partial.append("numerical")
                tool_scores["numerical"] = 0.5
            else:
                tools_failed.append("numerical")
                tool_scores["numerical"] = 0.0
        except Exception as e:
            tools_skipped.append("numerical")
            tool_scores["numerical"] = 0.0
            log.add_decision(
                step="multi_verify_numerical",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # ─── BACK-TRANSLATION ALIGNMENT ───
        log.add_decision(
            step="back_translation",
            choice="starting",
            alternatives=[],
            reasoning="Checking proposition-claim alignment via back-translation",
        )
        try:
            self.back_translator.check_alignment(proof, log)
        except Exception as e:
            log.add_decision(
                step="back_translation",
                choice="error",
                alternatives=[],
                reasoning=str(e),
            )

        # ─── CONSENSUS SCORING ───
        consensus_score = self._compute_consensus(tool_scores)
        verification_level = self._determine_level(
            tools_verified, tools_partial, tools_run
        )

        # ─── TIERED FORMALISATION ───
        tier = VerificationTier.from_proof(proof)
        proof.verification_tier = tier.value
        proof.verification_tier_reason = self._tier_reason(proof, tier)

        # ─── COVERAGE METRICS ───
        coverage = self._compute_coverage(proof, tools_verified, tools_partial)
        proof.coverage_percentage = coverage["coverage_percentage"]
        proof.coverage_detail = coverage

        consensus = {
            "tools_run": tools_run,
            "tools_verified": tools_verified,
            "tools_partial": tools_partial,
            "tools_failed": tools_failed,
            "tools_skipped": tools_skipped,
            "tool_scores": tool_scores,
            "consensus_score": round(consensus_score, 3),
            "verification_level": verification_level,
            "verification_tier": tier.value,
            "total_tools_attempted": len(tools_run),
            "total_tools_verified": len(tools_verified),
            "coverage": coverage,
            "back_translation_aligned": proof.back_translation_alignment.get("is_aligned", True),
        }

        proof.multi_tool_consensus = consensus

        # Update overall verification status based on consensus
        if verification_level == "fully_verified":
            proof.verification_status = "machine_verified"
        elif verification_level in ("multi_tool_verified", "single_tool_verified"):
            if proof.verification_status == "natural_language_only":
                proof.verification_status = "machine_verified"
        elif verification_level == "partially_verified":
            if proof.verification_status == "natural_language_only":
                proof.verification_status = "partially_verified"

        log.add_decision(
            step="multi_verify_consensus",
            choice=f"tier={tier.value}, level={verification_level}, "
                   f"score={consensus_score:.3f}, coverage={coverage['coverage_percentage']:.0f}%, "
                   f"verified={len(tools_verified)}/{len(tools_run)}",
            alternatives=[],
            reasoning=f"Tools verified: {tools_verified}. "
                       f"Partial: {tools_partial}. "
                       f"Failed: {tools_failed}. "
                       f"Skipped: {tools_skipped}. "
                       f"Tier reason: {proof.verification_tier_reason}",
        )

        return consensus

    def _compute_consensus(self, tool_scores: dict) -> float:
        """Compute weighted consensus score from individual tool results."""
        total_weight = 0.0
        weighted_sum = 0.0

        for tool, score in tool_scores.items():
            weight = TOOL_WEIGHTS.get(tool, 0.1)
            # Only count tools that were actually attempted (score > 0 or explicitly failed)
            if tool in TOOL_WEIGHTS:
                total_weight += weight
                weighted_sum += weight * score

        if total_weight == 0:
            return 0.0

        return weighted_sum / total_weight

    def _determine_level(
        self,
        verified: list[str],
        partial: list[str],
        run: list[str],
    ) -> str:
        """Determine the verification level from tool results."""
        n_verified = len(verified)
        n_partial = len(partial)

        if n_verified >= 4:
            return "fully_verified"
        elif n_verified >= 2:
            return "multi_tool_verified"
        elif n_verified >= 1:
            return "single_tool_verified"
        elif n_partial >= 1:
            return "partially_verified"
        else:
            return "natural_language_only"

    def _compute_coverage(
        self, proof: ProofRecord,
        tools_verified: list[str], tools_partial: list[str],
    ) -> dict:
        """Compute what percentage of the proof is machine-verified.

        Considers how many proof steps each tool checked and computes
        a combined unique coverage percentage.
        """
        total_steps = len(proof.proof_steps) or 1
        steps_covered = set()

        # Lean: if verified/partial, consider all steps covered by Lean
        if "lean" in tools_verified:
            steps_covered.update(range(total_steps))
        elif "lean" in tools_partial:
            # Partial — estimate coverage from sorry count
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            covered = max(0, total_steps - sorrys)
            steps_covered.update(range(covered))

        # Z3: check which steps were encoded
        z3_steps = proof.z3_result.get("output", "")
        for i in range(total_steps):
            if f"STEP {i+1}: PASSED" in z3_steps:
                steps_covered.add(i)

        # SymPy: check which steps were encoded
        sympy_steps = proof.sympy_result.get("output", "")
        for i in range(total_steps):
            if f"STEP {i+1}: PASSED" in sympy_steps:
                steps_covered.add(i)

        # Numerical: if consistent, adds weak coverage to all steps
        # (doesn't add to steps_covered — numerical isn't proof)

        coverage_pct = round(100 * len(steps_covered) / total_steps, 1)

        return {
            "coverage_percentage": coverage_pct,
            "steps_total": total_steps,
            "steps_machine_verified": len(steps_covered),
            "steps_covered_by": {
                "lean": "lean" in tools_verified or "lean" in tools_partial,
                "z3": "z3" in tools_verified,
                "sympy": "sympy" in tools_verified,
                "numerical": proof.numerical_consistent,
            },
        }

    def _tier_reason(self, proof: ProofRecord, tier: VerificationTier) -> str:
        """Explain why the proof is at this tier and not higher."""
        if tier == VerificationTier.PROVEN:
            return "Full Lean 4 proof with 0 sorry gaps — machine verified"

        reasons = []
        if tier != VerificationTier.PROVEN:
            if proof.lean_partial:
                sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
                reasons.append(f"Lean: {sorrys} sorry gap(s) remain")
            elif proof.lean_failure_reason:
                reasons.append(f"Lean: {proof.lean_failure_reason[:80]}")
            elif not proof.proof_lean:
                reasons.append("Lean: not feasible for this proof type")

        if tier == VerificationTier.PROOF_WITH_GAPS:
            return "; ".join(reasons) or "Lean type-checks but sorry gaps remain"

        if tier == VerificationTier.FORMALLY_VERIFIED:
            verified_by = []
            if proof.z3_verified:
                verified_by.append("Z3")
            if proof.sympy_verified:
                verified_by.append("SymPy")
            return f"Verified by {', '.join(verified_by)}. {'; '.join(reasons)}"

        if tier == VerificationTier.NUMERICALLY_CONFIRMED:
            reasons.append("No formal tool could verify, but numerical tests pass")
            return "; ".join(reasons)

        if tier == VerificationTier.RIGOROUS_ARGUMENT:
            reasons.append("Structured proof generated but no external tool could verify")
            return "; ".join(reasons)

        return "No proof generated"
