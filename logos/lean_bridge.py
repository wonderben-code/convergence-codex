"""Lean 4 Bridge — code generation and verification.

Works WITHOUT Lean installed (generates code, marks as unverified).
With Lean on PATH, also type-checks generated code.
"""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

from logos.api import ClaudeAPI
from logos.config import LogosConfig
from logos.models import ProofRecord, LogRecord
from logos.prompts.lean_gen import LEAN_FEASIBILITY_PROMPT, LEAN_GENERATE_PROMPT


SYSTEM_PROMPT = (
    "You are a Lean 4 expert. Generate valid, idiomatic Lean 4 code with Mathlib imports. "
    "Use sorry for parts that cannot be formalised, with clear comments explaining why."
)


class LeanBridge:
    """Lean 4 code generation and verification bridge."""

    def __init__(self, api: ClaudeAPI, config: LogosConfig):
        self.api = api
        self.config = config
        self._lean_available = bool(config.lean_binary)

    @property
    def lean_available(self) -> bool:
        """Whether Lean 4 is available for verification."""
        return self._lean_available

    def assess_feasibility(self, proof: ProofRecord) -> dict:
        """Check whether this proof can be formalised in Lean 4."""

        # Build key theorems list from dependencies
        key_theorems = [
            d.get("name", "") for d in proof.dependencies_literature
        ]

        prompt = LEAN_FEASIBILITY_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            apparatus=", ".join(proof.mathematical_apparatus),
            key_theorems=", ".join(key_theorems) or "(none specified)",
            mathlib_coverage="unknown",
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data
        except Exception:
            return {
                "feasible": False,
                "partial": False,
                "difficulty": "unknown",
                "notes": "Feasibility assessment failed",
            }

    def generate_lean(self, proof: ProofRecord, feasibility: dict, log: LogRecord) -> str:
        """Generate Lean 4 code for the proof."""

        if not feasibility.get("feasible") and not feasibility.get("partial"):
            log.add_decision(
                step="lean_generation",
                choice="skipped",
                alternatives=[],
                reasoning=f"Lean formalisation not feasible: {feasibility.get('notes', '')}",
            )
            return ""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        prompt = LEAN_GENERATE_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            steps_text=steps_text,
            available_in_mathlib=", ".join(feasibility.get("available_in_mathlib", [])),
            missing_from_mathlib=", ".join(feasibility.get("missing_from_mathlib", [])),
        )

        try:
            data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
            lean_code = data.get("lean_code", "")
            sorry_count = data.get("sorry_count", 0)

            log.add_decision(
                step="lean_generation",
                choice=f"Generated {len(lean_code)} chars, {sorry_count} sorry(s)",
                alternatives=[],
                reasoning=data.get("notes", ""),
            )

            return lean_code
        except Exception as e:
            log.add_decision(
                step="lean_generation",
                choice="failed",
                alternatives=[],
                reasoning=str(e),
            )
            return ""

    def verify_lean(self, lean_code: str) -> dict:
        """Type-check Lean code using the lean binary.

        Returns verification result. Works gracefully when Lean is not installed.
        """
        if not lean_code:
            return {"verified": False, "reason": "no_code", "errors": []}

        if not self._lean_available:
            return {
                "verified": False,
                "reason": "lean_not_available",
                "errors": [],
                "note": "Lean 4 not found on PATH. Code generated but unverified.",
            }

        # Write to temp file and run lean
        try:
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", delete=False
            ) as f:
                f.write(lean_code)
                temp_path = f.name

            result = subprocess.run(
                [self.config.lean_binary, temp_path],
                capture_output=True,
                text=True,
                timeout=self.config.lean_timeout_seconds,
            )

            # Clean up
            Path(temp_path).unlink(missing_ok=True)

            if result.returncode == 0:
                has_sorry = "sorry" in lean_code.lower()
                return {
                    "verified": not has_sorry,
                    "partial": has_sorry,
                    "reason": "type_check_passed" if not has_sorry else "type_check_passed_with_sorry",
                    "errors": [],
                    "warnings": result.stderr.strip().split("\n") if result.stderr.strip() else [],
                }
            else:
                errors = result.stderr.strip().split("\n") if result.stderr else ["Unknown error"]
                return {
                    "verified": False,
                    "reason": "type_check_failed",
                    "errors": errors,
                }

        except subprocess.TimeoutExpired:
            return {
                "verified": False,
                "reason": "timeout",
                "errors": [f"Lean timed out after {self.config.lean_timeout_seconds}s"],
            }
        except Exception as e:
            return {
                "verified": False,
                "reason": "error",
                "errors": [str(e)],
            }

    def count_sorrys(self, lean_code: str) -> int:
        """Count sorry occurrences in Lean code."""
        import re
        return len(re.findall(r'\bsorry\b', lean_code))

    def eliminate_sorrys(self, proof: ProofRecord, log: LogRecord, max_iterations: int = 3) -> int:
        """Iteratively attempt to fill sorry gaps in Lean code.

        Each iteration:
        1. Identify sorrys in the code
        2. Ask Claude to fill them
        3. Re-run Lean to verify
        4. Keep improvements, revert failures

        With Max Plan this is $0. Returns number of sorrys eliminated.

        Args:
            proof: ProofRecord with proof_lean code containing sorrys
            log: LogRecord for decision tracking
            max_iterations: Maximum attempts (default 3)

        Returns:
            Number of sorrys eliminated
        """
        if not proof.proof_lean or not self._lean_available:
            return 0

        initial_sorrys = self.count_sorrys(proof.proof_lean)
        if initial_sorrys == 0:
            return 0

        current_code = proof.proof_lean
        current_sorrys = initial_sorrys

        for iteration in range(max_iterations):
            if current_sorrys == 0:
                break

            # Ask Claude to fill sorrys
            prompt = (
                f"This Lean 4 code has {current_sorrys} sorry gap(s). "
                f"Replace as many sorrys as possible with actual proofs. "
                f"Keep the code structure intact. If a sorry genuinely cannot be "
                f"filled (e.g., requires results not in Mathlib), leave it.\n\n"
                f"```lean\n{current_code}\n```\n\n"
                f"Return JSON:\n"
                f'{{"lean_code": "the complete updated Lean code", '
                f'"sorrys_filled": N, "notes": "explanation"}}'
            )

            try:
                data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
                new_code = data.get("lean_code", "")
                if not new_code:
                    break

                new_sorrys = self.count_sorrys(new_code)
                if new_sorrys >= current_sorrys:
                    # No improvement
                    log.add_decision(
                        step=f"sorry_elimination_iter_{iteration+1}",
                        choice="no_improvement",
                        alternatives=[],
                        reasoning=f"Still {new_sorrys} sorrys after attempt",
                    )
                    break

                # Verify the new code type-checks
                result = self.verify_lean(new_code)
                if result.get("verified") or result.get("partial"):
                    # Improvement accepted
                    current_code = new_code
                    eliminated = current_sorrys - new_sorrys
                    current_sorrys = new_sorrys
                    log.add_decision(
                        step=f"sorry_elimination_iter_{iteration+1}",
                        choice=f"eliminated_{eliminated}_sorrys",
                        alternatives=[],
                        reasoning=f"{current_sorrys} sorrys remaining. {data.get('notes', '')}",
                    )
                else:
                    # New code doesn't type-check — revert
                    log.add_decision(
                        step=f"sorry_elimination_iter_{iteration+1}",
                        choice="reverted",
                        alternatives=[],
                        reasoning=f"Filled code failed type-check: {result.get('errors', [])[:2]}",
                    )

            except Exception as e:
                log.add_decision(
                    step=f"sorry_elimination_iter_{iteration+1}",
                    choice="error",
                    alternatives=[],
                    reasoning=str(e),
                )
                break

        # Update proof with best code
        total_eliminated = initial_sorrys - current_sorrys
        if total_eliminated > 0:
            proof.proof_lean = current_code
            # Re-verify
            result = self.verify_lean(current_code)
            proof.lean_verified = result.get("verified", False)
            proof.lean_partial = result.get("partial", False)

            log.add_decision(
                step="sorry_elimination_final",
                choice=f"eliminated_{total_eliminated}_of_{initial_sorrys}",
                alternatives=[],
                reasoning=f"Final: {current_sorrys} sorrys remaining. "
                          f"Lean verified={proof.lean_verified}, partial={proof.lean_partial}",
            )

        return total_eliminated

    def process(self, proof: ProofRecord, log: LogRecord) -> None:
        """Full Lean pipeline: assess feasibility → generate → verify → eliminate sorrys.

        Modifies proof in place with Lean results.
        """
        # Assess feasibility
        feasibility = self.assess_feasibility(proof)

        # Generate Lean code
        lean_code = self.generate_lean(proof, feasibility, log)
        proof.proof_lean = lean_code

        if not lean_code:
            proof.lean_verified = False
            proof.lean_partial = False
            proof.lean_failure_reason = feasibility.get("notes", "Not feasible for Lean formalisation")
            return

        # Verify
        result = self.verify_lean(lean_code)
        proof.lean_verified = result.get("verified", False)
        proof.lean_partial = result.get("partial", False)

        if not proof.lean_verified and not proof.lean_partial:
            proof.lean_failure_reason = "; ".join(result.get("errors", ["Unknown"]))

        # Sorry elimination — push partial proofs toward full verification
        if proof.lean_partial and self.count_sorrys(lean_code) > 0:
            self.eliminate_sorrys(proof, log)

        # Set verification status
        if proof.lean_verified:
            proof.verification_status = "machine_verified"
        elif proof.lean_partial:
            proof.verification_status = "partially_verified"
        else:
            proof.verification_status = "natural_language_only"
