"""Lean 4 Bridge — code generation and verification.

Uses `lake env lean` within the lean_verify/ Mathlib project so all
Mathlib imports resolve correctly. Runs locally in seconds.
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
from pathlib import Path

from logos.api import ClaudeAPI
from logos.config import LogosConfig
from logos.models import ProofRecord, LogRecord
from logos.prompts.lean_gen import LEAN_FEASIBILITY_PROMPT, LEAN_GENERATE_PROMPT


SYSTEM_PROMPT = (
    "You are a Lean 4 expert with deep knowledge of current Mathlib. "
    "Generate valid, idiomatic Lean 4 code that type-checks with the latest Mathlib. "
    "Use sorry ONLY for parts that genuinely cannot be formalised yet. "
    "Add clear comments explaining each sorry. "
    "CRITICAL: Use only import paths that exist in current Mathlib (2025). "
    "Many old paths have been reorganised. When unsure, use broader imports."
)

# Auto-detect paths
_PROJECT_ROOT = Path(__file__).parent.parent
_LEAN_PROJECT = _PROJECT_ROOT / "lean_verify"
_LAKE_BIN = os.path.expanduser("~/.elan/bin/lake")
_LEAN_BIN = os.path.expanduser("~/.elan/bin/lean")


def _detect_lean() -> bool:
    """Check if lean_verify project and lean binary exist."""
    return (
        Path(_LAKE_BIN).exists()
        and Path(_LEAN_BIN).exists()
        and _LEAN_PROJECT.exists()
        and ((_LEAN_PROJECT / "lakefile.lean").exists() or (_LEAN_PROJECT / "lakefile.toml").exists())
    )


class LeanBridge:
    """Lean 4 code generation and verification bridge."""

    def __init__(self, api: ClaudeAPI, config: LogosConfig):
        self.api = api
        self.config = config
        self._lean_available = _detect_lean()

    @property
    def lean_available(self) -> bool:
        return self._lean_available

    def assess_feasibility(self, proof: ProofRecord) -> dict:
        """Check whether this proof can be formalised in Lean 4."""
        key_theorems = [d.get("name", "") for d in proof.dependencies_literature]

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
                "feasible": False, "partial": False,
                "difficulty": "unknown",
                "notes": "Feasibility assessment failed",
            }

    def generate_lean(self, proof: ProofRecord, feasibility: dict, log: LogRecord) -> str:
        """Generate Lean 4 code for the proof."""
        if not feasibility.get("feasible") and not feasibility.get("partial"):
            log.add_decision(
                step="lean_generation", choice="skipped", alternatives=[],
                reasoning=f"Not feasible: {feasibility.get('notes', '')}",
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
            log.add_decision(
                step="lean_generation",
                choice=f"Generated {len(lean_code)} chars, {data.get('sorry_count', 0)} sorry(s)",
                alternatives=[], reasoning=data.get("notes", ""),
            )
            return lean_code
        except Exception as e:
            log.add_decision(
                step="lean_generation", choice="failed",
                alternatives=[], reasoning=str(e),
            )
            return ""

    def verify_lean(self, lean_code: str) -> dict:
        """Type-check Lean code using `lake env lean` within the Mathlib project."""
        if not lean_code:
            return {"verified": False, "reason": "no_code", "errors": []}

        if not self._lean_available:
            return {
                "verified": False, "reason": "lean_not_available", "errors": [],
                "note": "Lean/Mathlib project not found. Code generated but unverified.",
            }

        try:
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".lean", dir=str(_LEAN_PROJECT), delete=False
            ) as f:
                f.write(lean_code)
                temp_path = f.name

            result = subprocess.run(
                [_LAKE_BIN, "env", _LEAN_BIN, temp_path],
                capture_output=True, text=True,
                timeout=self.config.lean_timeout_seconds,
                cwd=str(_LEAN_PROJECT),
            )

            Path(temp_path).unlink(missing_ok=True)

            # Lean outputs errors to stdout (not stderr)
            output = (result.stdout + "\n" + result.stderr).strip()
            has_error = "error:" in output.lower()

            if result.returncode == 0 and not has_error:
                has_sorry = bool(re.search(r'\bsorry\b', lean_code))
                return {
                    "verified": not has_sorry,
                    "partial": has_sorry,
                    "reason": "type_check_passed" if not has_sorry else "type_check_passed_with_sorry",
                    "sorry_count": len(re.findall(r'\bsorry\b', lean_code)),
                    "errors": [],
                }
            else:
                errors = [l for l in output.split("\n") if "error" in l.lower()][:5]
                return {
                    "verified": False, "reason": "type_check_failed",
                    "errors": errors or [output[:200]],
                }

        except subprocess.TimeoutExpired:
            Path(temp_path).unlink(missing_ok=True)
            return {
                "verified": False, "reason": "timeout",
                "errors": [f"Lean timed out after {self.config.lean_timeout_seconds}s"],
            }
        except Exception as e:
            return {"verified": False, "reason": "error", "errors": [str(e)]}

    def count_sorrys(self, lean_code: str) -> int:
        return len(re.findall(r'\bsorry\b', lean_code))

    def eliminate_sorrys(self, proof: ProofRecord, log: LogRecord, max_iterations: int = 2) -> int:
        """Try to fill sorry gaps. Returns number eliminated."""
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

            prompt = (
                f"This Lean 4 code has {current_sorrys} sorry gap(s). "
                f"Replace as many sorrys as possible with actual proofs. "
                f"Keep the code structure intact. If a sorry genuinely cannot be "
                f"filled, leave it with a comment.\n\n"
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
                    break

                result = self.verify_lean(new_code)
                if result.get("verified") or result.get("partial"):
                    eliminated = current_sorrys - new_sorrys
                    current_code = new_code
                    current_sorrys = new_sorrys
                    log.add_decision(
                        step=f"sorry_elimination_iter_{iteration+1}",
                        choice=f"eliminated_{eliminated}_sorrys",
                        alternatives=[],
                        reasoning=f"{current_sorrys} remaining. {data.get('notes', '')}",
                    )
                else:
                    break
            except Exception:
                break

        total_eliminated = initial_sorrys - current_sorrys
        if total_eliminated > 0:
            proof.proof_lean = current_code
            result = self.verify_lean(current_code)
            proof.lean_verified = result.get("verified", False)
            proof.lean_partial = result.get("partial", False)

        return total_eliminated

    def process(self, proof: ProofRecord, log: LogRecord) -> None:
        """Full Lean pipeline: assess feasibility -> generate -> verify -> eliminate sorrys."""
        feasibility = self.assess_feasibility(proof)
        lean_code = self.generate_lean(proof, feasibility, log)
        proof.proof_lean = lean_code

        if not lean_code:
            proof.lean_verified = False
            proof.lean_partial = False
            proof.lean_failure_reason = feasibility.get("notes", "Not feasible")
            return

        result = self.verify_lean(lean_code)
        proof.lean_verified = result.get("verified", False)
        proof.lean_partial = result.get("partial", False)

        if not proof.lean_verified and not proof.lean_partial:
            proof.lean_failure_reason = "; ".join(result.get("errors", ["Unknown"]))

        if proof.lean_partial and self.count_sorrys(lean_code) > 0:
            self.eliminate_sorrys(proof, log)

        if proof.lean_verified:
            proof.verification_status = "machine_verified"
        elif proof.lean_partial:
            proof.verification_status = "partially_verified"
        else:
            proof.verification_status = "natural_language_only"
