"""Z3 SMT Solver Bridge — automated logical verification.

Uses Z3 to check logical validity of proof propositions and steps.
Claude translates the proof into Z3-Py code; Z3 does the actual verification.
The verification verdict is EXTERNAL — Z3, not Claude.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from logos.api import ClaudeAPI
from logos.models import ProofRecord, LogRecord


SYSTEM_PROMPT = (
    "You are a Z3 SMT solver expert. You translate mathematical propositions and proofs "
    "into Z3-Py (Python z3 module) scripts that check validity. "
    "Your generated scripts MUST print a clear verdict: VERIFIED, PARTIAL, or FAILED. "
    "Be precise. Use z3.Solver, z3.prove, or z3.ForAll/z3.Exists as appropriate."
)

Z3_FEASIBILITY_PROMPT = """Assess whether this mathematical proof can be checked by Z3 SMT solver.

PROPOSITION: {proposition}

PROOF TYPE: {formalisation_type}

MATHEMATICAL APPARATUS: {apparatus}

PROOF STEPS:
{steps_text}

ASSUMPTIONS:
{assumptions}

Z3 can handle:
- Propositional/predicate logic
- Linear/non-linear arithmetic (integer and real)
- Arrays, bit-vectors, datatypes
- Quantified formulas (with heuristics)
- Fixed-point reasoning

Z3 CANNOT handle well:
- Higher-order logic / dependent types
- Category theory / abstract algebra (without encoding)
- Topological arguments
- Most analysis (limits, continuity, measure theory)

Return JSON:
{{
    "feasible": true/false,
    "partial": true/false,
    "difficulty": "easy" | "moderate" | "hard" | "infeasible",
    "checkable_steps": [list of step numbers that Z3 can check],
    "notes": "explanation"
}}"""

Z3_GENERATE_PROMPT = """Generate a Z3-Py script to verify this proof.

PROPOSITION: {proposition}

PROOF STEPS:
{steps_text}

ASSUMPTIONS:
{assumptions}

CHECKABLE STEPS: {checkable_steps}

RULES:
1. Script must be self-contained Python using only `from z3 import *`
2. Script must print exactly one of: "VERDICT: VERIFIED", "VERDICT: PARTIAL", "VERDICT: FAILED"
3. For PARTIAL, also print which steps passed/failed
4. Check each checkable step independently where possible
5. Use appropriate Z3 types (Int, Real, Bool, etc.)
6. Set a timeout: set_option("timeout", 30000) at the top
7. Do NOT use sorry or placeholders — if a step can't be encoded, skip it and note why
8. Print step-by-step results: "STEP N: PASSED/FAILED/SKIPPED"

Return JSON:
{{
    "z3_script": "the complete Python script",
    "steps_encoded": [list of step numbers encoded],
    "steps_skipped": [list of step numbers skipped with reasons],
    "notes": "explanation of encoding choices"
}}"""


class Z3Bridge:
    """Z3 SMT solver verification bridge."""

    def __init__(self, api: ClaudeAPI):
        self.api = api
        self._z3_available = self._check_z3()

    @staticmethod
    def _check_z3() -> bool:
        """Check if z3 module is importable."""
        try:
            import z3  # noqa: F401
            return True
        except ImportError:
            return False

    @property
    def z3_available(self) -> bool:
        return self._z3_available

    def assess_feasibility(self, proof: ProofRecord) -> dict:
        """Check whether this proof can be verified by Z3."""
        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        prompt = Z3_FEASIBILITY_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            formalisation_type=proof.formalisation_type,
            apparatus=", ".join(proof.mathematical_apparatus),
            steps_text=steps_text or "(no structured steps)",
            assumptions=", ".join(proof.assumptions) or "(none)",
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data
        except Exception:
            return {"feasible": False, "partial": False, "difficulty": "unknown",
                    "notes": "Feasibility assessment failed"}

    def generate_z3_script(self, proof: ProofRecord, feasibility: dict, log: LogRecord) -> str:
        """Generate Z3-Py verification script."""
        if not feasibility.get("feasible") and not feasibility.get("partial"):
            log.add_decision(
                step="z3_generation",
                choice="skipped",
                alternatives=[],
                reasoning=f"Z3 verification not feasible: {feasibility.get('notes', '')}",
            )
            return ""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        checkable = feasibility.get("checkable_steps", [])

        prompt = Z3_GENERATE_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            steps_text=steps_text or "(no structured steps)",
            assumptions=", ".join(proof.assumptions) or "(none)",
            checkable_steps=", ".join(str(s) for s in checkable) if checkable else "all",
        )

        try:
            data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
            script = data.get("z3_script", "")

            log.add_decision(
                step="z3_generation",
                choice=f"Generated {len(script)} chars, "
                       f"{len(data.get('steps_encoded', []))} steps encoded",
                alternatives=[],
                reasoning=data.get("notes", ""),
            )
            return script
        except Exception as e:
            log.add_decision(
                step="z3_generation",
                choice="failed",
                alternatives=[],
                reasoning=str(e),
            )
            return ""

    def run_z3_script(self, script: str) -> dict:
        """Execute a Z3-Py script and parse the verdict.

        Runs in a subprocess for safety. Parses stdout for VERDICT line.
        """
        if not script:
            return {"verified": False, "reason": "no_script", "output": ""}

        if not self._z3_available:
            return {"verified": False, "reason": "z3_not_available",
                    "output": "Z3 not installed"}

        try:
            with tempfile.NamedTemporaryFile(
                mode="w", suffix=".py", delete=False
            ) as f:
                f.write(script)
                temp_path = f.name

            result = subprocess.run(
                [sys.executable, temp_path],
                capture_output=True,
                text=True,
                timeout=60,
            )

            Path(temp_path).unlink(missing_ok=True)

            output = result.stdout.strip()
            stderr = result.stderr.strip()

            # Parse verdict from output
            if "VERDICT: VERIFIED" in output:
                return {"verified": True, "partial": False,
                        "reason": "z3_verified", "output": output}
            elif "VERDICT: PARTIAL" in output:
                return {"verified": False, "partial": True,
                        "reason": "z3_partial", "output": output}
            elif "VERDICT: FAILED" in output:
                return {"verified": False, "partial": False,
                        "reason": "z3_failed", "output": output}
            elif result.returncode != 0:
                return {"verified": False, "reason": "script_error",
                        "output": output, "stderr": stderr}
            else:
                return {"verified": False, "reason": "no_verdict",
                        "output": output}

        except subprocess.TimeoutExpired:
            Path(temp_path).unlink(missing_ok=True)
            return {"verified": False, "reason": "timeout",
                    "output": "Z3 script timed out after 60s"}
        except Exception as e:
            return {"verified": False, "reason": "error", "output": str(e)}

    def _retry_script(self, script: str, error: str, proof: ProofRecord) -> str:
        """Ask Claude to fix a broken Z3 script given the error message."""
        prompt = (
            f"This Z3-Py verification script failed with an error. Fix it.\n\n"
            f"ORIGINAL SCRIPT:\n```python\n{script}\n```\n\n"
            f"ERROR:\n{error[:1000]}\n\n"
            f"PROPOSITION BEING VERIFIED:\n{proof.proposition or proof.proposition_natural}\n\n"
            f"Fix the script so it runs without errors. Keep the same verification logic.\n"
            f"Return JSON:\n"
            f'{{"z3_script": "the fixed Python script", "fix_notes": "what was wrong"}}'
        )
        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data.get("z3_script", "")
        except Exception:
            return ""

    def process(self, proof: ProofRecord, log: LogRecord) -> None:
        """Full Z3 pipeline: assess → generate → verify → retry if script errors.

        Modifies proof in place with Z3 results.
        """
        feasibility = self.assess_feasibility(proof)
        script = self.generate_z3_script(proof, feasibility, log)

        if not script:
            proof.z3_verified = False
            proof.z3_result = {
                "verified": False,
                "reason": "not_feasible",
                "feasibility": feasibility,
            }
            return

        result = self.run_z3_script(script)

        # Retry once if script had a runtime error
        if result.get("reason") == "script_error" and (result.get("stderr") or result.get("output")):
            error_msg = result.get("stderr", "") or result.get("output", "")
            log.add_decision(
                step="z3_retry",
                choice="retrying",
                alternatives=[],
                reasoning=f"Script error: {error_msg[:200]}",
            )
            fixed_script = self._retry_script(script, error_msg, proof)
            if fixed_script:
                result = self.run_z3_script(fixed_script)

        proof.z3_verified = result.get("verified", False)
        proof.z3_result = result

        # Update verification status if Z3 verified
        if proof.z3_verified:
            if proof.verification_status == "natural_language_only":
                proof.verification_status = "machine_verified"
