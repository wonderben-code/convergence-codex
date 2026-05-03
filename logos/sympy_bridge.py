"""SymPy Bridge — algebraic and symbolic verification.

Uses SymPy to verify algebraic identities, equation manipulations,
and symbolic relationships in proofs. Claude generates SymPy verification
scripts; SymPy does the actual computation. Verdict is EXTERNAL.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from logos.api import ClaudeAPI
from logos.models import ProofRecord, LogRecord


SYSTEM_PROMPT = (
    "You are a SymPy expert. You translate mathematical proofs into SymPy scripts "
    "that verify algebraic identities, equation manipulations, and symbolic relationships. "
    "Your scripts MUST print a clear verdict: VERIFIED, PARTIAL, or FAILED. "
    "Use sympy.simplify, sympy.expand, sympy.Eq, sympy.solve, etc. as appropriate."
)

SYMPY_FEASIBILITY_PROMPT = """Assess whether this mathematical proof can be checked by SymPy.

PROPOSITION: {proposition}

PROOF TYPE: {formalisation_type}

MATHEMATICAL APPARATUS: {apparatus}

PROOF STEPS:
{steps_text}

ASSUMPTIONS:
{assumptions}

SymPy excels at:
- Algebraic simplification and identity verification
- Equation solving (polynomial, transcendental, ODE, PDE)
- Matrix operations, eigenvalues, determinants
- Calculus (differentiation, integration, limits, series)
- Group theory basics (permutations, generators)
- Number theory (primality, factoring, modular arithmetic)
- Combinatorics
- Tensor algebra

SymPy is weaker at:
- Abstract/categorical reasoning
- Topological arguments
- Non-constructive proofs
- Higher-order logic

Return JSON:
{{
    "feasible": true/false,
    "partial": true/false,
    "difficulty": "easy" | "moderate" | "hard" | "infeasible",
    "checkable_steps": [list of step numbers that SymPy can check],
    "verification_strategy": "what SymPy operations to use",
    "notes": "explanation"
}}"""

SYMPY_GENERATE_PROMPT = """Generate a SymPy script to verify this proof.

PROPOSITION: {proposition}

PROOF STEPS:
{steps_text}

ASSUMPTIONS:
{assumptions}

CHECKABLE STEPS: {checkable_steps}
VERIFICATION STRATEGY: {strategy}

RULES:
1. Script must be self-contained Python using only `from sympy import *` and `import sympy`
2. Script must print exactly one of: "VERDICT: VERIFIED", "VERDICT: PARTIAL", "VERDICT: FAILED"
3. Check each step independently where possible
4. Print step-by-step results: "STEP N: PASSED/FAILED/SKIPPED"
5. Use simplify(), expand(), factor(), trigsimp(), etc. to check algebraic equivalences
6. For equation solving, verify that solutions satisfy original equations
7. For matrix proofs, verify eigenvalue/determinant/rank claims
8. Do NOT assume results — compute and verify
9. If a step cannot be encoded in SymPy, skip it with explanation

Return JSON:
{{
    "sympy_script": "the complete Python script",
    "steps_encoded": [list of step numbers encoded],
    "steps_skipped": [list of step numbers skipped with reasons],
    "notes": "explanation of encoding choices"
}}"""


class SymPyBridge:
    """SymPy algebraic verification bridge."""

    def __init__(self, api: ClaudeAPI):
        self.api = api
        self._sympy_available = self._check_sympy()

    @staticmethod
    def _check_sympy() -> bool:
        """Check if sympy is importable."""
        try:
            import sympy  # noqa: F401
            return True
        except ImportError:
            return False

    @property
    def sympy_available(self) -> bool:
        return self._sympy_available

    def assess_feasibility(self, proof: ProofRecord) -> dict:
        """Check whether this proof can be verified by SymPy."""
        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        prompt = SYMPY_FEASIBILITY_PROMPT.format(
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

    def generate_sympy_script(self, proof: ProofRecord, feasibility: dict, log: LogRecord) -> str:
        """Generate SymPy verification script."""
        if not feasibility.get("feasible") and not feasibility.get("partial"):
            log.add_decision(
                step="sympy_generation",
                choice="skipped",
                alternatives=[],
                reasoning=f"SymPy verification not feasible: {feasibility.get('notes', '')}",
            )
            return ""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        checkable = feasibility.get("checkable_steps", [])
        strategy = feasibility.get("verification_strategy", "general algebraic checks")

        prompt = SYMPY_GENERATE_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            steps_text=steps_text or "(no structured steps)",
            assumptions=", ".join(proof.assumptions) or "(none)",
            checkable_steps=", ".join(str(s) for s in checkable) if checkable else "all",
            strategy=strategy,
        )

        try:
            data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
            script = data.get("sympy_script", "")

            log.add_decision(
                step="sympy_generation",
                choice=f"Generated {len(script)} chars, "
                       f"{len(data.get('steps_encoded', []))} steps encoded",
                alternatives=[],
                reasoning=data.get("notes", ""),
            )
            return script
        except Exception as e:
            log.add_decision(
                step="sympy_generation",
                choice="failed",
                alternatives=[],
                reasoning=str(e),
            )
            return ""

    def run_sympy_script(self, script: str) -> dict:
        """Execute a SymPy script and parse the verdict."""
        if not script:
            return {"verified": False, "reason": "no_script", "output": ""}

        if not self._sympy_available:
            return {"verified": False, "reason": "sympy_not_available",
                    "output": "SymPy not installed"}

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
                timeout=120,
            )

            Path(temp_path).unlink(missing_ok=True)

            output = result.stdout.strip()
            stderr = result.stderr.strip()

            if "VERDICT: VERIFIED" in output:
                return {"verified": True, "partial": False,
                        "reason": "sympy_verified", "output": output}
            elif "VERDICT: PARTIAL" in output:
                return {"verified": False, "partial": True,
                        "reason": "sympy_partial", "output": output}
            elif "VERDICT: FAILED" in output:
                return {"verified": False, "partial": False,
                        "reason": "sympy_failed", "output": output}
            elif result.returncode != 0:
                return {"verified": False, "reason": "script_error",
                        "output": output, "stderr": stderr}
            else:
                return {"verified": False, "reason": "no_verdict",
                        "output": output}

        except subprocess.TimeoutExpired:
            Path(temp_path).unlink(missing_ok=True)
            return {"verified": False, "reason": "timeout",
                    "output": "SymPy script timed out after 120s"}
        except Exception as e:
            return {"verified": False, "reason": "error", "output": str(e)}

    def _retry_script(self, script: str, error: str, proof: ProofRecord, log: LogRecord) -> str:
        """Ask Claude to fix a broken script given the error message."""
        prompt = (
            f"This SymPy verification script failed with an error. Fix it.\n\n"
            f"ORIGINAL SCRIPT:\n```python\n{script}\n```\n\n"
            f"ERROR:\n{error[:1000]}\n\n"
            f"PROPOSITION BEING VERIFIED:\n{proof.proposition or proof.proposition_natural}\n\n"
            f"Fix the script so it runs without errors. Keep the same verification logic.\n"
            f"Return JSON:\n"
            f'{{"sympy_script": "the fixed Python script", "fix_notes": "what was wrong"}}'
        )
        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data.get("sympy_script", "")
        except Exception:
            return ""

    def process(self, proof: ProofRecord, log: LogRecord) -> None:
        """Full SymPy pipeline: assess → generate → verify → retry if script errors.

        Modifies proof in place with SymPy results.
        """
        feasibility = self.assess_feasibility(proof)
        script = self.generate_sympy_script(proof, feasibility, log)

        if not script:
            proof.sympy_verified = False
            proof.sympy_result = {
                "verified": False,
                "reason": "not_feasible",
                "feasibility": feasibility,
            }
            return

        result = self.run_sympy_script(script)

        # Retry once if script had a runtime error
        if result.get("reason") == "script_error" and (result.get("stderr") or result.get("output")):
            error_msg = result.get("stderr", "") or result.get("output", "")
            log.add_decision(
                step="sympy_retry",
                choice="retrying",
                alternatives=[],
                reasoning=f"Script error: {error_msg[:200]}",
            )
            fixed_script = self._retry_script(script, error_msg, proof, log)
            if fixed_script:
                result = self.run_sympy_script(fixed_script)

        proof.sympy_verified = result.get("verified", False)
        proof.sympy_result = result

        if proof.sympy_verified:
            if proof.verification_status == "natural_language_only":
                proof.verification_status = "machine_verified"
