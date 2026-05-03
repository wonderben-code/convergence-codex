"""Numerical Bridge — sanity checks via NumPy/SciPy.

Generates numerical test cases for proof propositions and runs them.
Does NOT prove anything — catches obvious nonsense, dimensional errors,
and numerical inconsistencies. A "smell test" for the proof.

Claude generates test scripts; NumPy/SciPy does the computation.
Verdict is EXTERNAL.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from logos.api import ClaudeAPI
from logos.models import ProofRecord, LogRecord


SYSTEM_PROMPT = (
    "You are a numerical methods expert. You generate Python scripts using NumPy and SciPy "
    "that perform numerical sanity checks on mathematical propositions. Your scripts test "
    "concrete instances, boundary cases, and random samples to verify consistency. "
    "Scripts MUST print a clear verdict: CONSISTENT, PARTIAL, or INCONSISTENT."
)

NUMERICAL_GENERATE_PROMPT = """Generate a numerical sanity-check script for this proof.

PROPOSITION: {proposition}

PROOF STEPS:
{steps_text}

ASSUMPTIONS:
{assumptions}

MATHEMATICAL APPARATUS: {apparatus}

RULES:
1. Script must use only numpy and scipy (both installed)
2. Script must print: "VERDICT: CONSISTENT", "VERDICT: PARTIAL", or "VERDICT: INCONSISTENT"
3. Test at LEAST 3 concrete examples where the proposition should hold
4. Test at LEAST 1 boundary/edge case
5. Test at LEAST 1 case where assumptions are violated (should fail or be undefined)
6. For each test, print "TEST N: PASSED/FAILED - description"
7. If the proposition involves continuous quantities, sample multiple random values
8. Check dimensional consistency where applicable
9. Use numpy.testing.assert_allclose for approximate comparisons (rtol=1e-6)
10. If the proposition is purely abstract/categorical with no numerical content, output:
    "VERDICT: NOT_APPLICABLE" and explain why

DO NOT:
- Import any module other than numpy, scipy, math, random
- Make network requests
- Access the filesystem beyond the script itself

Return JSON:
{{
    "numerical_script": "the complete Python script",
    "tests_planned": N,
    "test_descriptions": ["what each test checks"],
    "applicability": "full" | "partial" | "none",
    "notes": "explanation"
}}"""


class NumericalBridge:
    """Numerical sanity-check bridge using NumPy/SciPy."""

    def __init__(self, api: ClaudeAPI):
        self.api = api

    def generate_tests(self, proof: ProofRecord, log: LogRecord) -> str:
        """Generate numerical test script for the proof."""
        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        prompt = NUMERICAL_GENERATE_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            steps_text=steps_text or "(no structured steps)",
            assumptions=", ".join(proof.assumptions) or "(none)",
            apparatus=", ".join(proof.mathematical_apparatus),
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT, max_tokens=4096)
            script = data.get("numerical_script", "")
            applicability = data.get("applicability", "none")

            log.add_decision(
                step="numerical_generation",
                choice=f"Generated {len(script)} chars, "
                       f"applicability={applicability}, "
                       f"{data.get('tests_planned', 0)} tests planned",
                alternatives=[],
                reasoning=data.get("notes", ""),
            )

            if applicability == "none":
                log.add_decision(
                    step="numerical_generation",
                    choice="skipped",
                    alternatives=[],
                    reasoning="Proposition has no numerical content to test",
                )
                return ""

            return script
        except Exception as e:
            log.add_decision(
                step="numerical_generation",
                choice="failed",
                alternatives=[],
                reasoning=str(e),
            )
            return ""

    def run_tests(self, script: str) -> dict:
        """Execute numerical test script and parse results."""
        if not script:
            return {"consistent": False, "reason": "no_script",
                    "applicable": False, "output": ""}

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

            # Count passed/failed tests
            passed = output.count("PASSED")
            failed = output.count("FAILED")

            if "VERDICT: NOT_APPLICABLE" in output:
                return {"consistent": True, "applicable": False,
                        "reason": "not_applicable", "output": output,
                        "tests_passed": 0, "tests_failed": 0}
            elif "VERDICT: CONSISTENT" in output:
                return {"consistent": True, "applicable": True,
                        "reason": "numerically_consistent", "output": output,
                        "tests_passed": passed, "tests_failed": failed}
            elif "VERDICT: PARTIAL" in output:
                return {"consistent": True, "applicable": True, "partial": True,
                        "reason": "partially_consistent", "output": output,
                        "tests_passed": passed, "tests_failed": failed}
            elif "VERDICT: INCONSISTENT" in output:
                return {"consistent": False, "applicable": True,
                        "reason": "numerically_inconsistent", "output": output,
                        "tests_passed": passed, "tests_failed": failed}
            elif result.returncode != 0:
                return {"consistent": False, "reason": "script_error",
                        "applicable": True, "output": output, "stderr": stderr}
            else:
                return {"consistent": False, "reason": "no_verdict",
                        "applicable": True, "output": output}

        except subprocess.TimeoutExpired:
            Path(temp_path).unlink(missing_ok=True)
            return {"consistent": False, "reason": "timeout",
                    "applicable": True, "output": "Script timed out after 60s"}
        except Exception as e:
            return {"consistent": False, "reason": "error",
                    "applicable": True, "output": str(e)}

    def process(self, proof: ProofRecord, log: LogRecord) -> None:
        """Full numerical pipeline: generate tests → run → store results.

        Modifies proof in place.
        """
        script = self.generate_tests(proof, log)

        if not script:
            proof.numerical_consistent = False
            proof.numerical_result = {
                "consistent": False, "applicable": False,
                "reason": "not_applicable",
            }
            return

        result = self.run_tests(script)
        proof.numerical_consistent = result.get("consistent", False)
        proof.numerical_result = result
