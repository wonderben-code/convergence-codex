#!/usr/bin/env python3
"""Upgrade all 256 formalisations with fresh Lean 4 code targeting current Mathlib.

For each proof:
  1. Take existing natural language proof + proposition
  2. Ask Claude to generate fresh Lean 4 code for current Mathlib
  3. Run Lean locally (seconds) to verify
  4. If partial (has sorry), try sorry elimination (1-2 Claude calls)
  5. Save, commit, push (Bitcoin stamp)

Incremental: saves after each proof. Resume-safe: skips already-upgraded proofs.
Free: uses Max Plan ($0) for all Claude calls.

Usage:
    python3 scripts/upgrade_lean_v2.py [--limit N] [--dry-run]
"""

import argparse
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

PROJECT_ROOT = Path(__file__).parent.parent
LEAN_PROJECT = PROJECT_ROOT / "lean_verify"
LEAN_BIN = os.path.expanduser("~/.elan/bin/lean")
LAKE_BIN = os.path.expanduser("~/.elan/bin/lake")

SYSTEM_PROMPT = (
    "You are a Lean 4 expert with deep knowledge of current Mathlib. "
    "Generate valid, idiomatic Lean 4 code that type-checks with the latest Mathlib. "
    "Use sorry ONLY for parts that genuinely cannot be formalised yet. "
    "Add clear comments explaining each sorry. "
    "CRITICAL: Use only import paths that exist in current Mathlib (2025). "
    "Many old paths have been reorganised. When unsure, use broader imports."
)

GENERATE_PROMPT = """Generate Lean 4 code to formalise this mathematical proposition.

PROPOSITION (formal):
{proposition}

PROPOSITION (natural language):
{proposition_natural}

PROOF OUTLINE:
{proof_natural_short}

PROOF STEPS:
{steps_text}

MATHEMATICAL APPARATUS: {apparatus}
ASSUMPTIONS: {assumptions}

RULES:
1. Use ONLY current Mathlib import paths (2025 version). Many old paths have moved:
   - Mathlib.Analysis.NormedSpace.* is now often Mathlib.Analysis.Normed.*
   - Mathlib.Data.Real.Basic is now Mathlib.Data.Real.Defs or similar
   - Mathlib.Topology.Connected is now Mathlib.Topology.Connected.Basic
   - When unsure, use a broader parent import or check if the module exists
2. The code MUST type-check with `lake env lean file.lean`
3. Use sorry for genuinely unformalizable parts — explain why in comments
4. Keep it simple and focused — formalise the core proposition, not peripheral details
5. Prefer concrete types over abstract ones where possible

Return JSON:
{{
    "lean_code": "the complete Lean 4 code",
    "sorry_count": N,
    "notes": "brief explanation of formalisation choices"
}}"""

SORRY_ELIMINATION_PROMPT = """This Lean 4 code type-checks but has {sorry_count} sorry gap(s).
Replace as many sorrys as possible with actual proofs.
Keep the code structure intact. If a sorry genuinely cannot be
filled (e.g., requires results not in Mathlib), leave it with a comment.

```lean
{lean_code}
```

Return JSON:
{{"lean_code": "the complete updated Lean code", "sorrys_filled": N, "notes": "explanation"}}"""


def log(msg: str, log_file: Path | None = None):
    ts = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line, flush=True)
    if log_file:
        with open(log_file, "a") as f:
            f.write(line + "\n")


def count_sorrys(code: str) -> int:
    return len(re.findall(r'\bsorry\b', code))


def verify_lean(code: str) -> dict:
    """Run Lean on code within the Mathlib project. Returns verification result."""
    if not code or len(code) < 10:
        return {"verified": False, "partial": False, "reason": "no_code", "errors": []}

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", dir=str(LEAN_PROJECT), delete=False
    ) as f:
        f.write(code)
        temp_path = f.name

    try:
        result = subprocess.run(
            [LAKE_BIN, "env", LEAN_BIN, temp_path],
            capture_output=True, text=True, timeout=120,
            cwd=str(LEAN_PROJECT),
        )

        Path(temp_path).unlink(missing_ok=True)

        if result.returncode == 0:
            has_sorry = count_sorrys(code) > 0
            return {
                "verified": not has_sorry,
                "partial": has_sorry,
                "reason": "verified" if not has_sorry else "partial_with_sorry",
                "sorry_count": count_sorrys(code),
                "errors": [],
            }
        else:
            errors = [l for l in result.stderr.strip().split("\n") if l.strip()][:5]
            return {
                "verified": False,
                "partial": False,
                "reason": "type_check_failed",
                "errors": errors,
            }

    except subprocess.TimeoutExpired:
        Path(temp_path).unlink(missing_ok=True)
        return {"verified": False, "partial": False, "reason": "timeout", "errors": ["Lean timed out after 120s"]}
    except Exception as e:
        Path(temp_path).unlink(missing_ok=True)
        return {"verified": False, "partial": False, "reason": "error", "errors": [str(e)]}


def generate_lean_code(api, proof_dict: dict) -> tuple:
    """Generate fresh Lean 4 code for a proof. Returns (code, notes)."""
    proposition = proof_dict.get("proposition", "")
    proposition_natural = proof_dict.get("proposition_natural", "")
    proof_natural = proof_dict.get("proof_natural", "")
    steps = proof_dict.get("proof_steps", [])
    apparatus = proof_dict.get("mathematical_apparatus", [])
    assumptions = proof_dict.get("assumptions", [])

    steps_text = "\n".join(
        f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
        f"[{s.get('justification', '')}]"
        for i, s in enumerate(steps)
    ) or "(no structured steps)"

    prompt = GENERATE_PROMPT.format(
        proposition=proposition or proposition_natural,
        proposition_natural=proposition_natural or proposition,
        proof_natural_short=proof_natural[:1500] if proof_natural else "(none)",
        steps_text=steps_text,
        apparatus=", ".join(apparatus) or "(none)",
        assumptions=", ".join(assumptions) or "(none)",
    )

    try:
        data = api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
        return data.get("lean_code", ""), data.get("notes", "")
    except Exception as e:
        return "", f"Generation failed: {e}"


def try_sorry_elimination(api, code: str, max_attempts: int = 2) -> tuple:
    """Try to fill sorry gaps. Returns (improved_code, sorrys_eliminated)."""
    initial = count_sorrys(code)
    if initial == 0:
        return code, 0

    current_code = code
    total_eliminated = 0

    for attempt in range(max_attempts):
        current_sorrys = count_sorrys(current_code)
        if current_sorrys == 0:
            break

        prompt = SORRY_ELIMINATION_PROMPT.format(
            sorry_count=current_sorrys,
            lean_code=current_code,
        )

        try:
            data = api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=8192)
            new_code = data.get("lean_code", "")
            if not new_code:
                break

            new_sorrys = count_sorrys(new_code)
            if new_sorrys >= current_sorrys:
                break  # No improvement

            # Verify the new code type-checks
            result = verify_lean(new_code)
            if result.get("verified") or result.get("partial"):
                eliminated = current_sorrys - new_sorrys
                total_eliminated += eliminated
                current_code = new_code
            else:
                break  # New code doesn't compile — keep old

        except Exception:
            break

    return current_code, total_eliminated


def is_already_upgraded_v2(proof_dict: dict) -> bool:
    """Check if this proof has already been upgraded with v2 Lean verification."""
    return proof_dict.get("lean_v2_upgraded", False)


def git_commit_and_push(conv_id: str, tier: str, index: int, total: int):
    """Commit and push for Bitcoin stamping."""
    try:
        subprocess.run(["git", "add", "data/"], cwd=str(PROJECT_ROOT), capture_output=True, check=True)
        result = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=str(PROJECT_ROOT), capture_output=True)
        if result.returncode == 0:
            return

        msg = f"Lean v2 upgrade [{index}/{total}]: {conv_id} -> {tier}"
        subprocess.run(["git", "commit", "-m", msg], cwd=str(PROJECT_ROOT), capture_output=True, check=True)

        push = subprocess.run(["git", "push", "origin", "main"], cwd=str(PROJECT_ROOT), capture_output=True)
        if push.returncode != 0:
            subprocess.run(["git", "pull", "--rebase", "origin", "main"], cwd=str(PROJECT_ROOT), capture_output=True)
            subprocess.run(["git", "push", "origin", "main"], cwd=str(PROJECT_ROOT), capture_output=True)
    except subprocess.CalledProcessError:
        pass


def upgrade_one_proof(api, proof_dict: dict, proof_path: Path, index: int, total: int, log_file: Path) -> dict:
    """Upgrade a single proof with fresh Lean code."""
    conv_id = proof_dict.get("convergence_id", proof_dict.get("id", "unknown"))
    claim = (proof_dict.get("proposition_natural", "") or proof_dict.get("proposition", ""))[:60]

    log(f"  [{index}/{total}] {conv_id} -- {claim}", log_file)

    t0 = time.time()
    result = {
        "convergence_id": conv_id,
        "status": "error",
        "tier": "unknown",
        "sorry_count": -1,
        "sorrys_eliminated": 0,
        "time": 0.0,
    }

    # Step 1: Generate fresh Lean code
    log(f"    Generating Lean code...", log_file)
    lean_code, notes = generate_lean_code(api, proof_dict)

    if not lean_code:
        log(f"    FAILED: no code generated ({notes})", log_file)
        result["status"] = "generation_failed"
        result["time"] = round(time.time() - t0, 1)
        return result

    # Step 2: Verify with Lean
    log(f"    Verifying with Lean ({len(lean_code)} chars)...", log_file)
    lean_result = verify_lean(lean_code)

    if lean_result["verified"]:
        tier = "proven"
        log(f"    PROVEN (0 sorry, fully verified)", log_file)
    elif lean_result["partial"]:
        sorry_count = lean_result.get("sorry_count", count_sorrys(lean_code))
        log(f"    PARTIAL ({sorry_count} sorry gaps) -- trying elimination...", log_file)

        # Step 3: Sorry elimination
        improved_code, eliminated = try_sorry_elimination(api, lean_code)
        if eliminated > 0:
            lean_code = improved_code
            lean_result = verify_lean(lean_code)
            result["sorrys_eliminated"] = eliminated
            log(f"    Eliminated {eliminated} sorrys", log_file)

        if lean_result["verified"]:
            tier = "proven"
            log(f"    PROVEN after sorry elimination!", log_file)
        else:
            tier = "proof_with_gaps"
            remaining = count_sorrys(lean_code)
            log(f"    PROOF_WITH_GAPS ({remaining} sorry remaining)", log_file)
    else:
        # Lean failed — try one regeneration with error feedback
        errors = lean_result.get("errors", [])[:3]
        log(f"    Lean failed: {errors[0][:80] if errors else 'unknown'}", log_file)
        log(f"    Retrying with error feedback...", log_file)

        retry_prompt = (
            f"This Lean 4 code failed to type-check. Fix it.\n\n"
            f"```lean\n{lean_code}\n```\n\n"
            f"ERRORS:\n" + "\n".join(errors[:5]) + "\n\n"
            f"Fix the errors. The code must compile with current Mathlib.\n"
            f"Return JSON: {{\"lean_code\": \"fixed code\", \"notes\": \"what was wrong\"}}"
        )

        try:
            data = api.query_deep_json(retry_prompt, system=SYSTEM_PROMPT, max_tokens=8192)
            fixed_code = data.get("lean_code", "")
            if fixed_code:
                lean_result2 = verify_lean(fixed_code)
                if lean_result2["verified"]:
                    lean_code = fixed_code
                    tier = "proven"
                    log(f"    PROVEN after retry!", log_file)
                elif lean_result2["partial"]:
                    lean_code = fixed_code
                    tier = "proof_with_gaps"
                    remaining = count_sorrys(lean_code)
                    log(f"    PROOF_WITH_GAPS after retry ({remaining} sorry)", log_file)
                else:
                    tier = "rigorous_argument"
                    log(f"    Still failed after retry -- keeping as rigorous_argument", log_file)
            else:
                tier = "rigorous_argument"
        except Exception:
            tier = "rigorous_argument"
            log(f"    Retry failed -- keeping as rigorous_argument", log_file)

    # Update proof dict
    proof_dict["proof_lean"] = lean_code
    proof_dict["lean_verified"] = (tier == "proven")
    proof_dict["lean_partial"] = (tier == "proof_with_gaps")
    proof_dict["verification_tier"] = tier
    proof_dict["lean_v2_upgraded"] = True
    proof_dict["lean_v2_notes"] = notes
    proof_dict["lean_v2_sorry_count"] = count_sorrys(lean_code)

    if tier == "proven":
        proof_dict["verification_status"] = "machine_verified"
        proof_dict["verification_tier_reason"] = "Full Lean 4 proof, 0 sorry gaps"
    elif tier == "proof_with_gaps":
        proof_dict["verification_status"] = "partially_verified"
        proof_dict["verification_tier_reason"] = f"Lean type-checks, {count_sorrys(lean_code)} sorry gap(s)"
    else:
        proof_dict["verification_tier_reason"] = "Lean code could not be verified"

    # Save
    with open(proof_path, "w") as f:
        json.dump(proof_dict, f, indent=2, default=str)

    result["status"] = "upgraded"
    result["tier"] = tier
    result["sorry_count"] = count_sorrys(lean_code)
    result["time"] = round(time.time() - t0, 1)

    log(f"    DONE: {tier} | {result['time']}s", log_file)
    return result


def main():
    parser = argparse.ArgumentParser(description="Upgrade formalisations with fresh Lean 4 code")
    parser.add_argument("--limit", type=int, default=0, help="Limit number of proofs (0=all)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be upgraded")
    args = parser.parse_args()

    from logos.config import LogosConfig
    from logos.api import create_api

    config = LogosConfig.load()
    api = create_api(config, use_max_plan=True)

    proofs_dir = PROJECT_ROOT / "data" / "logos" / "proofs"
    log_file = PROJECT_ROOT / "data" / "pipeline" / f"lean_upgrade_{time.strftime('%Y%m%d_%H%M%S')}.log"
    log_file.parent.mkdir(parents=True, exist_ok=True)

    proof_files = sorted(proofs_dir.glob("*.json"))
    if args.limit > 0:
        proof_files = proof_files[:args.limit]

    # Check resume state
    to_upgrade = []
    already_done = 0
    for pf in proof_files:
        with open(pf) as f:
            d = json.load(f)
        if is_already_upgraded_v2(d):
            already_done += 1
        else:
            to_upgrade.append(pf)

    print(f"\n{'=' * 60}")
    print(f"  LEAN V2 UPGRADE -- Fresh Lean Code + Local Verification")
    print(f"  Mode: Max Plan ($0)")
    print(f"{'=' * 60}")
    print(f"\n  Total proofs: {len(proof_files)}")
    print(f"  Already upgraded: {already_done}")
    print(f"  To upgrade: {len(to_upgrade)}")
    print(f"  Saves + Bitcoin stamps after each proof")
    print(f"  Log: {log_file}")

    if args.dry_run:
        print(f"\n  DRY RUN -- would upgrade {len(to_upgrade)} proofs")
        return

    if not to_upgrade:
        print("\n  All proofs already upgraded!")
        return

    results = []
    total = len(to_upgrade)
    tier_counts = {"proven": 0, "proof_with_gaps": 0, "rigorous_argument": 0, "error": 0}

    for i, pf in enumerate(to_upgrade):
        with open(pf) as f:
            proof_dict = json.load(f)

        result = upgrade_one_proof(api, proof_dict, pf, i + 1, total, log_file)
        results.append(result)

        tier = result.get("tier", "error")
        if tier in tier_counts:
            tier_counts[tier] += 1
        else:
            tier_counts["error"] += 1

        # Commit and push
        if result["status"] == "upgraded":
            git_commit_and_push(result["convergence_id"], tier, i + 1, total)

        # Running tally every 5 proofs
        if (i + 1) % 5 == 0 or (i + 1) == total:
            print(f"\n  --- Tally ({i+1}/{total}) ---", flush=True)
            for t in ["proven", "proof_with_gaps", "rigorous_argument", "error"]:
                if tier_counts[t] > 0:
                    print(f"    {t}: {tier_counts[t]}", flush=True)

        # Save running summary
        summary = PROJECT_ROOT / "data" / "pipeline" / "lean_upgrade_running.json"
        with open(summary, "w") as f:
            json.dump({"done": i + 1, "total": total, "tiers": tier_counts, "results": results}, f, indent=2)

    # Final summary
    print(f"\n{'=' * 60}")
    print(f"  UPGRADE COMPLETE")
    print(f"{'=' * 60}")
    for t in ["proven", "proof_with_gaps", "rigorous_argument", "error"]:
        if tier_counts[t] > 0:
            print(f"    {t}: {tier_counts[t]}")
    total_sorrys = sum(r.get("sorrys_eliminated", 0) for r in results)
    print(f"  Sorrys eliminated: {total_sorrys}")


if __name__ == "__main__":
    main()
