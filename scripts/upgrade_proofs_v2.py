#!/usr/bin/env python3
"""Upgrade existing Logos v1 proofs with v2 multi-tool verification.

Loads all 256 proofs from Stage A, runs them through the v2 verification
stack (Z3, SymPy, Numerical, sorry elimination, back-translation, tiered
formalisation), and saves the upgraded versions.

Non-destructive: adds new fields, preserves all existing data.
Free: uses Max Plan ($0) for all Claude calls.

Usage:
    python3 scripts/upgrade_proofs_v2.py [--max-plan] [--workers N] [--limit N]
"""

import argparse
import json
import time
from dataclasses import asdict
from pathlib import Path

# Add project root to path
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))


def log(msg: str, log_file: Path | None = None):
    ts = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line)
    if log_file:
        with open(log_file, "a") as f:
            f.write(line + "\n")


def load_proof(path: Path) -> dict:
    """Load a proof JSON file."""
    with open(path) as f:
        return json.load(f)


def save_proof(proof_dict: dict, path: Path):
    """Save an upgraded proof."""
    with open(path, "w") as f:
        json.dump(proof_dict, f, indent=2, default=str)


def upgrade_one_proof(proof_dict: dict, index: int, total: int,
                      use_max_plan: bool, log_file: Path) -> dict:
    """Upgrade a single proof with v2 verification."""
    from logos.config import LogosConfig
    from logos.api import create_api
    from logos.models import ProofRecord, LogRecord, VerificationTier
    from logos.z3_bridge import Z3Bridge
    from logos.sympy_bridge import SymPyBridge
    from logos.numerical_bridge import NumericalBridge
    from logos.lean_bridge import LeanBridge
    from logos.back_translation import BackTranslator

    config = LogosConfig.load()
    api = create_api(config, use_max_plan=use_max_plan)

    # Reconstruct ProofRecord from dict
    proof = ProofRecord()
    for key, val in proof_dict.items():
        if hasattr(proof, key):
            setattr(proof, key, val)

    proof_log = LogRecord(proof_id=proof.id)
    conv_id = proof.convergence_id or proof.id
    claim = (proof.proposition_natural or proof.proposition or "")[:60]

    log(f"  [{index}/{total}] {conv_id} — {claim}", log_file)

    t0 = time.time()
    result = {
        "proof_id": proof.id,
        "convergence_id": conv_id,
        "status": "error",
        "previous_tier": "unknown",
        "new_tier": "unknown",
        "tools_verified": 0,
        "sorry_eliminated": 0,
        "aligned": True,
        "time": 0.0,
    }

    # Record previous state
    prev_status = proof.verification_status
    prev_lean = proof.lean_verified
    prev_lean_partial = proof.lean_partial

    try:
        # ─── Z3 VERIFICATION ───
        log(f"    [{conv_id}] Z3...", log_file)
        z3 = Z3Bridge(api)
        z3.process(proof, proof_log)
        if proof.z3_verified:
            log(f"    [{conv_id}] Z3: VERIFIED", log_file)

        # ─── SYMPY VERIFICATION ───
        log(f"    [{conv_id}] SymPy...", log_file)
        sympy = SymPyBridge(api)
        sympy.process(proof, proof_log)
        if proof.sympy_verified:
            log(f"    [{conv_id}] SymPy: VERIFIED", log_file)

        # ─── NUMERICAL VERIFICATION ───
        log(f"    [{conv_id}] Numerical...", log_file)
        num = NumericalBridge(api)
        num.process(proof, proof_log)
        if proof.numerical_consistent:
            log(f"    [{conv_id}] Numerical: CONSISTENT", log_file)

        # ─── SORRY ELIMINATION ───
        if proof.proof_lean and proof.lean_partial:
            log(f"    [{conv_id}] Sorry elimination...", log_file)
            lean = LeanBridge(api, config)
            eliminated = lean.eliminate_sorrys(proof, proof_log)
            result["sorry_eliminated"] = eliminated
            if eliminated > 0:
                log(f"    [{conv_id}] Eliminated {eliminated} sorrys", log_file)

        # ─── BACK-TRANSLATION ───
        log(f"    [{conv_id}] Back-translation...", log_file)
        bt = BackTranslator(api)
        alignment = bt.check_alignment(proof, proof_log)
        result["aligned"] = alignment.get("is_aligned", True)

        # ─── TIERED FORMALISATION ───
        tier = VerificationTier.from_proof(proof)
        proof.verification_tier = tier.value

        # Determine tier reason
        if tier == VerificationTier.PROVEN:
            proof.verification_tier_reason = "Full Lean 4 proof, 0 sorry gaps"
        elif tier == VerificationTier.PROOF_WITH_GAPS:
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            proof.verification_tier_reason = f"Lean type-checks, {sorrys} sorry gap(s)"
        elif tier == VerificationTier.FORMALLY_VERIFIED:
            tools = []
            if proof.z3_verified: tools.append("Z3")
            if proof.sympy_verified: tools.append("SymPy")
            proof.verification_tier_reason = f"Verified by {', '.join(tools)}"
        elif tier == VerificationTier.NUMERICALLY_CONFIRMED:
            proof.verification_tier_reason = "Numerical tests pass, no formal verification"
        elif tier == VerificationTier.RIGOROUS_ARGUMENT:
            proof.verification_tier_reason = "Structured NL proof, no tool could verify"
        else:
            proof.verification_tier_reason = "No proof generated"

        # ─── COVERAGE ───
        total_steps = len(proof.proof_steps) or 1
        steps_covered = set()
        if proof.lean_verified:
            steps_covered.update(range(total_steps))
        elif proof.lean_partial:
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            steps_covered.update(range(max(0, total_steps - sorrys)))

        z3_out = proof.z3_result.get("output", "")
        sympy_out = proof.sympy_result.get("output", "")
        for i in range(total_steps):
            if f"STEP {i+1}: PASSED" in z3_out:
                steps_covered.add(i)
            if f"STEP {i+1}: PASSED" in sympy_out:
                steps_covered.add(i)

        proof.coverage_percentage = round(100 * len(steps_covered) / total_steps, 1)
        proof.coverage_detail = {
            "steps_total": total_steps,
            "steps_machine_verified": len(steps_covered),
        }

        # ─── MULTI-TOOL CONSENSUS ───
        tools_verified = []
        if proof.lean_verified: tools_verified.append("lean")
        if proof.z3_verified: tools_verified.append("z3")
        if proof.sympy_verified: tools_verified.append("sympy")
        if proof.numerical_consistent and proof.numerical_result.get("applicable"):
            tools_verified.append("numerical")

        proof.multi_tool_consensus = {
            "tools_verified": tools_verified,
            "total_tools_verified": len(tools_verified),
            "verification_tier": tier.value,
            "coverage_percentage": proof.coverage_percentage,
            "back_translation_aligned": result["aligned"],
        }

        result["status"] = "upgraded"
        result["previous_tier"] = prev_status
        result["new_tier"] = tier.value
        result["tools_verified"] = len(tools_verified)

        log(f"    [{conv_id}] Tier: {tier.value} | "
            f"Tools: {len(tools_verified)} | "
            f"Coverage: {proof.coverage_percentage:.0f}% | "
            f"Aligned: {result['aligned']}", log_file)

    except Exception as e:
        result["error"] = str(e)
        log(f"    [{conv_id}] ERROR: {e}", log_file)

    result["time"] = round(time.time() - t0, 1)
    return result, asdict(proof)


def main():
    parser = argparse.ArgumentParser(description="Upgrade v1 proofs with v2 verification")
    parser.add_argument("--max-plan", action="store_true", help="Use Max Plan ($0)")
    parser.add_argument("--limit", type=int, default=0, help="Limit number of proofs (0=all)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be upgraded")
    args = parser.parse_args()

    project_root = Path(__file__).parent.parent
    proofs_dir = project_root / "data" / "logos" / "proofs"
    log_file = project_root / "data" / "pipeline" / f"upgrade_v2_{time.strftime('%Y%m%d_%H%M%S')}.log"
    log_file.parent.mkdir(parents=True, exist_ok=True)

    # Find all proofs
    proof_files = sorted(proofs_dir.glob("*.json"))
    if not proof_files:
        print(f"No proofs found in {proofs_dir}")
        return

    if args.limit > 0:
        proof_files = proof_files[:args.limit]

    print(f"\n{'=' * 60}")
    print(f"  LOGOS v2 UPGRADE — Verification Enhancement Pass")
    print(f"  Mode: {'Max Plan ($0)' if args.max_plan else 'API'}")
    print(f"{'=' * 60}")
    print(f"\n  Proofs to upgrade: {len(proof_files)}")
    print(f"  Log file: {log_file}")

    if args.dry_run:
        print(f"\n  DRY RUN — would upgrade {len(proof_files)} proofs")
        # Show current state
        tiers = {"natural_language_only": 0, "machine_verified": 0,
                 "partially_verified": 0, "unverified": 0}
        for pf in proof_files:
            data = load_proof(pf)
            status = data.get("verification_status", "unknown")
            tiers[status] = tiers.get(status, 0) + 1
        print(f"\n  Current verification status:")
        for status, count in sorted(tiers.items(), key=lambda x: -x[1]):
            print(f"    {status}: {count}")
        return

    results = []
    upgraded = 0
    total = len(proof_files)

    for i, pf in enumerate(proof_files):
        proof_dict = load_proof(pf)
        result, upgraded_proof = upgrade_one_proof(
            proof_dict, i + 1, total, args.max_plan, log_file
        )

        if result["status"] == "upgraded":
            save_proof(upgraded_proof, pf)
            upgraded += 1

        results.append(result)

    # Summary
    print(f"\n{'=' * 60}")
    print(f"  UPGRADE COMPLETE")
    print(f"{'=' * 60}")
    print(f"  Upgraded: {upgraded}/{total}")

    # Tier distribution
    tier_counts = {}
    for r in results:
        t = r.get("new_tier", "error")
        tier_counts[t] = tier_counts.get(t, 0) + 1

    print(f"\n  Tier distribution after upgrade:")
    tier_order = ["proven", "proof_with_gaps", "formally_verified",
                  "numerically_confirmed", "rigorous_argument", "conjecture", "error"]
    for tier in tier_order:
        if tier in tier_counts:
            print(f"    {tier}: {tier_counts[tier]}")

    # Tools stats
    total_verified = sum(r.get("tools_verified", 0) for r in results)
    total_sorrys = sum(r.get("sorry_eliminated", 0) for r in results)
    misaligned = sum(1 for r in results if not r.get("aligned", True))

    print(f"\n  Total tool verifications: {total_verified}")
    print(f"  Sorrys eliminated: {total_sorrys}")
    print(f"  Misaligned propositions: {misaligned}")

    # Save summary
    summary_path = project_root / "data" / "pipeline" / f"upgrade_v2_summary_{time.strftime('%Y%m%d_%H%M%S')}.json"
    with open(summary_path, "w") as f:
        json.dump({
            "total_proofs": total,
            "upgraded": upgraded,
            "tier_distribution": tier_counts,
            "total_tool_verifications": total_verified,
            "sorrys_eliminated": total_sorrys,
            "misaligned": misaligned,
            "results": results,
        }, f, indent=2)
    print(f"\n  Summary saved: {summary_path}")


if __name__ == "__main__":
    main()
