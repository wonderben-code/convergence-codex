#!/usr/bin/env python3
"""Stage A Runner — processes all Gnosis v1 convergences through Logos, then Synthesis.

PARALLEL: runs N convergences simultaneously (default 8)
RESUMABLE: checks which convergences already have proofs and skips them
SAVES AFTER EVERY ITEM: no data loss on crash
LOGS EVERYTHING: progress file tracks every step
THREAD-SAFE: each worker has its own API client

Usage:
    export ANTHROPIC_API_KEY="your-key"
    python3 scripts/run_stage_a.py                    # full run, 8 parallel
    python3 scripts/run_stage_a.py --workers 12       # faster with more workers
    python3 scripts/run_stage_a.py --max-cost 50      # cost cap
    python3 scripts/run_stage_a.py --logos-only        # skip synthesis
    python3 scripts/run_stage_a.py --synthesis-only    # skip logos (requires prior run)
"""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path

# Add project root to path
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


# --- Thread-safe utilities ---

_log_lock = threading.Lock()
_cost_lock = threading.Lock()
_stats_lock = threading.Lock()
_total_cost = 0.0


def now_iso():
    return datetime.now(timezone.utc).isoformat()


def log(msg: str, log_file: Path):
    """Thread-safe print and log."""
    ts = datetime.now(timezone.utc).strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with _log_lock:
        print(line, flush=True)
        with open(log_file, "a") as f:
            f.write(line + "\n")


def add_cost(amount: float) -> float:
    """Thread-safe cost accumulation. Returns new total."""
    global _total_cost
    with _cost_lock:
        _total_cost += amount
        return _total_cost


def get_cost() -> float:
    with _cost_lock:
        return _total_cost


# --- Data loading ---

def load_convergences(gnosis_dir: Path) -> list[dict]:
    """Load all non-negative convergences from Gnosis data."""
    conv_dir = gnosis_dir / "convergences"
    convergences = []
    for f in sorted(conv_dir.glob("*.json")):
        try:
            data = json.loads(f.read_text())
            if not data.get("negative", False):
                convergences.append(data)
        except (json.JSONDecodeError, Exception):
            continue
    return convergences


def load_findings(gnosis_dir: Path) -> list[dict]:
    """Load all findings from Gnosis data."""
    findings_dir = gnosis_dir / "findings"
    findings = []
    if findings_dir.exists():
        for f in sorted(findings_dir.glob("*.json")):
            try:
                findings.append(json.loads(f.read_text()))
            except (json.JSONDecodeError, Exception):
                continue
    return findings


def get_completed_convergence_ids(proofs_dir: Path) -> set[str]:
    """Get IDs of convergences that already have proofs."""
    done = set()
    if proofs_dir.exists():
        for f in proofs_dir.glob("*.json"):
            try:
                data = json.loads(f.read_text())
                cid = data.get("convergence_id", "")
                if cid:
                    done.add(cid)
            except (json.JSONDecodeError, Exception):
                continue
    return done


# --- Worker function (runs in thread) ---

def process_one_convergence(conv: dict, index: int, total: int,
                            config_template, log_file: Path) -> dict:
    """Process a single convergence through Logos. Each call creates its own API client."""
    from logos.config import LogosConfig
    from logos.api import ClaudeAPI
    from logos.store import ProofStore
    from logos.formaliser import Formaliser
    from logos.validator import ProofValidator
    from logos.lean_bridge import LeanBridge

    # Each worker gets its own API client (thread-safe)
    config = LogosConfig.load()
    config.max_cost_usd = 999  # per-worker limit disabled; global cost tracked separately
    api = ClaudeAPI(config)
    store = ProofStore(config)
    formaliser = Formaliser(api)
    validator = ProofValidator(api, store)
    lean = LeanBridge(api, config)

    conv_id = conv.get("id", "unknown")
    claim = conv.get("structural_claim", "")[:70]
    domains = ", ".join(conv.get("domain_names", conv.get("domains", [])))

    log(f"  [{index}/{total}] {conv_id} — {domains}", log_file)

    t0 = time.time()
    result = {
        "convergence_id": conv_id,
        "status": "error",
        "confidence": 0.0,
        "confidence_category": "low",
        "formalisation_type": "",
        "flagged": False,
        "lean_code": False,
        "cost": 0.0,
        "time": 0.0,
        "error": "",
    }

    try:
        # Formalise
        proof, proof_log, flag = formaliser.formalise(conv)
        result["formalisation_type"] = proof.formalisation_type
        log(f"    [{conv_id}] Type: {proof.formalisation_type} | "
            f"Apparatus: {', '.join(proof.mathematical_apparatus[:2])} | "
            f"Steps: {len(proof.proof_steps)}", log_file)

        # Lean
        lean.process(proof, proof_log)
        result["lean_code"] = bool(proof.proof_lean)

        # Validate
        val_result = validator.validate(proof)
        result["confidence"] = val_result.overall_confidence
        result["confidence_category"] = val_result.confidence_category
        log(f"    [{conv_id}] Confidence: {val_result.overall_confidence:.2f} ({val_result.confidence_category})", log_file)

        # Save immediately (thread-safe — each proof has unique filename)
        store.save_proof(proof)
        store.save_log(proof_log)
        store.save_flag(flag)

        result["status"] = "completed"
        result["flagged"] = flag.requires_human_review

    except Exception as e:
        result["error"] = str(e)
        log(f"    [{conv_id}] ERROR: {e}", log_file)

    elapsed = time.time() - t0
    worker_cost = api.stats.cost_usd
    total_now = add_cost(worker_cost)
    result["cost"] = worker_cost
    result["time"] = elapsed
    log(f"    [{conv_id}] Done: {elapsed:.0f}s, ${worker_cost:.2f} (total: ${total_now:.2f})", log_file)

    return result


# --- Logos parallel runner ---

def run_logos_parallel(convergences: list[dict], max_cost: float,
                       workers: int, log_file: Path) -> dict:
    """Run Logos on all convergences in parallel."""
    from logos.config import LogosConfig

    config = LogosConfig.load()

    # Check what's already done
    done_ids = get_completed_convergence_ids(config.proofs_dir)
    remaining = [c for c in convergences if c.get("id", "") not in done_ids]

    log(f"Logos: {len(convergences)} total, {len(done_ids)} already done, "
        f"{len(remaining)} remaining, {workers} workers", log_file)

    if not remaining:
        log("Nothing to process — all convergences already have proofs.", log_file)
        return {"completed": 0, "already_done": len(done_ids), "total_cost": 0}

    stats = {
        "started": now_iso(),
        "total": len(convergences),
        "already_done": len(done_ids),
        "workers": workers,
        "completed": 0,
        "errors": 0,
        "high_confidence": 0,
        "medium_confidence": 0,
        "low_confidence": 0,
        "flagged": 0,
        "lean_code_generated": 0,
        "results": [],
    }

    total_count = len(convergences)
    start_index = len(done_ids) + 1

    # Submit all work to thread pool
    with ThreadPoolExecutor(max_workers=workers) as executor:
        futures = {}
        for i, conv in enumerate(remaining):
            future = executor.submit(
                process_one_convergence, conv, start_index + i, total_count,
                config, log_file
            )
            futures[future] = conv

        # Collect results as they complete
        for future in as_completed(futures):
            result = future.result()
            stats["results"].append(result)

            if result["status"] == "completed":
                stats["completed"] += 1
                cat = result["confidence_category"]
                if cat == "high":
                    stats["high_confidence"] += 1
                elif cat == "medium":
                    stats["medium_confidence"] += 1
                else:
                    stats["low_confidence"] += 1
                if result["flagged"]:
                    stats["flagged"] += 1
                if result["lean_code"]:
                    stats["lean_code_generated"] += 1
            else:
                stats["errors"] += 1

            # Check global cost
            current_cost = get_cost()
            if current_cost >= max_cost:
                log(f"\n  COST LIMIT: ${current_cost:.2f} >= ${max_cost:.2f}. "
                    f"Cancelling remaining work...", log_file)
                executor.shutdown(wait=False, cancel_futures=True)
                break

    stats["completed_at"] = now_iso()
    stats["total_cost"] = get_cost()

    # Save run stats
    stats_path = config.runs_dir / f"stage_a_logos_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.json"
    # Don't save full results list to run stats (too large) — save summary
    summary = {k: v for k, v in stats.items() if k != "results"}
    stats_path.write_text(json.dumps(summary, indent=2))
    log(f"\nLogos run stats saved to {stats_path}", log_file)

    return stats


# --- Synthesis runner (sequential — papers depend on each other for corpus context) ---

def run_synthesis(convergences: list[dict], findings: list[dict],
                  proofs_dir: Path, max_cost: float, log_file: Path) -> dict:
    """Run Synthesis on convergences + proofs."""
    from synthesis.config import SynthesisConfig
    from synthesis.api import ClaudeAPI
    from synthesis.store import PaperStore
    from synthesis.composer import Composer

    config = SynthesisConfig.load()
    config.max_cost_usd = max_cost

    api = ClaudeAPI(config)
    store = PaperStore(config)
    composer = Composer(api, config.corpus_papers_dir)

    # Load proofs
    proofs = []
    if proofs_dir.exists():
        for f in sorted(proofs_dir.glob("*.json")):
            try:
                proofs.append(json.loads(f.read_text()))
            except (json.JSONDecodeError, Exception):
                continue

    # Enrich proofs with reasoning logs (so Synthesis appendices have full methodology)
    logs_dir = proofs_dir.parent / "logs"
    if logs_dir.exists():
        for p in proofs:
            log_path = logs_dir / f"{p.get('convergence_id', p.get('id', ''))}.json"
            if log_path.exists():
                try:
                    p["_reasoning_log"] = json.loads(log_path.read_text())
                except (json.JSONDecodeError, Exception):
                    pass

    # Enrich proofs with flag data (so Synthesis appendices have review status)
    flags_dir = proofs_dir.parent / "flags"
    if flags_dir.exists():
        for p in proofs:
            flag_path = flags_dir / f"{p.get('convergence_id', p.get('id', ''))}.json"
            if flag_path.exists():
                try:
                    p["_flag_data"] = json.loads(flag_path.read_text())
                except (json.JSONDecodeError, Exception):
                    pass

    log(f"\nSynthesis: {len(convergences)} convergences, {len(proofs)} proofs, "
        f"{len(findings)} findings", log_file)

    # Detect paper boundaries
    log("  Detecting paper boundaries...", log_file)
    bundles = composer.detect_boundaries(convergences, proofs, findings)
    log(f"  Papers to generate: {len(bundles)}", log_file)

    stats = {
        "started": now_iso(),
        "bundles": len(bundles),
        "completed": 0,
        "errors": 0,
        "total_words": 0,
    }

    for i, bundle in enumerate(bundles):
        log(f"\n  [{i+1}/{len(bundles)}] Paper — {len(bundle.convergences)} convergences, "
            f"{len(bundle.proofs)} proofs", log_file)

        try:
            paper, review = composer.compose(bundle)
            log(f"    Title: {paper.title[:60]}...", log_file)
            log(f"    Words: {paper.total_word_count}", log_file)

            # Review
            review_result = composer.review_paper(paper)
            log(f"    Review: {paper.confidence_score:.2f} ({paper.confidence_category})", log_file)

            # Build review items from issues
            issues = review_result.get("issues", [])
            for issue in issues:
                review.sections_to_review.append({
                    "section": issue.get("section", ""),
                    "reason": issue.get("issue", ""),
                    "priority": issue.get("severity", "minor"),
                    "suggested_fix": issue.get("suggested_fix", ""),
                })

            # Save
            store.save_paper(paper)
            store.save_markdown(paper)
            store.save_review(review)

            stats["completed"] += 1
            stats["total_words"] += paper.total_word_count
            log(f"    Saved: {paper.id}", log_file)

        except Exception as e:
            stats["errors"] += 1
            log(f"    ERROR: {e}", log_file)

        if api.stats.cost_usd >= max_cost:
            log(f"\n  COST LIMIT REACHED: ${api.stats.cost_usd:.2f}", log_file)
            break

    stats["completed_at"] = now_iso()
    stats["total_cost"] = api.stats.cost_usd
    stats["total_calls"] = api.stats.calls

    # Save run stats
    stats_path = config.runs_dir / f"stage_a_synthesis_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.json"
    stats_path.write_text(json.dumps(stats, indent=2))
    log(f"\nSynthesis run stats saved to {stats_path}", log_file)

    return stats


# --- Main ---

def main():
    parser = argparse.ArgumentParser(
        description="Stage A Runner — Logos + Synthesis on existing Gnosis data (parallel)"
    )
    parser.add_argument("--gnosis-dir",
                        default="/Users/ekramalam/gnosis-ai/results/test-3-auto",
                        help="Path to Gnosis data directory")
    parser.add_argument("--max-cost", type=float, default=200.0,
                        help="Max total API cost in USD")
    parser.add_argument("--workers", type=int, default=8,
                        help="Number of parallel Logos workers (default 8)")
    parser.add_argument("--logos-only", action="store_true",
                        help="Only run Logos (skip Synthesis)")
    parser.add_argument("--synthesis-only", action="store_true",
                        help="Only run Synthesis (requires prior Logos run)")
    parser.add_argument("--logos-max-cost", type=float, default=None,
                        help="Max cost for Logos stage (defaults to 80%% of --max-cost)")
    parser.add_argument("--synthesis-max-cost", type=float, default=None,
                        help="Max cost for Synthesis stage (defaults to 20%% of --max-cost)")
    args = parser.parse_args()

    gnosis_dir = Path(args.gnosis_dir)
    log_file = (PROJECT_ROOT / "data" / "pipeline" /
                f"stage_a_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.log")
    log_file.parent.mkdir(parents=True, exist_ok=True)

    logos_max = args.logos_max_cost or args.max_cost * 0.8
    synthesis_max = args.synthesis_max_cost or args.max_cost * 0.2

    log("=" * 60, log_file)
    log("  STAGE A — Pipeline Validation (Parallel)", log_file)
    log("=" * 60, log_file)
    log(f"  Gnosis data: {gnosis_dir}", log_file)
    log(f"  Workers: {args.workers}", log_file)
    log(f"  Max cost: ${args.max_cost:.2f} (Logos: ${logos_max:.2f}, "
        f"Synthesis: ${synthesis_max:.2f})", log_file)
    log(f"  Log file: {log_file}", log_file)
    log(f"  Started: {now_iso()}", log_file)

    # Load data
    convergences = load_convergences(gnosis_dir)
    findings = load_findings(gnosis_dir)
    log(f"  Loaded: {len(convergences)} convergences, {len(findings)} findings", log_file)

    proofs_dir = PROJECT_ROOT / "data" / "logos" / "proofs"

    # Run Logos (parallel)
    if not args.synthesis_only:
        log("\n" + "=" * 60, log_file)
        log(f"  LOGOS — Formalisation ({args.workers} workers)", log_file)
        log("=" * 60, log_file)
        logos_stats = run_logos_parallel(convergences, logos_max, args.workers, log_file)
        log(f"\n  Logos summary: {logos_stats['completed']} completed, "
            f"{logos_stats['errors']} errors, ${logos_stats.get('total_cost', 0):.2f}", log_file)

    # Run Synthesis (sequential — papers need corpus context)
    if not args.logos_only:
        log("\n" + "=" * 60, log_file)
        log("  SYNTHESIS — Paper Composition", log_file)
        log("=" * 60, log_file)
        synthesis_stats = run_synthesis(convergences, findings, proofs_dir,
                                       synthesis_max, log_file)
        log(f"\n  Synthesis summary: {synthesis_stats['completed']} papers, "
            f"{synthesis_stats['total_words']} words, "
            f"${synthesis_stats.get('total_cost', 0):.2f}", log_file)

    log("\n" + "=" * 60, log_file)
    log("  STAGE A COMPLETE", log_file)
    log(f"  Finished: {now_iso()}", log_file)
    log("=" * 60, log_file)


if __name__ == "__main__":
    main()
