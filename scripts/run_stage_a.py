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
import subprocess
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


# --- Git provenance ---

def git_stamp_paper(paper_id: str, title: str, num_convergences: int, log_file: Path):
    """Commit and push a paper immediately for Bitcoin timestamping."""
    try:
        # Stage the paper's 3 files (JSON, markdown, review)
        subprocess.run(
            ["git", "add",
             f"data/synthesis/papers/{paper_id}.json",
             f"data/synthesis/drafts/{paper_id}.md",
             f"data/synthesis/reviews/{paper_id}.json"],
            cwd=str(PROJECT_ROOT), capture_output=True, timeout=30
        )
        # Also stage the log file so progress is captured
        subprocess.run(
            ["git", "add", "data/pipeline/"],
            cwd=str(PROJECT_ROOT), capture_output=True, timeout=30
        )
        # Commit
        short_title = title[:60] if title else paper_id
        msg = (f"Synthesis paper: {short_title} "
               f"({num_convergences} convergences) [{paper_id}]")
        result = subprocess.run(
            ["git", "commit", "-m", msg],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            log(f"    Git commit skipped: {result.stderr.strip()[:100]}", log_file)
            return
        # Push for Bitcoin timestamping
        push = subprocess.run(
            ["git", "push", "origin", "main"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=60
        )
        if push.returncode != 0:
            # Remote may have Bitcoin timestamp commits — pull and retry
            subprocess.run(
                ["git", "pull", "--rebase", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
            subprocess.run(
                ["git", "push", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
        log(f"    Bitcoin stamped: {paper_id}", log_file)
    except Exception as e:
        log(f"    Git stamp warning: {e}", log_file)


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
                            config_template, log_file: Path,
                            use_max_plan: bool = False) -> dict:
    """Process a single convergence through Logos. Each call creates its own API client."""
    from logos.config import LogosConfig
    from logos.api import create_api
    from logos.store import ProofStore
    from logos.formaliser import Formaliser
    from logos.validator import ProofValidator
    from logos.lean_bridge import LeanBridge

    # Each worker gets its own API client (thread-safe)
    config = LogosConfig.load()
    config.max_cost_usd = 999  # per-worker limit disabled; global cost tracked separately
    api = create_api(config, use_max_plan=use_max_plan)
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
                       workers: int, log_file: Path,
                       use_max_plan: bool = False) -> dict:
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
                config, log_file, use_max_plan=use_max_plan
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
    # NOTE: Log/flag files are named by PROOF ID, not convergence_id.
    # Proof file: proofs/{proof_id}.json  →  contains {"id": proof_id, "convergence_id": conv_id}
    # Log file:   logs/{proof_id}.json    →  contains {"proof_id": proof_id, "decisions": [...]}
    # Flag file:  flags/{proof_id}.json   →  contains {"proof_id": proof_id, ...}
    logs_dir = proofs_dir.parent / "logs"
    enriched_logs = 0
    if logs_dir.exists():
        for p in proofs:
            # Look up by proof ID (filename matches proof, not convergence)
            proof_id = p.get("id", "")
            log_path = logs_dir / f"{proof_id}.json"
            if log_path.exists():
                try:
                    p["_reasoning_log"] = json.loads(log_path.read_text())
                    enriched_logs += 1
                except (json.JSONDecodeError, Exception):
                    pass

    # Enrich proofs with flag data (so Synthesis appendices have review status)
    flags_dir = proofs_dir.parent / "flags"
    enriched_flags = 0
    if flags_dir.exists():
        for p in proofs:
            proof_id = p.get("id", "")
            flag_path = flags_dir / f"{proof_id}.json"
            if flag_path.exists():
                try:
                    p["_flag_data"] = json.loads(flag_path.read_text())
                    enriched_flags += 1
                except (json.JSONDecodeError, Exception):
                    pass

    log(f"  Enrichment: {enriched_logs}/{len(proofs)} logs, "
        f"{enriched_flags}/{len(proofs)} flags attached to proofs", log_file)

    log(f"\nSynthesis: {len(convergences)} convergences, {len(proofs)} proofs, "
        f"{len(findings)} findings", log_file)

    # Detect paper boundaries
    log("  Detecting paper boundaries...", log_file)
    bundles = composer.detect_boundaries(convergences, proofs, findings)
    log(f"  Papers to generate: {len(bundles)}", log_file)

    # ─── COMPLETENESS VERIFICATION ───
    manifest = composer.verify_completeness(bundles, convergences, proofs)
    log(f"  Completeness: {manifest['covered_convergences']}/{manifest['total_convergences']} "
        f"convergences covered", log_file)
    if manifest["missed_convergences"]:
        log(f"  WARNING: {len(manifest['missed_convergences'])} convergences not assigned to any paper!", log_file)
        log(f"  Missed IDs: {manifest['missed_convergences'][:10]}...", log_file)
    else:
        log(f"  All convergences assigned to papers.", log_file)

    # Save manifest
    manifest_path = config.runs_dir / f"manifest_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.json"
    manifest_path.write_text(json.dumps(manifest, indent=2))
    log(f"  Manifest saved: {manifest_path}", log_file)

    stats = {
        "started": now_iso(),
        "bundles": len(bundles),
        "completed": 0,
        "errors": 0,
        "total_words": 0,
        "completeness": manifest["complete"],
    }

    # Track which convergences end up in final papers
    final_covered_ids = set()

    # ─── RESUME SUPPORT ───
    # Scan existing papers to find already-completed convergence IDs.
    # If a bundle's convergences are fully covered, skip it on restart.
    existing_papers = store.list_papers()
    already_covered_ids = set()
    for ep in existing_papers:
        already_covered_ids.update(ep.convergence_ids)
    if already_covered_ids:
        log(f"\n  Resume: found {len(existing_papers)} existing papers covering "
            f"{len(already_covered_ids)} convergences", log_file)
    skipped = 0

    for i, bundle in enumerate(bundles):
        # Check if this bundle is already fully covered by existing papers
        bundle_conv_ids = {c.get("id", "") for c in bundle.convergences}
        if bundle_conv_ids and bundle_conv_ids.issubset(already_covered_ids):
            skipped += 1
            final_covered_ids.update(bundle_conv_ids)
            log(f"\n  [{i+1}/{len(bundles)}] SKIP (already completed) — "
                f"{len(bundle.convergences)} convergences", log_file)
            continue

        log(f"\n  [{i+1}/{len(bundles)}] Paper — {len(bundle.convergences)} convergences, "
            f"{len(bundle.proofs)} proofs", log_file)

        try:
            # ─── STEP 1: COMPOSE (first draft) ───
            paper, review = composer.compose(bundle)
            log(f"    Title: {paper.title[:60]}...", log_file)
            log(f"    Words: {paper.total_word_count}", log_file)

            # ─── STEP 2: REVIEW (adversarial) ───
            review_result = composer.review_paper(paper)
            verdict = review_result.get("verdict", "unknown")
            log(f"    Review: {paper.confidence_score:.2f} ({paper.confidence_category}) — {verdict}", log_file)

            # Build review items from issues
            issues = review_result.get("issues", [])
            for issue in issues:
                review.sections_to_review.append({
                    "section": issue.get("section", ""),
                    "reason": issue.get("issue", ""),
                    "priority": issue.get("severity", "minor"),
                    "suggested_fix": issue.get("suggested_fix", ""),
                })

            # ─── STEP 3: REVISE (if review found critical/major issues) ───
            critical_or_major = [iss for iss in issues if iss.get("severity") in ("critical", "major")]
            if critical_or_major:
                log(f"    Revising: {len(critical_or_major)} critical/major issues to fix...", log_file)
                paper = composer.revise_paper(paper, review_result, bundle)
                log(f"    Revised: {paper.total_word_count} words", log_file)

                # ─── STEP 4: SECOND REVIEW (verify fixes) ───
                review_result_2 = composer.review_paper(paper)
                log(f"    Post-revision review: {paper.confidence_score:.2f} ({paper.confidence_category})", log_file)

                # Merge any remaining issues into review
                for issue in review_result_2.get("issues", []):
                    review.sections_to_review.append({
                        "section": issue.get("section", ""),
                        "reason": f"[POST-REVISION] {issue.get('issue', '')}",
                        "priority": issue.get("severity", "minor"),
                        "suggested_fix": issue.get("suggested_fix", ""),
                    })

            # ─── STEP 5: SAVE + BITCOIN STAMP ───
            store.save_paper(paper)
            store.save_markdown(paper)
            store.save_review(review)

            stats["completed"] += 1
            stats["total_words"] += paper.total_word_count
            final_covered_ids.update(paper.convergence_ids)
            log(f"    Saved: {paper.id}", log_file)

            # Commit + push immediately for provenance
            git_stamp_paper(paper.id, paper.title,
                            len(paper.convergence_ids), log_file)

        except Exception as e:
            stats["errors"] += 1
            log(f"    ERROR: {e}", log_file)

        if api.stats.cost_usd >= max_cost:
            log(f"\n  COST LIMIT REACHED: ${api.stats.cost_usd:.2f}", log_file)
            break

    stats["completed_at"] = now_iso()
    stats["total_cost"] = api.stats.cost_usd
    stats["total_calls"] = api.stats.calls
    stats["skipped_existing"] = skipped

    if skipped:
        log(f"\n  Resume summary: {skipped} papers skipped (already done), "
            f"{stats['completed']} new papers composed this run", log_file)

    # ─── FINAL COMPLETENESS CHECK ───
    all_input_ids = {c.get("id", "") for c in convergences}
    final_missed = all_input_ids - final_covered_ids
    stats["convergences_in_papers"] = len(final_covered_ids)
    stats["convergences_missed"] = len(final_missed)
    if final_missed:
        stats["missed_ids"] = sorted(final_missed)
        log(f"\n  WARNING: {len(final_missed)} convergences NOT in any final paper!", log_file)
    else:
        log(f"\n  All {len(all_input_ids)} convergences covered in final papers.", log_file)

    # Save run stats
    stats_path = config.runs_dir / f"stage_a_synthesis_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.json"
    stats_path.write_text(json.dumps(stats, indent=2))
    log(f"\nSynthesis run stats saved to {stats_path}", log_file)

    return stats


# --- Capstone runner ---

def git_stamp_capstone(paper_id: str, title: str, tier: str, log_file: Path):
    """Commit and push a capstone paper for Bitcoin timestamping."""
    try:
        subprocess.run(
            ["git", "add",
             f"data/synthesis/capstone/papers/{paper_id}.json",
             f"data/synthesis/capstone/drafts/{paper_id}.md",
             f"data/synthesis/capstone/reviews/{paper_id}.json"],
            cwd=str(PROJECT_ROOT), capture_output=True, timeout=30
        )
        subprocess.run(
            ["git", "add", "data/pipeline/"],
            cwd=str(PROJECT_ROOT), capture_output=True, timeout=30
        )
        short_title = title[:60] if title else paper_id
        msg = f"Capstone [{tier}]: {short_title} [{paper_id}]"
        result = subprocess.run(
            ["git", "commit", "-m", msg],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            log(f"    Git commit skipped: {result.stderr.strip()[:100]}", log_file)
            return
        push = subprocess.run(
            ["git", "push", "origin", "main"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=60
        )
        if push.returncode != 0:
            subprocess.run(
                ["git", "pull", "--rebase", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
            subprocess.run(
                ["git", "push", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
        log(f"    Bitcoin stamped: {paper_id}", log_file)
    except Exception as e:
        log(f"    Git stamp warning: {e}", log_file)


def git_stamp_predictions(log_file: Path):
    """Separately timestamp the predictions register."""
    try:
        subprocess.run(
            ["git", "add",
             "data/synthesis/capstone/predictions.json",
             "data/synthesis/capstone/PREDICTIONS_REGISTER.md"],
            cwd=str(PROJECT_ROOT), capture_output=True, timeout=30
        )
        result = subprocess.run(
            ["git", "commit", "-m",
             "Capstone: Predictions Register (separately timestamped)"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            log(f"    Predictions commit skipped: {result.stderr.strip()[:100]}", log_file)
            return
        push = subprocess.run(
            ["git", "push", "origin", "main"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, timeout=60
        )
        if push.returncode != 0:
            subprocess.run(
                ["git", "pull", "--rebase", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
            subprocess.run(
                ["git", "push", "origin", "main"],
                cwd=str(PROJECT_ROOT), capture_output=True, timeout=60
            )
        log(f"    Predictions register Bitcoin stamped", log_file)
    except Exception as e:
        log(f"    Predictions stamp warning: {e}", log_file)


def run_capstone(gnosis_dir: Path, proofs_dir: Path, max_cost: float, log_file: Path) -> dict:
    """Run the Capstone pipeline — Nobel-grade papers from cascade data."""
    from synthesis.config import SynthesisConfig
    from synthesis.api import ClaudeAPI
    from synthesis.capstone import CapstoneComposer
    from synthesis.models import CapstoneRun

    config = SynthesisConfig.load()
    config.max_cost_usd = max_cost
    api = ClaudeAPI(config)

    capstone_dir = PROJECT_ROOT / "data" / "synthesis" / "capstone"
    synthesis_papers_dir = config.papers_dir  # Standard Synthesis papers

    composer = CapstoneComposer(
        api=api,
        capstone_dir=capstone_dir,
        gnosis_dir=gnosis_dir,
        proofs_dir=proofs_dir,
        synthesis_papers_dir=synthesis_papers_dir,
    )

    run = CapstoneRun()

    # ─── STAGE 1: DATA CENSUS ───
    log("\n  Stage 1: Data Census (deterministic)...", log_file)
    ctx = composer.census()
    run.census_convergences = ctx.total_convergences
    run.census_proofs = ctx.total_proofs
    run.census_findings = ctx.total_findings
    run.census_fixed_points = len(ctx.fixed_points)

    log(f"    Convergences: {ctx.total_convergences}", log_file)
    log(f"    Proofs: {ctx.total_proofs}", log_file)
    log(f"    Findings: {ctx.total_findings} (across {len(ctx.cascade_levels)} levels)", log_file)
    log(f"    Fixed points: {len(ctx.fixed_points)}", log_file)
    log(f"    Synthesis papers: {len(ctx.synthesis_papers)}", log_file)
    log(f"    Cross-domain hubs: {', '.join(ctx.cross_domain_hubs[:5])}", log_file)
    log(f"    Independence clusters: {len(ctx.independence_clusters)}", log_file)
    log(f"    Cascade: {ctx.cascade_dag.get('reduction', '')}", log_file)

    # ─── STAGE 2: CLAIM FORMULATION (with resume) ───
    claims_cache = capstone_dir / "claims" / "all_candidates.json"
    claims = None
    if claims_cache.exists():
        log("\n  Stage 2: Claim Formulation — RESUMING from cached claims", log_file)
        try:
            import json as _json
            cached = _json.loads(claims_cache.read_text())
            if not isinstance(cached, list) or not cached:
                raise ValueError(f"Invalid cache: expected non-empty list, got {type(cached)}")
            # Validate first entry has required fields
            required = {"claim_text", "tier", "supporting_convergence_ids"}
            if not required.issubset(set(cached[0].keys())):
                raise ValueError(f"Cache missing required fields: {required - set(cached[0].keys())}")
            from synthesis.models import CandidateClaim
            claims = [CandidateClaim(**c) for c in cached]
            log(f"    Loaded {len(claims)} cached claims (skipping ~$5-10 API cost)", log_file)
        except Exception as e:
            log(f"    WARNING: Cache invalid ({e}), regenerating claims...", log_file)
            claims = None
    if claims is None:
        log("\n  Stage 2: Claim Formulation (cascade-driven)...", log_file)
        claims = composer.generate_claims(ctx)
    run.candidates_generated = len(claims)

    log(f"    Claims formulated: {len(claims)}", log_file)
    for claim in claims:
        log(f"      [{claim.tier}] L{claim.source_finding_level} "
            f"({claim.num_source_convergences} convs): {claim.coined_term or claim.claim_text[:50]}", log_file)

    # ─── STAGE 3: PAPER PLANNING (with resume) ───
    plans_cache = capstone_dir / "plans" / "paper_plans.json"
    plans = None
    if plans_cache.exists():
        log("\n  Stage 3: Paper Planning — RESUMING from cached plans", log_file)
        try:
            import json as _json2
            cached_plans = _json2.loads(plans_cache.read_text())
            if not isinstance(cached_plans, list) or not cached_plans:
                raise ValueError(f"Invalid cache: expected non-empty list, got {type(cached_plans)}")
            required = {"tier", "title", "convergence_ids"}
            if not required.issubset(set(cached_plans[0].keys())):
                raise ValueError(f"Cache missing required fields: {required - set(cached_plans[0].keys())}")
            from synthesis.models import PaperPlan
            plans = [PaperPlan(**p) for p in cached_plans]
            log(f"    Loaded {len(plans)} cached plans (skipping ~$2-3 API cost)", log_file)
        except Exception as e:
            log(f"    WARNING: Cache invalid ({e}), regenerating plans...", log_file)
            plans = None
    if plans is None:
        log("\n  Stage 3: Paper Planning (quality-filtered)...", log_file)
        plans = composer.plan_papers(claims, ctx)
    run.papers_planned = len(plans)

    log(f"    Papers planned: {len(plans)}", log_file)
    for plan in plans:
        log(f"      [{plan.tier}] {plan.title} ({len(plan.convergence_ids)} convs)", log_file)

    # ─── STAGE 4 + 5: COMPOSE + REVIEW ───
    log(f"\n  Stage 4+5: Composition & Review ({len(plans)} papers)...", log_file)

    # Resume support: check which papers are already done
    completed_ids = composer.list_completed_paper_ids()
    if completed_ids:
        log(f"    Resume: {len(completed_ids)} papers already completed", log_file)

    all_papers = composer.load_completed_papers()
    skipped = 0

    for i, plan in enumerate(plans):
        if plan.id in completed_ids:
            skipped += 1
            log(f"\n    [{i+1}/{len(plans)}] SKIP (already completed): {plan.title}", log_file)
            continue

        log(f"\n    [{i+1}/{len(plans)}] Composing: {plan.title}", log_file)
        log(f"      Tier: {plan.tier}, Convergences: {len(plan.convergence_ids)}", log_file)

        try:
            # Compose
            paper = composer.compose_paper(plan, ctx)
            log(f"      Words: {paper.total_word_count}", log_file)

            # Review
            review = composer.review_capstone(paper)
            verdict = review.get("verdict", "unknown")
            quality = review.get("overall_quality", 0)
            drift = review.get("nobel_model_scores", review.get("capstone_scores", {})).get("drift_detection", 0)
            log(f"      Review: quality={quality:.2f}, drift={drift:.2f}, verdict={verdict}", log_file)

            # Unsupported claims warning
            unsupported = review.get("unsupported_claims", [])
            if unsupported:
                log(f"      WARNING: {len(unsupported)} unsupported claims detected!", log_file)
                for uc in unsupported[:3]:
                    log(f"        - {uc[:80]}", log_file)

            # Revise if needed
            issues = review.get("issues", [])
            critical_major = [i for i in issues if i.get("severity") in ("critical", "major")]
            if critical_major:
                log(f"      Revising: {len(critical_major)} critical/major issues...", log_file)
                paper = composer.revise_capstone(paper, review, plan, ctx)

                # Second review
                review2 = composer.review_capstone(paper)
                log(f"      Post-revision: quality={review2.get('overall_quality', 0):.2f}", log_file)
                review = review2  # Use latest review

            # Save
            composer.save_paper(paper)
            composer.save_markdown(paper)
            composer.save_review(paper.id, review)

            run.papers_composed += 1
            run.total_word_count += paper.total_word_count
            run.paper_ids.append(paper.id)
            all_papers.append(paper)

            log(f"      Saved: {paper.id}", log_file)

            # Bitcoin stamp immediately — separate try so paper is still saved
            try:
                git_stamp_capstone(paper.id, paper.title,
                                   plan.tier, log_file)
            except Exception as stamp_err:
                log(f"      CRITICAL: Bitcoin stamping FAILED for {paper.id}: {stamp_err}", log_file)
                log(f"      Paper is saved but NOT Bitcoin-timestamped. Re-run to retry.", log_file)

        except Exception as e:
            log(f"      ERROR composing paper: {e}", log_file)
            import traceback
            log(f"      {traceback.format_exc()[:300]}", log_file)

        # Cost check
        if api.stats.cost_usd >= max_cost:
            log(f"\n    COST LIMIT: ${api.stats.cost_usd:.2f}", log_file)
            break

    if skipped:
        log(f"\n    Resume: {skipped} skipped, {run.papers_composed} new", log_file)

    # ─── STAGE 5b: CROSS-PAPER CHECK ───
    if len(all_papers) >= 2:
        log("\n  Stage 5b: Cross-paper consistency check...", log_file)
        try:
            consistency = composer.cross_paper_check(all_papers)
            contradictions = consistency.get("contradictions", [])
            redundancies = consistency.get("redundancies", [])
            log(f"    Contradictions: {len(contradictions)}", log_file)
            log(f"    Redundancies: {len(redundancies)}", log_file)
            for c in contradictions:
                log(f"      CONTRADICTION: {c.get('paper_a')} vs {c.get('paper_b')}: "
                    f"{c.get('contradiction', '')[:80]}", log_file)

            # Save consistency report
            consistency_path = capstone_dir / "consistency_report.json"
            consistency_path.write_text(json.dumps(consistency, indent=2, default=str))
        except Exception as e:
            log(f"    Consistency check error: {e}", log_file)

    # ─── STAGE 6: PREDICTION EXTRACTION ───
    if all_papers:
        log("\n  Stage 6: Prediction extraction & timestamping...", log_file)
        try:
            register = composer.extract_predictions(all_papers)
            run.total_predictions = register.get("total_predictions", 0)
            log(f"    Predictions extracted: {run.total_predictions}", log_file)

            if run.total_predictions == 0:
                log(f"    WARNING: Zero predictions extracted — skipping timestamping", log_file)
            else:
                # Bitcoin stamp predictions separately
                try:
                    git_stamp_predictions(log_file)
                except Exception as stamp_err:
                    log(f"    CRITICAL: Prediction register stamping FAILED: {stamp_err}", log_file)
        except Exception as e:
            log(f"    ERROR extracting predictions: {e}", log_file)
            import traceback
            log(f"    {traceback.format_exc()[:300]}", log_file)

    # ─── FINAL STATS ───
    run.total_cost_usd = api.stats.cost_usd
    run.total_api_calls = api.stats.calls
    run.papers_completed = run.papers_composed
    run.complete()

    # Save run
    run_path = capstone_dir / "runs" / f"{run.id}.json"
    from dataclasses import asdict as _asdict
    run_path.write_text(json.dumps(_asdict(run), indent=2, default=str))

    log(f"\n  Capstone complete: {run.papers_completed} papers, "
        f"{run.total_word_count} words, {run.total_predictions} predictions, "
        f"${run.total_cost_usd:.2f}", log_file)

    return _asdict(run)


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
    parser.add_argument("--capstone", action="store_true",
                        help="Run Capstone mode — Nobel-grade papers from cascade data. "
                             "Skips Logos and standard Synthesis.")
    parser.add_argument("--logos-max-cost", type=float, default=None,
                        help="Max cost for Logos stage (defaults to 80%% of --max-cost)")
    parser.add_argument("--synthesis-max-cost", type=float, default=None,
                        help="Max cost for Synthesis stage (defaults to 20%% of --max-cost)")
    parser.add_argument("--max-plan", action="store_true",
                        help="Use Claude Code CLI (Max plan) instead of API — $0 cost")
    args = parser.parse_args()

    gnosis_dir = Path(args.gnosis_dir)
    log_file = (PROJECT_ROOT / "data" / "pipeline" /
                f"stage_a_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.log")
    log_file.parent.mkdir(parents=True, exist_ok=True)

    proofs_dir = PROJECT_ROOT / "data" / "logos" / "proofs"

    use_max_plan = args.max_plan
    mode_label = "Max Plan (Claude Code CLI — $0 cost)" if use_max_plan else "API"

    # ─── CAPSTONE MODE ───
    if args.capstone:
        log("=" * 60, log_file)
        log("  CAPSTONE — Nobel-Grade Paper Generation", log_file)
        log("=" * 60, log_file)
        log(f"  Gnosis data: {gnosis_dir}", log_file)
        log(f"  Backend: {mode_label}", log_file)
        log(f"  Max cost: ${args.max_cost:.2f}", log_file)
        log(f"  Log file: {log_file}", log_file)
        log(f"  Started: {now_iso()}", log_file)

        capstone_stats = run_capstone(gnosis_dir, proofs_dir, args.max_cost, log_file)

        log("\n" + "=" * 60, log_file)
        log("  CAPSTONE COMPLETE", log_file)
        log(f"  Papers: {capstone_stats.get('papers_completed', 0)}", log_file)
        log(f"  Predictions: {capstone_stats.get('total_predictions', 0)}", log_file)
        log(f"  Cost: ${capstone_stats.get('total_cost_usd', 0):.2f}", log_file)
        log(f"  Finished: {now_iso()}", log_file)
        log("=" * 60, log_file)
        return

    # ─── STANDARD MODE ───
    logos_max = args.logos_max_cost or args.max_cost * 0.8
    synthesis_max = args.synthesis_max_cost or args.max_cost * 0.2

    log("=" * 60, log_file)
    log("  STAGE A — Pipeline Validation (Parallel)", log_file)
    log("=" * 60, log_file)
    log(f"  Gnosis data: {gnosis_dir}", log_file)
    log(f"  Backend: {mode_label}", log_file)
    log(f"  Workers: {args.workers}", log_file)
    log(f"  Max cost: ${args.max_cost:.2f} (Logos: ${logos_max:.2f}, "
        f"Synthesis: ${synthesis_max:.2f})", log_file)
    log(f"  Log file: {log_file}", log_file)
    log(f"  Started: {now_iso()}", log_file)

    # Load data
    convergences = load_convergences(gnosis_dir)
    findings = load_findings(gnosis_dir)
    log(f"  Loaded: {len(convergences)} convergences, {len(findings)} findings", log_file)

    # Run Logos (parallel)
    if not args.synthesis_only:
        log("\n" + "=" * 60, log_file)
        log(f"  LOGOS — Formalisation ({args.workers} workers)", log_file)
        log("=" * 60, log_file)
        logos_stats = run_logos_parallel(convergences, logos_max, args.workers, log_file,
                                         use_max_plan=use_max_plan)
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
