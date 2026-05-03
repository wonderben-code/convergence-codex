"""Logos AI — CLI interface."""

from __future__ import annotations

import json
import sys
from dataclasses import asdict
from pathlib import Path

import click

from logos.config import LogosConfig
from logos.api import ClaudeAPI, MaxPlanAPI, create_api
from logos.store import ProofStore
from logos.models import LogosRun, ProofConfidence
from logos.formaliser import Formaliser
from logos.validator import ProofValidator
from logos.multi_verifier import MultiVerifier


@click.group()
@click.option("--max-plan", is_flag=True, default=False,
              help="Use Claude Code CLI (Max plan) instead of API — $0 cost")
@click.pass_context
def cli(ctx, max_plan: bool):
    """Logos AI — the Formaliser. Produces formal mathematical proofs from discoveries."""
    ctx.ensure_object(dict)
    ctx.obj["use_max_plan"] = max_plan


@cli.command()
@click.argument("convergence_path", type=click.Path(exists=True))
@click.option("--output", "-o", type=click.Path(), help="Output proof JSON path")
@click.option("--skip-lean", is_flag=True, help="Skip Lean 4 generation")
@click.option("--skip-validation", is_flag=True, help="Skip adversarial validation")
@click.option("--max-cost", type=float, default=20.0, help="Max API cost in USD")
@click.pass_context
def prove(ctx, convergence_path, output, skip_lean, skip_validation, max_cost):
    """Formalise a single convergence into a mathematical proof."""

    config = LogosConfig.load()
    config.max_cost_usd = max_cost
    use_max_plan = ctx.obj.get("use_max_plan", False)

    convergence = _load_convergence(convergence_path)

    click.echo(f"\n{'=' * 60}")
    click.echo("  LOGOS AI — Formalisation")
    if use_max_plan:
        click.echo("  Mode: Max Plan (Claude Code CLI — $0 cost)")
    click.echo(f"{'=' * 60}")
    click.echo(f"\n  Convergence: {convergence.get('structural_claim', '')[:80]}...")
    click.echo(f"  Domains: {', '.join(convergence.get('domain_names', convergence.get('domains', [])))}")
    click.echo(f"  Type: {convergence.get('convergence_type', 'unknown')}")

    api = create_api(config, use_max_plan=use_max_plan)
    store = ProofStore(config)

    # Stage 1-4: Formalise
    click.echo("\n  [1/4] Detecting formalisation type...")
    formaliser = Formaliser(api)
    proof, log, flag = formaliser.formalise(convergence)
    click.echo(f"         Type: {proof.formalisation_type}")
    click.echo(f"         Apparatus: {', '.join(proof.mathematical_apparatus)}")
    click.echo(f"         Steps: {len(proof.proof_steps)}")

    # Stage 5: Lean verification
    if not skip_lean:
        click.echo("\n  [2/4] Lean 4 verification...")
        mv = MultiVerifier(api, config)
        consensus = mv.verify(proof, log)
        level = consensus.get("verification_level", "unknown")
        tier = consensus.get("verification_tier", "unknown")
        click.echo(f"         Tier: {tier}")
        click.echo(f"         Level: {level}")
        if proof.lean_verified:
            click.echo(f"         Lean: VERIFIED (0 sorry)")
        elif proof.lean_partial:
            sorrys = proof.proof_lean.lower().count("sorry") if proof.proof_lean else 0
            click.echo(f"         Lean: PARTIAL ({sorrys} sorry)")
        else:
            click.echo(f"         Lean: {proof.lean_failure_reason or 'failed'}")
    else:
        click.echo("\n  [2/4] Lean verification... SKIPPED")

    # Stage 6: Validation
    if not skip_validation:
        click.echo("\n  [3/4] Adversarial validation...")
        validator = ProofValidator(api, store)
        result = validator.validate(proof)
        click.echo(f"         Adversarial: {result.scores.adversarial:.2f}")
        click.echo(f"         Internal: {result.scores.internal:.2f}")
        click.echo(f"         Cross-proof: {result.scores.cross_proof:.2f}")
        click.echo(f"         Overall: {result.overall_confidence:.2f} ({result.confidence_category})")
    else:
        click.echo("\n  [3/4] Adversarial validation... SKIPPED")
        proof.confidence_score = 0.0
        proof.confidence_category = "low"

    # Save
    click.echo("\n  [4/4] Saving...")
    store.save_proof(proof)
    store.save_log(log)
    store.save_flag(flag)

    if output:
        Path(output).write_text(json.dumps(asdict(proof), indent=2, default=str))
        click.echo(f"         Output: {output}")

    # Summary
    click.echo(f"\n{'─' * 60}")
    click.echo(f"  Proof ID: {proof.id}")
    click.echo(f"  Confidence: {proof.confidence_score:.2f} ({proof.confidence_category})")
    click.echo(f"  Verification: {proof.verification_status}")
    if flag.requires_human_review:
        click.echo(f"  FLAGGED for review: {flag.review_priority}")
        for r in flag.review_reasons:
            click.echo(f"    - {r}")
    click.echo(f"  Cost: ${api.stats.cost_usd:.2f}")
    click.echo(f"  API calls: {api.stats.calls}")
    click.echo(f"{'─' * 60}\n")


@cli.command()
@click.argument("convergences_dir", type=click.Path(exists=True))
@click.option("--output-dir", "-o", type=click.Path(), help="Output directory for proof JSONs")
@click.option("--filter", "filter_expr", type=str, help="Filter: formalisability=high, confidence=supported")
@click.option("--skip-lean", is_flag=True, help="Skip Lean 4 generation")
@click.option("--skip-validation", is_flag=True, help="Skip adversarial validation")
@click.option("--max-cost", type=float, default=100.0, help="Max API cost in USD")
@click.option("--max-proofs", type=int, default=0, help="Max number of proofs to generate (0=unlimited)")
@click.pass_context
def batch(ctx, convergences_dir, output_dir, filter_expr, skip_lean, skip_validation, max_cost, max_proofs):
    """Formalise all convergences in a directory."""

    config = LogosConfig.load()
    config.max_cost_usd = max_cost
    use_max_plan = ctx.obj.get("use_max_plan", False)

    convergences_path = Path(convergences_dir)
    convergence_files = sorted(convergences_path.glob("*.json"))

    if not convergence_files:
        click.echo("No convergence JSON files found.")
        return

    # Apply filters
    convergences = []
    for f in convergence_files:
        conv = json.loads(f.read_text())
        if _passes_filter(conv, filter_expr):
            convergences.append(conv)

    if max_proofs > 0:
        convergences = convergences[:max_proofs]

    click.echo(f"\n{'=' * 60}")
    click.echo("  LOGOS AI — Batch Formalisation")
    if use_max_plan:
        click.echo("  Mode: Max Plan (Claude Code CLI — $0 cost)")
    click.echo(f"{'=' * 60}")
    click.echo(f"\n  Convergences: {len(convergences)} (of {len(convergence_files)} total)")
    click.echo(f"  Max cost: ${max_cost:.2f}")

    api = create_api(config, use_max_plan=use_max_plan)
    store = ProofStore(config)
    formaliser = Formaliser(api)
    mv = MultiVerifier(api, config) if not skip_lean else None
    validator = ProofValidator(api, store) if not skip_validation else None

    run = LogosRun()
    run.proofs_attempted = len(convergences)

    if output_dir:
        Path(output_dir).mkdir(parents=True, exist_ok=True)

    for i, conv in enumerate(convergences):
        click.echo(f"\n  [{i+1}/{len(convergences)}] {conv.get('structural_claim', '')[:60]}...")

        try:
            # Formalise
            proof, log, flag = formaliser.formalise(conv)

            # Multi-tool verification
            if mv:
                mv.verify(proof, log)

            # Validate
            if validator:
                result = validator.validate(proof)
                click.echo(f"           Confidence: {result.overall_confidence:.2f} ({result.confidence_category})")
            else:
                proof.confidence_score = 0.0
                proof.confidence_category = "low"

            # Save
            store.save_proof(proof)
            store.save_log(log)
            store.save_flag(flag)

            if output_dir:
                out_path = Path(output_dir) / f"{proof.id}.json"
                out_path.write_text(json.dumps(asdict(proof), indent=2, default=str))

            # Update run stats
            run.proofs_completed += 1
            run.proof_ids.append(proof.id)
            cat = proof.confidence_category
            if cat == "high":
                run.proofs_high_confidence += 1
            elif cat == "medium":
                run.proofs_medium_confidence += 1
            else:
                run.proofs_low_confidence += 1
            if proof.lean_verified:
                run.proofs_lean_verified += 1
            if flag.requires_human_review:
                run.proofs_flagged += 1

            click.echo(f"           Type: {proof.formalisation_type}, Verification: {proof.verification_status}")

        except Exception as e:
            click.echo(f"           ERROR: {e}")

        # Cost check
        if api.stats.cost_usd >= max_cost:
            click.echo(f"\n  Cost limit reached (${api.stats.cost_usd:.2f}). Stopping.")
            break

    # Complete run
    run.total_api_calls = api.stats.calls
    run.total_cost_usd = api.stats.cost_usd
    run.complete()
    store.save_run(run)

    # Summary
    click.echo(f"\n{'=' * 60}")
    click.echo("  BATCH COMPLETE")
    click.echo(f"{'=' * 60}")
    click.echo(f"  Attempted: {run.proofs_attempted}")
    click.echo(f"  Completed: {run.proofs_completed}")
    click.echo(f"  High confidence: {run.proofs_high_confidence}")
    click.echo(f"  Medium confidence: {run.proofs_medium_confidence}")
    click.echo(f"  Low confidence: {run.proofs_low_confidence}")
    click.echo(f"  Lean verified: {run.proofs_lean_verified}")
    click.echo(f"  Flagged for review: {run.proofs_flagged}")
    click.echo(f"  Cost: ${run.total_cost_usd:.2f}")
    click.echo(f"  Run ID: {run.id}")
    click.echo(f"{'=' * 60}\n")


@cli.command()
@click.argument("proof_path", type=click.Path(exists=True))
@click.option("--max-cost", type=float, default=10.0, help="Max API cost in USD")
@click.pass_context
def validate(ctx, proof_path, max_cost):
    """Re-run adversarial validation on an existing proof."""

    config = LogosConfig.load()
    config.max_cost_usd = max_cost

    data = json.loads(Path(proof_path).read_text())
    from logos.models import ProofRecord
    proof = ProofRecord(**data)

    api = create_api(config, use_max_plan=ctx.obj.get("use_max_plan", False))
    store = ProofStore(config)
    validator = ProofValidator(api, store)

    click.echo(f"\nValidating proof {proof.id}...")
    result = validator.validate(proof)

    click.echo(f"  Mechanical:  {result.scores.mechanical:.2f}")
    click.echo(f"  Adversarial: {result.scores.adversarial:.2f}")
    click.echo(f"  Internal:    {result.scores.internal:.2f}")
    click.echo(f"  Cross-proof: {result.scores.cross_proof:.2f}")
    click.echo(f"  Calibration: {result.scores.calibration:.2f}")
    click.echo(f"  OVERALL:     {result.overall_confidence:.2f} ({result.confidence_category})")

    # Save updated proof
    store.save_proof(proof)
    click.echo(f"\n  Updated proof saved. Cost: ${api.stats.cost_usd:.2f}")


@cli.command()
@click.argument("proofs_dir", type=click.Path(exists=True), default="data/logos/proofs")
@click.option("--format", "fmt", type=click.Choice(["synthesis", "summary", "json"]), default="summary")
@click.pass_context
def export(ctx, proofs_dir, fmt):
    """Export proofs for Synthesis or review."""

    config = LogosConfig.load()
    store = ProofStore(config)

    proofs = store.list_proofs()
    if not proofs:
        click.echo("No proofs found.")
        return

    if fmt == "summary":
        click.echo(f"\n{'=' * 60}")
        click.echo("  LOGOS PROOF CORPUS")
        click.echo(f"{'=' * 60}")
        for p in proofs:
            status = "V" if p.lean_verified else "P" if p.lean_partial else "N"
            cat = p.confidence_category[0].upper()
            click.echo(f"  [{status}|{cat}] {p.proposition_natural[:70]}...")
        click.echo(f"\n  Total: {len(proofs)}")

    elif fmt == "synthesis":
        # Export in Synthesis-compatible bundle format
        bundle = {
            "proofs": [asdict(p) for p in proofs],
            "stats": store.stats(),
        }
        click.echo(json.dumps(bundle, indent=2, default=str))

    elif fmt == "json":
        click.echo(json.dumps([asdict(p) for p in proofs], indent=2, default=str))


@cli.command()
@click.pass_context
def stats(ctx):
    """Show proof corpus statistics."""

    config = LogosConfig.load()
    store = ProofStore(config)

    s = store.stats()
    if s.get("total_proofs", 0) == 0:
        click.echo("No proofs in corpus yet.")
        return

    click.echo(f"\n{'=' * 60}")
    click.echo("  LOGOS PROOF CORPUS — Statistics")
    click.echo(f"{'=' * 60}")
    click.echo(f"  Total proofs: {s['total_proofs']}")
    click.echo(f"  High confidence: {s['high_confidence']}")
    click.echo(f"  Medium confidence: {s['medium_confidence']}")
    click.echo(f"  Low confidence: {s['low_confidence']}")
    click.echo(f"  Lean verified: {s['lean_verified']}")
    click.echo(f"  Lean partial: {s['lean_partial']}")
    click.echo(f"  Flagged for review: {s['flagged_for_review']}")
    click.echo(f"  Needs new mathematics: {s['new_mathematics_needed']}")
    click.echo(f"\n  By formalisation type:")
    for t, c in s.get("by_formalisation_type", {}).items():
        click.echo(f"    {t}: {c}")
    click.echo(f"\n  By mathematical apparatus:")
    for a, c in s.get("by_apparatus", []):
        click.echo(f"    {a}: {c}")
    click.echo(f"{'=' * 60}\n")


@cli.command()
@click.pass_context
def flagged(ctx):
    """Show all proofs flagged for human review."""

    config = LogosConfig.load()
    store = ProofStore(config)

    flags = store.flagged_proofs()
    if not flags:
        click.echo("No proofs flagged for human review.")
        return

    click.echo(f"\n{'=' * 60}")
    click.echo("  PROOFS REQUIRING HUMAN REVIEW")
    click.echo(f"{'=' * 60}")
    for f in flags:
        proof = store.load_proof(f.proof_id)
        name = proof.proposition_natural[:60] if proof else f.proof_id
        click.echo(f"\n  [{f.review_priority.upper()}] {name}...")
        for r in f.review_reasons:
            click.echo(f"    - {r}")
        if f.suggested_expertise:
            click.echo(f"    Expertise needed: {', '.join(f.suggested_expertise)}")
    click.echo(f"\n  Total flagged: {len(flags)}")
    click.echo(f"{'=' * 60}\n")


def _load_convergence(path: str) -> dict:
    """Load a convergence JSON file."""
    data = json.loads(Path(path).read_text())
    # Handle both direct convergence format and nested format
    if "convergences" in data:
        # It's a run export — take the first convergence
        return data["convergences"][0]
    return data


def _passes_filter(conv: dict, filter_expr: str | None) -> bool:
    """Check if a convergence passes the filter expression."""
    if not filter_expr:
        return True

    # Skip negative convergences by default
    if conv.get("negative", False):
        return False

    for part in filter_expr.split(","):
        part = part.strip()
        if "=" not in part:
            continue
        key, val = part.split("=", 1)
        key = key.strip()
        val = val.strip()

        if key == "formalisability":
            if conv.get("formalisability_hint", "") != val:
                return False
        elif key == "confidence":
            ea = conv.get("ea_scores", {})
            if ea.get("confidence_category", "") != val:
                return False
        elif key == "type":
            if conv.get("convergence_type", "") != val:
                return False

    return True


def main():
    cli()


if __name__ == "__main__":
    main()
