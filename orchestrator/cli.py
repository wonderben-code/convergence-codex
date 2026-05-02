"""Pipeline Orchestrator — CLI interface."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

import click

from orchestrator.pipeline import Pipeline, CheckpointAction


@click.group()
@click.pass_context
def cli(ctx):
    """Pipeline Orchestrator — Gnosis → Logos → Synthesis."""
    ctx.ensure_object(dict)


@cli.command()
@click.argument("gnosis_data_dir", type=click.Path(exists=True))
@click.option("--logos-dir", "-l", type=click.Path(), default="data/logos", help="Logos output directory")
@click.option("--synthesis-dir", "-s", type=click.Path(), default="data/synthesis", help="Synthesis output directory")
@click.option("--skip-logos", is_flag=True, help="Skip Logos formalisation")
@click.option("--skip-synthesis", is_flag=True, help="Skip Synthesis paper generation")
@click.option("--logos-filter", type=str, default="", help="Filter for Logos (e.g. formalisability=high)")
@click.option("--logos-cost", type=float, default=100.0, help="Max Logos API cost")
@click.option("--synthesis-cost", type=float, default=50.0, help="Max Synthesis API cost")
@click.option("--auto-approve", is_flag=True, help="Skip all human checkpoints")
@click.pass_context
def run(ctx, gnosis_data_dir, logos_dir, synthesis_dir, skip_logos, skip_synthesis,
        logos_filter, logos_cost, synthesis_cost, auto_approve):
    """Run the full pipeline on Gnosis output."""

    click.echo(f"\n{'=' * 60}")
    click.echo("  CONVERGENCE CODEX — Pipeline Run")
    click.echo(f"{'=' * 60}")

    gnosis_path = Path(gnosis_data_dir)
    logos_path = Path(logos_dir)
    synthesis_path = Path(synthesis_dir)

    # Checkpoint callback
    checkpoint = None if auto_approve else _interactive_checkpoint

    pipeline = Pipeline(
        gnosis_data_dir=gnosis_path,
        logos_output_dir=logos_path,
        synthesis_output_dir=synthesis_path,
        checkpoint_callback=checkpoint,
    )

    click.echo(f"\n  Gnosis data: {gnosis_path}")
    click.echo(f"  Logos output: {logos_path}")
    click.echo(f"  Synthesis output: {synthesis_path}")

    result = pipeline.execute(
        skip_logos=skip_logos,
        skip_synthesis=skip_synthesis,
        logos_filter=logos_filter,
        logos_max_cost=logos_cost,
        synthesis_max_cost=synthesis_cost,
    )

    # Save run record
    runs_dir = Path("data/pipeline/runs")
    pipeline.save_run(runs_dir)

    # Summary
    click.echo(f"\n{'=' * 60}")
    click.echo("  PIPELINE COMPLETE")
    click.echo(f"{'=' * 60}")
    click.echo(f"  Run ID: {result.id}")
    click.echo(f"  Convergences loaded: {result.convergences_count}")
    click.echo(f"  Proofs generated: {result.proofs_generated}")
    click.echo(f"  Papers generated: {result.papers_generated}")
    click.echo(f"  Total cost: ${result.total_cost_usd:.2f}")

    click.echo(f"\n  Stages:")
    for stage in result.stages:
        name = stage.get("name", "")
        status = stage.get("status", "")
        items_in = stage.get("items_in", 0)
        items_out = stage.get("items_out", 0)
        cost = stage.get("cost_usd", 0)
        click.echo(f"    {name}: {status} (in={items_in}, out={items_out}, ${cost:.2f})")

    if result.provenance_chain:
        click.echo(f"\n  Provenance chain: {len(result.provenance_chain)} paper(s) traceable")

    click.echo(f"{'=' * 60}\n")


@cli.command()
@click.argument("run_file", type=click.Path(exists=True))
@click.pass_context
def status(ctx, run_file):
    """Show status of a pipeline run."""

    data = json.loads(Path(run_file).read_text())

    click.echo(f"\n  Run: {data.get('id', '')}")
    click.echo(f"  Started: {data.get('started_at', '')}")
    click.echo(f"  Completed: {data.get('completed_at', 'in progress')}")
    click.echo(f"  Convergences: {data.get('convergences_count', 0)}")
    click.echo(f"  Proofs: {data.get('proofs_generated', 0)}")
    click.echo(f"  Papers: {data.get('papers_generated', 0)}")
    click.echo(f"  Cost: ${data.get('total_cost_usd', 0):.2f}")


def _interactive_checkpoint(stage: str, items: list) -> str:
    """Interactive human checkpoint between pipeline stages."""

    click.echo(f"\n  ── CHECKPOINT: {stage} ──")
    click.echo(f"  Items to review: {len(items)}")

    if stage == "pre_logos":
        click.echo("  These convergences will be formalised by Logos.")
    elif stage == "pre_synthesis":
        click.echo("  These proofs will be used by Synthesis to generate papers.")
    elif stage == "post_synthesis":
        click.echo("  These papers are ready for human review before publication.")

    response = click.prompt(
        "  Action",
        type=click.Choice(["approve", "reject", "skip"]),
        default="approve",
    )

    return response


def main():
    cli()


if __name__ == "__main__":
    main()
