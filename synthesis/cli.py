"""Synthesis AI — CLI interface."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

import click

from synthesis.config import SynthesisConfig
from synthesis.api import ClaudeAPI
from synthesis.store import PaperStore
from synthesis.models import SynthesisRun, PaperBundle
from synthesis.composer import Composer


@click.group()
@click.pass_context
def cli(ctx):
    """Synthesis AI — the Communicator. Produces publication-quality papers from discoveries and proofs."""
    ctx.ensure_object(dict)


@cli.command()
@click.argument("convergences_dir", type=click.Path(exists=True))
@click.option("--proofs-dir", type=click.Path(exists=True), help="Directory of Logos proof JSONs")
@click.option("--findings-dir", type=click.Path(exists=True), help="Directory of finding JSONs")
@click.option("--output-dir", "-o", type=click.Path(), help="Output directory for paper drafts")
@click.option("--auto-boundary", is_flag=True, default=True, help="Auto-detect paper boundaries")
@click.option("--skip-review", is_flag=True, help="Skip adversarial review")
@click.option("--max-cost", type=float, default=50.0, help="Max API cost in USD")
@click.option("--max-papers", type=int, default=0, help="Max papers to generate (0=unlimited)")
@click.pass_context
def compose(ctx, convergences_dir, proofs_dir, findings_dir, output_dir,
            auto_boundary, skip_review, max_cost, max_papers):
    """Compose papers from convergences and proofs."""

    config = SynthesisConfig.load()
    config.max_cost_usd = max_cost

    # Load data
    convergences = _load_json_dir(convergences_dir)
    proofs = _load_json_dir(proofs_dir) if proofs_dir else []
    findings = _load_json_dir(findings_dir) if findings_dir else []

    # Filter out negatives
    convergences = [c for c in convergences if not c.get("negative", False)]

    click.echo(f"\n{'=' * 60}")
    click.echo("  SYNTHESIS AI — Paper Composition")
    click.echo(f"{'=' * 60}")
    click.echo(f"\n  Convergences: {len(convergences)}")
    click.echo(f"  Proofs: {len(proofs)}")
    click.echo(f"  Findings: {len(findings)}")

    api = ClaudeAPI(config)
    store = PaperStore(config)
    composer = Composer(api, config.corpus_papers_dir)

    # Detect paper boundaries
    click.echo("\n  Detecting paper boundaries...")
    if auto_boundary:
        bundles = composer.detect_boundaries(convergences, proofs, findings)
    else:
        bundles = [PaperBundle(convergences=convergences, proofs=proofs, findings=findings)]

    if max_papers > 0:
        bundles = bundles[:max_papers]

    click.echo(f"  Papers to generate: {len(bundles)}")

    run = SynthesisRun()
    run.papers_attempted = len(bundles)

    if output_dir:
        Path(output_dir).mkdir(parents=True, exist_ok=True)

    for i, bundle in enumerate(bundles):
        click.echo(f"\n  [{i+1}/{len(bundles)}] Composing paper...")
        click.echo(f"    Convergences: {len(bundle.convergences)}, Proofs: {len(bundle.proofs)}")

        try:
            paper, review = composer.compose(bundle)
            click.echo(f"    Title: {paper.title[:60]}...")
            click.echo(f"    Words: {paper.total_word_count}")

            # Review
            if not skip_review:
                click.echo("    Reviewing...")
                review_result = composer.review_paper(paper)
                click.echo(f"    Review: {paper.confidence_score:.2f} ({paper.confidence_category})")

                # Build review request from issues
                issues = review_result.get("issues", [])
                for issue in issues:
                    review.sections_to_review.append({
                        "section": issue.get("section", ""),
                        "reason": issue.get("issue", ""),
                        "priority": issue.get("severity", "minor"),
                        "suggested_fix": issue.get("suggested_fix", ""),
                    })
            else:
                paper.confidence_score = 0.0
                paper.confidence_category = "low"

            # Save
            store.save_paper(paper)
            store.save_markdown(paper)
            store.save_review(review)

            if output_dir:
                md_path = Path(output_dir) / f"{paper.id}.md"
                md_path.write_text(paper.full_markdown)
                json_path = Path(output_dir) / f"{paper.id}.json"
                json_path.write_text(json.dumps(asdict(paper), indent=2, default=str))

            # Update run
            run.papers_completed += 1
            run.paper_ids.append(paper.id)
            run.total_word_count += paper.total_word_count
            cat = paper.confidence_category
            if cat == "high":
                run.papers_high_confidence += 1
            elif cat == "medium":
                run.papers_medium_confidence += 1
            else:
                run.papers_low_confidence += 1

            click.echo(f"    Saved: {paper.id}")

        except Exception as e:
            click.echo(f"    ERROR: {e}")

        if api.stats.cost_usd >= max_cost:
            click.echo(f"\n  Cost limit reached (${api.stats.cost_usd:.2f}). Stopping.")
            break

    # Complete run
    run.total_api_calls = api.stats.calls
    run.total_cost_usd = api.stats.cost_usd
    run.complete()
    store.save_run(run)

    click.echo(f"\n{'=' * 60}")
    click.echo("  COMPOSITION COMPLETE")
    click.echo(f"{'=' * 60}")
    click.echo(f"  Papers: {run.papers_completed}")
    click.echo(f"  Total words: {run.total_word_count}")
    click.echo(f"  High confidence: {run.papers_high_confidence}")
    click.echo(f"  Medium: {run.papers_medium_confidence}")
    click.echo(f"  Low: {run.papers_low_confidence}")
    click.echo(f"  Cost: ${run.total_cost_usd:.2f}")
    click.echo(f"  Run ID: {run.id}")
    click.echo(f"{'=' * 60}\n")


@cli.command()
@click.argument("paper_path", type=click.Path(exists=True))
@click.option("--max-cost", type=float, default=10.0, help="Max API cost in USD")
@click.pass_context
def review(ctx, paper_path, max_cost):
    """Run adversarial review on a paper draft."""

    config = SynthesisConfig.load()
    config.max_cost_usd = max_cost

    data = json.loads(Path(paper_path).read_text())
    from synthesis.models import PaperDraft
    paper = PaperDraft(**data)

    api = ClaudeAPI(config)
    composer = Composer(api)

    click.echo(f"\nReviewing: {paper.title}")
    result = composer.review_paper(paper)

    click.echo(f"\n  Overall quality: {result.get('overall_quality', 0):.2f}")
    click.echo(f"  Verdict: {result.get('verdict', 'unknown')}")

    sections = result.get("section_scores", {})
    if sections:
        click.echo("  Section scores:")
        for s, score in sections.items():
            click.echo(f"    {s}: {score:.2f}")

    issues = result.get("issues", [])
    if issues:
        click.echo(f"\n  Issues ({len(issues)}):")
        for issue in issues:
            click.echo(f"    [{issue.get('severity', '')}] {issue.get('section', '')}: {issue.get('issue', '')}")

    click.echo(f"\n  Cost: ${api.stats.cost_usd:.2f}")


@cli.command()
@click.pass_context
def stats(ctx):
    """Show paper corpus statistics."""

    config = SynthesisConfig.load()
    store = PaperStore(config)
    s = store.stats()

    if s.get("total_papers", 0) == 0:
        click.echo("No papers in corpus yet.")
        return

    click.echo(f"\n{'=' * 60}")
    click.echo("  SYNTHESIS PAPER CORPUS — Statistics")
    click.echo(f"{'=' * 60}")
    click.echo(f"  Total papers: {s['total_papers']}")
    click.echo(f"  High confidence: {s['high_confidence']}")
    click.echo(f"  Medium confidence: {s['medium_confidence']}")
    click.echo(f"  Low confidence: {s['low_confidence']}")
    click.echo(f"  Total words: {s['total_word_count']}")
    click.echo(f"  Convergences covered: {s['total_convergences_covered']}")
    click.echo(f"  Proofs covered: {s['total_proofs_covered']}")
    click.echo(f"{'=' * 60}\n")


@cli.command(name="list")
@click.pass_context
def list_papers(ctx):
    """List all paper drafts."""

    config = SynthesisConfig.load()
    store = PaperStore(config)

    papers = store.list_papers()
    if not papers:
        click.echo("No papers yet.")
        return

    for p in papers:
        cat = p.confidence_category[0].upper()
        click.echo(f"  [{cat}] {p.id} — {p.title[:60]}... ({p.total_word_count} words)")


def _load_json_dir(dir_path: str) -> list[dict]:
    """Load all JSON files from a directory."""
    path = Path(dir_path)
    items = []
    for f in sorted(path.glob("*.json")):
        try:
            items.append(json.loads(f.read_text()))
        except (json.JSONDecodeError, Exception):
            continue
    return items


def main():
    cli()


if __name__ == "__main__":
    main()
