"""Pipeline Orchestrator — coordinates the Gnosis → Logos → Synthesis pipeline.

This is a thin coordination layer, NOT a fourth AI. It:
1. Reads Gnosis output (convergences, findings)
2. Passes through Logos for formalisation
3. Passes through Synthesis for paper generation
4. Maintains provenance at every stage
5. Supports human-in-the-loop checkpoints

Each stage remains independently runnable.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


def _uid() -> str:
    import uuid
    return uuid.uuid4().hex[:12]


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


class CheckpointAction:
    """Result of a human review checkpoint."""
    APPROVE = "approve"
    REJECT = "reject"
    MODIFY = "modify"
    SKIP = "skip"


@dataclass
class PipelineStage:
    """Status of one pipeline stage."""
    name: str
    status: str = "pending"  # pending | running | completed | failed | skipped
    started_at: str = ""
    completed_at: str = ""
    items_in: int = 0
    items_out: int = 0
    items_flagged: int = 0
    cost_usd: float = 0.0
    error: str = ""


@dataclass
class PipelineRun:
    """A complete pipeline execution."""

    id: str = field(default_factory=lambda: f"pipeline_{_uid()}")
    started_at: str = field(default_factory=_now)
    completed_at: str = ""

    # Input
    gnosis_data_dir: str = ""
    convergences_count: int = 0
    findings_count: int = 0

    # Stages
    stages: list[dict] = field(default_factory=list)

    # Output
    proofs_generated: int = 0
    papers_generated: int = 0
    total_cost_usd: float = 0.0

    # Provenance
    provenance_chain: list[dict] = field(default_factory=list)

    def complete(self):
        self.completed_at = _now()


class Pipeline:
    """Orchestrates Gnosis → Logos → Synthesis.

    Each stage is optional and independently configurable.
    Human checkpoints can be inserted between stages.
    """

    def __init__(
        self,
        gnosis_data_dir: Path,
        logos_output_dir: Path,
        synthesis_output_dir: Path,
        checkpoint_callback=None,
    ):
        """
        Args:
            gnosis_data_dir: Path to Gnosis data directory (convergences/, findings/)
            logos_output_dir: Where Logos writes proofs
            synthesis_output_dir: Where Synthesis writes papers
            checkpoint_callback: Optional function(stage, items) -> CheckpointAction
                                 Called between stages for human review.
                                 If None, auto-approves everything.
        """
        self.gnosis_dir = gnosis_data_dir
        self.logos_dir = logos_output_dir
        self.synthesis_dir = synthesis_output_dir
        self.checkpoint = checkpoint_callback
        self.run = PipelineRun(gnosis_data_dir=str(gnosis_data_dir))

    def execute(
        self,
        skip_logos: bool = False,
        skip_synthesis: bool = False,
        logos_filter: str = "",
        logos_max_cost: float = 100.0,
        synthesis_max_cost: float = 50.0,
    ) -> PipelineRun:
        """Execute the full pipeline.

        Args:
            skip_logos: Skip formalisation stage
            skip_synthesis: Skip paper generation stage
            logos_filter: Filter expression for Logos (e.g., "formalisability=high")
            logos_max_cost: Max API cost for Logos
            synthesis_max_cost: Max API cost for Synthesis

        Returns:
            PipelineRun with complete execution record.
        """

        # Stage 1: Load Gnosis output
        convergences, findings = self._load_gnosis()
        self.run.convergences_count = len(convergences)
        self.run.findings_count = len(findings)

        self._record_stage("gnosis_load", "completed",
                          items_in=0, items_out=len(convergences))

        # Checkpoint: Review convergences before formalisation
        if self.checkpoint:
            action = self.checkpoint("pre_logos", convergences)
            if action == CheckpointAction.REJECT:
                self.run.complete()
                return self.run

        # Stage 2: Logos formalisation
        proofs = []
        if not skip_logos:
            proofs = self._run_logos(convergences, logos_filter, logos_max_cost)
            self.run.proofs_generated = len(proofs)
        else:
            self._record_stage("logos", "skipped")

        # Checkpoint: Review proofs before synthesis
        if self.checkpoint and proofs:
            action = self.checkpoint("pre_synthesis", proofs)
            if action == CheckpointAction.REJECT:
                self.run.complete()
                return self.run

        # Stage 3: Synthesis paper generation
        papers = []
        if not skip_synthesis:
            papers = self._run_synthesis(convergences, proofs, findings, synthesis_max_cost)
            self.run.papers_generated = len(papers)
        else:
            self._record_stage("synthesis", "skipped")

        # Checkpoint: Review papers before finalisation
        if self.checkpoint and papers:
            self.checkpoint("post_synthesis", papers)

        # Record provenance
        self._build_provenance(convergences, proofs, papers)

        self.run.complete()
        return self.run

    def _load_gnosis(self) -> tuple[list[dict], list[dict]]:
        """Load convergences and findings from Gnosis data directory."""

        conv_dir = self.gnosis_dir / "convergences"
        findings_dir = self.gnosis_dir / "findings"

        convergences = []
        if conv_dir.exists():
            for f in sorted(conv_dir.glob("*.json")):
                try:
                    data = json.loads(f.read_text())
                    if not data.get("negative", False):
                        convergences.append(data)
                except (json.JSONDecodeError, Exception):
                    continue

        findings = []
        if findings_dir.exists():
            for f in sorted(findings_dir.glob("*.json")):
                try:
                    findings.append(json.loads(f.read_text()))
                except (json.JSONDecodeError, Exception):
                    continue

        return convergences, findings

    def _run_logos(self, convergences: list[dict], filter_expr: str, max_cost: float) -> list[dict]:
        """Run Logos on convergences. Returns proof dicts."""

        from logos.config import LogosConfig
        from logos.api import ClaudeAPI as LogosAPI
        from logos.store import ProofStore
        from logos.formaliser import Formaliser
        from logos.validator import ProofValidator
        from logos.lean_bridge import LeanBridge
        from logos.cli import _passes_filter

        stage = PipelineStage(name="logos", status="running")
        stage.started_at = _now()

        config = LogosConfig.load()
        config.max_cost_usd = max_cost
        config.proofs_dir = self.logos_dir / "proofs"
        config.logs_dir = self.logos_dir / "logs"
        config.flags_dir = self.logos_dir / "flags"
        config.runs_dir = self.logos_dir / "runs"
        config.ensure_dirs()

        api = LogosAPI(config)
        store = ProofStore(config)
        formaliser = Formaliser(api)
        validator = ProofValidator(api, store)
        lean = LeanBridge(api, config)

        filtered = [c for c in convergences if _passes_filter(c, filter_expr or None)]
        stage.items_in = len(filtered)

        proofs = []
        for conv in filtered:
            try:
                proof, log, flag = formaliser.formalise(conv)
                lean.process(proof, log)
                validator.validate(proof)
                store.save_proof(proof)
                store.save_log(log)
                store.save_flag(flag)
                proofs.append(asdict(proof))
            except Exception:
                stage.items_flagged += 1

            if api.stats.cost_usd >= max_cost:
                break

        stage.items_out = len(proofs)
        stage.cost_usd = api.stats.cost_usd
        stage.status = "completed"
        stage.completed_at = _now()
        self.run.stages.append(asdict(stage))
        self.run.total_cost_usd += stage.cost_usd

        return proofs

    def _run_synthesis(self, convergences: list[dict], proofs: list[dict],
                       findings: list[dict], max_cost: float) -> list[dict]:
        """Run Synthesis on convergences + proofs. Returns paper dicts."""

        from synthesis.config import SynthesisConfig
        from synthesis.api import ClaudeAPI as SynthesisAPI
        from synthesis.store import PaperStore
        from synthesis.composer import Composer

        stage = PipelineStage(name="synthesis", status="running")
        stage.started_at = _now()

        config = SynthesisConfig.load()
        config.max_cost_usd = max_cost
        config.papers_dir = self.synthesis_dir / "papers"
        config.drafts_dir = self.synthesis_dir / "drafts"
        config.reviews_dir = self.synthesis_dir / "reviews"
        config.runs_dir = self.synthesis_dir / "runs"
        config.ensure_dirs()

        api = SynthesisAPI(config)
        store = PaperStore(config)
        composer = Composer(api, config.corpus_papers_dir)

        bundles = composer.detect_boundaries(convergences, proofs, findings)
        stage.items_in = len(bundles)

        papers = []
        for bundle in bundles:
            try:
                paper, review = composer.compose(bundle)
                composer.review_paper(paper)
                store.save_paper(paper)
                store.save_markdown(paper)
                store.save_review(review)
                papers.append(asdict(paper))
            except Exception:
                stage.items_flagged += 1

            if api.stats.cost_usd >= max_cost:
                break

        stage.items_out = len(papers)
        stage.cost_usd = api.stats.cost_usd
        stage.status = "completed"
        stage.completed_at = _now()
        self.run.stages.append(asdict(stage))
        self.run.total_cost_usd += stage.cost_usd

        return papers

    def _build_provenance(self, convergences: list[dict], proofs: list[dict], papers: list[dict]):
        """Build provenance chain linking papers → proofs → convergences."""

        for paper in papers:
            chain = {
                "paper_id": paper.get("id", ""),
                "paper_title": paper.get("title", ""),
                "proof_ids": paper.get("proof_ids", []),
                "convergence_ids": paper.get("convergence_ids", []),
                "gnosis_data_dir": str(self.gnosis_dir),
            }
            self.run.provenance_chain.append(chain)

    def _record_stage(self, name: str, status: str, items_in: int = 0, items_out: int = 0):
        """Record a simple stage completion."""
        stage = PipelineStage(name=name, status=status)
        stage.items_in = items_in
        stage.items_out = items_out
        stage.completed_at = _now()
        self.run.stages.append(asdict(stage))

    def save_run(self, output_dir: Path):
        """Save the pipeline run record."""
        output_dir.mkdir(parents=True, exist_ok=True)
        path = output_dir / f"{self.run.id}.json"
        path.write_text(json.dumps(asdict(self.run), indent=2, default=str))
