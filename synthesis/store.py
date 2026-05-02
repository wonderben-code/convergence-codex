"""Paper Store — persistent JSON storage for Synthesis outputs."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Optional

from synthesis.config import SynthesisConfig
from synthesis.models import PaperDraft, ReviewRequest, SynthesisRun


class PaperStore:
    """JSON-file-based storage for paper drafts, reviews, and runs."""

    def __init__(self, config: SynthesisConfig):
        self.config = config
        config.ensure_dirs()

    # --- Papers ---

    def save_paper(self, paper: PaperDraft):
        path = self.config.papers_dir / f"{paper.id}.json"
        path.write_text(json.dumps(asdict(paper), indent=2, default=str))

    def load_paper(self, paper_id: str) -> Optional[PaperDraft]:
        path = self.config.papers_dir / f"{paper_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return PaperDraft(**data)

    def list_papers(self) -> list[PaperDraft]:
        papers = []
        for path in sorted(self.config.papers_dir.glob("*.json")):
            data = json.loads(path.read_text())
            papers.append(PaperDraft(**data))
        return papers

    # --- Markdown export ---

    def save_markdown(self, paper: PaperDraft):
        """Save the full markdown to the drafts directory."""
        if not paper.full_markdown:
            return
        path = self.config.drafts_dir / f"{paper.id}.md"
        path.write_text(paper.full_markdown)

    # --- Reviews ---

    def save_review(self, review: ReviewRequest):
        path = self.config.reviews_dir / f"{review.paper_id}.json"
        path.write_text(json.dumps(asdict(review), indent=2, default=str))

    def load_review(self, paper_id: str) -> Optional[ReviewRequest]:
        path = self.config.reviews_dir / f"{paper_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return ReviewRequest(**data)

    # --- Runs ---

    def save_run(self, run: SynthesisRun):
        path = self.config.runs_dir / f"{run.id}.json"
        path.write_text(json.dumps(asdict(run), indent=2, default=str))

    def load_run(self, run_id: str) -> Optional[SynthesisRun]:
        path = self.config.runs_dir / f"{run_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return SynthesisRun(**data)

    # --- Stats ---

    def stats(self) -> dict:
        """Paper corpus statistics."""
        papers = self.list_papers()
        total = len(papers)
        if total == 0:
            return {"total_papers": 0}

        high = sum(1 for p in papers if p.confidence_category == "high")
        medium = sum(1 for p in papers if p.confidence_category == "medium")
        low = sum(1 for p in papers if p.confidence_category == "low")
        total_words = sum(p.total_word_count for p in papers)
        total_convs = sum(len(p.convergence_ids) for p in papers)
        total_proofs = sum(len(p.proof_ids) for p in papers)

        return {
            "total_papers": total,
            "high_confidence": high,
            "medium_confidence": medium,
            "low_confidence": low,
            "total_word_count": total_words,
            "total_convergences_covered": total_convs,
            "total_proofs_covered": total_proofs,
        }
