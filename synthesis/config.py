"""Configuration management for Synthesis AI."""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class SynthesisConfig:
    """Runtime configuration for Synthesis."""

    # API
    api_key: str = ""
    model_fast: str = "claude-sonnet-4-20250514"
    model_deep: str = "claude-opus-4-20250514"
    model_fallback: str = "claude-sonnet-4-20250514"

    # Paths
    data_dir: Path = field(default_factory=lambda: Path("data/synthesis"))
    papers_dir: Path = field(default_factory=lambda: Path("data/synthesis/papers"))
    drafts_dir: Path = field(default_factory=lambda: Path("data/synthesis/drafts"))
    reviews_dir: Path = field(default_factory=lambda: Path("data/synthesis/reviews"))
    runs_dir: Path = field(default_factory=lambda: Path("data/synthesis/runs"))

    # Limits
    max_cost_usd: float = 100.0
    max_retries: int = 3

    # Quality
    target_word_count_min: int = 4000
    target_word_count_max: int = 25000
    min_confidence_for_publication: float = 0.45

    # Corpus context
    corpus_papers_dir: Path = field(default_factory=lambda: Path("papers"))

    @classmethod
    def load(cls, project_root: Path | None = None) -> SynthesisConfig:
        """Load config from environment and optional config file."""
        if project_root is None:
            project_root = _find_project_root()

        cfg = cls()
        cfg.data_dir = project_root / "data" / "synthesis"
        cfg.papers_dir = cfg.data_dir / "papers"
        cfg.drafts_dir = cfg.data_dir / "drafts"
        cfg.reviews_dir = cfg.data_dir / "reviews"
        cfg.runs_dir = cfg.data_dir / "runs"
        cfg.corpus_papers_dir = project_root / "papers"

        config_file = project_root / "synthesis.json"
        if config_file.exists():
            with open(config_file) as f:
                data = json.load(f)
            key_map = {"anthropic_api_key": "api_key"}
            for key, val in data.items():
                attr = key_map.get(key, key)
                if hasattr(cfg, attr):
                    if isinstance(getattr(cfg, attr), Path):
                        setattr(cfg, attr, Path(val))
                    else:
                        setattr(cfg, attr, val)

        env_key = os.environ.get("ANTHROPIC_API_KEY", "")
        if env_key and not cfg.api_key:
            cfg.api_key = env_key

        return cfg

    def ensure_dirs(self):
        """Create data directories if they don't exist."""
        for d in [self.papers_dir, self.drafts_dir, self.reviews_dir, self.runs_dir]:
            d.mkdir(parents=True, exist_ok=True)


def _find_project_root() -> Path:
    """Find the convergence-codex project root."""
    pkg_root = Path(__file__).resolve().parent.parent
    if (pkg_root / "synthesis").is_dir():
        return pkg_root

    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / "synthesis").is_dir() and (parent / "docs").is_dir():
            return parent
    return current
