"""Configuration management for Logos AI."""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class LogosConfig:
    """Runtime configuration for Logos."""

    # API
    api_key: str = ""
    model_fast: str = "claude-sonnet-4-20250514"
    model_deep: str = "claude-opus-4-20250514"
    model_fallback: str = "claude-sonnet-4-20250514"

    # Paths
    data_dir: Path = field(default_factory=lambda: Path("data/logos"))
    proofs_dir: Path = field(default_factory=lambda: Path("data/logos/proofs"))
    logs_dir: Path = field(default_factory=lambda: Path("data/logos/logs"))
    flags_dir: Path = field(default_factory=lambda: Path("data/logos/flags"))
    runs_dir: Path = field(default_factory=lambda: Path("data/logos/runs"))

    # Limits
    max_cost_usd: float = 100.0
    max_retries: int = 3

    # Lean
    lean_binary: str = ""  # Path to lean binary; empty = auto-detect
    lean_timeout_seconds: int = 120

    # Quality
    min_confidence_for_synthesis: float = 0.45
    auto_flag_below_confidence: float = 0.45
    auto_flag_new_mathematics: bool = True

    @classmethod
    def load(cls, project_root: Path | None = None) -> LogosConfig:
        """Load config from environment and optional config file."""
        if project_root is None:
            project_root = _find_project_root()

        cfg = cls()
        cfg.data_dir = project_root / "data" / "logos"
        cfg.proofs_dir = cfg.data_dir / "proofs"
        cfg.logs_dir = cfg.data_dir / "logs"
        cfg.flags_dir = cfg.data_dir / "flags"
        cfg.runs_dir = cfg.data_dir / "runs"

        # Load from config file
        config_file = project_root / "logos.json"
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

        # Environment variable overrides
        env_key = os.environ.get("ANTHROPIC_API_KEY", "")
        if env_key and not cfg.api_key:
            cfg.api_key = env_key

        # Auto-detect Lean (check PATH and common install locations)
        if not cfg.lean_binary:
            import shutil
            lean_path = shutil.which("lean")
            if not lean_path:
                # Check elan default install location
                elan_lean = Path.home() / ".elan" / "bin" / "lean"
                if elan_lean.exists():
                    lean_path = str(elan_lean)
            if lean_path:
                cfg.lean_binary = lean_path

        return cfg

    def ensure_dirs(self):
        """Create data directories if they don't exist."""
        for d in [self.proofs_dir, self.logs_dir, self.flags_dir, self.runs_dir]:
            d.mkdir(parents=True, exist_ok=True)


def _find_project_root() -> Path:
    """Find the convergence-codex project root."""
    pkg_root = Path(__file__).resolve().parent.parent
    if (pkg_root / "logos").is_dir():
        return pkg_root

    current = Path.cwd()
    for parent in [current, *current.parents]:
        if (parent / "logos").is_dir() and (parent / "docs").is_dir():
            return parent
    return current
