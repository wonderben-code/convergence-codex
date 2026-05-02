"""Proof Store — persistent JSON storage for Logos outputs."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Optional

from logos.config import LogosConfig
from logos.models import ProofRecord, LogRecord, FlagRecord, LogosRun


class ProofStore:
    """JSON-file-based storage for proofs, logs, flags, and runs."""

    def __init__(self, config: LogosConfig):
        self.config = config
        config.ensure_dirs()

    # --- Proofs ---

    def save_proof(self, proof: ProofRecord):
        path = self.config.proofs_dir / f"{proof.id}.json"
        path.write_text(json.dumps(asdict(proof), indent=2, default=str))

    def load_proof(self, proof_id: str) -> Optional[ProofRecord]:
        path = self.config.proofs_dir / f"{proof_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return ProofRecord(**data)

    def list_proofs(self) -> list[ProofRecord]:
        proofs = []
        for path in sorted(self.config.proofs_dir.glob("*.json")):
            data = json.loads(path.read_text())
            proofs.append(ProofRecord(**data))
        return proofs

    def proof_exists(self, convergence_id: str) -> bool:
        """Check if a proof already exists for this convergence."""
        for path in self.config.proofs_dir.glob("*.json"):
            data = json.loads(path.read_text())
            if data.get("convergence_id") == convergence_id:
                return True
        return False

    def find_by_convergence(self, convergence_id: str) -> Optional[ProofRecord]:
        """Find proof by source convergence ID."""
        for path in self.config.proofs_dir.glob("*.json"):
            data = json.loads(path.read_text())
            if data.get("convergence_id") == convergence_id:
                return ProofRecord(**data)
        return None

    # --- Logs ---

    def save_log(self, log: LogRecord):
        path = self.config.logs_dir / f"{log.proof_id}.json"
        path.write_text(json.dumps(asdict(log), indent=2, default=str))

    def load_log(self, proof_id: str) -> Optional[LogRecord]:
        path = self.config.logs_dir / f"{proof_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return LogRecord(**data)

    # --- Flags ---

    def save_flag(self, flag: FlagRecord):
        path = self.config.flags_dir / f"{flag.proof_id}.json"
        path.write_text(json.dumps(asdict(flag), indent=2, default=str))

    def load_flag(self, proof_id: str) -> Optional[FlagRecord]:
        path = self.config.flags_dir / f"{proof_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return FlagRecord(**data)

    def flagged_proofs(self) -> list[FlagRecord]:
        """All proofs flagged for human review."""
        flags = []
        for path in sorted(self.config.flags_dir.glob("*.json")):
            data = json.loads(path.read_text())
            flag = FlagRecord(**data)
            if flag.requires_human_review:
                flags.append(flag)
        return flags

    # --- Runs ---

    def save_run(self, run: LogosRun):
        path = self.config.runs_dir / f"{run.id}.json"
        path.write_text(json.dumps(asdict(run), indent=2, default=str))

    def load_run(self, run_id: str) -> Optional[LogosRun]:
        path = self.config.runs_dir / f"{run_id}.json"
        if not path.exists():
            return None
        data = json.loads(path.read_text())
        return LogosRun(**data)

    def latest_run(self) -> Optional[LogosRun]:
        runs = sorted(self.config.runs_dir.glob("*.json"), key=lambda p: p.stat().st_mtime)
        if not runs:
            return None
        data = json.loads(runs[-1].read_text())
        return LogosRun(**data)

    # --- Stats ---

    def stats(self) -> dict:
        """Proof corpus statistics."""
        proofs = self.list_proofs()
        total = len(proofs)
        if total == 0:
            return {"total_proofs": 0}

        high = sum(1 for p in proofs if p.confidence_category == "high")
        medium = sum(1 for p in proofs if p.confidence_category == "medium")
        low = sum(1 for p in proofs if p.confidence_category == "low")
        lean_verified = sum(1 for p in proofs if p.lean_verified)
        lean_partial = sum(1 for p in proofs if p.lean_partial)
        flagged = len(self.flagged_proofs())

        by_type = {}
        by_apparatus = {}
        for p in proofs:
            by_type[p.formalisation_type] = by_type.get(p.formalisation_type, 0) + 1
            for a in p.mathematical_apparatus:
                by_apparatus[a] = by_apparatus.get(a, 0) + 1

        return {
            "total_proofs": total,
            "high_confidence": high,
            "medium_confidence": medium,
            "low_confidence": low,
            "lean_verified": lean_verified,
            "lean_partial": lean_partial,
            "flagged_for_review": flagged,
            "by_formalisation_type": by_type,
            "by_apparatus": sorted(by_apparatus.items(), key=lambda x: -x[1]),
            "new_mathematics_needed": sum(1 for p in proofs if not p.within_standard_mathematics),
        }
