"""Core data models for Synthesis AI."""

from __future__ import annotations

import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from typing import Optional


def _uid() -> str:
    return uuid.uuid4().hex[:12]


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


class PaperSection(str, Enum):
    """Standard sections in a Codex paper."""
    ABSTRACT = "abstract"
    INTRODUCTION = "introduction"
    METHODS = "methods"
    RESULTS = "results"
    DISCUSSION = "discussion"
    HONEST_SCOPE = "honest_scope"
    REFERENCES = "references"
    CONCLUSION = "conclusion"


class PaperConfidence(str, Enum):
    """Overall confidence in the generated paper."""
    HIGH = "high"          # All claims well-supported, citations verified
    MEDIUM = "medium"      # Most claims supported, some flagged
    LOW = "low"            # Significant uncertainty, requires heavy review

    @classmethod
    def from_score(cls, score: float) -> PaperConfidence:
        if score >= 0.75:
            return cls.HIGH
        elif score >= 0.45:
            return cls.MEDIUM
        return cls.LOW


@dataclass
class Citation:
    """A citation in a paper."""
    key: str                  # BibTeX key
    authors: str = ""
    title: str = ""
    year: str = ""
    venue: str = ""           # Journal/conference/preprint server
    doi: str = ""
    url: str = ""
    citation_type: str = ""   # "corpus" | "literature" | "methodology"
    verified: bool = False    # Has this citation been verified to exist?


@dataclass
class SectionDraft:
    """A draft of one section of a paper."""
    section: str              # PaperSection value
    title: str = ""
    content: str = ""
    confidence: float = 0.0
    flags: list[str] = field(default_factory=list)  # Things requiring human review
    word_count: int = 0


@dataclass
class PaperDraft:
    """A complete paper draft — the primary output of Synthesis."""

    # Identity
    id: str = field(default_factory=lambda: f"paper_{_uid()}")
    timestamp: str = field(default_factory=_now)

    # Paper metadata
    title: str = ""
    authors: list[str] = field(default_factory=lambda: ["Mark E. Mala"])
    date: str = field(default_factory=lambda: datetime.now(timezone.utc).strftime("%Y-%m-%d"))
    abstract: str = ""
    keywords: list[str] = field(default_factory=list)

    # Content
    sections: list[dict] = field(default_factory=list)  # list of SectionDraft dicts
    full_markdown: str = ""                               # Complete rendered markdown

    # Citations
    citations: list[dict] = field(default_factory=list)   # list of Citation dicts
    corpus_citations: list[str] = field(default_factory=list)  # Codex paper IDs cited

    # Source data
    convergence_ids: list[str] = field(default_factory=list)
    proof_ids: list[str] = field(default_factory=list)
    finding_ids: list[str] = field(default_factory=list)

    # Quality
    confidence_score: float = 0.0
    confidence_category: str = "low"
    total_word_count: int = 0
    flagged_sections: list[str] = field(default_factory=list)

    # Provenance
    source_bundle: dict = field(default_factory=dict)
    generation_log: list[dict] = field(default_factory=list)
    run_metadata: dict = field(default_factory=dict)

    def get_sections(self) -> list[SectionDraft]:
        return [SectionDraft(**s) for s in self.sections]

    def get_citations(self) -> list[Citation]:
        return [Citation(**c) for c in self.citations]


@dataclass
class PaperBundle:
    """Input bundle for Synthesis — discoveries + proofs grouped for one paper."""

    id: str = field(default_factory=_uid)
    convergences: list[dict] = field(default_factory=list)
    proofs: list[dict] = field(default_factory=list)
    findings: list[dict] = field(default_factory=list)
    methodology_context: str = ""
    target_structure: str = ""     # Optional guidance on paper structure
    target_audience: str = ""      # Optional audience guidance
    theme: str = ""                # Optional thematic focus


@dataclass
class BoundaryDecision:
    """Records why convergences were grouped into this paper vs another."""
    bundle_id: str
    convergence_ids: list[str] = field(default_factory=list)
    reasoning: str = ""
    alternative_groupings: list[str] = field(default_factory=list)


@dataclass
class ReviewRequest:
    """Identifies sections requiring human review."""
    paper_id: str = ""
    sections_to_review: list[dict] = field(default_factory=list)
    # Each: {section, reason, priority, suggested_focus}
    citation_concerns: list[str] = field(default_factory=list)
    framing_decisions: list[str] = field(default_factory=list)
    overall_priority: str = "recommended"  # "critical" | "recommended" | "optional"


@dataclass
class SynthesisRun:
    """A complete Synthesis paper generation run."""

    id: str = field(default_factory=lambda: f"synthesis_{_uid()}")
    started_at: str = field(default_factory=_now)
    completed_at: str = ""
    papers_attempted: int = 0
    papers_completed: int = 0
    papers_high_confidence: int = 0
    papers_medium_confidence: int = 0
    papers_low_confidence: int = 0
    total_word_count: int = 0
    total_api_calls: int = 0
    total_cost_usd: float = 0.0
    paper_ids: list[str] = field(default_factory=list)

    def complete(self):
        self.completed_at = _now()


# ─── Capstone Models ───


@dataclass
class CapstoneContext:
    """Complete data census for capstone paper generation.

    Built deterministically from ALL available data — no AI involved.
    This is the foundation that drives which papers get written.
    """

    # Raw data
    convergences: list[dict] = field(default_factory=list)       # All 266
    proofs: list[dict] = field(default_factory=list)              # All 256+ with adversarial data
    findings: list[dict] = field(default_factory=list)            # All 26 meta-findings
    fixed_points: list[dict] = field(default_factory=list)        # Terminal fixed points (level 5)
    synthesis_papers: list[dict] = field(default_factory=list)    # All ~70 paper summaries

    # Pre-computed analytics
    domain_pair_counts: dict = field(default_factory=dict)        # {pair: count}
    recurring_structures: list[dict] = field(default_factory=list)  # Math structures appearing 3+ times
    confidence_distribution: dict = field(default_factory=dict)   # {bucket: count}
    strongest_convergences: list[dict] = field(default_factory=list)  # Top 20 by confidence
    cross_domain_hubs: list[str] = field(default_factory=list)    # Domains with most connections
    cascade_dag: dict = field(default_factory=dict)               # Full reduction graph (level → findings)
    independence_clusters: list[dict] = field(default_factory=list)  # Unrelated domains → same structure

    # Cascade summary
    cascade_levels: dict = field(default_factory=dict)            # {level: [finding_ids]}
    total_convergences: int = 0
    total_proofs: int = 0
    total_findings: int = 0


@dataclass
class CandidateClaim:
    """A candidate claim for a capstone paper — derived from cascade data."""

    id: str = field(default_factory=_uid)
    claim_text: str = ""                         # One sentence
    claim_type: str = ""                         # "fixed_point" | "cascade" | "bridge" | "prediction" | "framework"
    tier: str = ""                               # "anchor" | "bridge" | "framework" | "meta"

    # Data lineage — what drives this claim
    source_finding_id: str = ""                  # The finding this claim is based on (if any)
    source_finding_level: int = 0                # Cascade level of source finding
    coined_term: str = ""                        # The coined term from the finding
    supporting_convergence_ids: list[str] = field(default_factory=list)  # MUST be non-empty
    supporting_finding_ids: list[str] = field(default_factory=list)

    # Strength metrics
    mean_confidence: float = 0.0                 # Average confidence of supporting convergences
    num_source_convergences: int = 0             # How many convergences feed this finding
    independence_score: float = 0.0              # How many UNRELATED domain pairs support this?

    # Falsifiability
    falsification_criterion: str = ""            # What would disprove this?
    existing_crisis: str = ""                    # What open problem does this address?
    predictions: list[str] = field(default_factory=list)  # Specific predictions

    # Scope calibration (Nobel model)
    claim_too_broad: str = ""                    # The over-generalised version that must NOT be claimed
    claim_too_narrow: str = ""                   # The too-weak version that wastes the finding
    mathematical_sketch: str = ""                # What mathematical formulation captures this claim


@dataclass
class PaperPlan:
    """A plan for one capstone paper — what to write and how."""

    id: str = field(default_factory=lambda: f"capstone_{_uid()}")
    tier: str = ""                               # "anchor" | "bridge" | "framework" | "meta"
    title: str = ""
    claim: CandidateClaim | dict = field(default_factory=dict)

    # Content plan
    convergence_ids: list[str] = field(default_factory=list)
    finding_ids: list[str] = field(default_factory=list)
    proof_ids: list[str] = field(default_factory=list)
    existing_crisis: str = ""
    target_length_pages: str = ""                # e.g. "4-8"

    # Status
    status: str = "planned"                      # "planned" | "composed" | "reviewed" | "complete"


@dataclass
class CapstoneRun:
    """Tracks a capstone paper generation run."""

    id: str = field(default_factory=lambda: f"capstone_run_{_uid()}")
    started_at: str = field(default_factory=_now)
    completed_at: str = ""

    # Census
    census_convergences: int = 0
    census_proofs: int = 0
    census_findings: int = 0
    census_fixed_points: int = 0

    # Claims
    candidates_generated: int = 0
    papers_planned: int = 0

    # Papers
    papers_composed: int = 0
    papers_reviewed: int = 0
    papers_completed: int = 0
    total_word_count: int = 0
    paper_ids: list[str] = field(default_factory=list)

    # Predictions
    total_predictions: int = 0

    # Cost
    total_cost_usd: float = 0.0
    total_api_calls: int = 0

    def complete(self):
        self.completed_at = _now()
