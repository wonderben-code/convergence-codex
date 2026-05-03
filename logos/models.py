"""Core data models for Logos AI."""

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


class FormalisationType(str, Enum):
    """What kind of formal treatment a convergence needs."""
    ISOMORPHISM = "isomorphism"           # Two structures proven equivalent
    EQUIVALENCE = "equivalence"           # Weaker structural correspondence (functor, etc.)
    CATEGORICAL = "categorical"           # Abstract characterisation via universals
    AXIOMATIC = "axiomatic"               # Set of axioms characterising a structure
    CONSTRAINT_LOGIC = "constraint_logic" # Structure defined by constraints
    CUSTOM = "custom"                     # None of the above; novel approach needed


class VerificationStatus(str, Enum):
    """How mechanically verified the proof is."""
    MACHINE_VERIFIED = "machine_verified"
    PARTIALLY_VERIFIED = "partially_verified"
    NATURAL_LANGUAGE_ONLY = "natural_language_only"
    UNVERIFIED = "unverified"


class VerificationTier(str, Enum):
    """Tiered formalisation level — every proof gets the highest achievable tier.

    Not all-or-nothing. A proof that can't get Lean verification still gets
    the highest tier it CAN achieve. Nothing gets "nothing."
    """
    PROVEN = "proven"                            # Lean 0 sorrys — fully machine-verified
    PROOF_WITH_GAPS = "proof_with_gaps"          # Lean type-checks but has sorry gaps
    FORMALLY_VERIFIED = "formally_verified"      # Z3 or SymPy verified the formal structure
    NUMERICALLY_CONFIRMED = "numerically_confirmed"  # Numerical tests all pass
    RIGOROUS_ARGUMENT = "rigorous_argument"      # Structured NL proof with explicit steps
    CONJECTURE = "conjecture"                    # Stated but no proof generated

    @classmethod
    def from_proof(cls, proof: ProofRecord) -> VerificationTier:
        """Determine the highest tier achieved by this proof."""
        if proof.lean_verified:
            return cls.PROVEN
        if proof.lean_partial:
            return cls.PROOF_WITH_GAPS
        if proof.z3_verified or proof.sympy_verified:
            return cls.FORMALLY_VERIFIED
        if proof.numerical_consistent and proof.numerical_result.get("applicable"):
            return cls.NUMERICALLY_CONFIRMED
        if proof.proof_natural or proof.proof_steps:
            return cls.RIGOROUS_ARGUMENT
        return cls.CONJECTURE


class ProofConfidence(str, Enum):
    """Calibrated confidence in the proof."""
    HIGH = "high"          # >= 0.75
    MEDIUM = "medium"      # 0.45-0.74
    LOW = "low"            # < 0.45

    @classmethod
    def from_score(cls, score: float) -> ProofConfidence:
        if score >= 0.75:
            return cls.HIGH
        elif score >= 0.45:
            return cls.MEDIUM
        return cls.LOW


class ReviewPriority(str, Enum):
    """Priority for human review."""
    CRITICAL = "critical"       # Must review before use
    RECOMMENDED = "recommended" # Should review
    OPTIONAL = "optional"       # Review if time permits


@dataclass
class ProofStep:
    """A single step in a formal proof."""
    step_number: int
    statement: str
    justification: str
    dependencies: list[str] = field(default_factory=list)  # Previous step numbers or literature refs


@dataclass
class LiteratureDependency:
    """A reference to established mathematical results."""
    name: str
    authors: str = ""
    year: str = ""
    field: str = ""
    statement: str = ""
    usage: str = ""  # How it's used in this proof


@dataclass
class ValidationScores:
    """Scores from the 5-layer validation pipeline."""
    mechanical: float = 0.0       # Lean verification
    adversarial: float = 0.0      # Survived adversarial attack
    internal: float = 0.0         # Internal consistency
    cross_proof: float = 0.0      # Consistent with proof corpus
    calibration: float = 0.0      # Meta-calibration

    def compute_confidence(self) -> float:
        """Weighted aggregate confidence."""
        return (
            self.mechanical * 0.30
            + self.adversarial * 0.25
            + self.internal * 0.20
            + self.cross_proof * 0.15
            + self.calibration * 0.10
        )


@dataclass
class ProofRecord:
    """Complete proof record — the primary output of Logos."""

    # Identity
    id: str = field(default_factory=_uid)
    convergence_id: str = ""
    timestamp: str = field(default_factory=_now)

    # What's being proved
    proposition: str = ""             # Formal statement
    proposition_natural: str = ""     # Natural language statement

    # How it's being proved
    formalisation_type: str = ""      # FormalisationType value
    mathematical_apparatus: list[str] = field(default_factory=list)
    apparatus_justification: str = ""

    # The proof
    proof_natural: str = ""           # Natural-language formal proof (journal quality)
    proof_lean: str = ""              # Lean 4 code (empty if not applicable)
    proof_steps: list[dict] = field(default_factory=list)

    # Dependencies
    dependencies_literature: list[dict] = field(default_factory=list)
    dependencies_logos: list[str] = field(default_factory=list)
    assumptions: list[str] = field(default_factory=list)

    # Validation — Lean
    lean_verified: bool = False
    lean_partial: bool = False
    lean_failure_reason: str = ""

    # Validation — Z3 SMT solver
    z3_verified: bool = False
    z3_result: dict = field(default_factory=dict)

    # Validation — SymPy algebraic
    sympy_verified: bool = False
    sympy_result: dict = field(default_factory=dict)

    # Validation — Numerical sanity
    numerical_consistent: bool = False
    numerical_result: dict = field(default_factory=dict)

    # Multi-tool consensus
    multi_tool_consensus: dict = field(default_factory=dict)

    # Adversarial & consistency
    adversarial_result: dict = field(default_factory=dict)
    internal_consistency: dict = field(default_factory=dict)
    cross_proof_consistency: dict = field(default_factory=dict)

    # Confidence
    confidence_score: float = 0.0
    confidence_category: str = "low"
    confidence_breakdown: dict = field(default_factory=dict)
    validation_scores: dict = field(default_factory=dict)

    # Epistemic transparency
    verification_status: str = "natural_language_only"
    verification_tier: str = "rigorous_argument"  # VerificationTier value
    verification_tier_reason: str = ""  # Why this tier and not higher
    within_standard_mathematics: bool = True
    new_mathematics_needed: str = ""
    limitations: list[str] = field(default_factory=list)

    # Back-translation alignment (proposition ↔ convergence claim)
    back_translation_alignment: dict = field(default_factory=dict)

    # Coverage metrics
    coverage_percentage: float = 0.0  # % of proof steps machine-verified
    coverage_detail: dict = field(default_factory=dict)

    # Provenance
    source_convergence: dict = field(default_factory=dict)
    run_metadata: dict = field(default_factory=dict)

    def get_validation_scores(self) -> ValidationScores:
        return ValidationScores(**self.validation_scores) if self.validation_scores else ValidationScores()

    def get_steps(self) -> list[ProofStep]:
        return [ProofStep(**s) for s in self.proof_steps]

    def get_literature(self) -> list[LiteratureDependency]:
        return [LiteratureDependency(**d) for d in self.dependencies_literature]


@dataclass
class LogRecord:
    """Decision log for a proof — captures all reasoning."""

    proof_id: str = ""
    timestamp: str = field(default_factory=_now)
    decisions: list[dict] = field(default_factory=list)
    # Each decision: {step, choice, alternatives_considered, reasoning}

    def add_decision(self, step: str, choice: str, alternatives: list[str], reasoning: str):
        self.decisions.append({
            "step": step,
            "choice": choice,
            "alternatives_considered": alternatives,
            "reasoning": reasoning,
        })


@dataclass
class FlagRecord:
    """Human review flags for a proof."""

    proof_id: str = ""
    requires_human_review: bool = False
    review_reasons: list[str] = field(default_factory=list)
    review_priority: str = "optional"  # ReviewPriority value
    suggested_expertise: list[str] = field(default_factory=list)

    def flag(self, reason: str, priority: str = "recommended", expertise: list[str] | None = None):
        self.requires_human_review = True
        self.review_reasons.append(reason)
        # Upgrade priority if new flag is more urgent
        priority_order = {"critical": 3, "recommended": 2, "optional": 1}
        if priority_order.get(priority, 0) > priority_order.get(self.review_priority, 0):
            self.review_priority = priority
        if expertise:
            self.suggested_expertise.extend(e for e in expertise if e not in self.suggested_expertise)


@dataclass
class LogosRun:
    """A complete Logos formalisation run."""

    id: str = field(default_factory=lambda: f"logos_{_uid()}")
    started_at: str = field(default_factory=_now)
    completed_at: str = ""
    proofs_attempted: int = 0
    proofs_completed: int = 0
    proofs_high_confidence: int = 0
    proofs_medium_confidence: int = 0
    proofs_low_confidence: int = 0
    proofs_lean_verified: int = 0
    proofs_flagged: int = 0
    total_api_calls: int = 0
    total_cost_usd: float = 0.0
    proof_ids: list[str] = field(default_factory=list)

    def complete(self):
        self.completed_at = _now()
