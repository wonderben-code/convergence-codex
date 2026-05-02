# Logos AI — Technical Architecture Plan

**Created:** 2 May 2026
**Status:** Architecture sprint — this document resolves all design problems before any code is written.
**Repo:** `wonderben-code/convergence-codex` (lives in `logos/` directory)

Logos is the formalisation stage of the Convergence Codex pipeline. It takes structured discoveries from Gnosis (or any equivalent source) and produces formal mathematical proofs with verification status, adversarial validation, and confidence scoring.

---

## 1. Architecture Overview

```
logos/
├── __init__.py
├── config.py           # Logos configuration (API, paths, limits)
├── api.py              # Claude API wrapper (mirrors gnosis-ai pattern)
├── models.py           # Data models: ProofRecord, LogRecord, FlagRecord
├── formaliser.py        # Core: auto-detect type → select apparatus → produce proof
├── lean_bridge.py       # Lean 4 code generation + verification bridge
├── validator.py         # 5-layer adversarial validation pipeline
├── store.py            # JSON file persistence for proofs
├── cli.py              # Click CLI
└── prompts/
    ├── detect_type.py    # Formalisation type detection prompts
    ├── select_apparatus.py # Mathematical apparatus selection prompts
    ├── prove.py          # Proof generation prompts
    ├── lean_gen.py       # Lean 4 code generation prompts
    └── adversarial.py    # Adversarial validation prompts
```

### Data Flow

```
Input: Convergence JSON (from Gnosis or standard format)
  │
  ├── 1. Type Detection → isomorphism | equivalence | categorical | axiomatic | constraint-logic | custom
  │
  ├── 2. Apparatus Selection → category theory | type theory | topology | measure theory | ...
  │
  ├── 3. Proof Generation → natural-language formal proof (journal-quality)
  │
  ├── 4. Lean Bridge → Lean 4 + Mathlib code (where feasible)
  │
  ├── 5. Validation Pipeline:
  │      a. Lean type-check (mechanical verification)
  │      b. Adversarial scan (antagonistic frontier LLM)
  │      c. Internal consistency (proves what it claims, all assumptions listed)
  │      d. Cross-proof consistency (no contradictions with other Logos proofs)
  │      e. Confidence calibration
  │
  └── Output: ProofRecord JSON + LogRecord + FlagRecord
```

---

## 2. Data Models

### ProofRecord (Logos output per convergence)

```python
@dataclass
class ProofRecord:
    id: str                          # Unique proof ID
    convergence_id: str              # Source convergence from Gnosis
    timestamp: str

    # What's being proved
    proposition: str                 # Formal statement
    proposition_natural: str         # Natural language statement

    # How it's being proved
    formalisation_type: str          # "isomorphism" | "equivalence" | "categorical" | "axiomatic" | "constraint_logic" | "custom"
    mathematical_apparatus: list[str] # ["category theory", "topology", ...]
    apparatus_justification: str     # Why this apparatus was chosen

    # The proof itself
    proof_natural: str               # Natural-language formal proof (journal quality)
    proof_lean: str                  # Lean 4 code (empty string if not applicable)
    proof_steps: list[dict]          # Step-by-step with justifications

    # Dependencies
    dependencies_literature: list[dict]   # Established results cited
    dependencies_logos: list[str]         # Other Logos proof IDs
    assumptions: list[str]                # Explicit assumptions

    # Validation
    lean_verified: bool              # Lean type-check passed
    lean_partial: bool               # Some Lean verified, some not
    lean_failure_reason: str         # Why Lean failed (if applicable)
    adversarial_result: dict         # Adversarial scan output
    internal_consistency: dict       # Internal checks output
    cross_proof_consistency: dict    # Cross-proof checks output

    # Confidence
    confidence_score: float          # 0.0-1.0
    confidence_category: str         # "high" | "medium" | "low"
    confidence_breakdown: dict       # Per-layer scores

    # Epistemic transparency
    verification_status: str         # "machine_verified" | "partially_verified" | "natural_language_only"
    within_standard_mathematics: bool
    new_mathematics_needed: str      # Empty if standard; description if new maths needed
    limitations: list[str]           # Explicit limitations

    # Provenance
    source_convergence: dict         # Full source convergence data
    run_metadata: dict               # Model, temperature, timestamp, etc.
```

### LogRecord

```python
@dataclass
class LogRecord:
    proof_id: str
    decisions: list[dict]            # Each decision: {step, choice, alternatives, reasoning}
    # Captures: why this type, why this apparatus, why this structure,
    # what adversarial found, what limitations exist
```

### FlagRecord

```python
@dataclass
class FlagRecord:
    proof_id: str
    requires_human_review: bool
    review_reasons: list[str]
    review_priority: str            # "critical" | "recommended" | "optional"
    suggested_expertise: list[str]  # What kind of expert should review
```

---

## 3. Design Problem #1: Formalisation Type Detection

### The Problem
Different convergences need different kinds of formal treatment. An isomorphism between groups is different from a categorical characterisation of a fixed point.

### Detection Taxonomy

| Type | When | Example | Difficulty |
|------|------|---------|-----------|
| `isomorphism` | Two structures proven equivalent | Group ↔ Ring iso | Phase 1a |
| `equivalence` | Weaker structural correspondence | Functor, natural transformation | Phase 1a |
| `categorical` | Abstract characterisation via universals | Terminal object, adjunction | Phase 1b |
| `axiomatic` | Set of axioms characterising a structure | ZFC-style axiomatisation | Phase 1b |
| `constraint_logic` | Structure defined by constraints | Fixed point as constraint satisfaction | Phase 1b |
| `custom` | None of the above; needs novel approach | Genuinely new territory | Phase 1c |

### Detection Prompt Strategy

Single API call with the full convergence record. The model classifies AND explains why.

---

## 4. Design Problem #2: Lean 4 Integration

### Reality Check

Lean 4 + Mathlib is powerful but limited. Many cross-domain structural claims won't have the prerequisite definitions in Mathlib. The honest approach:

1. **Check Mathlib coverage** — does the required apparatus exist?
2. **If yes** — generate Lean code, attempt verification
3. **If partial** — generate what's possible, flag gaps
4. **If no** — produce natural-language proof only, explain what Mathlib would need

### Lean Bridge Design

```python
class LeanBridge:
    def can_formalise(self, apparatus: list[str], claim_type: str) -> dict:
        """Check whether Lean/Mathlib can handle this proof."""
        # Returns: {feasible: bool, partial: bool, missing: [...], available: [...]}

    def generate_lean(self, proposition: str, apparatus: list[str],
                     proof_sketch: str) -> str:
        """Generate Lean 4 code for the proof."""
        # Uses Claude to generate Lean code informed by the natural-language proof

    def verify_lean(self, lean_code: str) -> dict:
        """Type-check Lean code (requires lean4 binary on PATH)."""
        # Returns: {verified: bool, errors: [...], warnings: [...]}
```

### Lean Availability

Logos works WITHOUT Lean installed:
- If `lean` binary exists on PATH → full verification
- If not → generates Lean code but marks as "unverified (Lean not available)"
- Never BLOCKS on Lean; it's an additional validation layer

---

## 5. Design Problem #3: Adversarial Validation Pipeline

### 5 Layers

```python
class ProofValidator:
    def validate(self, proof: ProofRecord) -> ValidationResult:
        scores = {}

        # Layer 1: Mechanical (Lean)
        scores["mechanical"] = self._verify_lean(proof)

        # Layer 2: Adversarial (frontier LLM as antagonist)
        scores["adversarial"] = self._adversarial_scan(proof)

        # Layer 3: Internal consistency
        scores["internal"] = self._check_internal(proof)

        # Layer 4: Cross-proof consistency
        scores["cross_proof"] = self._check_cross_proof(proof)

        # Layer 5: Confidence calibration
        scores["calibration"] = self._calibrate_confidence(scores)

        return ValidationResult(scores=scores, overall=self._aggregate(scores))
```

### Layer 2 (Adversarial) — The Most Important

Uses Opus as an antagonistic reviewer. The prompt:
1. Present the proposition and proof
2. Instruct: "Your job is to BREAK this proof. Find gaps, unjustified steps, hidden assumptions, circular reasoning, over-generalisation."
3. Score: proof_soundness (0-1), gap_count, severity_of_gaps
4. The adversarial output either triggers corrections or becomes flagged limitations

### Layer 4 (Cross-Proof) — Corpus-Level

Checks against all existing Logos proofs:
- Does this proof contradict any existing proof?
- Does it depend on assumptions that conflict with other proofs?
- If it proves A ≅ B and another proof proves B ≇ C, does that create issues?

---

## 6. Confidence Calibration

### Scoring Formula

```python
confidence = (
    mechanical_score * 0.30     # Lean verification (strongest signal)
    + adversarial_score * 0.25  # Survived adversarial attack
    + internal_score * 0.20     # Internally consistent
    + cross_proof_score * 0.15  # Consistent with corpus
    + calibration_score * 0.10  # Meta-calibration
)
```

### Categories

| Category | Score | Meaning |
|----------|-------|---------|
| `high` | >= 0.75 | Machine-verified or robust natural-language proof |
| `medium` | 0.45-0.74 | Natural-language proof, minor concerns |
| `low` | < 0.45 | Significant gaps, exploratory, or ambitious |

### Honest Flagging

If confidence < 0.45, the proof is automatically flagged for human review. If `within_standard_mathematics` is False, flagged regardless of confidence.

---

## 7. Strategic Priorities (Build Order)

### Phase 1: Core Pipeline (~800 lines)
- `models.py` — all data models
- `config.py` — configuration
- `api.py` — Claude API wrapper
- `store.py` — JSON persistence
- `formaliser.py` — type detection + apparatus selection + proof generation
- `prompts/` — all prompt templates

### Phase 2: Validation Pipeline (~400 lines)
- `validator.py` — 5-layer validation
- Adversarial prompts
- Internal consistency checks
- Cross-proof checks
- Confidence calibration

### Phase 3: Lean Bridge (~200 lines)
- `lean_bridge.py` — Lean code generation + verification
- Mathlib coverage checking
- Graceful degradation when Lean unavailable

### Phase 4: CLI + Integration (~300 lines)
- `cli.py` — Click CLI
- Commands: `logos prove`, `logos validate`, `logos batch`, `logos export`
- Integration with Gnosis output format

### Total estimated: ~1,700 lines

---

## 8. CLI Commands

```bash
# Prove a single convergence
logos prove convergence.json --output proof.json

# Prove all convergences in a directory
logos batch /path/to/convergences/ --output-dir proofs/

# Prove only high-formalisability convergences
logos batch /path/to/convergences/ --filter formalisability=high

# Validate an existing proof
logos validate proof.json

# Re-run adversarial validation on all proofs
logos revalidate proofs/

# Export proofs for Synthesis
logos export proofs/ --format synthesis

# Corpus stats
logos stats proofs/
```

---

## 9. Input/Output Format Compatibility

### Input: Gnosis Convergence JSON

Logos reads any JSON file matching the Gnosis Convergence schema. The v2 enriched fields (`mathematical_structures`, `proposed_equivalence`, `formalisability_hint`) are used if present but not required — Logos auto-detects if they're missing.

### Output: ProofRecord JSON

Standard JSON per proof. Synthesis reads these directly.

### Standalone Operation

Logos can run on ANY convergence-shaped JSON, not just Gnosis output. This is a design requirement from the spec.

---

## 10. Verification Checklist

1. Logos takes a Gnosis convergence record → produces ProofRecord
2. Auto-detects formalisation type with logged reasoning
3. Auto-selects mathematical apparatus with logged reasoning
4. Produces natural-language formal proof at journal quality
5. Generates Lean 4 code where feasible
6. 5-layer validation produces calibrated confidence
7. Adversarial scan catches deliberately-flawed test proofs
8. Cross-proof consistency checked against corpus
9. Honest flagging of ambitious cases
10. Works standalone (no Gnosis dependency)
11. `logos prove` CLI command works
12. `logos batch` processes multiple convergences
13. All outputs JSON with full provenance
