# Version History — Gnosis AI & Logos AI

This document tracks the evolution of each AI system in the Convergence Codex
pipeline. Important for open-source users and for understanding which version
produced which results.

---

## Gnosis AI — Knowledge Discovery

### v1 (Stage A — 2 May 2026)
**What it did:** Surveyed 81 fields of science, extracted established results,
found structural convergences between domains, iterated through meta-convergence
cascade to terminal fixed points.

**Architecture:**
- Claude Opus for deep survey, Claude Sonnet for fast extraction
- CI (Convergence Intelligence) + EA (Epistemic Assurance) dual-engine
- Combinatorial pairwise comparison across domain pairs
- 4-level cascade: convergences → meta-convergences → fixed points

**Results:**
- 266 convergences discovered
- 26 meta-findings
- 4 terminal fixed points
- Cost: $28.99 (Claude API)

**Limitations:**
- Knowledge verification relied on Claude's parametric knowledge only
- No external database checks on surveyed results
- No formal criteria for convergence quality
- Structural conclusions unverified against source literature

### v2 (2 May 2026)
**Improvements over v1:**
- Enriched convergence data (mathematical structures, proposed equivalence,
  formalisability hints, EA scores embedded in convergence records)
- Cross-category and within-category pair tracking
- Negative convergence detection
- Better cascade structure with grouping strategies

### v3 (3 May 2026)
**Improvements over v2:**
- **5-checkpoint external verification**: Every surveyed result checked against
  Semantic Scholar, CrossRef, OpenAlex, arXiv, and Wikipedia. Results that
  cannot be verified externally are culled from the pipeline.
- **Structural fidelity checking**: Claude's interpretation of each result is
  compared against the actual paper abstract fetched from external databases.
  Catches misinterpretation of building blocks.
- **Convergence quality criteria**: 5 formal checks for each convergence
  (formal definitions, concrete mapping, structure preservation, non-triviality,
  prediction generation). Scores quality — does NOT filter. Novel discoveries
  are the point.
- **Counterexample testing**: Generates computational tests for convergence
  claims using NumPy/SymPy. Surviving tests raises confidence; failing them
  lowers it (but does not filter).
- **MaxPlanAPI**: Drop-in replacement for Claude API using Claude Code CLI.
  All runs $0 with Max subscription.

**Key principle:** Quality at every step + transparency, NOT filtering.
Novel discoveries get scored honestly — nothing thrown away because it's
hard to verify.

---

## Logos AI — Mathematical Formalisation

### v1 (Stage A — 2 May 2026)
**What it did:** Took 266 convergences from Gnosis, produced 256 formal
mathematical proofs with Lean 4 code generation.

**Architecture:**
- 3-stage formalisation: detect type → select apparatus → generate proof
- Lean 4 bridge: feasibility assessment → code generation → type-checking
- 5-layer adversarial validation (mechanical, adversarial, internal,
  cross-proof, calibration)

**Results:**
- 256 proofs generated
- Lean code generated for most proofs (with sorry gaps)
- 5-layer validation scores for each proof

**Limitations:**
- Lean-only mechanical verification (most proofs had sorry gaps)
- No alternative verification tools (Z3, SymPy, Numerical)
- No back-translation check (could prove the wrong thing)
- All-or-nothing: proofs either got Lean verified or "natural language only"
- No sorry elimination (sorry gaps stayed)

### v2 (3 May 2026)
**Improvements over v1:**
- **Multi-tool verification**: Lean 4 + Z3 SMT solver + SymPy + NumPy/SciPy.
  Consensus scoring across all 4 tools (Lean 40%, Z3 25%, SymPy 20%,
  Numerical 15%).
- **6-tier formalisation**: Every proof gets the HIGHEST achievable level.
  Not all-or-nothing. Tiers: PROVEN → PROOF_WITH_GAPS → FORMALLY_VERIFIED →
  NUMERICALLY_CONFIRMED → RIGOROUS_ARGUMENT → CONJECTURE.
- **Back-translation alignment**: Translates formal proposition back to natural
  language and compares with original convergence claim. Catches "proved the
  wrong thing" failures.
- **Sorry elimination loop**: Iteratively fills Lean sorry gaps ($0 via Max Plan).
  Pushes proofs from PROOF_WITH_GAPS toward PROVEN.
- **Coverage metrics**: Tracks exactly which proof steps are machine-verified
  by which tools. Reports combined unique coverage percentage.
- **Lean auto-detection**: Finds Lean at ~/.elan/bin/lean automatically.
- **MaxPlanAPI**: All verification runs $0.

---

## Pipeline Notes

### Stage A Papers (8 Capstone Papers, published May 2026)
These papers were produced using **Gnosis v1** convergences and **Logos v1**
proofs. They represent the initial Stage A output. The convergences and
formalisations in these papers have NOT been verified with the v3/v2
upgrades (external knowledge verification, multi-tool formalisation,
structural fidelity checks).

A verification upgrade pass of the existing 256 proofs through Logos v2
is planned to upgrade formalisations where possible.

### Open Source
- Gnosis AI: `wonderben-code/gnosis-ai` (MIT license)
- Convergence Codex: `wonderben-code/convergence-codex` (MIT license)
- All data Bitcoin-timestamped via git commits

### Cost
- Stage A (v1): $28.99 (Claude API)
- v2/v3 upgrades: $0 (Max Plan via Claude Code CLI)
- Future runs: $0 (Max Plan)

---

## Tool Versions

| Tool | Version | Purpose |
|------|---------|---------|
| Claude Opus | 4.6 | Deep reasoning (proofs, analysis) |
| Claude Sonnet | 4.6 | Fast operations (survey, extraction) |
| Lean 4 | 4.29.1 | Interactive theorem proving |
| Z3 | 4.16.0 | Automated SMT solving |
| SymPy | 1.14.0 | Symbolic algebra verification |
| NumPy | 2.4.3 | Numerical computation |
| SciPy | 1.17.1 | Scientific computation |
