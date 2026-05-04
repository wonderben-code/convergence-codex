# Paper F — Lean Proofs

Machine-verified proofs for the **Paper F Mathematical Programme**.

**Roadmap:** `docs/PAPER_F_ROADMAP.md`
**Builds on:** Papers D + E (206 theorems, `lean_verify/*.lean`)
**Goal:** Systematic closure of all tractable open problems in the GToE.

## File Naming Convention

Files are named `F{tier}_{number}_{short_name}.lean` matching the roadmap items.

| File | Roadmap Item | Theorems | Status |
|------|-------------|----------|--------|
| `F1_6_PatiSalamForced.lean` | F1.6 — Pati-Salam uniquely forced | 27 | PROVEN |
| `F2_3_ChiralityForced.lean` | F2.3 — Chirality forced (why left-handed) | 24 | PROVEN |
| `F3_2_HiggsForced.lean` | F3.2 — Higgs mechanism forced by cascade | 32 | PROVEN |
| `F3_1_ThreeGenerations.lean` | F3.1 — Three generations forced (quaternionic structure) | 27 | PROVEN |
| `F3_1b_ModuleSpectral.lean` | F3.1b — Module-level, spectral, and completeness strengthening | 22 | PROVEN |

## Relationship to Paper E Proofs

Paper E proofs live in `lean_verify/*.lean` (flat). Paper F proofs live here
in `lean_verify/paper_f/` and BUILD ON the Paper E results. They import from
the parent directory where needed.

The key distinction:
- **Paper E** proved that the cascade PRODUCES Pati-Salam (existence)
- **Paper F** proves that the cascade UNIQUELY FORCES Pati-Salam (no alternatives)

## Dependencies

Same toolchain as Paper E: Lean 4.29.1 + Mathlib v4.29.1.
