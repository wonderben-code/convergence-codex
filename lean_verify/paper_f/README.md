# Paper F — Lean Proofs

Machine-verified proofs for the **Paper F Mathematical Programme**.

**Roadmap:** `docs/PAPER_F_ROADMAP.md`
**Builds on:** Papers D + E (206 theorems, `lean_verify/*.lean`)
**Goal:** Systematic closure of all tractable open problems in the GToE.

## File Naming Convention

Files are named `F{tier}_{number}_{short_name}.lean` matching the roadmap items.

| File | Roadmap Item | Status |
|------|-------------|--------|
| `F1_6_PatiSalamForced.lean` | F1.6 — Pati-Salam uniquely forced | Active |

## Relationship to Paper E Proofs

Paper E proofs live in `lean_verify/*.lean` (flat). Paper F proofs live here
in `lean_verify/paper_f/` and BUILD ON the Paper E results. They import from
the parent directory where needed.

The key distinction:
- **Paper E** proved that the cascade PRODUCES Pati-Salam (existence)
- **Paper F** proves that the cascade UNIQUELY FORCES Pati-Salam (no alternatives)

## Dependencies

Same toolchain as Paper E: Lean 4.29.1 + Mathlib v4.29.1.
