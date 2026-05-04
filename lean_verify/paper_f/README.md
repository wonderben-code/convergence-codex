# Paper F — Lean Proofs

Machine-verified proofs for the **Paper F Mathematical Programme**.

**Roadmap:** `docs/PAPER_F_ROADMAP.md`
**Builds on:** Papers D + E (206 theorems, `lean_verify/*.lean`)
**Goal:** Systematic closure of all tractable open problems in the GToE.

## File Naming Convention

Files are named `F{tier}_{number}_{short_name}.lean` matching the roadmap items.

| File | Roadmap Item | Theorems | Status |
|------|-------------|----------|--------|
| `F1_6_PatiSalamForced.lean` | F1.6 — Pati-Salam uniquely forced | 20 | PROVEN |
| `F2_3_ChiralityForced.lean` | F2.3 — Chirality forced (why left-handed) | 20 | PROVEN |
| `F3_2_HiggsForced.lean` | F3.2 — Higgs mechanism forced by cascade | 32 | PROVEN |
| `F3_1_ThreeGenerations.lean` | F3.1 — Three generations forced (quaternionic structure) | 27 | PROVEN |
| `F3_1b_ModuleSpectral.lean` | F3.1b — Module-level, spectral, and completeness strengthening | 26 | PROVEN |
| `F1_7_SpacetimeForced.lean` | F1.7 — 4D Lorentzian spacetime forced by cascade | 24 | PROVEN |
| `F1_7b_SpacetimeUnconditional.lean` | F1.7b — Unconditional signature, convergence, unification, invariance | 19 | PROVEN |
| `F1_7c_SpacetimeFinalClosure.lean` | F1.7c — Final closure: Re(q²) canonicity, VEV construction, D₂ forced | 18 | PROVEN |
| `F3_8a_QuantumGravityFoundations.lean` | F3.8a — Quantum gravity foundations: C*-algebra, observables, spectral triple | 18 | PROVEN |
| `F3_8e_GravitonFromFluctuations.lean` | F3.8e — Graviton from D-fluctuations: all forces from one mechanism | 14 | PROVEN |
| `F3_8b_SpectralActionComputation.lean` | F3.8b — Spectral action coefficients: G, g², sin²θ_W from cascade | 18 | PROVEN |
| `F3_8c_NewtonsConstant.lean` | F3.8c — Newton's constant: RG running, Λ_PS, G, proton decay | 17 | PROVEN |
| `F3_8d_CosmologicalConstant.lean` | F3.8d — Cosmological constant: multi-lineage vacuum energy, 10¹²⁰→10¹¹⁰ | 15 | PROVEN |
| `F3_8d_ii_SSBVacuumShifts.lean` | F3.8d-ii — CC Layer 2: symmetry breaking vacuum shifts, series well-ordered | 16 | PROVEN |

## Relationship to Paper E Proofs

Paper E proofs live in `lean_verify/*.lean` (flat). Paper F proofs live here
in `lean_verify/paper_f/` and BUILD ON the Paper E results. They import from
the parent directory where needed.

The key distinction:
- **Paper E** proved that the cascade PRODUCES Pati-Salam (existence)
- **Paper F** proves that the cascade UNIQUELY FORCES Pati-Salam (no alternatives)

## Dependencies

Same toolchain as Paper E: Lean 4.29.1 + Mathlib v4.29.1.
