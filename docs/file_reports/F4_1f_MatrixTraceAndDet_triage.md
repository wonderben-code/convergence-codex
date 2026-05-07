# TRIAGE: F4_1f_MatrixTraceAndDet.lean

**Grade distribution:** 15A, 0B, 2C, 3D (20 declarations total)
**Assessment:** Strong file — 75% Grade A using real Mathlib trace/det.

## Grade A (keep as-is) — 15 theorems
- trace_identity, trace_I2, trace_I4 — Tr(I)=n via Mathlib
- trace_additive, trace_commutative, trace_commutator_zero — Linearity/cyclicity
- trace_cyclic — 3-matrix cyclicity via trace_mul_cycle
- trace_scalar — Tr(cA)=c·Tr(A)
- det_identity, det_multiplicative, det_transpose_eq — det properties
- trace_zero_matrix — Tr(0)=0
- det_power — det(A^k)=(det A)^k
- spectral_dimension_from_trace — Tr(I₄)=4
- spectral_action_algebraic_foundations — Master conjunction (all genuine)

## Grade C (arithmetic proxy)
- `normalised_trace_identity` — 4/4=1 (should use actual trace)
- `reality_j_squared` — (-1)²=1 (should construct matrix J)

## Grade D (tautological)
- `gauge_measure_invariance` — 1*1=1
- `first_order_finite_check` — 16*16=256
- `grading_squared` — 1²=1

## Action: FAST TRACK — Remove/relabel 5 arithmetic theorems. File is 100% Grade A with 15 genuine theorems.
