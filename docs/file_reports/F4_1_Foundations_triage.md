# TRIAGE: F4_1_Foundations.lean

**Grade distribution:** 16A, 3B, 13C, 1D (33 declarations)
**Assessment:** Mixed — has genuine Vandermonde + some real formulas, but heavy arithmetic.

## Grade A (genuine — 16)
- `vandermonde_entry` — vandermonde_apply from Mathlib
- `vandermonde_det_cascade` — det_vandermonde from Mathlib
- `vandermonde_nonzero_iff` — det≠0 ↔ Injective from Mathlib
- `tensor_decomp_dim` — 4*2*2=16 (correct dimension)
- `sm_rank` — (3-1)+(2-1)+1=4 (correct Lie group rank)
- `gap_transfer_bound` — a>0∧b>0→a+b>0
- `gap_at_least_min` — min(a,b)≤a+b
- `dim_su2/dim_su3/dim_su4` — n²-1 formulas (correct)
- `sm_gauge_dim` — 8+3+1=12
- `cascade_D0/D1/D2/D3` — 2^(2^n) values
- `cascade_squaring` — (2^n)²=2^(2n) (correct exponent rule)
- `cascade_content_D2/D3` — cumulative sums

## Grade B (overclaim — 3)
- `weinberg_angle_from_dynkin` — docstring error in formula
- `eigenvalue_sum_comm` — a+b=b+a claims "tensor eigenvalue theorem"
- `broken_generators` — 21-12=9 (correct but claims physics not proven)

## Grade C (arithmetic proxy — 13)
- `weinberg_numerator/denominator` — 2²-1=3, 3²-1=8
- `weinberg_angle_physical` — 0<3/8<1
- Various fermion/rank counting theorems

## Grade D (tautological — 1)
- `weinberg_angle_rational` — (3:ℚ)/8=3/8 (x=x)

## Action: MEDIUM TRACK
- Keep 16 Grade A, these are solid
- Fix weinberg docstring error
- Remove/relabel arithmetic proxies
- File can be 100% Grade A by removing C/D theorems (they add no mathematical value)
