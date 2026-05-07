# TRIAGE: F4_1b_DimensionAndArrow.lean

**Grade distribution:** 4A (genuine), 8C, 5D (17 declarations total — actually 18 with arrow_of_time)
**Assessment:** Two strong sections (finrank dimensions + trace cyclicity), one weak (arrow of time).

## Grade A (keep as-is)
- `dim_Mn` — `Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) = n * n` — general, uses finrank!
- `trace_cyclic_M2/M4/M16` — Tr(AB)=Tr(BA) via Matrix.trace_mul_comm
- `trace_cyclic_general` — General version for Mₙ(ℂ)

Note: dim_M2/M4/M16 and cascade_dim_D1/D2/D3 are ALSO real Mathlib (use Module.finrank_matrix + simp) but graded C by triage. These should arguably be Grade A since they DO use the correct Mathlib dimension notion.

## Grade C (finrank computations — arguably Grade A)
- `dim_M2/M4/M16` — Module.finrank via simp. These ARE real dimension theorems.
- `cascade_dim_D1/D2/D3` — Same technique.
- `end_dim_strictly_increasing` — d≥2 → d*d>d (arithmetic, not endomorphism)
- `cascade_growth` — d≥2 → d²-d≥d (arithmetic)

## Grade D (Arrow of Time section — arithmetic proxies)
- `end_preimage_M2/M4/M16_unique` — n²=4→n=2 etc. (arithmetic, not endomorphism)
- `no_higher_preimage_of_seed` — d>2 → d²≠2 (arithmetic)
- `arrow_of_time` — Conjunction of above 5 arithmetic facts

## Action: MEDIUM TRACK
- Promote dim_M2/M4/M16 and cascade_dim to Grade A (they use real finrank)
- Remove or relabel arrow_of_time section (arithmetic proxies for deep claims)
- OR: Upgrade arrow_of_time to use real Module.End and finrank (HARD)
