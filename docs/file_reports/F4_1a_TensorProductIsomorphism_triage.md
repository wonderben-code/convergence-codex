# TRIAGE: F4_1a_TensorProductIsomorphism.lean

**Grade distribution:** 7A, 0B, 0C, 3D (10 declarations total)
**Assessment:** Core file — genuine cascade algebra. 70% Grade A.

## Grade A (keep as-is)
- `cascadeTensorIso` — M₂⊗M₂ ≃ₐ M₄ via kroneckerAlgEquiv + reindexAlgEquiv
- `cascadeStepIso` — General Mₙ⊗Mₘ ≃ₐ M_{nm} (parametric)
- `cascadeD1toD2` — M₂⊗M₂ ≃ₐ M₄ (instance)
- `cascadeD2toD3` — M₄⊗M₄ ≃ₐ M₁₆ (instance)
- `cascadeTensorIso_preserves_one` — φ(1)=1 via map_one
- `cascadeTensorIso_preserves_mul` — φ(xy)=φ(x)φ(y) via map_mul
- `cascadeTensorIso_bijective` — Bijective via .bijective

## Grade D (remove or relabel)
- `fin_prod_card` — card(Fin2×Fin2)=card(Fin4), just 2×2=4
- `cascade_target_dims` — 2×2=4 ∧ 4×4=16, pure arithmetic
- `cascade_dimensions` — 2×2=4 ∧ 4×4=16 ∧ 16×16=256, pure arithmetic

## Action: FAST TRACK — Remove 3 arithmetic theorems, file is certified.
