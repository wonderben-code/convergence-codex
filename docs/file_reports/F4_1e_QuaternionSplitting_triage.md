# TRIAGE: F4_1e_QuaternionSplitting.lean

**Grade distribution:** 7A, 1B, 3C, 4D (14+ declarations)
**Assessment:** Genuine quaternion splitting theorem. 50% Grade A.

## Grade A (keep as-is)
- `quatToMatrix` — AlgHom H[C,1,0,1] →ₐ M₂(ℂ) via basis lift
- `matrixToQuat` — Explicit Pauli decomposition inverse
- `matrixToQuat_quatToMatrix` — Left inverse proof
- `quatToMatrix_matrixToQuat` — Right inverse proof (fin_cases + ring)
- `quatSplitEquiv` — **CORE: H[C,1,0,1] ≃ₐ M₂(ℂ)** via AlgEquiv.ofBijective
- `clifford2Iso` — **Cl₂(C) ≃ₐ M₂(ℂ)** via composition with CliffordAlgebraQuaternion.equiv
- splitQuatBasis (B — needs type review)

## Grade D (trivial functorial properties — remove)
- `quatSplitEquiv_map_one`, `quatSplitEquiv_map_mul`, `quatSplitEquiv_bijective`, `clifford2Iso_map_one`

## Grade C (arithmetic dimension proxies)
- `split_quat_matrix_dim` — 2*2=4
- `clifford2_dim` — 2^2=4
- `clifford4_dim` — 2^4=16 ∧ 16=4*4

## Action: FAST TRACK — Remove trivial functorial + arithmetic. Core quartet (quatSplitEquiv + clifford2Iso) is genuine.
