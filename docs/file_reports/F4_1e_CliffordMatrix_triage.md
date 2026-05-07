# TRIAGE: F4_1e_CliffordMatrix.lean

**Grade distribution:** 35A, 0B, 0C, 3D (38 declarations)
**Assessment:** OUTSTANDING — 92% Grade A. Best file in the corpus.

## Grade A (genuine — 35 declarations)
- Q₄ quadratic form definition via CliffordAlgebraQuaternion.Q.prod
- γ₁-γ₄ explicit gamma matrix definitions
- γ₁_sq through γ₄_sq — squaring relations (ext + fin_cases + simp)
- All 6 anticommutation relations γᵢγⱼ + γⱼγᵢ = 0
- clifford4Map linear map + clifford4Map_sq (Clifford squaring identity!)
- clifford4ToMatrix — CliffordAlgebra.lift Q₄ (canonical Clifford representation)
- clifford4ToMatrix_ι, _one, _mul — functorial properties
- Module.Finite/Free instances for Cl₂ algebras
- clifford2_finrank = 4 via QuaternionAlgebra.finrank_eq_four
- **clifford4_finrank = 16** via prodEquiv + tensor product (HARD, genuine)
- matrix4_finrank = 16 via Module.finrank_matrix
- clifford4_matrix4_finrank_eq — dimension matching
- All 5 basis element mappings (ι_e₁ through ι_e₁_mul_e₂)

## Grade D (arithmetic — 3)
- clifford_dim_formula — 2^4=16
- cascade_D2_dim — 4*4=16
- spacetime_algebra_dim — 2^4=4*4

## Action: FAST TRACK — Remove 3 arithmetic theorems. File is 100% Grade A.
This is the crown jewel of the corpus.
