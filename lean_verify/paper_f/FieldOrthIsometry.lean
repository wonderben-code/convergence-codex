import FieldReflectionCount

/-!
# Every orthogonal matrix commuting with the propagator is a symmetry, not only the reflections

`FieldHouseholder.reflIsometry` packages a **symmetric matrix squaring to `1`** as a linear
isometry, and every symmetry this chain has produced since is one of those. **The hypothesis is
stronger than the packaging needs.** What makes `mv M` an isometry is `Mᵀ M = 1` — orthogonality —
and a symmetric involution is the special case `Mᵀ = M`.

`PROOF_STRATEGY` §7 rule 3, and the hypothesis removed is *symmetric and involutive*, down to
*orthogonal*.

**This is the packaging the outstanding case needs.** Three files now name the same obstruction —
the rotations inside a degenerate eigenspace of `green` — and a rotation is orthogonal and **not**
symmetric, so `reflIsometry` could not have carried one whatever eigenspace was supplied. That is a
second reason the rotations were out of reach, independent of the eigenvector question, and it is
removed here.

## What is proved

**`inner_mv_transpose`** — `⟪Mx, y⟫ = ⟪x, Mᵀy⟫`, the adjoint identity with no hypothesis on `M`.
`FieldCommutant.inner_mv_comm` is its symmetric case and stays as written (`ERRATUM 337`).

**`orthIsometry`** — an orthogonal matrix as a `LinearIsometryEquiv`, with inverse `mv Mᵀ`. The norm
comes from `⟪Mx, Mx⟫ = ⟪x, MᵀMx⟫ = ⟪x, x⟫`; the inverse needs `M Mᵀ = 1`, which
`mul_eq_one_comm` supplies from `Mᵀ M = 1` because the matrix is finite and square.

**`orthIsometry_apply`**, and **`reflIsometry_eq_orthIsometry`** — the previous packaging is this
one at a symmetric involution, so the generalisation **covers** it rather than sitting beside it.

**`gaussianField_map_orthIsometry`** — **an orthogonal matrix commuting with `green` gives a
symmetry of the Gaussian field**, through `FieldCommutant.gaussianField_map_of_commutes`.

## What is NOT here

**No rotation is built.** This removes the *packaging* obstruction and no other. Building a rotation
inside a degenerate eigenspace still needs two orthogonal eigenvectors at one eigenvalue, and
**nothing in this estate produces a pair** ⚠ *— true when written; the next unit,*
`FieldComponentEigen`, *exhibits one on any disconnected graph, and the sentence is kept per*
`ERRATUM 94` — — `FieldReflectionCount`'s argument is explicitly blind
inside a single eigenspace, and the torus's eigenvectors are the complex characters. **Not
attempted, no cost claimed** (`ERRATUM 246`). **This file does not claim the rotations are now
easy**; it claims one of the two reasons they were impossible is gone.

**No description of the commutant.** The set of orthogonal matrices commuting with `green` is still
not characterised, and this file adds no member of it.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldOrthIsometry

open Matrix GraphLaplacian FieldIsometryInvariance FieldCommutant FieldHouseholder
open RayleighMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The adjoint identity, with no hypothesis -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **`⟪Mx, y⟫ = ⟪x, Mᵀy⟫`.** `FieldCommutant.inner_mv_comm` is the symmetric case. -/
theorem inner_mv_transpose (M : Matrix V V ℝ) (x y : EuclideanSpace ℝ V) :
    inner ℝ (mv M x) y = inner ℝ x (mv Mᵀ y) := by
  rw [inner_expand, inner_expand]
  simp only [mv_row, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [Matrix.transpose_apply]; ring

/-! ## 2. An orthogonal matrix is an isometry -/

/-- **AN ORTHOGONAL MATRIX AS A LINEAR ISOMETRY OF `EuclideanSpace`.** -/
noncomputable def orthIsometry {M : Matrix V V ℝ} (h : Mᵀ * M = 1) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V where
  toFun := mv M
  invFun := mv Mᵀ
  left_inv x := by rw [← mv_mul, h, mv_one]
  right_inv x := by rw [← mv_mul, mul_eq_one_comm.mp h, mv_one]
  map_add' := mv_add (A := M)
  map_smul' c x := mv_smul (A := M) c x
  norm_map' x := by
    have hinner : inner ℝ (mv M x) (mv M x) = inner ℝ x x := by
      rw [inner_mv_transpose, ← mv_mul, h, mv_one]
    have h1 : ‖mv M x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact hinner
    have := abs_eq_abs.mpr (Or.inl (by
      nlinarith [h1, norm_nonneg (mv M x), norm_nonneg x] : ‖mv M x‖ = ‖x‖))
    simpa using this

@[simp] theorem orthIsometry_apply {M : Matrix V V ℝ} (h : Mᵀ * M = 1) (x : EuclideanSpace ℝ V) :
    orthIsometry h x = mv M x := rfl

/-- A symmetric involution is orthogonal. -/
theorem transpose_mul_self_of_symm {M : Matrix V V ℝ} (hsymm : M.IsSymm) (hinv : M * M = 1) :
    Mᵀ * M = 1 := by rw [hsymm]; exact hinv

/-- **THE PREVIOUS PACKAGING IS THIS ONE AT A SYMMETRIC INVOLUTION**, so the generalisation covers
it rather than sitting beside it. -/
theorem reflIsometry_eq_orthIsometry {M : Matrix V V ℝ} (hsymm : M.IsSymm) (hinv : M * M = 1) :
    reflIsometry hsymm hinv = orthIsometry (transpose_mul_self_of_symm hsymm hinv) :=
  LinearIsometryEquiv.ext fun x => by
    rw [reflIsometry_apply, orthIsometry_apply]

/-! ## 3. And if it commutes with the propagator it is a symmetry of the field -/

/-- **AN ORTHOGONAL MATRIX COMMUTING WITH THE PROPAGATOR IS A SYMMETRY OF THE GAUSSIAN FIELD.** -/
theorem gaussianField_map_orthIsometry (hm : m ≠ 0) {M : Matrix V V ℝ} (h : Mᵀ * M = 1)
    (hcomm : M * green G m = green G m * M) :
    MeasureTheory.Measure.map (orthIsometry h) (gaussianField G m) = gaussianField G m := by
  refine gaussianField_map_of_commutes hm fun x => ?_
  rw [orthIsometry_apply, orthIsometry_apply, ← mv_mul, ← mv_mul, hcomm]

end FieldOrthIsometry
