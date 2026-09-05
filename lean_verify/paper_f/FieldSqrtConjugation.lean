import FieldLinearSymmetry
import FieldSimpleCriterion

/-!
# Conjugating by the propagator's square root, and a symmetry that is NOT an isometry

`FieldLinearSymmetry` removed the isometry hypothesis from the characterisation and then declined,
**twice under review**, to claim that the isometries are a *proper* subgroup of the linear
symmetries: the expected witness `C^{1/2} O C^{-1/2}` needs a square root that file never
constructs, and it exhibited no non-isometric symmetry. **This constructs the square root, builds
the witness, and lands it on a named graph.**

## What is proved

**`sqGreen`, `sqGreen_mul_self`, `sqGreen_transpose`, `sqGreen_det_isUnit`** — the positive square
root of `green` from Mathlib's continuous functional calculus, squaring back to `green`, symmetric,
and invertible because its determinant squares to `green`'s.

**`conjSq`, `conjSq_mul_green_mul_transpose`** — **conjugation `O ↦ C^{1/2} O C^{-1/2}` carries an
orthogonal matrix to a matrix satisfying `L C Lᵀ = C`**, which is the condition
`FieldLinearSymmetry.gaussianField_map_iff_quadForm` characterises. **So the linear symmetry group
contains a copy of the orthogonal group**, indexed by `O`.

**`quadForm_of_mul_green_mul_transpose`** — and `L C Lᵀ = C` **is** that condition, written for a
matrix and its transpose rather than a continuous linear map and its adjoint. The connection is a
theorem here rather than a step left to the reader (`ERRATUM 456`).

**`eq_one_iff_comm`** — **the conjugate is an isometry exactly when `O` commutes with `green`.**

**`rotMatrix_not_comm`** — and a quarter turn between eigenvectors at **distinct** eigenvalues does
not commute: it sends `u` to `v`, so the two sides of the commutator send `u` to `μ₁ • v` and
`μ₂ • v`. **`FieldRotation.rotMatrix` supplies the turn** — the matrix built on 5 September to prove
symmetries exist is reused here to prove one *fails* to be a symmetry of the wrong kind.

**`exists_nonIsometric`** — **so wherever `green` has two orthogonal eigenvectors of equal non-zero
length at distinct eigenvalues, there is a linear symmetry that is not an isometry.**

**`exists_nonIsometric_line`** — **and the line of `k+1 ≥ 2` sites is such a graph.** Its spectrum
is simple (`FieldSimpleCriterion.eigenvalues_injective_line`), so two eigenbasis vectors sit at
distinct eigenvalues, and an orthonormal basis supplies the orthogonality and the equal lengths for
free.

**WHAT THIS SETTLES.** `FieldLineCount.card_symmetries` says the field on a line has exactly
`2^(k+1)` **isometric** symmetries. It is now proved that the **linear** symmetries are strictly
more numerous, so that count is a count of a **proper** subgroup — which `FieldLinearSymmetry`
expected and declined to assert.

## What is NOT here

**NO COUNT OR STRUCTURE FOR THE LINEAR GROUP.** One non-isometric element is exhibited; the group is
neither counted nor identified with the orthogonal group, and **`conjSq` is not shown injective or
surjective onto the linear symmetries** — both are true by the standard argument and **neither is
proved**. Not attempted, no cost claimed (`ERRATUM 246`).
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`):
`FieldLinearClassified.conjSq_bijOn` proves both, and `gaussianField_map_iff_conjSq` is the
two-sided classification — a matrix's induced map preserves the Gaussian field **iff** the matrix
is `C^{1/2} O C^{-1/2}` for an orthogonal `O`. **The fence was right that they are short.**

**NOTHING ABOUT NON-LINEAR MAPS.** The full automorphism group of the measure is still untouched.

**NOTHING ABOUT `d ≥ 2`.** `exists_nonIsometric` applies wherever its hypotheses hold, and the only
graph on which they are **discharged** here is the line. On a box or torus in higher dimension the
eigenvectors at distinct eigenvalues are there, and **that composition is not made.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A larger
symmetry group in finite volume is a wider shadow of an axiom, not a smaller gap in it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by `sqGreen_mul_self`,
`sqGreen_det_isUnit`, `sqGreen_mul_inv`, `inv_mul_sqGreen`, `conjSq_mul_green_mul_transpose`,
`conjSq_transpose_mul_self`, `eq_one_iff_comm`, `exists_nonIsometric` and
`exists_nonIsometric_line`; it is **not** taken by `sqGreen`, `sqGreen_transpose`,
`inv_sqGreen_transpose`, `conjSq`, `conjSq_transpose`, `quadForm_of_mul_green_mul_transpose` or
`rotMatrix_not_comm` — **three of which shed it during the unit**, when the linter reported it
unused and the honest response was to delete it rather than to underscore it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSqrtConjugation

open Matrix GraphLaplacian
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The square root of the propagator -/

/-- The positive square root of `green`, from Mathlib's continuous functional calculus. -/
noncomputable def sqGreen (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Matrix V V ℝ :=
  CFC.sqrt (green G m)

theorem sqGreen_mul_self (hm : m ≠ 0) : sqGreen G m * sqGreen G m = green G m :=
  CFC.sqrt_mul_sqrt_self _ (green_posDef G hm).posSemidef.nonneg

theorem sqGreen_transpose : (sqGreen G m)ᵀ = sqGreen G m := by
  have h := (CFC.sqrt_nonneg (green G m)).isSelfAdjoint
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

theorem sqGreen_det_isUnit (hm : m ≠ 0) : IsUnit (sqGreen G m).det := by
  have h : (sqGreen G m).det * (sqGreen G m).det = (green G m).det := by
    rw [← Matrix.det_mul, sqGreen_mul_self hm]
  have hg : (green G m).det ≠ 0 := ((green_posDef G hm).det_pos).ne'
  refine isUnit_iff_ne_zero.mpr fun hz => hg ?_
  rw [← h, hz, mul_zero]

theorem sqGreen_mul_inv (hm : m ≠ 0) : sqGreen G m * (sqGreen G m)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (sqGreen_det_isUnit hm)

theorem inv_mul_sqGreen (hm : m ≠ 0) : (sqGreen G m)⁻¹ * sqGreen G m = 1 :=
  Matrix.nonsing_inv_mul _ (sqGreen_det_isUnit hm)

theorem inv_sqGreen_transpose : ((sqGreen G m)⁻¹)ᵀ = (sqGreen G m)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, sqGreen_transpose]

/-! ## 2. Conjugation sends orthogonal matrices to linear symmetries -/

/-- `O ↦ C^{1/2} O C^{-1/2}`. -/
noncomputable def conjSq (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    (O : Matrix V V ℝ) : Matrix V V ℝ :=
  sqGreen G m * O * (sqGreen G m)⁻¹

theorem conjSq_transpose (O : Matrix V V ℝ) :
    (conjSq G m O)ᵀ = (sqGreen G m)⁻¹ * Oᵀ * sqGreen G m := by
  rw [conjSq, Matrix.transpose_mul, Matrix.transpose_mul, inv_sqGreen_transpose,
    sqGreen_transpose, Matrix.mul_assoc]

/-- **CONJUGATION BY THE SQUARE ROOT CARRIES AN ORTHOGONAL MATRIX TO A LINEAR SYMMETRY**: it
preserves the propagator's form, which is `FieldLinearSymmetry`'s condition. -/
theorem conjSq_mul_green_mul_transpose (hm : m ≠ 0) {O : Matrix V V ℝ} (hO : Oᵀ * O = 1) :
    conjSq G m O * green G m * (conjSq G m O)ᵀ = green G m := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  rw [conjSq_transpose, conjSq, ← sqGreen_mul_self hm]
  calc sqGreen G m * O * (sqGreen G m)⁻¹ * (sqGreen G m * sqGreen G m)
        * ((sqGreen G m)⁻¹ * Oᵀ * sqGreen G m)
      = sqGreen G m * O * ((sqGreen G m)⁻¹ * sqGreen G m)
        * (sqGreen G m * (sqGreen G m)⁻¹) * Oᵀ * sqGreen G m := by
        simp only [Matrix.mul_assoc]
    _ = sqGreen G m * (O * Oᵀ) * sqGreen G m := by
        rw [inv_mul_sqGreen hm, sqGreen_mul_inv hm]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = sqGreen G m * sqGreen G m := by rw [hOO, Matrix.mul_one]

/-! ## 3. It is an isometry exactly when `O` commutes with the propagator -/

theorem conjSq_transpose_mul_self (hm : m ≠ 0) (O : Matrix V V ℝ) :
    (conjSq G m O)ᵀ * conjSq G m O
      = (sqGreen G m)⁻¹ * (Oᵀ * green G m * O) * (sqGreen G m)⁻¹ := by
  rw [conjSq_transpose, conjSq, ← sqGreen_mul_self hm]
  simp only [Matrix.mul_assoc]

theorem eq_one_iff_comm (hm : m ≠ 0) {O : Matrix V V ℝ} (hO : Oᵀ * O = 1) :
    (conjSq G m O)ᵀ * conjSq G m O = 1 ↔ O * green G m = green G m * O := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  rw [conjSq_transpose_mul_self hm]
  constructor
  · intro h
    have h2 : Oᵀ * green G m * O = green G m := by
      have := congrArg (fun M => sqGreen G m * M * sqGreen G m) h
      simp only [Matrix.mul_assoc, Matrix.mul_one] at this
      rw [inv_mul_sqGreen hm] at this
      simp only [← Matrix.mul_assoc, sqGreen_mul_inv hm, Matrix.one_mul] at this
      rw [sqGreen_mul_self hm] at this
      simpa [Matrix.mul_assoc] using this
    have := congrArg (fun M => O * M) h2
    simp only [← Matrix.mul_assoc, hOO, Matrix.one_mul] at this
    exact this.symm
  · intro h
    have h2 : Oᵀ * green G m * O = green G m := by
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, hO, Matrix.one_mul]
    rw [h2, ← sqGreen_mul_self hm, ← Matrix.mul_assoc, Matrix.mul_assoc _ (sqGreen G m),
      sqGreen_mul_inv hm, Matrix.mul_one, inv_mul_sqGreen hm]

/-! ## 4. A quarter turn between eigenvectors at DIFFERENT eigenvalues does not commute -/

theorem rotMatrix_not_comm {u v : V → ℝ} {n μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvu : v ⬝ᵥ u = 0) (hv0 : v ≠ 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    FieldRotation.rotMatrix u v n 0 1 * green G m
      ≠ green G m * FieldRotation.rotMatrix u v n 0 1 := by
  intro hcomm
  have hru : FieldRotation.rotMatrix u v n 0 1 *ᵥ u = v := by
    rw [FieldRotation.rotMatrix_mulVec_left hn huu hvu]
    simp
  have h1 : (FieldRotation.rotMatrix u v n 0 1 * green G m) *ᵥ u = μ₁ • v := by
    rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hru]
  have h2 : (green G m * FieldRotation.rotMatrix u v n 0 1) *ᵥ u = μ₂ • v := by
    rw [← Matrix.mulVec_mulVec, hru, hv]
  rw [hcomm, h2] at h1
  exact hne (smul_left_injective ℝ hv0 h1.symm)

/-! ## 5. So there is a linear symmetry that is not an isometry -/

/-- **A LINEAR SYMMETRY OF THE PROPAGATOR'S FORM THAT IS NOT AN ISOMETRY**, wherever the propagator
has two orthogonal eigenvectors of equal non-zero length at **distinct** eigenvalues. -/
theorem exists_nonIsometric (hm : m ≠ 0) {u v : V → ℝ} {n μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) (hv0 : v ≠ 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    ∃ L : Matrix V V ℝ, L * green G m * Lᵀ = green G m ∧ Lᵀ * L ≠ 1 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hO : (FieldRotation.rotMatrix u v n 0 1)ᵀ * FieldRotation.rotMatrix u v n 0 1 = 1 :=
    FieldRotation.rotMatrix_transpose_mul_self hn huu hvv huv (by norm_num)
  refine ⟨conjSq G m (FieldRotation.rotMatrix u v n 0 1),
    conjSq_mul_green_mul_transpose hm hO, ?_⟩
  exact fun hc => rotMatrix_not_comm hn huu hvu hv0 hu hv hne ((eq_one_iff_comm hm hO).mp hc)

/-! ## 5b. And that matrix condition is `FieldLinearSymmetry`'s condition -/

/-- **`L C Lᵀ = C` IS THE CONDITION `FieldLinearSymmetry.gaussianField_map_iff_quadForm`
CHARACTERISES**, written for a matrix and its transpose rather than for a continuous linear map and
its adjoint.

⚠ **ANNOTATED 2026-09-05** (`ERRATUM 94`). This docstring went on to say *"so a matrix produced
above really is a symmetry of the measure"*, which needed one step nobody had taken: that the
**adjoint** of a matrix is its transpose. `FieldLinearClassified.adjoint_mvCLM` takes it and
`gaussianField_map_conjSq` states the conclusion, so the sentence is now backed. It was an
implication read across a coercion (`ERRATUM 456`'s species) and is recorded rather than deleted. -/
theorem quadForm_of_mul_green_mul_transpose {L : Matrix V V ℝ}
    (h : L * green G m * Lᵀ = green G m) (x : V → ℝ) :
    (Lᵀ *ᵥ x) ⬝ᵥ (green G m *ᵥ (Lᵀ *ᵥ x)) = x ⬝ᵥ (green G m *ᵥ x) := by
  have hadj : ∀ z : V → ℝ, (Lᵀ *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (L *ᵥ z) := by
    intro z
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [Matrix.mulVec_mulVec, hadj, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h]

/-! ## 6. And it happens on a named graph: the line -/

open BoxGraph in
/-- **THE FIELD ON A LINE OF AT LEAST TWO SITES HAS A LINEAR SYMMETRY THAT IS NOT AN ISOMETRY.**
The line's spectrum is simple (`FieldSimpleCriterion.eigenvalues_injective_line`), so two
eigenbasis vectors sit at **distinct** eigenvalues, and they are orthonormal by construction. -/
theorem exists_nonIsometric_line {k : ℕ} (hk : 1 ≤ k) {mass : ℝ} (hmass : mass ≠ 0) :
    ∃ L : Matrix (Site 1 (k + 1)) (Site 1 (k + 1)) ℝ,
      L * green (boxGraph 1 (k + 1)) mass * Lᵀ = green (boxGraph 1 (k + 1)) mass ∧
        Lᵀ * L ≠ 1 := by
  classical
  set hH := (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian with hHdef
  set b := hH.eigenvectorBasis with hb
  set i : Site 1 (k + 1) := fun _ => ⟨0, by omega⟩ with hi
  set j : Site 1 (k + 1) := fun _ => ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    exact absurd (congrArg Fin.val this) (by simp [hi, hj])
  have hne : hH.eigenvalues i ≠ hH.eigenvalues j := fun h =>
    hij (FieldSimpleCriterion.eigenvalues_injective_line hmass hH h)
  have hinner : ∀ x y : EuclideanSpace ℝ (Site 1 (k + 1)),
      (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) = inner ℝ x y := by
    intro x y
    rw [RayleighMatrix.inner_expand]
    rfl
  have hii : (WithLp.ofLp (b i)) ⬝ᵥ (WithLp.ofLp (b i)) = 1 := by
    rw [hinner, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hjj : (WithLp.ofLp (b j)) ⬝ᵥ (WithLp.ofLp (b j)) = 1 := by
    rw [hinner, real_inner_self_eq_norm_sq, b.orthonormal.1 j]
    norm_num
  have hijz : (WithLp.ofLp (b i)) ⬝ᵥ (WithLp.ofLp (b j)) = 0 := by
    rw [hinner]; exact b.orthonormal.2 hij
  have hj0 : (WithLp.ofLp (b j) : Site 1 (k + 1) → ℝ) ≠ 0 := by
    intro hz
    rw [hz] at hjj
    simp at hjj
  exact exists_nonIsometric hmass one_ne_zero hii hjj hijz hj0
    (hH.mulVec_eigenvectorBasis i) (hH.mulVec_eigenvectorBasis j) hne

end FieldSqrtConjugation
