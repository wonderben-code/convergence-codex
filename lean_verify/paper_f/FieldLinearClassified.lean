import FieldSqrtConjugation

/-!
# The linear symmetries, classified: exactly a conjugate of the orthogonal group

`FieldSqrtConjugation` showed that conjugation by `C^{1/2}` carries every orthogonal matrix to a
matrix with `L C Lᵀ = C`, and fenced the converse: *`conjSq` is not shown injective or surjective
onto the linear symmetries — both true by the standard argument and neither proved.* **Both are
proved here**, and the fence was right that they are short: the inverse of the conjugation is the
conjugation the other way, `O = C^{-1/2} L C^{1/2}`.

**The unit then went further than the fence asked**, because the review found that neither this
chain nor `FieldLinearSymmetry` had ever connected a **matrix** to the measure: that file's
characterisation is stated for continuous linear maps and their adjoints, and nothing said the
adjoint of a matrix is its transpose. **That bridge is built here**, and with polarisation it closes
the classification on both sides.

## What is proved

**`conjSq_injective`** and **`exists_orthogonal_of_symmetry`** — distinct orthogonal matrices give
distinct conjugates, and **every** `L` with `L C Lᵀ = C` is one, namely at `O = C^{-1/2} L C^{1/2}`,
whose orthogonality is the single computation `O Oᵀ = C^{-1/2}(L C Lᵀ)C^{-1/2} = 1`.
**`conjSq_bijOn`** packages them as a `Set.BijOn`.

**`eq_zero_of_quadForm_zero`** — **polarisation**: a symmetric matrix whose quadratic form vanishes
identically is zero, from `Pi.single i 1` and `Pi.single i 1 + Pi.single j 1`.

**`mvCLM`, `adjoint_mvCLM`** — a matrix as a continuous linear map, and **its adjoint is its
transpose**. `FieldOrthIsometry.inner_mv_transpose` had the inner-product identity since 5
September; **nothing had made it an adjoint**, which is what the measure-level statement needs.

**`gaussianField_map_mvCLM_iff`** — so `FieldLinearSymmetry`'s characterisation reads, for a matrix,
in matrix terms; **`gaussianField_map_conjSq`** — every conjugated orthogonal matrix really does
preserve the measure; **`mul_green_mul_transpose_of_map`** — and conversely, by polarisation.

**`gaussianField_map_iff_conjSq`** — **the classification, two-sided: a matrix's induced map
preserves the Gaussian field IF AND ONLY IF the matrix is `C^{1/2} O C^{-1/2}` for an orthogonal
`O`.** On every finite graph, at every `m ≠ 0`. Nothing about the graph enters; what makes it true
is that `green` is positive definite.

## What is NOT here

**THE CLASSIFICATION IS OF MATRICES.** That every continuous linear map on `EuclideanSpace ℝ V` is
`mvCLM L` for some `L` is standard — `Matrix.toEuclideanLin` is a `LinearEquiv` and a linear map in
finite dimension is continuous — **and it is not invoked here**, so the statement quantifies over
matrices and not over continuous linear maps. Not attempted, no cost claimed (`ERRATUM 246`).

**NO CARDINALITY, and none is proved.** The bijection is onto the orthogonal matrices, so **any**
statement about how many linear symmetries there are is a statement about `O(V)`, which is Mathlib's
object and not this estate's. **Nothing here counts anything.**

**NO GROUP ISOMORPHISM.** `conjSq_bijOn` is a bijection of **sets**. That it carries matrix
multiplication to matrix multiplication is true and **not proved**, so the word *group* is not used
of the bijection.

**NOTHING ABOUT NON-LINEAR MAPS.** The full automorphism group of the measure is still untouched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. Knowing
the linear symmetries exactly, in finite volume, is a shadow known exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`; the first draft of this paragraph claimed
*every* declaration takes `m ≠ 0`, and seven of the twelve do). It is taken by `conjSq_injective`,
`exists_orthogonal_of_symmetry`, `conjSq_bijOn`, `gaussianField_map_mvCLM_iff`,
`gaussianField_map_conjSq`, `mul_green_mul_transpose_of_map` and `gaussianField_map_iff_conjSq` —
**seven**, each because it uses the invertibility of `C^{1/2}` or the symmetry of `green`. It is
**not** taken by `eq_zero_of_quadForm_zero`, `mvCLM`, `mvCLM_apply`, `adjoint_mvCLM` or
`dotProduct_conj`, which are linear algebra with no graph in them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldLinearClassified

open Matrix GraphLaplacian FieldSqrtConjugation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Injective -/

theorem conjSq_injective (hm : m ≠ 0) : Function.Injective (conjSq G m) := by
  have key : ∀ O : Matrix V V ℝ, (sqGreen G m)⁻¹ * conjSq G m O * sqGreen G m = O := by
    intro O
    rw [conjSq]
    calc (sqGreen G m)⁻¹ * (sqGreen G m * O * (sqGreen G m)⁻¹) * sqGreen G m
        = ((sqGreen G m)⁻¹ * sqGreen G m) * O * ((sqGreen G m)⁻¹ * sqGreen G m) := by
          simp only [Matrix.mul_assoc]
      _ = O := by rw [inv_mul_sqGreen hm, Matrix.one_mul, Matrix.mul_one]
  intro O₁ O₂ h
  rw [← key O₁, ← key O₂, h]

/-! ## 2. Surjective onto the linear symmetries -/

/-- **EVERY LINEAR SYMMETRY IS A CONJUGATED ORTHOGONAL MATRIX**, and the orthogonal matrix is
`C^{-1/2} L C^{1/2}`. -/
theorem exists_orthogonal_of_symmetry (hm : m ≠ 0) {L : Matrix V V ℝ}
    (hL : L * green G m * Lᵀ = green G m) :
    ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ conjSq G m O = L := by
  refine ⟨(sqGreen G m)⁻¹ * L * sqGreen G m, ?_, ?_⟩
  · refine mul_eq_one_comm.mp ?_
    have ht : ((sqGreen G m)⁻¹ * L * sqGreen G m)ᵀ
        = sqGreen G m * Lᵀ * (sqGreen G m)⁻¹ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, sqGreen_transpose,
        inv_sqGreen_transpose, Matrix.mul_assoc]
    rw [ht]
    calc (sqGreen G m)⁻¹ * L * sqGreen G m * (sqGreen G m * Lᵀ * (sqGreen G m)⁻¹)
        = (sqGreen G m)⁻¹ * (L * (sqGreen G m * sqGreen G m) * Lᵀ) * (sqGreen G m)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (sqGreen G m)⁻¹ * (sqGreen G m * sqGreen G m) * (sqGreen G m)⁻¹ := by
          rw [sqGreen_mul_self hm, hL]
      _ = 1 := by
          rw [← Matrix.mul_assoc, inv_mul_sqGreen hm, Matrix.one_mul, sqGreen_mul_inv hm]
  · rw [conjSq]
    calc sqGreen G m * ((sqGreen G m)⁻¹ * L * sqGreen G m) * (sqGreen G m)⁻¹
        = (sqGreen G m * (sqGreen G m)⁻¹) * L * (sqGreen G m * (sqGreen G m)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = L := by rw [sqGreen_mul_inv hm, Matrix.one_mul, Matrix.mul_one]

/-! ## 3. So the conjugation is a bijection -/

/-- **THE LINEAR SYMMETRY GROUP OF THE GAUSSIAN FIELD IS EXACTLY `C^{1/2} O(V) C^{-1/2}`.** -/
theorem conjSq_bijOn (hm : m ≠ 0) :
    Set.BijOn (conjSq G m) {O : Matrix V V ℝ | Oᵀ * O = 1}
      {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m} := by
  refine ⟨fun O hO => conjSq_mul_green_mul_transpose hm hO,
    fun O₁ _ O₂ _ h => conjSq_injective hm h, fun L hL => ?_⟩
  obtain ⟨O, hO, hOL⟩ := exists_orthogonal_of_symmetry hm hL
  exact ⟨O, hO, hOL⟩

/-! ## 3b. Polarisation: a symmetric matrix with vanishing quadratic form is zero -/

omit [DecidableEq V] in
theorem eq_zero_of_quadForm_zero {M : Matrix V V ℝ} (hsymm : Mᵀ = M)
    (h : ∀ x : V → ℝ, x ⬝ᵥ (M *ᵥ x) = 0) : M = 0 := by
  classical
  have hji : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hsymm j) i
    simpa [Matrix.transpose_apply] using this.symm
  have hd : ∀ k, M k k = 0 := fun k => by simpa using h (Pi.single k 1)
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [mulVec_add, mulVec_single, MulOpposite.op_one, one_smul, dotProduct_add,
    add_dotProduct, single_dotProduct, col_apply, hd, mul_zero, one_mul, zero_add,
    add_zero] at hij
  simp only [Matrix.zero_apply]
  linarith [hji i j]

/-! ## 4. The bridge to the measure: a matrix as a continuous linear map -/

/-- A matrix as a continuous linear map on `EuclideanSpace`. -/
noncomputable def mvCLM (M : Matrix V V ℝ) : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

@[simp] theorem mvCLM_apply (M : Matrix V V ℝ) (x : EuclideanSpace ℝ V) :
    mvCLM M x = RayleighMatrix.mv M x := rfl

/-- **THE ADJOINT OF A MATRIX IS ITS TRANSPOSE**, which is what the measure-level statement needs
and what no file of this chain had written down. -/
theorem adjoint_mvCLM (M : Matrix V V ℝ) :
    ContinuousLinearMap.adjoint (mvCLM M) = mvCLM Mᵀ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [mvCLM_apply, mvCLM_apply, FieldOrthIsometry.inner_mv_transpose,
    Matrix.transpose_transpose]

/-- **SO THE MATRIX CONDITION IS THE MEASURE CONDITION.** -/
theorem gaussianField_map_mvCLM_iff (hm : m ≠ 0) (L : Matrix V V ℝ) :
    MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m ↔
      ∀ x : EuclideanSpace ℝ V,
        (WithLp.ofLp (RayleighMatrix.mv Lᵀ x)) ⬝ᵥ
            (green G m *ᵥ (WithLp.ofLp (RayleighMatrix.mv Lᵀ x)))
          = (WithLp.ofLp x) ⬝ᵥ (green G m *ᵥ (WithLp.ofLp x)) := by
  rw [FieldLinearSymmetry.gaussianField_map_iff_quadForm hm]
  simp only [adjoint_mvCLM, mvCLM_apply]

/-- **AND EVERY CONJUGATED ORTHOGONAL MATRIX IS A SYMMETRY OF THE MEASURE.** -/
theorem gaussianField_map_conjSq (hm : m ≠ 0) {O : Matrix V V ℝ} (hO : Oᵀ * O = 1) :
    MeasureTheory.Measure.map (mvCLM (conjSq G m O)) (gaussianField G m) = gaussianField G m := by
  rw [gaussianField_map_mvCLM_iff hm]
  intro x
  exact FieldSqrtConjugation.quadForm_of_mul_green_mul_transpose
    (conjSq_mul_green_mul_transpose hm hO) (WithLp.ofLp x)

/-! ## 5. The converse, and the classification closes -/

omit [DecidableEq V] in
theorem dotProduct_conj (L A : Matrix V V ℝ) (x : V → ℝ) :
    (Lᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Lᵀ *ᵥ x)) = x ⬝ᵥ ((L * A * Lᵀ) *ᵥ x) := by
  rw [Matrix.mulVec_mulVec]
  have hstep : (Lᵀ *ᵥ x) ⬝ᵥ ((A * Lᵀ) *ᵥ x) = x ⬝ᵥ (L *ᵥ ((A * Lᵀ) *ᵥ x)) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hstep, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]

/-- **A MATRIX WHOSE INDUCED MAP PRESERVES THE GAUSSIAN FIELD SATISFIES `L C Lᵀ = C`**, by
polarisation. This is the direction that makes the classification two-sided. -/
theorem mul_green_mul_transpose_of_map (hm : m ≠ 0) {L : Matrix V V ℝ}
    (hL : MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m) :
    L * green G m * Lᵀ = green G m := by
  have hq := (gaussianField_map_mvCLM_iff hm L).mp hL
  have hsymm : (L * green G m * Lᵀ - green G m)ᵀ = L * green G m * Lᵀ - green G m := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, green_isSymm G hm, Matrix.mul_assoc]
  refine sub_eq_zero.mp (eq_zero_of_quadForm_zero hsymm fun x => ?_)
  rw [Matrix.sub_mulVec, dotProduct_sub, ← dotProduct_conj]
  simpa [RayleighMatrix.mv, Matrix.mulVec_mulVec] using sub_eq_zero.mpr (hq (WithLp.toLp 2 x))

/-- **THE CLASSIFICATION, TWO-SIDED: the matrices whose induced map preserves the Gaussian field
are exactly the conjugates `C^{1/2} O C^{-1/2}` of the orthogonal matrices.** -/
theorem gaussianField_map_iff_conjSq (hm : m ≠ 0) (L : Matrix V V ℝ) :
    MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m ↔
      ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ conjSq G m O = L := by
  refine ⟨fun hL => exists_orthogonal_of_symmetry hm (mul_green_mul_transpose_of_map hm hL), ?_⟩
  rintro ⟨O, hO, rfl⟩
  exact gaussianField_map_conjSq hm hO

end FieldLinearClassified
