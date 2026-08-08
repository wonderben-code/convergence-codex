/-
  LorentzIsometryEquiv.lean — the estate's two descriptions of the
  Lorentz group are the same group.

  WHY THIS EXISTS. `SpinToLorentzMat` built
  `toO13 : minkowskiForm.IsometryEquiv minkowskiForm →* O13` — every
  isometry of the Minkowski form has a Lorentz matrix. That is a map
  INTO `O13` and nothing more: it leaves open whether `O13` is exactly
  the isometry group or merely contains its image. Per PROOF_STRATEGY
  §7.2, a chain reported as "reached B" is still open, and that one
  was.

  This file closes it. The converse is the same polarisation argument
  run backwards through the dot product: `ΛᵀGΛ = G` says precisely that
  `Λ` preserves the bilinear form, hence the quadratic form, hence is
  an isometry.

  WHAT THIS FILE PROVES:
  1. `bil_eq_dotProduct` — the estate's hand-written Minkowski bilinear
     form IS `v ⬝ᵥ G *ᵥ w`. Small, and worth stating: `LorentzGroup`
     defines `bil` entrywise and `gram` as a diagonal matrix, and
     nothing connected them.
  2. **`minkowskiForm_mulVec`** — a Lorentz matrix preserves the
     Minkowski form. This is the converse of
     `SpinToLorentzMat.isLorentzMat_of_isometry`, and it is what the
     "into" map was missing.
  3. **`ofO13`** — hence every element of O(1,3) IS an isometry
     equivalence of `minkowskiForm`.
  4. **`o13MulEquiv : O13 ≃* minkowskiForm.IsometryEquiv minkowskiForm`**
     — the two descriptions are the same group, not merely related by a
     map in one direction.

  WHAT THIS CHANGES ELSEWHERE, and it is less than it sounds. It makes
  `SpinToLorentzMat.toO13` an isomorphism rather than an embedding, so
  `spinToO13` and `lorentzSpinRep` carry exactly the same information.
  It says **nothing** about SO⁺(1,3): `O13` is still the full
  orthogonal group, `gram` is still in it with determinant −1, and the
  proper orthochronous component is still not reached from the spin
  side. W7's step (d) is untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import SpinToLorentzMat

open MinkowskiSignature LorentzGroup
open scoped Matrix

noncomputable section

namespace LorentzIsometryEquiv

/-! ## 1. The bilinear form is the Gram matrix -/

theorem bil_eq_dotProduct (v w : Fin 4 → ℝ) : bil v w = v ⬝ᵥ gram *ᵥ w := by
  rw [bil, dotProduct, Fin.sum_univ_four, gram]
  simp only [Matrix.mulVec_diagonal]
  rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
    show mw 3 = -1 from rfl]
  ring

/-! ## 2. A Lorentz matrix is an isometry

The converse of `SpinToLorentzMat.isLorentzMat_of_isometry`: the Gram
identity says exactly that the bilinear form is preserved. -/

theorem bil_mulVec {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzMat M)
    (v w : Fin 4 → ℝ) : bil (M *ᵥ v) (M *ᵥ w) = bil v w := by
  rw [bil_eq_dotProduct, bil_eq_dotProduct, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hM, ← Matrix.dotProduct_mulVec]

/-- **A Lorentz matrix preserves the Minkowski form.** -/
theorem minkowskiForm_mulVec {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzMat M)
    (v : Fin 4 → ℝ) : minkowskiForm (M *ᵥ v) = minkowskiForm v := by
  rw [← bil_self, ← bil_self]
  exact bil_mulVec hM v v

/-! ## 3. Every element of O(1,3) is an isometry equivalence -/

/-- The linear equivalence attached to an element of GL₄(ℝ). -/
def linOfGL (M : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (M : Matrix (Fin 4) (Fin 4) ℝ))
    (Matrix.mulVecLin ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ))
    (by
      refine LinearMap.ext fun v => ?_
      change (M : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ _ *ᵥ v = v
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec])
    (by
      refine LinearMap.ext fun v => ?_
      change _ *ᵥ (M : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ v = v
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec])

@[simp] theorem linOfGL_apply (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)
    (v : Fin 4 → ℝ) : linOfGL M v = (M : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ v := rfl

/-- **Every element of O(1,3) is an isometry of the Minkowski form.** -/
def ofO13 (M : O13) : minkowskiForm.IsometryEquiv minkowskiForm where
  __ := linOfGL (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)
  map_app' v := minkowskiForm_mulVec M.2 v

@[simp] theorem ofO13_apply (M : O13) (v : Fin 4 → ℝ) :
    ofO13 M v = ((M : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) *ᵥ v := rfl

/-! ## 4. The two descriptions are the same group -/

/-- **O(1,3), as a matrix group, IS the isometry group of the Minkowski
    form.** `SpinToLorentzMat.toO13` was a map into `O13`; this says it
    is onto, so the two descriptions carry the same information. -/
def o13MulEquiv : O13 ≃* minkowskiForm.IsometryEquiv minkowskiForm where
  toFun := ofO13
  invFun := SpinToLorentzMat.toO13
  left_inv M := by
    refine Subtype.ext (Units.ext ?_)
    rw [SpinToLorentzMat.toO13_coe]
    refine Matrix.ext fun i j => ?_
    rw [LinearMap.toMatrix'_apply]
    change (((M : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single]
    simp
  right_inv g := by
    refine DFunLike.ext _ _ fun v => ?_
    change LinearMap.toMatrix' g.toLinearEquiv.toLinearMap *ᵥ v = g v
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  map_mul' M N := by
    refine DFunLike.ext _ _ fun v => ?_
    rw [QuadraticMap.IsometryEquiv.mul_apply, ofO13_apply, ofO13_apply, ofO13_apply,
      Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

/-- Restated as the sentence it is: the estate's two Lorentz groups are
    isomorphic. -/
theorem o13_isometryEquiv_group :
    Nonempty (O13 ≃* minkowskiForm.IsometryEquiv minkowskiForm) :=
  ⟨o13MulEquiv⟩

/-- And therefore `toO13` is surjective — the fact the "into" map was
    missing. -/
theorem toO13_surjective : Function.Surjective SpinToLorentzMat.toO13 :=
  fun M => ⟨ofO13 M, o13MulEquiv.left_inv M⟩

theorem toO13_injective : Function.Injective SpinToLorentzMat.toO13 :=
  o13MulEquiv.symm.injective

/-! ## 5. O(1,3) is still not SO⁺(1,3)

Review round 21's fold. The header says this isomorphism changes
nothing about properness; here is the witness rather than the
assurance. -/

/-- The Gram matrix as an explicit ELEMENT of the subgroup `O13` — it is
    its own inverse, so it is a unit without any invertibility
    argument. -/
def gramO13 : O13 :=
  ⟨⟨gram, gram, gram_mul_gram, gram_mul_gram⟩,
    (SpinToLorentzMat.gram_isLorentzMat_det_neg).1⟩

/-- **And its determinant is −1.** So `O13` genuinely contains improper
    elements, `O13 ≃* minkowskiForm.IsometryEquiv minkowskiForm` says
    nothing whatever about SO⁺(1,3), and neither does anything reached
    through it from the spin side. -/
theorem det_gramO13 :
    ((gramO13 : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ).det = -1 := det_gram

end LorentzIsometryEquiv
