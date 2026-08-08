/-
  SpinToLorentzMat.lean — the spin group lands in O(1,3), the estate's
  own bundled matrix Lorentz group. The two chains stop being adjacent.

  WHERE THIS SITS. `SpinMinkowskiBridge` established that the estate's
  two independent Minkowski developments are about the same quadratic
  form, and produced
  `lorentzSpinRep : spinGroup Q₁₃ →* minkowskiForm.IsometryEquiv
  minkowskiForm`. Its header then said, at length, what was still
  missing: `LorentzGroup` describes O(1,3) as a MATRIX subgroup of
  GL₄(ℝ) with membership `ΛᵀGΛ = G`, and an isometry-equivalence is the
  same group mathematically but a different Lean type. Until the matrix
  passage exists, `spinRep` and `O13` are adjacent, not connected.

  This file builds the passage.

  WHAT THIS FILE PROVES:
  1. **`isLorentzMat_of_isometry`** — for ANY ℝ-linear self-map of ℝ⁴
     preserving `minkowskiForm`, its matrix satisfies `ΛᵀGΛ = G`. The
     estate already had this for the specific map coming from SL₂(ℂ)
     (`LorentzGroup.lorentzMat_gram`); the general statement, which is
     the one a second chain needs, was not there. Polarisation does the
     work: preserving the quadratic form forces the bilinear form, and
     evaluating on `Pi.single` basis vectors turns that into the Gram
     identity entrywise.
  2. **`toO13`** — hence a group homomorphism
     `minkowskiForm.IsometryEquiv minkowskiForm →* O13`. The inverse
     matrix comes from the equivalence, so no invertibility argument is
     needed.
  3. **`spinToO13 : spinGroup Q₁₃ →* LorentzGroup.O13`** — the
     composite. **The Clifford/spin chain and the SL₂(ℂ)/Lorentz chain
     now land in the same object.**
  4. `spinToO13_not_injective`, `spinToO13_R₁₂'_ne_one`, and
     `spinToO13_B_moves_time` — non-injective, non-trivial, and
     containing an element that moves the time axis, all transported to
     the matrix group rather than left behind in the isometry type.

  WHAT IS STILL NOT PROVED, and it is the same gap as before, no
  smaller. O(1,3) is not SO⁺(1,3). Landing in `O13` says nothing about
  `det = 1` or `Λ⁰₀ > 0`, and **`SOplus13` is still not reached**. The
  estate's SL₂(ℂ) chain proves SL₂(ℂ) ↠ SO⁺(1,3); this chain proves
  spin ↪ O(1,3) with a nontrivial kernel. Those are not yet comparable
  statements, and no theorem here relates the two homomorphisms. W7's
  step (d) is unchanged: the image being SO⁺(1,3), surjectivity onto
  it, and the kernel being no larger than ±1 are all open.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import LorentzGroup
import SpinMinkowskiBridge

open MinkowskiSignature LorentzGroup SpinVectorRep SpinToOrthogonal
open SpinMinkowskiBridge CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

namespace SpinToLorentzMat

/-! ## 1. Any isometry of `minkowskiForm` has a Lorentz matrix

`LorentzGroup` proves this for the map coming from an SL₂(ℂ) element.
The general version is what a second chain needs, and it was not
there. -/

/-- Polarisation: preserving the quadratic form forces the bilinear
    form. -/
theorem bil_of_isometry (f : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hf : ∀ v, minkowskiForm (f v) = minkowskiForm v) (v w : Fin 4 → ℝ) :
    bil (f v) (f w) = bil v w := by
  have h1 := hf (v + w)
  rw [map_add, polarization, polarization, hf v, hf w] at h1
  linarith

/-- **The Gram identity, for any form-preserving linear self-map.** -/
theorem isLorentzMat_of_isometry (f : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hf : ∀ v, minkowskiForm (f v) = minkowskiForm v) :
    IsLorentzMat (LinearMap.toMatrix' f) := by
  ext i j
  have hb := bil_of_isometry f hf (Pi.single i 1) (Pi.single j 1)
  rw [bil_single] at hb
  have hcol : ∀ k l : Fin 4, f (Pi.single l (1 : ℝ)) k = LinearMap.toMatrix' f k l :=
    fun k l => (LinearMap.toMatrix'_apply f k l).symm
  rw [bil] at hb
  rw [hcol, hcol, hcol, hcol, hcol, hcol, hcol, hcol] at hb
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.transpose_apply, gram, Matrix.diagonal_mul]
  rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
    show mw 3 = -1 from rfl]
  rw [gram] at hb
  linarith [hb]

/-! ## 2. The isometry group of `minkowskiForm` sits inside O(1,3) -/

/-- An isometry equivalence as an element of GL₄(ℝ). The inverse matrix
    comes from the equivalence, so no invertibility argument is
    needed. -/
def toGL (g : minkowskiForm.IsometryEquiv minkowskiForm) :
    Matrix.GeneralLinearGroup (Fin 4) ℝ where
  val := LinearMap.toMatrix' g.toLinearEquiv.toLinearMap
  inv := LinearMap.toMatrix' g.toLinearEquiv.symm.toLinearMap
  val_inv := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun x => g.toLinearEquiv.apply_symm_apply x)
  inv_val := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun x => g.toLinearEquiv.symm_apply_apply x)

@[simp] theorem toGL_coe (g : minkowskiForm.IsometryEquiv minkowskiForm) :
    (toGL g : Matrix (Fin 4) (Fin 4) ℝ)
      = LinearMap.toMatrix' g.toLinearEquiv.toLinearMap := rfl

theorem toGL_mem (g : minkowskiForm.IsometryEquiv minkowskiForm) : toGL g ∈ O13 :=
  isLorentzMat_of_isometry _ (fun v => g.map_app v)

/-- **The isometry group of the Minkowski form, as a subgroup of
    GL₄(ℝ).** -/
def toO13 : minkowskiForm.IsometryEquiv minkowskiForm →* O13 where
  toFun g := ⟨toGL g, toGL_mem g⟩
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    rw [toGL_coe]
    exact LinearMap.toMatrix'_id
  map_mul' f g := by
    refine Subtype.ext (Units.ext ?_)
    rw [toGL_coe]
    show LinearMap.toMatrix' _ = _
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, toGL_coe, toGL_coe,
      ← LinearMap.toMatrix'_comp]
    rfl

@[simp] theorem toO13_coe (g : minkowskiForm.IsometryEquiv minkowskiForm) :
    ((toO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
      = LinearMap.toMatrix' g.toLinearEquiv.toLinearMap := rfl

/-! ## 3. The spin group in the estate's own Lorentz group -/

/-- **The two chains land in the same object.** The Clifford/spin side
    reaches `LorentzGroup.O13`, which is where the SL₂(ℂ) side has been
    since it was built. -/
def spinToO13 : spinGroup Q₁₃ →* O13 := toO13.comp lorentzSpinRep

theorem spinToO13_apply_entry (g : spinGroup Q₁₃) (i j : Fin 4) :
    ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) i j
      = coordEquiv (endo g (coordEquiv.symm (Pi.single j 1))) i :=
  LinearMap.toMatrix'_apply _ i j

/-! ## 4. It keeps its teeth -/

theorem spinToO13_R₁₂'_ne_one : spinToO13 R₁₂' ≠ 1 := by
  intro h
  apply lorentzSpinRep_R₁₂'_ne_one
  have h1 : (toO13 (lorentzSpinRep R₁₂') : O13) = 1 := h
  refine DFunLike.ext _ _ fun x => ?_
  have h2 : LinearMap.toMatrix'
      (lorentzSpinRep R₁₂').toLinearEquiv.toLinearMap = 1 := by
    have := congrArg
      (fun y : O13 => ((y : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ)) h1
    simpa using this
  have h3 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M *ᵥ x) h2
  simp only [Matrix.one_mulVec] at h3
  rw [LinearMap.toMatrix'_mulVec] at h3
  exact h3

theorem spinToO13_not_injective : ¬ Function.Injective spinToO13 := by
  intro hinj
  apply lorentzSpinRep_not_injective
  intro a b hab
  exact hinj (by simp only [spinToO13, MonoidHom.comp_apply]; rw [hab])

/-- The boost is in there, and it moves the time axis — read off the
    matrix entry, in the estate's Lorentz coordinates. -/
theorem spinToO13_B_moves_time :
    ((spinToO13 ⟨(SpinBoost.B : Cl), SpinBoost.B_mem⟩ :
        Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) 0 0 = 17 / 8 := by
  rw [spinToO13_apply_entry]
  have hcoord : coordEquiv.symm (Pi.single (0 : Fin 4) (1 : ℝ)) = e₀ := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
      simp [e₀]
  have hg : endo ⟨(SpinBoost.B : Cl), SpinBoost.B_mem⟩ e₀ = SpinBoost.boostTX e₀ := by
    rw [endo, spinToEndo_congr (toUnits_mem _) SpinBoost.B_mem (Units.ext rfl) e₀]
    exact SpinBoost.spinToEndo_B e₀
  rw [hcoord, hg, SpinBoost.boostTX_e₀]
  rfl

end SpinToLorentzMat
