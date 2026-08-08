/-
  SpinMinkowskiBridge.lean — the estate's two Minkowski developments are
  about the same quadratic form, and this joins them.

  WHAT THE RE-SWEEP FOUND. The estate contains two independent chains
  that both end at "the Minkowski form of signature (1,3)", built months
  apart, in different coordinate models, and never once connected:

    • the SL₂(ℂ) chain — `MinkowskiHerm2` → `MinkowskiSignature` →
      `LorentzGroup` → `LorentzSurjectivity` — which works on
      `Fin 4 → ℝ` with `minkowskiForm = weightedSumSquares ℝ ![1,−1,−1,−1]`
      and gets as far as O(1,3) and SO⁺(1,3) as bundled subgroups of
      GL₄(ℝ), with SL₂(ℂ) ↠ SO⁺(1,3) proved;

    • the Clifford chain — `CliffordRealMinkowski` → `SpinVectorRep` →
      `SpinToOrthogonal` → `SpinBoost` — which works on
      `(ℝ × ℝ) × (ℝ × ℝ)` with `Q₁₃ v = v₀² − v₁² − v₂² − v₃²` and gets
      as far as a spin representation `spinGroup Q₁₃ →* O(Q₁₃)`.

  Those are the same form written on two different models of ℝ⁴. Nothing
  in the estate said so, and W7's step (d) has been recording since it
  was written that this is "where the estate's existing SL₂(ℂ) chain
  would finally meet it". This file builds the meeting point.

  WHAT THIS FILE PROVES:
  1. **`coordEquiv`** — `(ℝ × ℝ) × (ℝ × ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)`, the
     coordinate identification, as a linear equivalence.
  2. **`Q₁₃IsometryMinkowski`** — that equivalence is an ISOMETRY from
     `Q₁₃` to `minkowskiForm`. So the two forms are equivalent as
     quadratic forms, not merely "both called Minkowski in their own
     docstrings".
  3. **`transportIsom`** — the induced group isomorphism between the two
     orthogonal groups, `O(Q₁₃) ≃* O(minkowskiForm)`, using the group
     structure built in `SpinToOrthogonal` §1 (which Mathlib does not
     have).
  4. **`lorentzSpinRep : spinGroup Q₁₃ →* minkowskiForm.IsometryEquiv
     minkowskiForm`** — the spin representation, now landing in the
     isometry group of the SAME form the estate's Lorentz files use.
     With `lorentzSpinRep_not_injective` and a non-trivial element, so
     the transported map inherits its teeth rather than merely existing.

  WHAT THIS DOES NOT DO, and it is the obvious next question. The
  `LorentzGroup` files describe O(1,3) as a subgroup of GL₄(ℝ) — a
  MATRIX group, with membership `ΛᵀGΛ = G`. This file lands in
  `minkowskiForm.IsometryEquiv minkowskiForm`, which is the same group
  mathematically but a different Lean type. Passing from one to the
  other means taking the matrix of a linear equivalence and turning the
  isometry condition into the Gram condition. **That is not done here.**
  Until it is, `spinRep` and `SOplus13` are adjacent rather than
  connected, and no claim about the image being SO⁺(1,3) follows from
  this file — for which one would additionally need `det = 1` and
  `Λ⁰₀ > 0`, neither of which is proved anywhere for the spin image.

  A CAUTION ABOUT `coordEquiv`, added by review round 19 and worth
  reading before using anything below. **Being an isometry does not
  determine the identification.** Swapping the y and z slots gives a
  DIFFERENT linear equivalence which is equally an isometry between the
  same two forms — `swapEquiv` and `swapEquiv_ne_coordEquiv` in §5
  prove exactly that. So `Q₁₃IsometryMinkowski` is a CHOICE, not a
  canonical object, and a mislabelled choice would make everything
  downstream conjugate-but-wrong while compiling identically. What pins
  this particular choice is not the isometry property but
  `coordEquiv_e₀` … `coordEquiv_e₃`: it sends the Clifford chain's
  basis to the standard basis of `Fin 4 → ℝ` IN ORDER, so slot 0 is the
  time direction on both sides.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import MinkowskiSignature
import SpinToOrthogonal
import SpinBoost

open CliffordAlgebra CliffordRealMinkowski SpinVectorRep SpinToOrthogonal
open MinkowskiSignature

noncomputable section

namespace SpinMinkowskiBridge

/-! ## 1. The coordinate identification -/

/-- `((t,x),(y,z)) ↦ ![t,x,y,z]`, as a linear equivalence. -/
def coordEquiv : V ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![v.1.1, v.1.2, v.2.1, v.2.2]
  map_add' u v := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl
  invFun f := ((f 0, f 1), (f 2, f 3))
  left_inv v := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

@[simp] theorem coordEquiv_apply (v : V) :
    coordEquiv v = ![v.1.1, v.1.2, v.2.1, v.2.2] := rfl

@[simp] theorem coordEquiv_symm_apply (f : Fin 4 → ℝ) :
    coordEquiv.symm f = ((f 0, f 1), (f 2, f 3)) := rfl

@[simp] theorem coordEquiv_zero (v : V) : coordEquiv v 0 = v.1.1 := rfl
@[simp] theorem coordEquiv_one (v : V) : coordEquiv v 1 = v.1.2 := rfl
@[simp] theorem coordEquiv_two (v : V) : coordEquiv v 2 = v.2.1 := rfl
@[simp] theorem coordEquiv_three (v : V) : coordEquiv v 3 = v.2.2 := rfl

/-- **What actually pins the choice.** The isometry property does not
    (see §5); these four do. The Clifford chain's basis goes to the
    standard basis in order, so slot 0 is the time direction on both
    sides. -/
@[simp] theorem coordEquiv_e₀ : coordEquiv e₀ = ![1, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl

@[simp] theorem coordEquiv_e₁ : coordEquiv e₁ = ![0, 1, 0, 0] := by
  funext i; fin_cases i <;> rfl

@[simp] theorem coordEquiv_e₂ : coordEquiv e₂ = ![0, 0, 1, 0] := by
  funext i; fin_cases i <;> rfl

@[simp] theorem coordEquiv_e₃ : coordEquiv e₃ = ![0, 0, 0, 1] := by
  funext i; fin_cases i <;> rfl

/-! ## 2. The two forms are the same form -/

/-- **`Q₁₃` and `minkowskiForm` are the same quadratic form**, read on
    two different models of ℝ⁴. Both chains in the estate were about
    this object; neither said so. -/
def Q₁₃IsometryMinkowski : Q₁₃.IsometryEquiv minkowskiForm where
  __ := coordEquiv
  map_app' v := by
    rw [minkowskiForm_apply, Q₁₃_apply]
    rfl

@[simp] theorem Q₁₃IsometryMinkowski_apply (v : V) :
    Q₁₃IsometryMinkowski v = coordEquiv v := rfl

/-- Stated on its own, because it is the sentence the estate was
    missing: the two forms are equivalent. -/
theorem Q₁₃_equivalent_minkowskiForm : Q₁₃.Equivalent minkowskiForm :=
  ⟨Q₁₃IsometryMinkowski⟩

/-! ## 3. Transporting the orthogonal group

The group structure used here is the one built in `SpinToOrthogonal` §1;
Mathlib has no algebraic structure on self-isometries of a quadratic
form, so without that section this transport has no target. -/

/-- Conjugation by the coordinate identification, as a map on
    isometries. -/
def transportFun (f : Q₁₃.IsometryEquiv Q₁₃) :
    minkowskiForm.IsometryEquiv minkowskiForm :=
  (Q₁₃IsometryMinkowski.symm.trans f).trans Q₁₃IsometryMinkowski

@[simp] theorem transportFun_apply (f : Q₁₃.IsometryEquiv Q₁₃) (x : Fin 4 → ℝ) :
    transportFun f x = coordEquiv (f (coordEquiv.symm x)) := rfl

/-- The inverse transport. -/
def transportInv (g : minkowskiForm.IsometryEquiv minkowskiForm) :
    Q₁₃.IsometryEquiv Q₁₃ :=
  (Q₁₃IsometryMinkowski.trans g).trans Q₁₃IsometryMinkowski.symm

@[simp] theorem transportInv_apply (g : minkowskiForm.IsometryEquiv minkowskiForm)
    (v : V) : transportInv g v = coordEquiv.symm (g (coordEquiv v)) := rfl

/-- **The two orthogonal groups are isomorphic**, by conjugation with
    the coordinate identification. -/
def transportIsom : Q₁₃.IsometryEquiv Q₁₃ ≃* minkowskiForm.IsometryEquiv minkowskiForm where
  toFun := transportFun
  invFun := transportInv
  left_inv _ := DFunLike.ext _ _ fun _ => rfl
  right_inv g := DFunLike.ext _ _ fun x => by
    rw [transportFun_apply, transportInv_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  map_mul' _ _ := DFunLike.ext _ _ fun _ => rfl

/-! ## 4. The spin representation on the Lorentz files' ℝ⁴ -/

/-- **The spin representation, landing in the isometry group of the
    same form `LorentzGroup` and `LorentzSurjectivity` work with.** -/
def lorentzSpinRep : spinGroup Q₁₃ →* minkowskiForm.IsometryEquiv minkowskiForm :=
  (transportIsom : Q₁₃.IsometryEquiv Q₁₃ ≃* _).toMonoidHom.comp spinRep

@[simp] theorem lorentzSpinRep_apply (g : spinGroup Q₁₃) (x : Fin 4 → ℝ) :
    lorentzSpinRep g x = coordEquiv (endo g (coordEquiv.symm x)) := rfl

/-- The transported representation is still not injective — the teeth
    survive the transport rather than having to be re-earned. -/
theorem lorentzSpinRep_not_injective : ¬ Function.Injective lorentzSpinRep := by
  intro hinj
  exact spinRep_not_injective fun a b hab =>
    hinj (by simp only [lorentzSpinRep, MonoidHom.comp_apply]; rw [hab])

/-- And it is still not trivial: the π-rotation acts nontrivially on the
    Lorentz files' ℝ⁴ too. -/
theorem lorentzSpinRep_R₁₂'_ne_one : lorentzSpinRep R₁₂' ≠ 1 := by
  intro h
  apply spinRep_R₁₂'_ne_one
  have h2 : transportIsom (spinRep R₁₂') = 1 := h
  have h3 := congrArg transportIsom.symm h2
  rwa [MulEquiv.symm_apply_apply, map_one] at h3

/-- The boost, read on `Fin 4 → ℝ`: the time coordinate moves. This is
    the statement in the coordinates the Lorentz files use. -/
theorem lorentzSpinRep_B_time :
    lorentzSpinRep ⟨(SpinBoost.B : Cl), SpinBoost.B_mem⟩ ![1, 0, 0, 0] 0 = 17 / 8 := by
  have hcoord : coordEquiv.symm ![(1 : ℝ), 0, 0, 0] = e₀ := rfl
  have hg : endo ⟨(SpinBoost.B : Cl), SpinBoost.B_mem⟩ e₀
      = SpinBoost.boostTX e₀ := by
    rw [endo, spinToEndo_congr (toUnits_mem _) SpinBoost.B_mem (Units.ext rfl) e₀]
    exact SpinBoost.spinToEndo_B e₀
  rw [lorentzSpinRep_apply, hcoord, hg, SpinBoost.boostTX_e₀]
  rfl

/-! ## 5. The identification is a choice, not a canonical object

Review round 19's finding, folded back as a proof rather than as a
hedge. If "it is an isometry" determined the map, §1's definition would
need no justification. It does not determine it. -/

/-- The same coordinate identification with y and z exchanged. -/
def swapEquiv : V ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![v.1.1, v.1.2, v.2.2, v.2.1]
  map_add' u v := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl
  invFun f := ((f 0, f 1), (f 3, f 2))
  left_inv v := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

/-- **It is equally an isometry.** -/
def swapIsometry : Q₁₃.IsometryEquiv minkowskiForm where
  __ := swapEquiv
  map_app' v := by
    rw [minkowskiForm_apply, Q₁₃_apply]
    change v.1.1 ^ 2 - v.1.2 ^ 2 - v.2.2 ^ 2 - v.2.1 ^ 2 = _
    ring

/-- **And it is a different map.** So the isometry property alone does
    not identify `coordEquiv`; the basis lemmas in §1 do. -/
theorem swapEquiv_ne_coordEquiv : swapEquiv ≠ (coordEquiv : V ≃ₗ[ℝ] (Fin 4 → ℝ)) := by
  intro h
  have h1 : swapEquiv e₂ 2 = coordEquiv e₂ 2 := by rw [h]
  have h2 : (0 : ℝ) = 1 := h1
  norm_num at h2

end SpinMinkowskiBridge
