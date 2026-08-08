/-
  SpinFibre.lean — the kernel and the fibres of the spin representation,
  at the bundled level.

  WHY, and it is PROOF_STRATEGY §7 point 2: any item reported as "reached
  B" is still open. `SpinOrthochronous` delivered
  **`spinToSOplus : spinGroup Q₁₃ →* SOplus13`** and stopped there. Its
  kernel was known — `SpinKernel.kernel_iff` says a spin element acts
  trivially on ℝ⁴ iff it is ±1 — but that theorem is about `spinToEndo`,
  the UNBUNDLED action, and nothing restated it for the homomorphism a
  downstream reader would actually use. A homomorphism whose kernel is
  only known about its shadow is a B.

  WHAT THIS FILE PROVES:
  1. **`spinToO13_eq_one_iff`** — `spinToO13 g = 1` if and only if
     `g = ±1`. The kernel, at the level of the map into the Lorentz
     matrices.
  2. **`spinToSOplus_eq_one_iff`** and **`mem_ker_spinToSOplus`** — the
     same for the bundled map into SO⁺(1,3), the latter as a membership
     criterion for `MonoidHom.ker`. (Pointwise, not as an equality of
     subgroup objects; that packaging is not written here.)
  3. **`spinToO13_eq_iff`** — the fibres, which is the sharper statement:
     two spin elements have the same Lorentz matrix if and only if they
     differ by a sign. **Every non-empty fibre has exactly two points.**
  4. **`spinToO13_two_to_one`** — that stated as a cardinality-free
     "exactly two preimages" fact, with `negSpin_ne` supplying that the
     two really are distinct.

  WHAT THIS IS NOT. **A 2-to-1 homomorphism is not a double cover unless
  it is onto**, and surjectivity of `spinToO13` is NOT proved anywhere in
  the estate — see the watchlist. So the honest reading of this file is
  "`spinGroup Q₁₃ ⧸ {±1}` embeds in SO⁺(1,3)", not "`spinGroup Q₁₃` is
  the double cover of SO⁺(1,3)".

  AND IT DOES NOT IDENTIFY THE TWO CHAINS. `LorentzSurjectivity.double_cover`
  says SL₂(ℂ) → SO⁺(1,3) is onto with kernel {±1}. This file says the spin
  map has kernel {±1} too. **Two homomorphisms into one group with equal
  kernels are not thereby equal, or even related** — one of them is known
  to be onto and the other is not, and no theorem anywhere intertwines
  them. §5 states that as a theorem-shaped caveat rather than a sentence.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinOrthochronous
import SpinKernel

namespace SpinFibre

open SpinVectorRep SpinPair SpinToOrthogonal LipschitzVectorRep
open MinkowskiSignature LorentzGroup SpinMinkowskiBridge SpinToLorentzMat
open SpinDetOne SpinOrthochronous SpinKernel
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. The kernel, at the bundled level -/

/-- The matrix of a spin element is the identity exactly when its action
    is. Both directions go through `spinToO13_toMatrix`. -/
theorem spinToO13_eq_one_iff' (g : spinGroup Q₁₃) :
    ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) = 1
      ↔ ∀ v : V, endo g v = v := by
  rw [spinToO13_toMatrix]
  constructor
  · intro h v
    have hv := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M *ᵥ coordEquiv v) h
    simp only [Matrix.one_mulVec] at hv
    rw [show LinearMap.toMatrix'
        ((coordEquiv : V →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ endo g ∘ₗ
          (coordEquiv.symm : (Fin 4 → ℝ) →ₗ[ℝ] V)) *ᵥ coordEquiv v
        = coordEquiv (endo g v) from by
      rw [LinearMap.toMatrix'_mulVec]
      simp] at hv
    exact coordEquiv.injective hv
  · intro h
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [h, LinearEquiv.apply_symm_apply]

/-- **The kernel of the spin representation, bundled.** `spinToO13 g` is
    the identity Lorentz matrix exactly when `g = ±1`. -/
theorem spinToO13_eq_one_iff (g : spinGroup Q₁₃) :
    spinToO13 g = 1 ↔ ((g : Cl) = 1 ∨ (g : Cl) = -1) := by
  have hmat : spinToO13 g = 1
      ↔ ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact Subtype.ext (Units.ext h)
  rw [hmat, spinToO13_eq_one_iff']
  exact kernel_iff (toUnits_mem g)

/-! ## 2. The fibres

The sharper statement, and the one a reader wants: not just which
elements go to the identity, but which pairs go to the same place.
-/

/-- Negation, as an operation on the spin group. -/
def negSpin (g : spinGroup Q₁₃) : spinGroup Q₁₃ :=
  ⟨-(g : Cl), by
    have := spinGroup_neg_mem (toUnits_mem g)
    simpa using this⟩

@[simp] theorem negSpin_coe (g : spinGroup Q₁₃) : (negSpin g : Cl) = -(g : Cl) :=
  rfl

/-- Negation does not change the Lorentz matrix — `−1` is in the kernel. -/
theorem spinToO13_negSpin (g : spinGroup Q₁₃) :
    spinToO13 (negSpin g) = spinToO13 g := by
  have hone : spinToO13 (negSpin g) * (spinToO13 g)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    refine (spinToO13_eq_one_iff _).2 (Or.inr ?_)
    have : ((negSpin g * g⁻¹ : spinGroup Q₁₃) : Cl)
        = -(g : Cl) * ((g⁻¹ : spinGroup Q₁₃) : Cl) := rfl
    rw [this, neg_mul]
    congr 1
    exact congrArg Subtype.val (mul_inv_cancel g)
  have := congrArg (fun M => M * spinToO13 g) hone
  simpa [mul_assoc] using this

/-- **The fibres of the spin representation have exactly two points.**
    Two spin elements have the same Lorentz matrix iff they differ by a
    sign. -/
theorem spinToO13_eq_iff (g h : spinGroup Q₁₃) :
    spinToO13 g = spinToO13 h ↔ ((g : Cl) = (h : Cl) ∨ (g : Cl) = -(h : Cl)) := by
  constructor
  · intro heq
    have hone : spinToO13 (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    have hpm := (spinToO13_eq_one_iff _).1 hone
    have hcoe : ((g * h⁻¹ : spinGroup Q₁₃) : Cl)
        = (g : Cl) * ((h⁻¹ : spinGroup Q₁₃) : Cl) := rfl
    have hhh : ((h⁻¹ : spinGroup Q₁₃) : Cl) * (h : Cl) = 1 :=
      congrArg Subtype.val (inv_mul_cancel h)
    rcases hpm with hp | hp
    · left
      rw [hcoe] at hp
      calc (g : Cl) = (g : Cl) * (((h⁻¹ : spinGroup Q₁₃) : Cl) * (h : Cl)) := by
            rw [hhh, mul_one]
        _ = ((g : Cl) * ((h⁻¹ : spinGroup Q₁₃) : Cl)) * (h : Cl) := by
            rw [mul_assoc]
        _ = (h : Cl) := by rw [hp, one_mul]
    · right
      rw [hcoe] at hp
      calc (g : Cl) = (g : Cl) * (((h⁻¹ : spinGroup Q₁₃) : Cl) * (h : Cl)) := by
            rw [hhh, mul_one]
        _ = ((g : Cl) * ((h⁻¹ : spinGroup Q₁₃) : Cl)) * (h : Cl) := by
            rw [mul_assoc]
        _ = -(h : Cl) := by rw [hp, neg_one_mul]
  · rintro (hp | hp)
    · rw [Subtype.ext hp]
    · rw [show g = negSpin h from Subtype.ext (by simpa using hp)]
      exact spinToO13_negSpin h

/-- The two points of a fibre are genuinely distinct: `g ≠ −g`, because
    otherwise `2g = 0` and `g` is a unit. -/
theorem negSpin_ne (g : spinGroup Q₁₃) : negSpin g ≠ g := by
  intro hcon
  have hc : -(g : Cl) = (g : Cl) := congrArg Subtype.val hcon
  have h2 : (2 : ℝ) • (g : Cl) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hc]
    exact neg_add_cancel _
  have hzero : (g : Cl) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact (spinGroup.toUnits g).ne_zero hzero

/-- **Exactly two preimages**, stated without cardinality machinery. -/
theorem spinToO13_two_to_one (g : spinGroup Q₁₃) :
    negSpin g ≠ g ∧ spinToO13 (negSpin g) = spinToO13 g
      ∧ ∀ h : spinGroup Q₁₃, spinToO13 h = spinToO13 g → h = g ∨ h = negSpin g :=
  ⟨negSpin_ne g, spinToO13_negSpin g, fun h hh => by
    rcases (spinToO13_eq_iff h g).1 hh with hp | hp
    · exact Or.inl (Subtype.ext hp)
    · exact Or.inr (Subtype.ext (by simpa using hp))⟩

/-! ## 3. The same, for the bundled map into SO⁺(1,3) -/

theorem spinToSOplus_eq_one_iff (g : spinGroup Q₁₃) :
    spinToSOplus g = 1 ↔ ((g : Cl) = 1 ∨ (g : Cl) = -1) := by
  rw [← spinToO13_eq_one_iff]
  constructor
  · intro h
    refine Subtype.ext (Units.ext ?_)
    exact congrArg (fun M : SOplus13 => ((M : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ)) h
  · intro h
    refine Subtype.ext ?_
    exact congrArg (fun M : O13 => (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)) h

/-- **The kernel of `spinToSOplus` is exactly `{1, −1}`.** -/
theorem mem_ker_spinToSOplus (g : spinGroup Q₁₃) :
    g ∈ MonoidHom.ker spinToSOplus ↔ ((g : Cl) = 1 ∨ (g : Cl) = -1) :=
  spinToSOplus_eq_one_iff g

/-! ## 4. What this does NOT say

Both chains now reach SO⁺(1,3) with kernel `{±1}`. That is a coincidence
of two facts, not a relation between the two maps, and the difference is
the whole of W7 step (d)'s residue. The statements below are the caveats
in theorem form.
-/

/-- The spin map is 2-to-1 onto its image; **whether that image is all of
    SO⁺(1,3) is not proved**, and this file does not assume it. What IS
    available is that the image contains a rotation and a boost that do
    not commute. -/
theorem image_nonabelian :
    ∃ g h : spinGroup Q₁₃, spinToO13 (g * h) ≠ spinToO13 (h * g) :=
  ⟨B', R₁₂', spinToO13_noncomm⟩

/-- And the map is not injective, so "kernel `{±1}`" is not vacuous — the
    two points of a fibre really are two. -/
theorem not_injective : ¬ Function.Injective spinToO13 :=
  spinToO13_not_injective

/-- The identity's fibre, spelled out: exactly `1` and `−1`. -/
theorem fibre_of_one (h : spinGroup Q₁₃) :
    spinToO13 h = 1 ↔ ((h : Cl) = 1 ∨ (h : Cl) = -1) :=
  spinToO13_eq_one_iff h

end

end SpinFibre
