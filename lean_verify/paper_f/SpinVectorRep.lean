/-
  SpinVectorRep.lean — the vector representation of Spin on ℝ⁴:
  steps (b) and (c) of the stair WALLS.md W7 maps.

  W7's residue item 3 was, until 6 August 2026, recorded as "no Mathlib
  `spinGroup`". That was false (ERRATUM 40): Mathlib has
  `LinearAlgebra/CliffordAlgebra/SpinGroup.lean`, defining
  `lipschitzGroup`, `pinGroup` and `spinGroup` with full group
  structure. What Mathlib does NOT have is the group's ACTION — no
  homomorphism to any orthogonal group, and its own `## TODO` is where
  that would go. This file builds that action for the estate's
  mostly-minus Minkowski form.

  THE ROUTE, as W7 records it and as walked here:
  (a) `ι Q₁₃` is injective — done in `CliffordRealMinkowski` §9. Mathlib
      proves this for NO quadratic form; the estate has it because the
      Cl(1,3;ℝ) ≅ M₂(ℍ) isomorphism makes the four coordinates visible
      as matrix entries.
  (b) A spin element conjugates `range (ι Q₁₃)` into itself — this is
      Mathlib's `spinGroup.conjAct_smul_ι_mem_range_ι`, and it is the
      one hard ingredient we did not have to build.
  (c) Transport along (a) to get an endomorphism of ℝ⁴, and check it
      preserves the form.

  WHAT THIS FILE PROVES (exactly this, nothing more):
  1. `conjLin` — conjugation by a unit as an ℝ-linear endomorphism of
     the Clifford algebra, with `conjLin_apply`.
  2. `conjLin_mapsTo` — for a SPIN element, `range (ι Q₁₃)` is
     invariant. The spin hypothesis is doing real work here and is not
     decoration: it is what licenses Mathlib's stability lemma.
  3. **`spinToEndo`** — the induced ℝ-linear endomorphism of ℝ⁴, with
     **`ι_spinToEndo`** as its defining property: `ι` of the image is
     the conjugate. Everything else is read off that one equation.
  4. **`spinToEndo_preserves`** — it preserves `Q₁₃`. So each spin
     element acts as an isometry of the mostly-minus Minkowski form.
  5. `spinToEndo_one` and `spinToEndo_mul` — the identity acts as the
     identity and the action is multiplicative, so this is a genuine
     action and not merely a family of maps.

  NOT proven here, and the reason W7 keeps a residue: nothing about the
  IMAGE of this action. That it lands in the identity component
  SO⁺(1,3), that the kernel is ±1, that the map is surjective onto
  SO⁺(1,3) — none of that is here, none of it follows from what is
  here, and W7 marks it research-level rather than bounded. This file
  is steps (b) and (c); step (d) is untouched and is not promised.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import CliffordRealMinkowski

open CliffordAlgebra CliffordRealMinkowski

noncomputable section

namespace SpinVectorRep

/-- The underlying real 4-space of the mostly-minus Minkowski form. -/
abbrev V : Type := (ℝ × ℝ) × (ℝ × ℝ)

/-- The Clifford algebra we are acting inside. -/
abbrev Cl : Type := CliffordAlgebra Q₁₃

/-! ## 1. Conjugation as a linear map -/

/-- Conjugation by a unit, as an ℝ-linear endomorphism of the algebra.
    Linear because multiplication on either side is. -/
def conjLin (x : Clˣ) : Cl →ₗ[ℝ] Cl :=
  LinearMap.mulLeft ℝ (x : Cl) ∘ₗ LinearMap.mulRight ℝ ((x⁻¹ : Clˣ) : Cl)

@[simp] theorem conjLin_apply (x : Clˣ) (a : Cl) :
    conjLin x a = (x : Cl) * a * ((x⁻¹ : Clˣ) : Cl) :=
  (mul_assoc _ _ _).symm

/-! ## 2. Spin elements preserve the image of ι

This is the step Mathlib supplies. `spinGroup.conjAct_smul_ι_mem_range_ι`
says twisted conjugation by a spin element sends `ι Q v` back into
`range (ι Q)`; because `range` of a linear map is an image rather than a
span, checking it on the generators IS checking it everywhere. -/

theorem conjLin_mapsTo {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) :
    ∀ a ∈ LinearMap.range (ι Q₁₃), conjLin x a ∈ LinearMap.range (ι Q₁₃) := by
  rintro _ ⟨v, rfl⟩
  have h := spinGroup.conjAct_smul_ι_mem_range_ι hx v
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at h
  rw [conjLin_apply]
  exact h

/-- The restriction of conjugation to the invariant subspace. -/
def spinRestrict {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) :
    LinearMap.range (ι Q₁₃) →ₗ[ℝ] LinearMap.range (ι Q₁₃) :=
  (conjLin x).restrict (conjLin_mapsTo hx)

/-! ## 3. Transport to ℝ⁴ -/

/-- `ι Q₁₃` as a linear equivalence onto its range — available only
    because step (a) proved it injective. -/
def ιEquiv : V ≃ₗ[ℝ] LinearMap.range (ι Q₁₃) :=
  LinearEquiv.ofInjective (ι Q₁₃) ι_injective

@[simp] theorem ιEquiv_coe (v : V) : ((ιEquiv v : LinearMap.range (ι Q₁₃)) : Cl)
    = ι Q₁₃ v := rfl

/-- **The vector representation.** A spin element acts on ℝ⁴ by
    conjugation, read through `ι`. -/
def spinToEndo {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) : V →ₗ[ℝ] V :=
  ιEquiv.symm.toLinearMap ∘ₗ spinRestrict hx ∘ₗ ιEquiv.toLinearMap

/-- **The defining property**, and the only thing about `spinToEndo`
    that needs a proof from its construction: `ι` of the image is the
    conjugate. Every later fact is read off this equation. -/
theorem ι_spinToEndo {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) (v : V) :
    ι Q₁₃ (spinToEndo hx v) = (x : Cl) * ι Q₁₃ v * ((x⁻¹ : Clˣ) : Cl) := by
  have h : ιEquiv (spinToEndo hx v) = spinRestrict hx (ιEquiv v) := by
    simp [spinToEndo]
  have h2 := congrArg (fun y : LinearMap.range (ι Q₁₃) => (y : Cl)) h
  simpa [spinRestrict, LinearMap.restrict_coe_apply, conjLin_apply] using h2

/-! ## 4. It is an isometry, and it is an action -/

/-- **A spin element acts as an isometry of `Q₁₃`.** Conjugation is an
    algebra map, so `ι(v)² = Q₁₃(v)` transports; the scalar comes back
    out because scalars are central. -/
theorem spinToEndo_preserves {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) (v : V) :
    Q₁₃ (spinToEndo hx v) = Q₁₃ v := by
  apply FaithfulSMul.algebraMap_injective ℝ Cl
  have key : ι Q₁₃ (spinToEndo hx v) * ι Q₁₃ (spinToEndo hx v)
      = algebraMap ℝ Cl (Q₁₃ v) := by
    rw [ι_spinToEndo]
    calc (x : Cl) * ι Q₁₃ v * ((x⁻¹ : Clˣ) : Cl)
          * ((x : Cl) * ι Q₁₃ v * ((x⁻¹ : Clˣ) : Cl))
        = (x : Cl) * (ι Q₁₃ v *
            (((x⁻¹ : Clˣ) : Cl) * ((x : Cl) * (ι Q₁₃ v * ((x⁻¹ : Clˣ) : Cl))))) := by
          simp only [mul_assoc]
      _ = (x : Cl) * (ι Q₁₃ v * ι Q₁₃ v) * ((x⁻¹ : Clˣ) : Cl) := by
          rw [Units.inv_mul_cancel_left]
          simp only [mul_assoc]
      _ = (x : Cl) * algebraMap ℝ Cl (Q₁₃ v) * ((x⁻¹ : Clˣ) : Cl) := by
          rw [ι_sq_scalar]
      _ = algebraMap ℝ Cl (Q₁₃ v) * ((x : Cl) * ((x⁻¹ : Clˣ) : Cl)) := by
          rw [← Algebra.commutes, mul_assoc]
      _ = algebraMap ℝ Cl (Q₁₃ v) := by
          simp
  rw [← ι_sq_scalar, key]

/-- The identity spin element acts as the identity. -/
theorem spinToEndo_one (h1 : ((1 : Clˣ) : Cl) ∈ spinGroup Q₁₃) :
    spinToEndo h1 = LinearMap.id :=
  LinearMap.ext fun v => ι_injective (by rw [ι_spinToEndo]; simp)

/-- The action is multiplicative: this is a genuine group action on ℝ⁴,
    not merely a family of isometries indexed by spin elements. -/
theorem spinToEndo_mul {x y : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃)
    (hy : (y : Cl) ∈ spinGroup Q₁₃) (hxy : ((x * y : Clˣ) : Cl) ∈ spinGroup Q₁₃)
    (v : V) :
    spinToEndo hxy v = spinToEndo hx (spinToEndo hy v) := by
  apply ι_injective
  rw [ι_spinToEndo, ι_spinToEndo, ι_spinToEndo]
  simp [mul_assoc]

end SpinVectorRep
