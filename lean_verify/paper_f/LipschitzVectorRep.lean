/-
  LipschitzVectorRep.lean — the vector representation, one group up.

  WHY. `SpinVectorRep` built the action of `spinGroup Q₁₃` on ℝ⁴ by
  conjugation. That is the group the estate cares about, but it is the
  wrong group to do INDUCTION over: `spinGroup` is defined by conditions
  (Lipschitz, unitary, even), not by generators, so there is no closure
  principle to induct with. `lipschitzGroup Q` IS defined by generators —
  `Subgroup.closure ((↑) ⁻¹' Set.range (ι Q))`, literally the units that
  are vectors — and it CONTAINS `spinGroup`. So any statement one wants to
  prove for every spin element by induction on word length has to be
  proved here first, and then restricted.

  The specific target is W7 step (d)'s determinant half: every spin
  element has `det = 1`, because it is an even-length word in reflections
  and each reflection contributes `−1`. `LorentzReflection` proved the
  `−1`. This file supplies the group to run the word argument in. The
  argument itself is the next file; nothing here does it.

  WHAT THIS FILE PROVES:
  1. **`lipToEndo`** — every element of `lipschitzGroup Q₁₃` acts on ℝ⁴
     by conjugation, with **`ι_lipToEndo`** the defining equation and
     **`lipToEndo_preserves`** making it an isometry of `Q₁₃`.
     **`lipToEndo_one`** and **`lipToEndo_mul`** make it an action.
  2. **`lipToEndo_eq_spinToEndo`** — on a spin element it is the map
     `SpinVectorRep` already built. Without this the file would be a
     parallel development rather than an extension, and anything proved
     here would say nothing about the estate's spin representation.
  3. **`lipToEndo_vecUnit`** — the action of a GENERATOR is `vreflect v`,
     the reflection `SpinPair` defined and `LorentzReflection` computed
     the determinant of. This is the base case of the induction the next
     file runs, and it is the only place the generators are touched.

  WHAT THIS DOES NOT DO. No induction is run here and no determinant
  appears. In particular nothing here says anything about `det = 1`, about
  SO⁺(1,3), or about W7 step (d) — this is the object the argument needs,
  not the argument. Everything in §1–§3 is `SpinVectorRep` §1–§4 with the
  hypothesis relaxed, and the one line that actually changes is the appeal
  to `lipschitzGroup.conjAct_smul_ι_mem_range_ι` in place of its
  `spinGroup` corollary; the rest was already general in the unit and only
  looked spin-specific.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinVectorRep
import SpinPair

namespace LipschitzVectorRep

open SpinVectorRep SpinPair
open CliffordAlgebra CliffordRealMinkowski

noncomputable section

/-! ## 1. Conjugation preserves the vectors, for a Lipschitz element

`SpinVectorRep.conjLin_mapsTo` appealed to
`spinGroup.conjAct_smul_ι_mem_range_ι`. That corollary is derived in
Mathlib from `lipschitzGroup.conjAct_smul_ι_mem_range_ι`, which is the
statement at the level this file needs; using the general one directly is
the only substantive change in §1–§3.
-/

theorem conjLin_mapsTo {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    ∀ a ∈ LinearMap.range (ι Q₁₃), conjLin x a ∈ LinearMap.range (ι Q₁₃) := by
  rintro _ ⟨v, rfl⟩
  have h := lipschitzGroup.conjAct_smul_ι_mem_range_ι hx v
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at h
  rw [conjLin_apply]
  exact h

/-- The restriction of conjugation to the invariant subspace. -/
def lipRestrict {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    LinearMap.range (ι Q₁₃) →ₗ[ℝ] LinearMap.range (ι Q₁₃) :=
  (conjLin x).restrict (conjLin_mapsTo hx)

/-! ## 2. The action on ℝ⁴ -/

/-- **The vector representation of the Lipschitz group.** -/
def lipToEndo {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) : V →ₗ[ℝ] V :=
  ιEquiv.symm.toLinearMap ∘ₗ lipRestrict hx ∘ₗ ιEquiv.toLinearMap

/-- **The defining property.** Everything below is read off this. -/
theorem ι_lipToEndo {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) (v : V) :
    ι Q₁₃ (lipToEndo hx v) = (x : Cl) * ι Q₁₃ v * ((x⁻¹ : Clˣ) : Cl) := by
  have h : ιEquiv (lipToEndo hx v) = lipRestrict hx (ιEquiv v) := by
    simp [lipToEndo]
  have h2 := congrArg (fun y : LinearMap.range (ι Q₁₃) => (y : Cl)) h
  simpa [lipRestrict, LinearMap.restrict_coe_apply, conjLin_apply] using h2

/-- The map depends on the unit, not on the membership proof — needed
    because `lipToEndo` is indexed by a proof whose type mentions the
    unit, exactly as `spinToEndo` is. -/
theorem lipToEndo_congr {x y : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hy : y ∈ lipschitzGroup Q₁₃) (h : x = y) (v : V) :
    lipToEndo hx v = lipToEndo hy v := by
  subst h
  rfl

/-! ## 3. It is an isometry, and it is an action -/

/-- **A Lipschitz element acts as an isometry of `Q₁₃`.** Conjugation is
    an algebra map, so `ι(v)² = Q₁₃(v)` transports and the scalar comes
    back out because scalars are central. -/
theorem lipToEndo_preserves {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) (v : V) :
    Q₁₃ (lipToEndo hx v) = Q₁₃ v := by
  apply FaithfulSMul.algebraMap_injective ℝ Cl
  have key : ι Q₁₃ (lipToEndo hx v) * ι Q₁₃ (lipToEndo hx v)
      = algebraMap ℝ Cl (Q₁₃ v) := by
    rw [ι_lipToEndo]
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

theorem lipToEndo_one (v : V) :
    lipToEndo (one_mem (lipschitzGroup Q₁₃)) v = v := by
  apply ι_injective
  rw [ι_lipToEndo]
  simp

theorem lipToEndo_mul {x y : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hy : y ∈ lipschitzGroup Q₁₃) (v : V) :
    lipToEndo (mul_mem hx hy) v = lipToEndo hx (lipToEndo hy v) := by
  apply ι_injective
  rw [ι_lipToEndo, ι_lipToEndo, ι_lipToEndo, Units.val_mul, mul_inv_rev,
    Units.val_mul]
  simp only [mul_assoc]

theorem lipToEndo_inv {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) (v : V) :
    lipToEndo (inv_mem hx) (lipToEndo hx v) = v := by
  apply ι_injective
  rw [ι_lipToEndo, ι_lipToEndo]
  simp only [inv_inv]
  simp [mul_assoc]

/-! ## 4. It extends the spin representation

Without this the file is a parallel development and nothing proved in it
says anything about the estate's spin work. The two maps are the same
restriction of the same conjugation, so the proof is the two defining
equations and `ι_injective`.
-/

/-- **On a spin element, this IS `SpinVectorRep.spinToEndo`.** -/
theorem lipToEndo_eq_spinToEndo {x : Clˣ} (hlip : x ∈ lipschitzGroup Q₁₃)
    (hspin : (x : Cl) ∈ spinGroup Q₁₃) (v : V) :
    lipToEndo hlip v = spinToEndo hspin v := by
  apply ι_injective
  rw [ι_lipToEndo, ι_spinToEndo]

/-- Every spin element is a Lipschitz element, at the level of the units,
    so that the statement above can always be applied. -/
theorem units_mem_lip {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) :
    x ∈ lipschitzGroup Q₁₃ :=
  spinGroup.units_mem_lipschitzGroup hx

/-! ## 5. The generators act by reflection

This is the base case of the word induction the next file runs, and the
only place in the development where a generator of `lipschitzGroup` is
touched. `SpinPair.conj_vecUnit` did the algebra; all that is left is to
read it through `ι_lipToEndo`.
-/

/-- **A vector unit acts as the reflection in that vector.** -/
theorem lipToEndo_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) (u : V) :
    lipToEndo (vecUnit_mem v hv) u = vreflect v u := by
  apply ι_injective
  rw [ι_lipToEndo]
  exact conj_vecUnit hv u

/-- The generators of `lipschitzGroup Q₁₃` are exactly the units whose
    value is a vector, spelled out — `Subgroup.closure_induction` will
    hand this shape back and it is worth having named. -/
theorem generator_spec {x : Clˣ} (hx : x ∈ ((↑) ⁻¹' Set.range (ι Q₁₃) : Set Clˣ)) :
    ∃ v : V, (x : Cl) = ι Q₁₃ v := by
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, hv.symm⟩

/-- …and such a vector is necessarily non-null, because `x` is a unit and
    `ι(v)² = Q₁₃(v)`. The induction's base case needs this: `vreflect` is
    only a reflection away from the null cone. -/
theorem generator_not_null {x : Clˣ} {v : V} (hxv : (x : Cl) = ι Q₁₃ v) :
    Q₁₃ v ≠ 0 := by
  intro hzero
  have hsq : (x : Cl) * (x : Cl) = 0 := by
    rw [hxv, ι_sq_scalar, hzero, map_zero]
  have hx0 : (x : Cl) = 0 := by
    have h := congrArg (fun a : Cl => a * ((x⁻¹ : Clˣ) : Cl)) hsq
    simp only [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h
    exact h
  exact x.ne_zero hx0

end

end LipschitzVectorRep
