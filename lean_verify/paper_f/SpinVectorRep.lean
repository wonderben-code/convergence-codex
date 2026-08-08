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
     action and not merely a family of maps. Neither carries a spin
     hypothesis for the reader to discharge: `spinGroup_one_mem` and
     `spinGroup_mul_mem` prove them.
  6. **`spinToEndo_R₁₂`** — a completely computed example. `R₁₂ =
     ι(e₁)·ι(e₂)` is exhibited as a spin element (`R₁₂_mem`: Lipschitz,
     unitary, even) and its action on ℝ⁴ is computed in full to be
     `(t,x,y,z) ↦ (t,−x,−y,z)`, the rotation by π about the z-axis.
     `spinToEndo_R₁₂_ne_id` then says the representation is not
     trivial. Without this section every theorem above would be true
     of the trivial group and would say nothing.
  7. **`spinToEndo_neg`** — `x` and `−x` induce the same map, and −1 is
     itself a spin element (`neg_one_mem`) acting as the identity. So
     ±1 lies in the kernel and the covering is at least two-to-one.
     `R₁₂_sq` shows the same factor of two in one element: `R₁₂` has
     order 4, its image has order 2.

  NOT proven here, and the reason W7 keeps a residue. Of the three
  things step (d) needs —
    • that the image lands in the identity component SO⁺(1,3),
    • that the map is onto SO⁺(1,3),
    • that the kernel is exactly ±1,
  the first two are untouched, and of the third only the easy half is
  done: ±1 is IN the kernel (item 7). That the kernel is no LARGER than
  ±1 is not proved and does not follow from anything here. W7 marks the
  remainder research-level rather than bounded. This file is steps (b)
  and (c) plus a worked example; step (d) is not promised.

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

/-- The unit `1` is a spin element. Stated so that `spinToEndo_one`
    below carries no hypothesis for the reader to discharge. -/
theorem spinGroup_one_mem : ((1 : Clˣ) : Cl) ∈ spinGroup Q₁₃ := by
  rw [Units.val_one]
  exact one_mem _

/-- Spin elements are closed under multiplication, at the level of the
    units rather than of their images — again so that the action lemma
    below needs no supplied hypothesis. -/
theorem spinGroup_mul_mem {x y : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃)
    (hy : (y : Cl) ∈ spinGroup Q₁₃) : ((x * y : Clˣ) : Cl) ∈ spinGroup Q₁₃ := by
  rw [Units.val_mul]
  exact mul_mem hx hy

/-- The identity spin element acts as the identity. -/
theorem spinToEndo_one : spinToEndo spinGroup_one_mem = LinearMap.id :=
  LinearMap.ext fun v => ι_injective (by rw [ι_spinToEndo]; simp)

/-- The action is multiplicative: this is a genuine group action on ℝ⁴,
    not merely a family of isometries indexed by spin elements. -/
theorem spinToEndo_mul {x y : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃)
    (hy : (y : Cl) ∈ spinGroup Q₁₃) (v : V) :
    spinToEndo (spinGroup_mul_mem hx hy) v = spinToEndo hx (spinToEndo hy v) := by
  apply ι_injective
  rw [ι_spinToEndo, ι_spinToEndo, ι_spinToEndo]
  simp [mul_assoc]

/-! ## 5. Non-vacuity: a spin element that actually moves ℝ⁴

Everything above would be true, and useless, if `spinGroup Q₁₃` were
`{1}` or `{±1}` — the action would exist and be trivial. This section
rules that out by construction. It exhibits one explicit spin element
and computes its action completely.

`R₁₂ = ι e₁ · ι e₂`, the product of the two spacelike unit vectors in
the x- and y-directions. It is in the Lipschitz group because it is a
product of two generators; it is unitary because each factor squares to
−1 and the two signs cancel; it is even because it is a product of two
vectors. Its action on ℝ⁴ is `(t,x,y,z) ↦ (t,−x,−y,z)`: the rotation by
π about the z-axis. That map fixes the time axis, has determinant +1,
and is not the identity — so the representation built above is neither
trivial nor a disguised sign. -/

/-- The timelike unit vector. -/
def e₀ : V := ((1, 0), (0, 0))
/-- The spacelike unit vector in the x-direction. -/
def e₁ : V := ((0, 1), (0, 0))
/-- The spacelike unit vector in the y-direction. -/
def e₂ : V := ((0, 0), (1, 0))
/-- The spacelike unit vector in the z-direction. -/
def e₃ : V := ((0, 0), (0, 1))

theorem Q₁₃_e₀ : Q₁₃ e₀ = 1 := by rw [Q₁₃_apply]; norm_num [e₀]
theorem Q₁₃_e₁ : Q₁₃ e₁ = -1 := by rw [Q₁₃_apply]; norm_num [e₁]
theorem Q₁₃_e₂ : Q₁₃ e₂ = -1 := by rw [Q₁₃_apply]; norm_num [e₂]
theorem Q₁₃_e₃ : Q₁₃ e₃ = -1 := by rw [Q₁₃_apply]; norm_num [e₃]

/-- Orthogonal vectors anticommute in the Clifford algebra. -/
theorem ι_anticomm {a b : V} (h : QuadraticMap.polar Q₁₃ a b = 0) :
    ι Q₁₃ a * ι Q₁₃ b = - (ι Q₁₃ b * ι Q₁₃ a) := by
  have hs := ι_mul_ι_add_swap (Q := Q₁₃) a b
  rw [h, map_zero] at hs
  exact eq_neg_of_add_eq_zero_left hs

/-- Anticommutation in the shape the associativity-normalised goals need. -/
private theorem swapL {a b : V} (h : QuadraticMap.polar Q₁₃ a b = 0) (y : Cl) :
    ι Q₁₃ a * (ι Q₁₃ b * y) = - (ι Q₁₃ b * (ι Q₁₃ a * y)) := by
  rw [← mul_assoc, ι_anticomm h, neg_mul, mul_assoc]

/-- The Clifford relation in the same shape. -/
private theorem sqL (a : V) (y : Cl) :
    ι Q₁₃ a * (ι Q₁₃ a * y) = algebraMap ℝ Cl (Q₁₃ a) * y := by
  rw [← mul_assoc, ι_sq_scalar]

theorem polar_e₀_e₁ : QuadraticMap.polar Q₁₃ e₀ e₁ = 0 := by
  simp [QuadraticMap.polar, Q₁₃_apply, e₀, e₁]
theorem polar_e₀_e₂ : QuadraticMap.polar Q₁₃ e₀ e₂ = 0 := by
  simp [QuadraticMap.polar, Q₁₃_apply, e₀, e₂]
theorem polar_e₃_e₁ : QuadraticMap.polar Q₁₃ e₃ e₁ = 0 := by
  simp [QuadraticMap.polar, Q₁₃_apply, e₃, e₁]
theorem polar_e₃_e₂ : QuadraticMap.polar Q₁₃ e₃ e₂ = 0 := by
  simp [QuadraticMap.polar, Q₁₃_apply, e₃, e₂]
theorem polar_e₁_e₂ : QuadraticMap.polar Q₁₃ e₁ e₂ = 0 := by
  simp [QuadraticMap.polar, Q₁₃_apply, e₁, e₂]

theorem ι_e₁_sq : ι Q₁₃ e₁ * ι Q₁₃ e₁ = -1 := by
  rw [ι_sq_scalar, Q₁₃_e₁]; simp

theorem ι_e₂_sq : ι Q₁₃ e₂ * ι Q₁₃ e₂ = -1 := by
  rw [ι_sq_scalar, Q₁₃_e₂]; simp

/-- `ι e₁` as a unit: it squares to −1, so its inverse is its negative. -/
def U₁ : Clˣ where
  val := ι Q₁₃ e₁
  inv := - ι Q₁₃ e₁
  val_inv := by rw [mul_neg, ι_e₁_sq, neg_neg]
  inv_val := by rw [neg_mul, ι_e₁_sq, neg_neg]

/-- `ι e₂` as a unit. -/
def U₂ : Clˣ where
  val := ι Q₁₃ e₂
  inv := - ι Q₁₃ e₂
  val_inv := by rw [mul_neg, ι_e₂_sq, neg_neg]
  inv_val := by rw [neg_mul, ι_e₂_sq, neg_neg]

/-- **The witness.** The product of two orthogonal spacelike unit
    vectors: a rotation by π in the xy-plane. -/
def R₁₂ : Clˣ := U₁ * U₂

theorem R₁₂_val : (R₁₂ : Cl) = ι Q₁₃ e₁ * ι Q₁₃ e₂ := rfl

theorem R₁₂_inv : ((R₁₂⁻¹ : Clˣ) : Cl) = ι Q₁₃ e₂ * ι Q₁₃ e₁ := by
  change (-ι Q₁₃ e₂) * (-ι Q₁₃ e₁) = _
  rw [neg_mul_neg]

theorem U₁_mem : U₁ ∈ lipschitzGroup Q₁₃ := Subgroup.subset_closure ⟨e₁, rfl⟩
theorem U₂_mem : U₂ ∈ lipschitzGroup Q₁₃ := Subgroup.subset_closure ⟨e₂, rfl⟩

/-- `R₁₂` really is a spin element: Lipschitz, unitary, and even. -/
theorem R₁₂_mem : (R₁₂ : Cl) ∈ spinGroup Q₁₃ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact lipschitzGroup.coe_mem_iff_mem.2 (mul_mem U₁_mem U₂_mem)
  · change star (ι Q₁₃ e₁ * ι Q₁₃ e₂) * (ι Q₁₃ e₁ * ι Q₁₃ e₂) = 1
    rw [star_mul, star_ι, star_ι]
    calc -ι Q₁₃ e₂ * -ι Q₁₃ e₁ * (ι Q₁₃ e₁ * ι Q₁₃ e₂)
        = ι Q₁₃ e₂ * ((ι Q₁₃ e₁ * ι Q₁₃ e₁) * ι Q₁₃ e₂) := by
          simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = 1 := by rw [ι_e₁_sq]; simp [Q₁₃_e₂]
  · change (ι Q₁₃ e₁ * ι Q₁₃ e₂) * star (ι Q₁₃ e₁ * ι Q₁₃ e₂) = 1
    rw [star_mul, star_ι, star_ι]
    calc ι Q₁₃ e₁ * ι Q₁₃ e₂ * (-ι Q₁₃ e₂ * -ι Q₁₃ e₁)
        = ι Q₁₃ e₁ * ((ι Q₁₃ e₂ * ι Q₁₃ e₂) * ι Q₁₃ e₁) := by
          simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = 1 := by rw [ι_e₂_sq]; simp [Q₁₃_e₁]
  · exact ι_mul_ι_mem_evenOdd_zero Q₁₃ e₁ e₂

/-- A vector orthogonal to both e₁ and e₂ is fixed by the rotation. -/
private theorem conj_of_orth {a : V} (h1 : QuadraticMap.polar Q₁₃ a e₁ = 0)
    (h2 : QuadraticMap.polar Q₁₃ a e₂ = 0) :
    (R₁₂ : Cl) * ι Q₁₃ a * ((R₁₂⁻¹ : Clˣ) : Cl) = ι Q₁₃ a := by
  rw [R₁₂_val, R₁₂_inv]
  simp only [mul_assoc]
  rw [swapL h2, ι_anticomm h1]
  simp only [mul_neg, neg_neg]
  rw [sqL, Q₁₃_e₂]
  simp only [map_neg, map_one, neg_mul, one_mul, mul_neg]
  rw [sqL, Q₁₃_e₁]
  simp

theorem conj_e₀ : (R₁₂ : Cl) * ι Q₁₃ e₀ * ((R₁₂⁻¹ : Clˣ) : Cl) = ι Q₁₃ e₀ :=
  conj_of_orth polar_e₀_e₁ polar_e₀_e₂

theorem conj_e₃ : (R₁₂ : Cl) * ι Q₁₃ e₃ * ((R₁₂⁻¹ : Clˣ) : Cl) = ι Q₁₃ e₃ :=
  conj_of_orth polar_e₃_e₁ polar_e₃_e₂

theorem conj_e₁ : (R₁₂ : Cl) * ι Q₁₃ e₁ * ((R₁₂⁻¹ : Clˣ) : Cl) = - ι Q₁₃ e₁ := by
  rw [R₁₂_val, R₁₂_inv]
  simp only [mul_assoc]
  rw [swapL polar_e₁_e₂, sqL, Q₁₃_e₁]
  simp only [map_neg, map_one, neg_mul, one_mul, mul_neg, neg_neg]
  rw [sqL, Q₁₃_e₂]
  simp

theorem conj_e₂ : (R₁₂ : Cl) * ι Q₁₃ e₂ * ((R₁₂⁻¹ : Clˣ) : Cl) = - ι Q₁₃ e₂ := by
  rw [R₁₂_val, R₁₂_inv]
  simp only [mul_assoc]
  rw [sqL, Q₁₃_e₂]
  simp only [map_neg, map_one, neg_mul, one_mul, mul_neg]
  rw [swapL polar_e₁_e₂]
  simp only [neg_neg]
  rw [ι_sq_scalar, Q₁₃_e₁]
  simp

/-- Rotation by π about the z-axis: `(t,x,y,z) ↦ (t,−x,−y,z)`. -/
def rotXY : V → V := fun v => ((v.1.1, -v.1.2), (-v.2.1, v.2.2))

/-- **The action of `R₁₂` on ℝ⁴, computed in full.** -/
theorem spinToEndo_R₁₂ (v : V) : spinToEndo R₁₂_mem v = rotXY v := by
  apply ι_injective
  rw [ι_spinToEndo]
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  have hd : (((a, b), (c, d)) : V) = a • e₀ + b • e₁ + c • e₂ + d • e₃ := by
    simp [e₀, e₁, e₂, e₃]
  have hd' : (rotXY ((a, b), (c, d)) : V)
      = a • e₀ + (-b) • e₁ + (-c) • e₂ + d • e₃ := by
    simp [rotXY, e₀, e₁, e₂, e₃]
  rw [hd', hd]
  simp only [map_add, map_smul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
  rw [conj_e₀, conj_e₁, conj_e₂, conj_e₃]
  simp [smul_neg, neg_smul]

/-- The time axis is fixed. -/
theorem spinToEndo_R₁₂_e₀ : spinToEndo R₁₂_mem e₀ = e₀ := by
  rw [spinToEndo_R₁₂]; simp [rotXY, e₀]

/-- The x-axis is reversed. -/
theorem spinToEndo_R₁₂_e₁ : spinToEndo R₁₂_mem e₁ = -e₁ := by
  rw [spinToEndo_R₁₂]; simp [rotXY, e₁]

/-- **The representation is not trivial.** There is a spin element whose
    action on ℝ⁴ is not the identity, so the theorems above are about a
    genuine action and not an elaborate way of saying nothing. -/
theorem spinToEndo_R₁₂_ne_id : spinToEndo R₁₂_mem ≠ LinearMap.id := by
  intro h
  have h1 : spinToEndo R₁₂_mem e₁ = e₁ := by rw [h]; rfl
  rw [spinToEndo_R₁₂_e₁] at h1
  have h2 : ((-e₁ : V)).1.2 = (e₁ : V).1.2 := by rw [h1]
  norm_num [e₁] at h2

/-! ## 6. ±1 acts trivially: the covering is at least two-to-one

Step (d) — identifying the image of `spinToEndo` with SO⁺(1,3) — needs
three things: that the image lands in SO⁺(1,3), that the map is onto,
and that the kernel is exactly ±1. The first two are research-level and
are not attempted anywhere in this file. The third splits into two
halves, and the easy half is provable here: **±1 lies in the kernel**.
That −1 is itself a spin element, and that it acts as the identity, is
what makes the vector representation a representation of a group that
double-covers its image rather than an injection.

Nothing below claims the kernel is no larger than ±1. That inclusion is
the direction that needs the hard work, and it is not done. -/

theorem R₁₂_inv_eq_neg : ((R₁₂⁻¹ : Clˣ) : Cl) = - (R₁₂ : Cl) := by
  rw [R₁₂_inv, R₁₂_val, ι_anticomm polar_e₁_e₂, neg_neg]

/-- `R₁₂` squares to −1, so it has order 4 in the spin group while its
    image — rotation by π — has order 2. The factor of two is visible
    here in a single element. -/
theorem R₁₂_sq : (R₁₂ : Cl) * (R₁₂ : Cl) = -1 := by
  have h1 : (R₁₂ : Cl) * ((R₁₂⁻¹ : Clˣ) : Cl) = 1 := R₁₂.mul_inv
  rw [R₁₂_inv_eq_neg, mul_neg] at h1
  exact neg_eq_iff_eq_neg.mp h1

/-- −1 is a spin element: it is `(ι e₁)²`, hence Lipschitz; it is
    self-inverse, hence unitary; and it is even. -/
theorem neg_one_mem : ((-1 : Clˣ) : Cl) ∈ spinGroup Q₁₃ := by
  have hU : (-1 : Clˣ) = U₁ * U₁ := by
    refine Units.ext ?_
    rw [Units.val_mul]
    exact ι_e₁_sq.symm
  have hval : ((-1 : Clˣ) : Cl) = -1 := by simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact lipschitzGroup.coe_mem_iff_mem.2 (hU ▸ mul_mem U₁_mem U₁_mem)
  · simp
  · simp
  · rw [hval, ← ι_e₁_sq]
    exact ι_mul_ι_mem_evenOdd_zero Q₁₃ e₁ e₁

/-- Negation stays inside the spin group. -/
theorem spinGroup_neg_mem {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) :
    ((-x : Clˣ) : Cl) ∈ spinGroup Q₁₃ := by
  have h : ((-x : Clˣ) : Cl) = ((-1 : Clˣ) : Cl) * (x : Cl) := by simp
  rw [h]
  exact mul_mem neg_one_mem hx

/-- **−1 acts as the identity.** The two signs in the conjugation
    cancel. -/
theorem spinToEndo_neg_one : spinToEndo neg_one_mem = LinearMap.id :=
  LinearMap.ext fun v => ι_injective (by rw [ι_spinToEndo]; simp)

/-- **The covering is two-to-one everywhere, not just at the identity:**
    `x` and `−x` induce the same map on ℝ⁴. -/
theorem spinToEndo_neg {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) (v : V) :
    spinToEndo (spinGroup_neg_mem hx) v = spinToEndo hx v := by
  apply ι_injective
  rw [ι_spinToEndo, ι_spinToEndo]
  simp

/-- And the two elements really are distinct, so "two-to-one" is not
    "one-to-one written twice". -/
theorem R₁₂_ne_neg_R₁₂ : (R₁₂ : Cl) ≠ ((-R₁₂ : Clˣ) : Cl) := by
  intro h
  rw [Units.val_neg] at h
  have h2 : (2 : ℝ) • (R₁₂ : Cl) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    simp
  rw [smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · norm_num at h2
  · exact R₁₂.ne_zero h2

/-- And `R₁₂` is not 1 in the algebra either — the nontriviality is in
    the group element, not smuggled in by the transport. -/
theorem R₁₂_ne_one : (R₁₂ : Cl) ≠ 1 := by
  intro h
  have := spinToEndo_R₁₂_ne_id
  apply this
  refine LinearMap.ext fun v => ι_injective ?_
  rw [ι_spinToEndo, h]
  have hinv : ((R₁₂⁻¹ : Clˣ) : Cl) = 1 := by
    rw [← Units.val_one (α := Cl)]
    congr 1
    rw [inv_eq_one, ← Units.val_eq_one, h]
  rw [hinv]
  simp

end SpinVectorRep
