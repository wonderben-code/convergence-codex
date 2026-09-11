import FieldAffineMapSymmetry

/-!
# The affine symmetries bundled, and no translation among them

`FieldAffineMapSymmetry` classified the affine symmetries of the Gaussian field —
`gaussianField_map_affine_iff_linear`: an affine map is a symmetry **iff** it fixes the origin and
its linear part is one, taking no hypothesis on the mass — and then fenced what it had not done:
*`bijective_affine_of_map` proves the underlying function is a bijection and **no `AffineEquiv` is
constructed**; the affine symmetries are not bundled as a group of any kind.* **This file bundles
them and draws the corollary the classification was one step from.**

**`affineSymmetrySubmonoid`** is a `Submonoid (E →ᵃ[ℝ] E)` — affine maps carry a `Monoid` instance
under composition, so this is the same choice `FieldSymmetryGroup.symmetrySubmonoid` and
`FieldSymmetryIso.linSym` make, and it takes **no hypothesis on the mass**. The two closure proofs
are `MeasureTheory.Measure.map_map` through `AffineMap.continuous_of_finiteDimensional`: an affine
map on a finite-dimensional space is continuous, hence measurable, which is the only analysis in
the file.

**`constVAdd_symmetry_iff`** is the corollary: **a translation is a symmetry if and only if it is
the identity.** The Gaussian field is centred, so the only vector it can be translated by is zero —
`gaussianField_map_affine_iff_linear`'s *fixes the origin* clause is the whole proof, and it needs
no mass, no graph and no covariance. **`affineSymmetrySubgroup`** carries the bundling into
`E ≃ᵃ[ℝ] E`, where Mathlib's `Group` instance supplies the inverse — **so it takes no mass either**,
the same reason `FieldSymmetrySubgroup.symmetrySubgroup` does not — and
`mem_affineSymmetrySubgroup_constVAdd_iff` is the translation statement there.

**AND THE TWO BUNDLINGS HAVE THE SAME ELEMENTS**, which is the one place a mass is needed and the
reason they are two objects rather than one: `toAffineMap_mem_submonoid` is free, while
`exists_equiv_of_mem_submonoid` needs every affine symmetry to be BIJECTIVE, which is
`FieldAffineMapSymmetry.bijective_affine_of_map` and which needs the covariance non-degenerate. So
the `Subgroup` exists at every mass and is known to exhaust the `Submonoid` only away from zero.

## Which symmetry group this is, because the estate holds two

**The affine symmetries reduce to the LINEAR ones, and those are NOT the isometric ones.** An
affine symmetry fixes the origin, so it *is* its linear part (`eq_linear_of_mem`); the linear
symmetries of this field are `FieldSymmetryIso.linSym`, which `FieldSymmetryIso.conjSqEquiv` makes
isomorphic to the **full** orthogonal group `Matrix.unitaryGroup V ℝ` at every graph. They are
**not** `FieldRotationCount.symmetryMatrices`, whose structure is
`FieldBlockProduct.symmetry_mulEquiv_prod`'s product `∏ᵢ O(dᵢ)` over the propagator's distinct
eigenvalues. So **the product decomposition of the last four units does not apply here**, and a
reader who composes them gets the wrong group. `FieldSymmetryProper.symmetryMatrices_eq_linSym_iff`
says exactly when the two coincide.

## What is NOT here

* **No isomorphism onto `linSym`.** `eq_linear_of_mem` says an affine symmetry equals its linear
  part as a FUNCTION; turning that into `affineSymmetrySubmonoid ≃* linSym G m` needs the passage
  from a linear map on `EuclideanSpace ℝ V` to a matrix, which is `Matrix.toEuclideanLin` and which
  `FieldAffineMapSymmetry`'s own item records as **not invoked** anywhere in this chain. **Not
  attempted, 11 September 2026**, and no cost is claimed (`ERRATUM 246`).
* **No cardinality.** The linear symmetry group is the full orthogonal group, infinite as soon as
  `|V| ≥ 2`, so there is no count to make and `FieldSymmetryCount`'s `2 ^ |V|` is about the
  isometric group and does not transfer.
* **No `MulEquiv` between the `Submonoid` and the `Subgroup`.** §5 gives the two inclusions —
  every equivalence is a map, and at a non-zero mass every map in the monoid comes from an
  equivalence — but not a bundled isomorphism, which would need the map `e ↦ e.toAffineMap` shown
  injective on the carrier and a choice of inverse. **Not attempted, 11 September 2026**, and no
  cost is claimed (`ERRATUM 246`).
* **Nothing about non-affine maps.** The full automorphism group of the measure is untouched,
  unchanged since `FieldLinearClassified` said so.

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype V]` and `[DecidableEq V]`
throughout. **`m ≠ 0` is taken by exactly ONE of the eleven declarations** —
`exists_equiv_of_mem_submonoid` — and the reason is worth stating, because the first draft of this
paragraph guessed two and guessed wrong before `binder_scan.py` read the binders: **the `Subgroup`
needs no mass**, its inverses coming from the ambient group, and the mass is needed only to show
that every affine symmetry is invertible and so that the `Submonoid` has no elements the `Subgroup`
lacks. The other ten hold at every mass **including zero**, where they say the massless field's
affine symmetries are a monoid and a group containing no translation but the identity.
`measurable_coe` and `measurable_equiv` take no graph either.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldAffineGroup

open Matrix GraphLaplacian MeasureTheory FieldAffineMapSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Affine maps on a finite-dimensional space are measurable -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The only analysis in this file: an affine map on `EuclideanSpace ℝ V` is continuous because the
space is finite-dimensional, hence measurable, which is what `Measure.map_map` asks for. -/
theorem measurable_coe (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
    Measurable (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) :=
  (AffineMap.continuous_of_finiteDimensional f).measurable

/-! ## 2. The affine symmetries as a `Submonoid` -/

/-- **THE AFFINE SYMMETRIES OF THE GAUSSIAN FIELD AS A `Submonoid`**, for any mass. Affine maps
compose, `Measure.map_map` turns that into composition of pushforwards, and measurability is §1. -/
def affineSymmetrySubmonoid (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Submonoid (EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) where
  carrier := {f | Measure.map f (gaussianField G m) = gaussianField G m}
  one_mem' := by
    change Measure.map ((1 : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
      EuclideanSpace ℝ V → EuclideanSpace ℝ V) (gaussianField G m) = gaussianField G m
    simp
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [show ((f * g : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
        EuclideanSpace ℝ V → EuclideanSpace ℝ V)
      = (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) ∘ g from rfl,
      ← Measure.map_map (measurable_coe f) (measurable_coe g), hg, hf]

@[simp] theorem mem_affineSymmetrySubmonoid
    {f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V} :
    f ∈ affineSymmetrySubmonoid G m ↔ Measure.map f (gaussianField G m) = gaussianField G m :=
  Iff.rfl

/-- **AN AFFINE SYMMETRY IS ITS OWN LINEAR PART.** It fixes the origin, and an affine map fixing
the origin is its linear part as a function. -/
theorem eq_linear_of_mem {f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V}
    (hf : f ∈ affineSymmetrySubmonoid G m) :
    (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) = f.linear :=
  coe_eq_linear f (apply_zero_of_map f hf)

/-! ## 3. No translation is a symmetry, except the identity -/

/-- **A TRANSLATION IS A SYMMETRY IF AND ONLY IF IT IS THE IDENTITY.** The Gaussian field is
centred, so the only vector it can be translated by is zero. **No mass, no graph, no covariance**
— the *fixes the origin* clause of `gaussianField_map_affine_iff_linear` is the whole argument. -/
theorem constVAdd_symmetry_iff (v : EuclideanSpace ℝ V) :
    Measure.map (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ V) v :
        EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) (gaussianField G m) = gaussianField G m
      ↔ v = 0 := by
  constructor
  · intro h
    have h0 := apply_zero_of_map _ h
    simpa using h0
  · intro hv
    subst hv
    have : ((AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ V) (0 : EuclideanSpace ℝ V)) :
        EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) = AffineMap.id ℝ (EuclideanSpace ℝ V) := by
      ext x
      simp
    rw [this]
    simp

/-! ## 4. The affine symmetries as a `Subgroup` of the affine equivalences -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- An affine equivalence and its inverse are both measurable, being affine maps. -/
theorem measurable_equiv (f : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
    Measurable (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) :=
  measurable_coe f.toAffineMap

/-- **THE AFFINE SYMMETRIES AS A `Subgroup`**, of Mathlib's group of affine equivalences. **No
hypothesis on the mass**: the inverse is supplied by the ambient group, and the proof that it lands
back in the carrier is `Measure.map_map` applied to `f⁻¹ ∘ f = id` — the same shape as
`FieldSymmetrySubgroup.symmetrySubgroup`, where the transpose played the part `f⁻¹` plays here. -/
def affineSymmetrySubgroup (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Subgroup (EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) where
  carrier := {f | Measure.map (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V)
    (gaussianField G m) = gaussianField G m}
  one_mem' := by
    simp
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [show ((f * g : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
        EuclideanSpace ℝ V → EuclideanSpace ℝ V)
      = (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) ∘ g from rfl,
      ← Measure.map_map (measurable_equiv f) (measurable_equiv g), hg, hf]
  inv_mem' {f} hf := by
    simp only [Set.mem_setOf_eq] at hf ⊢
    calc Measure.map ((f⁻¹ : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
            EuclideanSpace ℝ V → EuclideanSpace ℝ V) (gaussianField G m)
        = Measure.map ((f⁻¹ : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
            EuclideanSpace ℝ V → EuclideanSpace ℝ V)
            (Measure.map (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V) (gaussianField G m)) := by
          rw [hf]
      _ = Measure.map (((f⁻¹ : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
            EuclideanSpace ℝ V → EuclideanSpace ℝ V) ∘ f) (gaussianField G m) :=
          Measure.map_map (measurable_equiv f⁻¹) (measurable_equiv f)
      _ = gaussianField G m := by
          rw [show (((f⁻¹ : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V) :
              EuclideanSpace ℝ V → EuclideanSpace ℝ V) ∘ f) = id from
              funext fun x => f.symm_apply_apply x]
          simp

@[simp] theorem mem_affineSymmetrySubgroup
    {f : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V} :
    f ∈ affineSymmetrySubgroup G m ↔
      Measure.map (f : EuclideanSpace ℝ V → EuclideanSpace ℝ V)
        (gaussianField G m) = gaussianField G m := Iff.rfl

/-- **AND NO TRANSLATION LIES IN IT EXCEPT THE IDENTITY**, the group form of §3. -/
theorem mem_affineSymmetrySubgroup_constVAdd_iff (v : EuclideanSpace ℝ V) :
    AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ V) v ∈ affineSymmetrySubgroup G m ↔ v = 0 :=
  constVAdd_symmetry_iff v

/-! ## 5. The monoid and the group have the same elements -/

/-- Every member of the `Subgroup` is a member of the `Submonoid`, forgetting invertibility. No
mass: the two carriers are the same condition on the same underlying function. -/
theorem toAffineMap_mem_submonoid {f : EuclideanSpace ℝ V ≃ᵃ[ℝ] EuclideanSpace ℝ V}
    (hf : f ∈ affineSymmetrySubgroup G m) :
    (f.toAffineMap) ∈ affineSymmetrySubmonoid G m := by
  simpa only [mem_affineSymmetrySubmonoid, AffineEquiv.coe_toAffineMap] using hf

/-- **AND CONVERSELY, AT A NON-ZERO MASS, EVERY MEMBER OF THE `Submonoid` IS ONE.** Every affine
symmetry is bijective (`FieldAffineMapSymmetry.bijective_affine_of_map`), so it IS an affine
equivalence. **This is the only place in the file the mass is used, and it is the only place it is
needed**: the `Subgroup` of §4 gets its inverses from the ambient group and takes no hypothesis,
while identifying its elements with the `Submonoid`'s needs the covariance non-degenerate. -/
theorem exists_equiv_of_mem_submonoid (hm : m ≠ 0)
    {f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V}
    (hf : f ∈ affineSymmetrySubmonoid G m) :
    ∃ e ∈ affineSymmetrySubgroup G m,
      (e : EuclideanSpace ℝ V → EuclideanSpace ℝ V) = f := by
  refine ⟨AffineEquiv.ofBijective (bijective_affine_of_map hm f hf), ?_, rfl⟩
  simpa only [mem_affineSymmetrySubgroup] using hf

end FieldAffineGroup
