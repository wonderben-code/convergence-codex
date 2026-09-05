import FieldSymmetryIso

/-!
# Two hypotheses removed: the symmetry may be affine, and its linear part need not be continuous

`FieldSymmetryIso` classified the symmetries of the Gaussian field among **continuous linear** maps.
Two words in that sentence are hypotheses, and this file removes one each.

## What is proved

**`affMap`, `affMap_apply`, `affMap_zero`, `measurable_affMap`** — an affine self-map of `ℝ^V` as a
continuous linear part plus a translation, and it is measurable.

**`integral_id_gaussianField`** — the field's mean, **as a vector**, is `0`. This estate has had the
fact since `gaussianField` was defined and had **never named it**: `GraphLaplacian.integral_eval`
derives it inline as a `have`, and `LatticeGeneratingFunctional.integral_pair` re-derives it through
`gaussianField, integral_id_multivariateGaussian` (two sites, counted — `ERRATUM 450`; two further
sites do the same for `latticeField` and `fieldMeasure`, which are different measures). What was
named before was the mean of a **coordinate** (`integral_eval`) and of a **pairing**
(`integral_pair`), never of the point itself.

**`integral_affMap`** — the mean of an affine image is the image of the mean, by
`ContinuousLinearMap.integral_comp_comm` against `IsGaussian.integrable_id`.

**`eq_zero_of_map_affMap`** — **so no translation survives**: if an affine map preserves the field
then its translation is zero. **This takes no hypothesis on the mass at all**, because being centred
is a property of `multivariateGaussian 0 _` whatever the covariance turns out to be. It therefore
covers the degenerate `m = 0`, where `FieldMassNecessity.gaussianField_zero` — which needs
`[Nonempty V]`, not needed here — says the field is the point mass at the origin, and translating a
point mass visibly moves it. That illustration is **not** what proves the theorem; the mean is.

**`gaussianField_map_affMap_iff`** — **THE AFFINE SYMMETRIES ARE EXACTLY THE LINEAR ONES.** An
affine map preserves the Gaussian field **iff** its translation vanishes and its linear part is a
conjugated orthogonal matrix. Allowing translations does not enlarge the symmetry group.

**`gaussianField_map_linearMap_iff`** — **and continuity was not a hypothesis either.** The
classification holds for a bare `→ₗ[ℝ]` map, through `LinearMap.toContinuousLinearMap` being a
`LinearEquiv` in finite dimension; the conclusion is stated at the level of
`Matrix.toEuclideanLin`, so no coercion is being read across.

**`gaussianField_map_add_const_iff`** — the extreme case on its own: a pure translation preserves
the field **iff** it is the identity. No hypothesis on the mass.

## What is NOT here

**AFFINE IS NOT NON-LINEAR.** The full automorphism group of the measure — arbitrary measurable
bijections preserving it — is **still untouched**, and it is enormous. What is proved is that the
symmetries do not grow when the maps are allowed a constant term, which is a statement about one
extra parameter and not about non-linear maps of any kind.

**THE TWO REMOVALS ARE NOT COMBINED.** `gaussianField_map_affMap_iff` takes a
`ContinuousLinearMap` part; `gaussianField_map_linearMap_iff` drops continuity but has no
translation. **An affine map with a merely-linear part is not stated**, and no `AffineMap` from
Mathlib is used — `affMap` is a bare function. Not attempted, no cost claimed (`ERRATUM 246`).
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`):
`FieldAffineMapSymmetry.gaussianField_map_affine_iff` takes `f : E →ᵃ[ℝ] E`, whose linear part is a
bare `→ₗ[ℝ]`, so **all three clauses are answered at once** — Mathlib's `AffineMap` is adopted, the
merely-linear part is stated, and the two removals are combined. **The fence was right that the
route was the bundling**: the whole file is `AffineMap.decomp` plus this file's two theorems.

**NO CARDINALITY**, unchanged: the isomorphism of `FieldSymmetryIso` moves every counting question
onto `Matrix.unitaryGroup V ℝ`, and `FieldLineCount`'s `2^(k+1)` is still a count of the
**isometric** symmetries only.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
symmetry group that does not grow under translation, in finite volume, is a shadow that does not
grow.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`gaussianField_map_affMap_iff` and `gaussianField_map_linearMap_iff` — **two of the ten**, and both
only because they invoke `FieldSymmetryIso`'s classification, which needs `green` **positive
definite** — that is what `FieldSqrtConjugation.sqGreen_det_isUnit` uses to invert the square
root, and `green_posDef` is where `m ≠ 0` is spent. Every
other declaration, **including the whole no-translation argument**, is free of it. Three `omit`
`[DecidableEq V]`: `affMap_apply`, `affMap_zero` and `measurable_affMap`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldAffineSymmetry

open Matrix GraphLaplacian MeasureTheory ProbabilityTheory FieldSqrtConjugation
  FieldLinearClassified FieldSymmetryIso

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Affine maps of `ℝ^V` -/

/-- An affine self-map of `ℝ^V`: a continuous linear part and a translation. -/
noncomputable def affMap (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
    (b : EuclideanSpace ℝ V) : EuclideanSpace ℝ V → EuclideanSpace ℝ V :=
  fun x => T x + b

omit [DecidableEq V] in
@[simp] theorem affMap_apply (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
    (b x : EuclideanSpace ℝ V) : affMap T b x = T x + b := rfl

omit [DecidableEq V] in
@[simp] theorem affMap_zero (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    affMap T 0 = T := by
  ext x
  simp [affMap]

omit [DecidableEq V] in
theorem measurable_affMap (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
    (b : EuclideanSpace ℝ V) : Measurable (affMap T b) := by
  unfold affMap
  fun_prop

/-! ## 2. The field is centred, and an affine image has the obvious mean -/

theorem integral_id_gaussianField (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    ∫ x, x ∂(gaussianField G m) = 0 :=
  integral_id_multivariateGaussian

theorem integral_affMap (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
    (b : EuclideanSpace ℝ V) :
    ∫ x, affMap T b x ∂(gaussianField G m) = T (∫ x, x ∂(gaussianField G m)) + b := by
  have hint : Integrable (fun x : EuclideanSpace ℝ V => x) (gaussianField G m) :=
    IsGaussian.integrable_id
  simp only [affMap]
  rw [integral_add (T.integrable_comp hint) (integrable_const b),
    ContinuousLinearMap.integral_comp_comm T hint, integral_const]
  simp

/-! ## 3. So the translation must vanish -/

theorem eq_zero_of_map_affMap (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
    (b : EuclideanSpace ℝ V)
    (h : Measure.map (affMap T b) (gaussianField G m) = gaussianField G m) : b = 0 := by
  have h1 : ∫ x, x ∂(Measure.map (affMap T b) (gaussianField G m))
      = ∫ x, affMap T b x ∂(gaussianField G m) :=
    integral_map (measurable_affMap T b).aemeasurable (by fun_prop)
  rw [h, integral_affMap, integral_id_gaussianField] at h1
  simpa using h1.symm

/-! ## 4. So the affine symmetries are exactly the linear ones -/

theorem gaussianField_map_affMap_iff (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) (b : EuclideanSpace ℝ V) :
    Measure.map (affMap T b) (gaussianField G m) = gaussianField G m ↔
      b = 0 ∧ ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ mvCLM (conjSq G m O) = T := by
  constructor
  · intro h
    obtain rfl := eq_zero_of_map_affMap T b h
    rw [affMap_zero] at h
    exact ⟨rfl, (gaussianField_map_iff_exists_orthogonal hm T).mp h⟩
  · rintro ⟨rfl, hO⟩
    rw [affMap_zero]
    exact (gaussianField_map_iff_exists_orthogonal hm T).mpr hO

/-! ## 5. And the linear part need not be assumed continuous -/

theorem gaussianField_map_linearMap_iff (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) :
    Measure.map T (gaussianField G m) = gaussianField G m ↔
      ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ Matrix.toEuclideanLin (conjSq G m O) = T := by
  constructor
  · intro h
    obtain ⟨O, hO, hOT⟩ :=
      (gaussianField_map_iff_exists_orthogonal hm (LinearMap.toContinuousLinearMap T)).mp h
    exact ⟨O, hO, LinearMap.toContinuousLinearMap.injective hOT⟩
  · rintro ⟨O, hO, hOT⟩
    exact (gaussianField_map_iff_exists_orthogonal hm
      (LinearMap.toContinuousLinearMap T)).mpr ⟨O, hO, congrArg _ hOT⟩

/-! ## 6. In particular, no translation at all -/

theorem gaussianField_map_add_const_iff (b : EuclideanSpace ℝ V) :
    Measure.map (fun x => x + b) (gaussianField G m) = gaussianField G m ↔ b = 0 := by
  constructor
  · intro h
    refine eq_zero_of_map_affMap (G := G) (m := m)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ V)) b ?_
    simpa [affMap] using h
  · rintro rfl
    have hid : (fun x : EuclideanSpace ℝ V => x + 0) = id := by
      ext x
      simp
    rw [hid, Measure.map_id]

end FieldAffineSymmetry
