import FieldAffineMapSymmetry
import FieldInvarianceCommutes
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Linearity was not a hypothesis of the isometry chain either: it is a consequence

Every symmetry result in this chain that speaks of an isometry takes a **linear** isometry.
**Fourteen** files in `paper_f` mention `EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V` and **nine**
of them — `FieldCommutant`, `FieldHouseholder`, `FieldInvarianceCommutes`, `FieldLineCount`,
`FieldLinearSymmetry`, `FieldMassNecessity`, `FieldOrthIsometry`, `FieldSimpleCriterion`,
`FieldSimpleSpectrum` — do so in a statement about `Measure.map` (counted, not sampled;
`ERRATUM 450`). **The linearity need not be assumed.** A distance-preserving bijection of `ℝ^V`
that preserves the Gaussian field is linear whether you ask it to be or not.

## What is proved

**`coe_isometryEquiv_eq_affMap`** — a distance-preserving bijection is an `affMap`: Mathlib's
`IsometryEquiv.toRealLinearIsometryEquiv_apply` says `f x - f 0` is linear, which is
`FieldAffineSymmetry.affMap` of that linear part and the translation `f 0`.

**`isometryEquiv_apply_zero_of_map`** — **so a distance-preserving symmetry fixes the origin.** At
every mass, on every graph, by the previous unit's mean argument and nothing else.

**`exists_linearIsometryEquiv_of_map`** — **AND IS THEREFORE LINEAR**: there is a linear isometry
equivalence with the same underlying function. **No hypothesis on the mass.**

**`gaussianField_map_isometryEquiv_iff`** — **the classification with linearity derived rather than
assumed**: a distance-preserving bijection preserves the Gaussian field **iff** it fixes the origin
and commutes with the propagator. `FieldInvarianceCommutes.gaussianField_map_iff_commutes` supplies
the second half, for the linear isometry this file produces.

## HOW THE WORK IS DIVIDED, because the headline invites a wrong reading

**The Gaussian field supplies exactly one fact here: that the origin is fixed.** Everything after
that is **Mazur–Ulam** — `IsometryEquiv.toRealLinearIsometryEquivOfMapZero`, which makes *any*
distance-preserving bijection of a real normed space fixing `0` into a linear isometry, with no
measure anywhere in sight. It is **not** the case that the field's structure forces its symmetries
to be linear; what the field does is refuse to be translated, and a theorem of 1932 does the rest.
Saying otherwise would credit the covariance with a result about normed spaces.

## What is NOT here

**BIJECTIVITY IS ASSUMED, AND IT IS A REAL HYPOTHESIS HERE.** `IsometryEquiv` is a distance-
preserving **bijection**. That a distance-preserving map of a finite-dimensional Euclidean space
into itself is automatically surjective is true and **is not proved here**; Mathlib was searched for
it and it is not there — every `ofSurjective` constructor takes surjectivity as **input**, and
`LinearIsometry.toLinearIsometryEquiv`, which does derive it from equal `finrank`, needs the map to
be linear already, which is what this file is trying to conclude. **A search, not an impression**
(`ERRATUM 450`). Not attempted, no cost claimed (`ERRATUM 246`).
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`, `ERRATUM 463`):
`InnerIsometryOnto.surjective` proves it, and **without Mazur–Ulam**. The search above was right and
the *framing* was wrong: the statement filed as missing is the **normed**-space one, which is indeed
not in Mathlib; the estate's objects form an **inner product** space, where polarisation gives
linearity directly and no surjectivity is assumed.
`InnerIsometryOnto.gaussianField_map_isometry_iff` restates this file's classification for an
`Isometry`. **The normed-space question is still open and still not in Mathlib** — it was simply
never the blocker.

**NOTHING ABOUT MAPS THAT ARE NEITHER LINEAR NOR ISOMETRIC.** What is removed is the *linearity*
assumption from the isometry chain; the *isometry* assumption stays and is doing all the work.
`FieldSqrtConjugation.exists_nonIsometric` already exhibits a linear symmetry that is not an
isometry, so the isometric symmetries are a **proper** part of the linear ones, and the full
automorphism group of the measure remains untouched.

**NOTHING IS BUNDLED.** No group of isometric symmetries is constructed here, and
`FieldSymmetryIso.conjSqEquiv` is not extended.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
hypothesis shown unnecessary in finite volume leaves the shadow where it was.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`gaussianField_map_isometryEquiv_iff` alone — **one of the four** — and only because
`FieldInvarianceCommutes` takes it. **The three that matter for the headline take no hypothesis on
the mass**, the degenerate `m = 0` included. `coe_isometryEquiv_eq_affMap` `omit`s
`[DecidableEq V]` and `[DecidableRel G.Adj]`: it mentions no graph and no measure.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldIsometryLinear

open Matrix GraphLaplacian MeasureTheory FieldSqrtConjugation FieldLinearClassified
  FieldSymmetryIso FieldAffineSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A distance-preserving bijection is an `affMap` -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem coe_isometryEquiv_eq_affMap (f : EuclideanSpace ℝ V ≃ᵢ EuclideanSpace ℝ V) :
    ⇑f = affMap f.toRealLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap (f 0) := by
  funext x
  rw [affMap_apply]
  change f x = f.toRealLinearIsometryEquiv x + f 0
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, sub_add_cancel]

/-! ## 2. So it fixes the origin -/

theorem isometryEquiv_apply_zero_of_map (f : EuclideanSpace ℝ V ≃ᵢ EuclideanSpace ℝ V)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) : f 0 = 0 := by
  rw [coe_isometryEquiv_eq_affMap f] at h
  exact eq_zero_of_map_affMap _ _ h

/-! ## 3. And is therefore linear -/

theorem exists_linearIsometryEquiv_of_map (f : EuclideanSpace ℝ V ≃ᵢ EuclideanSpace ℝ V)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) :
    ∃ g : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V, ⇑g = ⇑f :=
  ⟨f.toRealLinearIsometryEquivOfMapZero (isometryEquiv_apply_zero_of_map f h),
    IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero _ _⟩

/-! ## 4. The classification, with linearity derived rather than assumed -/

theorem gaussianField_map_isometryEquiv_iff (hm : m ≠ 0)
    (f : EuclideanSpace ℝ V ≃ᵢ EuclideanSpace ℝ V) :
    Measure.map f (gaussianField G m) = gaussianField G m ↔
      f 0 = 0 ∧ ∀ x : EuclideanSpace ℝ V,
        RayleighMatrix.mv (green G m) (f x) = f (RayleighMatrix.mv (green G m) x) := by
  constructor
  · intro h
    have h0 : f 0 = 0 := isometryEquiv_apply_zero_of_map f h
    have hcoe : ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = ⇑f :=
      IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero _ _
    rw [← hcoe] at h ⊢
    exact ⟨h0, (FieldInvarianceCommutes.gaussianField_map_iff_commutes hm _).mp h⟩
  · rintro ⟨h0, hc⟩
    have hcoe : ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = ⇑f :=
      IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero _ _
    rw [← hcoe] at hc ⊢
    exact (FieldInvarianceCommutes.gaussianField_map_iff_commutes hm _).mpr hc

end FieldIsometryLinear
