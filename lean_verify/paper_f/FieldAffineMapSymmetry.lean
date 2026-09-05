import FieldAffineSymmetry

/-!
# The joint the previous unit left unglued: a bundled affine map, with no continuity assumed

`FieldAffineSymmetry` removed two hypotheses from `FieldSymmetryIso`'s classification and **did not
remove them together**, and said so in its own fence: *the affine theorem's linear part is a
`ContinuousLinearMap`, the continuity-free theorem has no translation, and Mathlib's `AffineMap` is
not used.* **All three are answered here**, by taking `f : E →ᵃ[ℝ] E` — whose linear part is a bare
`→ₗ[ℝ]`, so adopting Mathlib's bundling *is* the combination.

## What is proved

**`coe_eq_affMap`** — Mathlib's affine map is this estate's `affMap`, by `AffineMap.decomp`:
`f = f.linear + f 0`. **`coe_eq_linear`** — and an affine map that fixes the origin **is** its own
linear part, as a function.

**`apply_zero_of_map`** — **EVERY AFFINE SYMMETRY OF THE GAUSSIAN FIELD FIXES THE ORIGIN.** On every
graph, at **every** mass — the degenerate `m = 0` included. Nothing about the covariance is used;
the field is centred, and a map that moves the origin moves the mean.

**`gaussianField_map_affine_iff_linear`** — **so an affine map is a symmetry IFF it fixes the origin
and its linear part is a symmetry.** This separates the two questions completely and **takes no
hypothesis on the mass or the covariance** — no `m ≠ 0`, no classification, no positive
definiteness, only the instances every statement in the file carries. It is the sharpest statement
here and the cheapest.

**`gaussianField_map_affine_iff`** — **and then the classification, combined**: an affine map
preserves the Gaussian field **iff** it fixes the origin and its linear part is
`Matrix.toEuclideanLin (C^{1/2} O C^{-1/2})` for an orthogonal `O`. The linear part is **not**
assumed continuous; `FieldAffineSymmetry.gaussianField_map_linearMap_iff` supplies that half.

**`bijective_affine_of_map`** — **and an affine symmetry is a bijection**, through
`FieldLinearSymmetry.bijective_of_map` once the origin is known fixed. Named
`bijective_affine_of_map` rather than `bijective_of_map` because that name is taken in
`FieldLinearSymmetry`, which this file imports transitively and uses; `newnames_scan` flagged the
collision and the rename is the answer to it.

## What is NOT here

**NO `AffineEquiv`.** `bijective_affine_of_map` proves the underlying function is a bijection; **no
`AffineEquiv` is constructed**, and the affine symmetries are **not** bundled as a group of any
kind. `FieldSymmetryIso.conjSqEquiv` bundles the *linear* symmetries and nothing here extends it.
Not attempted, no cost claimed (`ERRATUM 246`).

**STILL NOTHING NON-LINEAR.** An affine map is a linear map plus a constant, and this file's own
headline is that the constant must vanish. **The full automorphism group of the measure — arbitrary
measurable bijections preserving it — remains untouched and is enormous.** What has been shown is
that two families that *look* larger than the linear symmetries are not larger at all.

**NO CARDINALITY**, unchanged.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. An affine
symmetry group that collapses onto the linear one, in finite volume, is a shadow that collapses.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`gaussianField_map_affine_iff` and `bijective_affine_of_map` — **two of the six**, and only because
each invokes a classification result that spends it on `green` being positive definite. The other
four, **including both of the file's structural statements**, hold at every mass.
`coe_eq_affMap` and `coe_eq_linear` `omit` `[DecidableEq V]` and `[DecidableRel G.Adj]`: they
mention no graph and no measure — only Mathlib's `AffineMap` and this estate's `affMap`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldAffineMapSymmetry

open Matrix GraphLaplacian MeasureTheory FieldSqrtConjugation FieldLinearClassified
  FieldSymmetryIso FieldAffineSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Mathlib's affine map is this estate's `affMap` -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem coe_eq_affMap (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
    ⇑f = affMap (LinearMap.toContinuousLinearMap f.linear) (f 0) := by
  have h := AffineMap.decomp f
  funext x
  simpa using congrFun h x

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem coe_eq_linear (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) (h : f 0 = 0) :
    ⇑f = ⇑f.linear := by
  rw [coe_eq_affMap f, h]
  funext x
  simp [affMap]

/-! ## 2. Every affine symmetry fixes the origin -/

theorem apply_zero_of_map (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) : f 0 = 0 := by
  rw [coe_eq_affMap f] at h
  exact eq_zero_of_map_affMap _ _ h

/-! ## 3. So an affine symmetry is a linear symmetry that fixes the origin -/

theorem gaussianField_map_affine_iff_linear (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
    Measure.map f (gaussianField G m) = gaussianField G m ↔
      f 0 = 0 ∧ Measure.map f.linear (gaussianField G m) = gaussianField G m := by
  constructor
  · intro h
    have h0 : f 0 = 0 := apply_zero_of_map f h
    rw [coe_eq_linear f h0] at h
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    rwa [coe_eq_linear f h0]

/-! ## 4. And the classification, for a bundled affine map with no continuity assumed -/

theorem gaussianField_map_affine_iff (hm : m ≠ 0)
    (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V) :
    Measure.map f (gaussianField G m) = gaussianField G m ↔
      f 0 = 0 ∧ ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧
        Matrix.toEuclideanLin (conjSq G m O) = f.linear := by
  rw [gaussianField_map_affine_iff_linear f, gaussianField_map_linearMap_iff hm]

/-! ## 5. And an affine symmetry is a bijection -/

theorem bijective_affine_of_map (hm : m ≠ 0)
    (f : EuclideanSpace ℝ V →ᵃ[ℝ] EuclideanSpace ℝ V)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) : Function.Bijective f := by
  obtain ⟨h0, hlin⟩ := (gaussianField_map_affine_iff_linear f).mp h
  rw [coe_eq_linear f h0]
  exact FieldLinearSymmetry.bijective_of_map hm
    (L := LinearMap.toContinuousLinearMap f.linear) hlin

end FieldAffineMapSymmetry
