import LatticeGradientForm
import LatticePoincarePi

/-!
# The Poincaré inequality for the correlated field, in all directions at once

`LatticePoincare` and `LatticeSobolevPoincare` proved this inequality **along one direction at a
time** — for observables that are functions of a single smearing `⟪f,ω⟫` — and both headers said
the same thing about what was missing: the version for a function of *all* the coordinates, with
the gradient paired against the propagator, was untouched.

This is that version.

```
∫ Φ² dμ − (∫ Φ dμ)²  ≤  ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ) dμ
```

where `∂Φ` is the tuple of partial derivatives. **The measure is `gaussianField G m`, whose
coordinates are correlated**, and the constant is the propagator's own quadratic form.

## The chain, and how wrong every estimate of it was

Four units named the next obstacle and four times it was somewhere else:

* *the change of variables would be the work* — it is Mathlib's **definition** of a
  multivariate Gaussian;
* *identifying the two measures would bind* — `map_pi_eq_stdGaussian`, already written;
* *the gradient hypothesis class would be expensive* — `poincare_contDiff` takes a plain
  `C¹` function, there is no class;
* *the last identity needs the Riesz representative* — it needs no gradients at all.

All four wrong guesses are still in the record. The one thing that was never predicted — the
finite-dimensional linearity argument of `LatticeGradientForm.apply_eq_sum_coords` — is what made
the identity trivial.

## What is proved

* `sqrtMap` — the change of variables `y ↦ toLp 2 (√G *ᵥ y)` as a continuous linear map, with
  `sqrtMap_apply` a definitional unfolding;
* `fderiv_comp_sqrtMap` — the chain rule through it;
* **`poincare_correlated`** — the inequality above, on every graph with vertex type `Fin n`, at
  every nonzero mass.

## What this is NOT

*The first version of this file left the two `L²` side conditions phrased on the composed
function, and recorded that as a restriction. **§3 removes it**: `poincare_correlated_field` states
the observable and both side conditions against `gaussianField G m`, with the side conditions on
the ordinary coordinate partial derivatives — the same tuple the right-hand side uses. The
`√G`-direction derivatives the proof needs are finite linear combinations of those, so nothing
extra is assumed.*

*The vertex type was `Fin n` in §§1–2. **§4 removes that too**, so the inequality now reaches
`boxGraph` and `torusGraph`; §§1–2 are kept because they are what §3 is stated against.*

**No spectral gap is claimed, OS4 does not move, and no published tag moves.**
-/

namespace LatticeCorrelatedPoincare

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GaussianProductMeasure
open LatticeFieldProduct LatticeGradientForm
open scoped MatrixOrder

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The change of variables as a continuous linear map -/

/-- `y ↦ toLp 2 (S *ᵥ y)`, bundled. Continuity is automatic in finite dimensions. -/
noncomputable def sqrtMap (S : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin S)

@[simp] theorem sqrtMap_apply (S : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    sqrtMap S y = WithLp.toLp 2 (S *ᵥ y) := rfl

/-- The chain rule through `sqrtMap`. -/
theorem fderiv_comp_sqrtMap (S : Matrix (Fin n) (Fin n) ℝ) {Φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦ : Differentiable ℝ Φ) (y v : Fin n → ℝ) :
    fderiv ℝ (fun z => Φ (sqrtMap S z)) y v = fderiv ℝ Φ (sqrtMap S y) (sqrtMap S v) := by
  have h := fderiv_comp (𝕜 := ℝ) y (hΦ (sqrtMap S y)) (sqrtMap S).differentiableAt
  simp only [Function.comp_def] at h
  rw [h]
  simp

/-! ## 2. The inequality -/

/-- **THE GAUSSIAN POINCARÉ INEQUALITY FOR A CORRELATED FIELD.**

`∫Φ² − (∫Φ)² ≤ ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ)`, against `gaussianField G m` — a measure whose coordinates
are **not** independent — with the propagator's own quadratic form as the constant.

The proof is the composition of four things now in the estate and none of them analytic beyond the
chain rule: the field is the product Gaussian pushed through `√G`
(`gaussianField_eq_map_gaussPi`); the product Gaussian satisfies Poincaré for `C¹` functions
(`SteinGeneralPi.poincare_contDiff`); the chain rule turns the composed derivative into `Φ`'s
derivative along the `√G`-images of the axes; and `sum_sq_apply_sqrt_green` turns the resulting sum
of squares into the Green quadratic form. -/
theorem poincare_correlated (hm : m ≠ 0) {Φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp (fun y => Φ (sqrtMap (CFC.sqrt (green G m)) y)) 2 (gaussPi n))
    (hgrad : ∀ i, MemLp (fun y => fderiv ℝ
      (fun z => Φ (sqrtMap (CFC.sqrt (green G m)) z)) y (Pi.single i (1 : ℝ))) 2 (gaussPi n)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField G m)) - (∫ ω, Φ ω ∂(gaussianField G m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green G m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField G m) := by
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by norm_num)
  have hcomp : ContDiff ℝ 1 (fun z => Φ (sqrtMap (CFC.sqrt (green G m)) z)) :=
    hΦc.comp (sqrtMap (CFC.sqrt (green G m))).contDiff
  -- the product-measure inequality, for the composed observable
  have key := SteinGeneralPi.poincare_contDiff (n := n) hcomp hmem hgrad
  simp only [sqrtMap_apply] at key hgrad
  -- the left-hand side is the field's variance
  rw [← variance_field_eq (G := G) (m := m) hΦd.continuous] at key
  refine key.trans (le_of_eq ?_)
  -- and each summand of the right-hand side is the Green form, pointwise in `y`
  have hpt : ∀ y : Fin n → ℝ,
      ∑ i : Fin n,
          fderiv ℝ (fun z => Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ z))) y
              (Pi.single i (1 : ℝ))
            * fderiv ℝ (fun z => Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ z))) y
              (Pi.single i (1 : ℝ))
        = (fun j => fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
              (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
            ⬝ᵥ green G m *ᵥ
              (fun j => fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
                (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) := by
    intro y
    have hchain : ∀ i : Fin n,
        fderiv ℝ (fun z => Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ z))) y
            (Pi.single i (1 : ℝ))
          = fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
              (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ))) := by
      intro i
      have h := fderiv_comp_sqrtMap (CFC.sqrt (green G m)) hΦd y (Pi.single i (1 : ℝ))
      simpa only [sqrtMap_apply] using h
    simp only [hchain, ← sq]
    exact sum_sq_apply_sqrt_green hm
      (fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y)))
  rw [integral_field_eq_integral_gaussPi (G := G) (m := m)
    (Φ := fun ω => (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
      ⬝ᵥ green G m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))))
    (by fun_prop)]
  have hint : ∀ i : Fin n, Integrable (fun y : Fin n → ℝ =>
      fderiv ℝ (fun z => Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ z))) y (Pi.single i (1 : ℝ))
        * fderiv ℝ (fun z => Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ z))) y
            (Pi.single i (1 : ℝ))) (gaussPi n) :=
    fun i => (hgrad i).integrable_mul (hgrad i)
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-! ## 3. The hypotheses moved onto the field

`poincare_correlated`'s conclusion is about `gaussianField G m` and its two `L²` side conditions
are about the **composed** observable against `gaussPi n`. That mismatch was recorded as a
restriction rather than hidden; this section removes it, so that hypotheses and conclusion speak
about the same measure and the same function.

Two things make it work. `memLp_map_measure_iff` transports square-integrability across
`gaussianField_eq_map_gaussPi` in both directions. And the derivative in a `√G`-direction is a
*finite linear combination* of the ordinary coordinate partial derivatives
(`LatticeGradientForm.apply_eq_sum_coords`), so requiring the coordinate partials to be `L²` is
enough — which is also the form the conclusion is stated in. -/

/-- Square-integrability against the field is square-integrability of the composition against the
product measure. Both directions, since `memLp_map_measure_iff` is an iff.

**No hypothesis on the mass**, because `gaussianField_eq_map_gaussPi` needs none — it is a
definitional identity. This was first written with `m ≠ 0` by habit and the linter caught it: the
fourth such catch today. -/
theorem memLp_field_iff {Ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΨ : AEStronglyMeasurable Ψ (gaussianField G m)) :
    MemLp Ψ 2 (gaussianField G m)
      ↔ MemLp (fun y => Ψ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))) 2 (gaussPi n) := by
  rw [gaussianField_eq_map_gaussPi (G := G) (m := m)] at hΨ ⊢
  simpa [Function.comp_def] using memLp_map_measure_iff hΨ (by fun_prop)

/-- **THE INEQUALITY WITH EVERY HYPOTHESIS ON THE FIELD.**

Same conclusion as `poincare_correlated`, but now the observable and both side conditions are
stated against `gaussianField G m`, and the side conditions are about the **ordinary coordinate
partial derivatives** — the very tuple `∂Φ` that appears on the right-hand side.

The `√G`-direction derivatives the proof actually needs are recovered as finite linear
combinations of those, which is why no extra hypothesis is required. -/
theorem poincare_correlated_field (hm : m ≠ 0) {Φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField G m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField G m)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField G m)) - (∫ ω, Φ ω ∂(gaussianField G m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green G m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField G m) := by
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by norm_num)
  -- the observable, transported
  have hmem' : MemLp (fun y => Φ (sqrtMap (CFC.sqrt (green G m)) y)) 2 (gaussPi n) := by
    simpa only [sqrtMap_apply] using (memLp_field_iff hmem.1).mp hmem
  -- each coordinate partial, transported
  have hpart : ∀ j, MemLp (fun y => fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
      (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2 (gaussPi n) :=
    fun j => (memLp_field_iff (hgrad j).1).mp (hgrad j)
  -- and hence each `√G`-direction derivative, as a finite linear combination of them
  have hgrad' : ∀ i, MemLp (fun y => fderiv ℝ
      (fun z => Φ (sqrtMap (CFC.sqrt (green G m)) z)) y (Pi.single i (1 : ℝ))) 2 (gaussPi n) := by
    intro i
    have hrw : (fun y => fderiv ℝ (fun z => Φ (sqrtMap (CFC.sqrt (green G m)) z)) y
        (Pi.single i (1 : ℝ)))
        = fun y => ∑ j, (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ)) j
            * fderiv ℝ Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
                (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
      funext y
      rw [fderiv_comp_sqrtMap _ hΦd y (Pi.single i (1 : ℝ)), sqrtMap_apply, sqrtMap_apply,
        LatticeGradientForm.apply_eq_sum_coords]
    rw [hrw]
    exact memLp_finset_sum _ (fun j _ => (hpart j).const_mul _)
  exact poincare_correlated hm hΦc hmem' hgrad'

/-! ## 4. The inequality at an arbitrary vertex type

Every ingredient now exists off `Fin n`: the measure identity
(`LatticeFieldProduct.gaussianField_eq_map_pi`), the product-measure inequality
(`LatticePoincarePi.poincare_contDiff_pi`), and the algebraic identity
(`LatticeGradientForm.sum_sq_apply_sqrt_green`, stated at an arbitrary linear functional and, since
this unit, an arbitrary index). **So this section is the same proof as §2 with the `Fin n`
removed**, and it is what carries the inequality to `boxGraph` and `torusGraph`, whose vertex types
are products. -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! `sqrtMapOf` and its two lemmas are about a matrix, not a graph, so the graph variables are
introduced below them; and they need no `DecidableEq` either, which is `omit`-ted explicitly. Both
facts were reported by the linter rather than noticed by the author — the sixth such report
today. -/

/-- `y ↦ toLp 2 (S *ᵥ y)` at an arbitrary index type. -/
noncomputable def sqrtMapOf (S : Matrix W W ℝ) : (W → ℝ) →L[ℝ] EuclideanSpace ℝ W :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (W → ℝ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin S)

omit [DecidableEq W] in
@[simp] theorem sqrtMapOf_apply (S : Matrix W W ℝ) (y : W → ℝ) :
    sqrtMapOf S y = WithLp.toLp 2 (S *ᵥ y) := rfl

omit [DecidableEq W] in
theorem fderiv_comp_sqrtMapOf (S : Matrix W W ℝ) {Φ : EuclideanSpace ℝ W → ℝ}
    (hΦ : Differentiable ℝ Φ) (y v : W → ℝ) :
    fderiv ℝ (fun z => Φ (sqrtMapOf S z)) y v = fderiv ℝ Φ (sqrtMapOf S y) (sqrtMapOf S v) := by
  have h := fderiv_comp (𝕜 := ℝ) y (hΦ (sqrtMapOf S y)) (sqrtMapOf S).differentiableAt
  simp only [Function.comp_def] at h
  rw [h]
  simp

variable {K : SimpleGraph W} [DecidableRel K.Adj]

/-- **THE CORRELATED POINCARÉ INEQUALITY AT EVERY FINITE VERTEX TYPE.**

`∫Φ² − (∫Φ)² ≤ ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ)` against `gaussianField K m`, with no restriction on the vertex
type — so it applies to `boxGraph` and `torusGraph`, whose vertices are tuples.

Hypotheses and conclusion are both stated against the field, as in §3. -/
theorem poincare_correlated_general (hm : m ≠ 0) {Φ : EuclideanSpace ℝ W → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green K m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField K m) := by
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by norm_num)
  have hmap : Measure.map (fun y => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
      (LatticePoincarePi.gaussPiOf W) = gaussianField K m :=
    (LatticeFieldProduct.gaussianField_eq_map_pi (H := K) (m := m)).symm
  have htrans : ∀ g : EuclideanSpace ℝ W → ℝ, AEStronglyMeasurable g (gaussianField K m) →
      ∫ ω, g ω ∂(gaussianField K m)
        = ∫ y, g (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
            ∂(LatticePoincarePi.gaussPiOf W) := by
    intro g hg
    rw [← hmap] at hg ⊢
    rw [integral_map (by fun_prop) hg]
  have hmemc : ∀ g : EuclideanSpace ℝ W → ℝ, MemLp g 2 (gaussianField K m) →
      MemLp (fun y => g (sqrtMapOf (CFC.sqrt (green K m)) y)) 2
        (LatticePoincarePi.gaussPiOf W) := by
    intro g hg
    have := (memLp_map_measure_iff (μ := LatticePoincarePi.gaussPiOf W)
      (f := fun y => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
      (by rw [hmap]; exact hg.1) (by fun_prop)).mp (by rw [hmap]; exact hg)
    simpa [Function.comp_def] using this
  have hcomp : ContDiff ℝ 1 (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) :=
    hΦc.comp (sqrtMapOf (CFC.sqrt (green K m))).contDiff
  have hchain : ∀ (y : W → ℝ) (i : W),
      fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
        = ∑ j, (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j
            * fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
                (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
    intro y i
    rw [fderiv_comp_sqrtMapOf _ hΦd y (Pi.single i (1 : ℝ)), sqrtMapOf_apply,
      LatticeGradientForm.apply_eq_sum_coords]
    rfl
  have hgrad' : ∀ i, MemLp (fun y => fderiv ℝ
      (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))) 2
        (LatticePoincarePi.gaussPiOf W) := by
    intro i
    have hrw : (fun y => fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y
        (Pi.single i (1 : ℝ)))
        = fun y => ∑ j, (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j
            * fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
                (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := funext fun y => hchain y i
    rw [hrw]
    exact memLp_finset_sum _ (fun j _ => (hmemc _ (hgrad j)).const_mul _)
  have key := LatticePoincarePi.poincare_contDiff_pi hcomp
    (hmemc Φ hmem) hgrad'
  have hpt : ∀ y : W → ℝ,
      ∑ i : W, fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
          * fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
        = (fun j => fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
              (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
            ⬝ᵥ green K m *ᵥ
              (fun j => fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
                (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) := by
    intro y
    have hch : ∀ i : W,
        fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
          = fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
              (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ))) := by
      intro i
      rw [fderiv_comp_sqrtMapOf _ hΦd y (Pi.single i (1 : ℝ))]
      rfl
    simp only [hch, ← sq]
    exact LatticeGradientForm.sum_sq_apply_sqrt_green hm _
  rw [htrans (fun ω => Φ ω * Φ ω) (hmem.1.mul hmem.1), htrans Φ hmem.1]
  refine key.trans (le_of_eq ?_)
  rw [htrans (fun ω => (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
      ⬝ᵥ green K m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))) (by fun_prop)]
  have hint : ∀ i : W, Integrable (fun y : W → ℝ =>
      fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
        * fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ)))
      (LatticePoincarePi.gaussPiOf W) := fun i => (hgrad' i).integrable_mul (hgrad' i)
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end LatticeCorrelatedPoincare
