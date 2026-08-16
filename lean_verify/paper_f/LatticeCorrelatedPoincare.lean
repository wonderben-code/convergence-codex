import LatticeGradientForm

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

**The two `L²` side conditions are stated on the composed function**, not on `Φ` against the
field. Transporting them across `gaussianField_eq_map_gaussPi` is a `memLp_map_measure_iff`
exercise that is **not done here**, so a user must supply them in the `gaussPi` vocabulary. That is
recorded as a restriction rather than hidden: the conclusion is about the field, the hypotheses are
not.

**And the vertex type is `Fin n`.** The estate's concrete lattices (`boxGraph`, `torusGraph`) have
product vertex types, so **this does not reach them** until someone transports across
`Fintype.equivFin`. Both restrictions are named in the `UNLOCK_WATCHLIST` item.

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

end LatticeCorrelatedPoincare
