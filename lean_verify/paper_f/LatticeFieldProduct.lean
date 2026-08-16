import LatticeSobolevPoincare
import SteinGeneralPi

/-!
# The lattice field IS the standard product Gaussian, pushed through `√G`

Every multi-dimensional result in this estate — the `HermitePi` chain, `GaussianPoincareProduct`,
`SteinGeneralPi` — is stated against `gaussPi n`, the product of `n` independent standard
Gaussians. Every lattice result is stated against `gaussianField G m`, whose coordinates are
correlated. **Nothing had ever connected the two**, and `LatticePoincare` and
`LatticeSobolevPoincare` both had to go around the problem by looking along one direction at a
time, where the pushforward is one-dimensional.

This connects them, and the connection is an equality of measures rather than an estimate:

```
gaussianField G m = (gaussPi n).map (fun y => toLp 2 (√(green G m) *ᵥ y))
```

## Why this was available all along, which is the finding

`UNLOCK_WATCHLIST`'s derived staircase named this as step (b) and called it the binding one. It is
not binding; it is three citations, and the reason nobody had used them is that **`stdGaussian`
occurs in no other file of this estate**:

* Mathlib **defines** `multivariateGaussian μ S` as `(stdGaussian E).map (fun x => μ + √S x)` —
  the change of variables is definitional, not a theorem;
* `ProbabilityTheory.map_pi_eq_stdGaussian` identifies `stdGaussian (EuclideanSpace ℝ ι)` with
  `Measure.pi (fun _ => gaussianReal 0 1)` transported by the `WithLp` wrapper;
* and this estate's `GaussianProductMeasure.gaussPi n` **is** that `Measure.pi`, by definition.

So the two ends of the bridge were already touching. All that was missing was `Measure.map_map`
and someone opening the file.

## What is proved

* **`gaussianField_eq_map_gaussPi`** — the identity above, on every graph with vertex type
  `Fin n`, at every mass;
* `integral_field_eq_integral_gaussPi` — hence every integral against the field is an integral
  against `gaussPi n` of the observable precomposed with `√G`;
* `variance_field_eq` — and the same for the two-term variance expression, which is the shape
  every Poincaré statement in the estate uses.

## What this is NOT, and the restriction is honest rather than incidental

**The vertex type is `Fin n`.** `gaussPi` is indexed by `Fin n` and `gaussianField` by an
arbitrary `Fintype V`; transporting between them across `Fintype.equivFin` is bookkeeping that is
**not done here**. The estate's concrete lattices (`boxGraph`, `torusGraph`) have product vertex
types, so this does not yet reach them — it reaches every graph whose vertices are already
`Fin n`.

**And the Poincaré inequality is NOT proved here.** With the three lemmas above the remaining step
is exactly one: `∑ᵢ (DΦ(x)(√G eᵢ))² = ⟪∇Φ(x), G ∇Φ(x)⟫`, which needs the gradient representation
of `DΦ` and `CFC.sqrt_mul_sqrt_self`. **That step is named, not costed** (`ERRATUM 183`), and it
is the only thing between this file and the correlated inequality in all directions at once.

**No published tag moves. OS4 does not move.**
-/

namespace LatticeFieldProduct

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GaussianProductMeasure
open scoped MatrixOrder

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The identity -/

/-- **THE LATTICE FIELD IS THE STANDARD PRODUCT GAUSSIAN PUSHED THROUGH `√G`.**

Not an approximation and not a limit — an equality of measures, holding at every mass, on every
graph with vertex type `Fin n`. The whole proof is `Measure.map_map` between two facts that were
already in place: Mathlib's *definition* of a multivariate Gaussian, and its identification of
the standard Gaussian on a Euclidean space with a product of one-dimensional ones. -/
theorem gaussianField_eq_map_gaussPi :
    gaussianField G m
      = (gaussPi n).map (fun y => WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y)) := by
  have hg : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      (0 : EuclideanSpace ℝ (Fin n))
        + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (green G m)) x) := by fun_prop
  have hf : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  rw [gaussianField, multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map hg hf]
  simp [gaussPi, Function.comp_def]

/-! ## 2. What it does to integrals -/

/-- Every integral against the field is an integral against `gaussPi n` of the observable
precomposed with `√G`. -/
theorem integral_field_eq_integral_gaussPi {Φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦ : Continuous Φ) :
    ∫ ω, Φ ω ∂(gaussianField G m)
      = ∫ y, Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y)) ∂(gaussPi n) := by
  rw [gaussianField_eq_map_gaussPi (G := G) (m := m)]
  rw [integral_map (by fun_prop) hΦ.aestronglyMeasurable]

/-- **AND HENCE THE VARIANCE EXPRESSION TRANSPORTS**, which is the shape every Poincaré statement
in this estate is written in. This is what a correlated Poincaré inequality would apply the
`gaussPi` theorem to. -/
theorem variance_field_eq {Φ : EuclideanSpace ℝ (Fin n) → ℝ} (hΦ : Continuous Φ) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField G m)) - (∫ ω, Φ ω ∂(gaussianField G m)) ^ 2
      = (∫ y, Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y))
            * Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y)) ∂(gaussPi n))
        - (∫ y, Φ (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ y)) ∂(gaussPi n)) ^ 2 := by
  rw [integral_field_eq_integral_gaussPi (G := G) (m := m)
      (Φ := fun ω => Φ ω * Φ ω) (hΦ.mul hΦ),
    integral_field_eq_integral_gaussPi (G := G) (m := m) hΦ]

/-- The square root really is a square root of the propagator, which is the fact the remaining
step needs and which is recorded here so that step starts from a proved statement. -/
theorem sqrt_green_mul_self (hm : m ≠ 0) :
    CFC.sqrt (green G m) * CFC.sqrt (green G m) = green G m :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr (green_posDef G hm).posSemidef)

end LatticeFieldProduct
