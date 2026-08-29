import LatticeUniformPoincare
import LatticeSqrtEquiv

/-!
# The volume-uniform bound, on the class the rest of the chain now uses

`LatticeUniformPoincare` proved

```
∫Φ² dμ − (∫Φ dμ)²  ≤  m⁻² · ∫ ∑ⱼ (∂ⱼΦ)² dμ
```

with a constant that names no graph — the point being that it survives the box growing. It was
written for `ContDiff ℝ 1` observables, because that was the only class available on the day.

**Four units later it was the only statement in this family with no Stein-class counterpart at
all.** `LatticeCorrelatedStein` and `LatticeSqrtEquiv` moved the sharp inequality onto the Stein
pair class and `LatticeFieldWitness` showed that class is strictly wider —
`LatticeCorrelatedPoincare` is still stated for `C¹` too, but it is explicitly subsumed by
`poincare_correlated_general_of_stein`, so nothing it says is out of reach. The uniform bound had
no such counterpart. This file supplies it.

*Found by `RE-SWEEP #19` rather than by working forwards: sweeping the watchlist against
everything now proved turned up no fired trigger, but did turn up this — a file overtaken by the
chain that grew out of it. That is the kind of gap a sweep is for and the kind that nothing else
looks for, since no item asks about it and the build is green either way.*

## What is proved

* **`poincare_uniform_stein`** — the displayed inequality for any Stein pair `(Φ, γ)` against the
  field, with `∑ⱼ γⱼ²` in place of the gradient. Only hypotheses: `m ≠ 0` and class membership.
* **`poincare_uniform_stein_of_bounded`** — the form with no integral: if `∑ⱼ γⱼ² ≤ L²` pointwise
  then `Var Φ ≤ m⁻²·L²`.
* A machine-checked `example` that the smooth theorem is the special case, so the generalisation
  did not quietly change the conclusion.

## The proof is two citations

`LatticeSqrtEquiv.poincare_correlated_stein_of_class` gives `Var Φ ≤ ∫ γ ⬝ᵥ G *ᵥ γ`;
`LatticeUniformPoincare.quadForm_green_le` bounds the integrand pointwise by `m⁻²·∑ⱼ γⱼ²`. The
square-integrability needed to compare the integrals comes from `LatticeSqrtEquiv.memLp_gamma`,
which is why this could not have been written before that unit either.

## What this is NOT

**The constant is uniform in the graph; that does not make every APPLICATION uniform.** Applying
this to `LatticeFieldWitness.absCoordField` gives a bound whose `L` involves `(√G)⁻¹`, and
**nothing here analyses how that grows with the box**. It plausibly does not grow — `(√G)⁻¹` is
controlled by the largest eigenvalue of `massive`, which a degree bound controls — but that is
**not proved here and not costed** (`ERRATUM 183`). The uniformity claimed is exactly the
constant's, and no more.

> **^ CLOSED 2026-08-29 AND THE PARAGRAPH IS KEPT** (`ERRATUM 94`).
> `WitnessVarianceUniform.absCoordField_var_le_boxGraph`: on the `d`-dimensional box the variance
> of that witness at any site is at most `m⁻²·(2d + m²)`, **at every side length**. So the
> application IS uniform, and the paragraph's *"plausibly does not grow"* was right.
> **ITS REASON WAS NOT.** It says `(√G)⁻¹` is controlled by the largest eigenvalue of `massive`,
> which a degree bound controls — true, and **not what the application needs**. The tuple is
> `((√G)⁻¹) j v · sgn(…)`, so what is consumed is the squared norm of **one column**, and that is
> an exact diagonal entry of `massive`: `deg(v) + m²`, by `sqrtGreenInv_col_sq`. **No bound on the
> whole matrix enters.** A file was built for the reason this paragraph gave before the consumer
> was read (`ERRATUM 334`).

**`OS4` does not move**, for the reason it has not moved throughout: a bound whose constant does
not blow up is an ingredient of a tightness argument and not one. No sequence of measures, no
limit, no compactness appears here.

**No spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeUniformStein

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeUniformPoincare LatticeCorrelatedStein LatticeSqrtEquiv
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}
variable {Φ : EuclideanSpace ℝ W → ℝ} {γ : W → EuclideanSpace ℝ W → ℝ}

/-- **THE VOLUME-UNIFORM VARIANCE BOUND ON THE STEIN CLASS.**

```
∫Φ² − (∫Φ)²  ≤  m⁻² · ∫ ∑ⱼ (γ j)²
```

against `gaussianField K m`, at every finite vertex type, for any Stein pair against the field.
The constant is `m⁻²` and mentions no graph; `γ` is not required to be a derivative of anything. -/
theorem poincare_uniform_stein (hm : m ≠ 0) (h : SteinPairField K m Φ γ) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ∫ ω, ∑ j, (γ j ω) ^ 2 ∂(gaussianField K m) := by
  classical
  refine (poincare_correlated_stein_of_class hm h).trans ?_
  have hint : Integrable (fun ω => ∑ j, (γ j ω) ^ 2) (gaussianField K m) :=
    integrable_finset_sum _ fun j _ => (memLp_gamma (K := K) hm h j).integrable_sq
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    (hint.const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
  · exact quadForm_nonneg_of_posSemidef (green_posDef K hm).posSemidef _
  · exact quadForm_green_le K hm _

/-- **AND THE FORM WITH NO INTEGRAL LEFT.** A Stein pair whose tuple is bounded in `ℓ²` by `L`
pointwise has variance at most `m⁻²·L²` — no graph, no dimension, no integral. -/
theorem poincare_uniform_stein_of_bounded (hm : m ≠ 0) (h : SteinPairField K m Φ γ)
    {L : ℝ} (hL : ∀ ω, ∑ j, (γ j ω) ^ 2 ≤ L ^ 2) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * L ^ 2 := by
  classical
  refine (poincare_uniform_stein hm h).trans ?_
  have hpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hint : Integrable (fun ω => ∑ j, (γ j ω) ^ 2) (gaussianField K m) :=
    integrable_finset_sum _ fun j _ => (memLp_gamma (K := K) hm h j).integrable_sq
  have hle := integral_mono hint (integrable_const (L ^ 2)) hL
  simpa using hle

/-- **AND THEREFORE THE SMOOTH UNIFORM BOUND, IN ONE LINE.**
`LatticeUniformPoincare.poincare_uniform` follows, the class membership being supplied by
`LatticeCorrelatedStein.steinPairField_of_contDiff`. -/
theorem poincare_uniform_of_stein (hm : m ≠ 0) (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ∫ ω, ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2
          ∂(gaussianField K m) :=
  poincare_uniform_stein hm (steinPairField_of_contDiff hΦc hmem hgrad)

/-- **The smooth theorem is the special case, machine-checked.**

`LatticeUniformPoincare.poincare_uniform`'s conclusion is literally this one at
`γ j ω = ∂ⱼΦ ω`, so generalising the observable class did not quietly move the right-hand side.
Proof irrelevance closes `A = B` by `rfl` exactly when the two propositions coincide. -/
example (hm : m ≠ 0) (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m))
    (h : SteinPairField K m Φ (fun j ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))) :
    poincare_uniform hm hΦc hmem hgrad = poincare_uniform_stein hm h := rfl

end LatticeUniformStein
