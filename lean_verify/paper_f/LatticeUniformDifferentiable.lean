import LatticeUniformStein
import LatticeSmearedFromGeneral

/-!
# The volume-uniform bound, without `C¹`

`LatticeUniformStein` moved the volume-uniform variance bound

```
∫Φ² dμ − (∫Φ dμ)²  ≤  m⁻² · ∫ ∑ⱼ γⱼ² dμ
```

onto the Stein pair class, and observed that this made it the last statement in the family with a
class-level form. It kept one `C¹` corollary — `poincare_uniform_of_stein` — because
`steinPairField_of_contDiff` was the only way into the class from a hypothesis anyone could check.

`LatticeFieldDifferentiable.steinPairField_of_differentiable` is now a second way in, and it asks
for differentiability and polynomial growth rather than `C¹`. **So the last `C¹` in the Stein-class
chain comes out**, and the volume-uniform bound holds for observables whose gradient is nowhere
required to be continuous.

## What is proved

* **`poincare_uniform_differentiable`** — the displayed inequality for any differentiable `Φ` of
  polynomial growth, constant `m⁻²`, naming no graph;
* **`poincare_uniform_differentiable_of_bounded`** — the form with no integral, when the gradient is
  bounded in `ℓ²` pointwise;
* **`poincare_uniform_wigSmear`** — run on `ω ↦ wig ⟪f,ω⟫`, which
  `LatticeSmearedFromGeneral.not_contDiff_wig_smear` proves is **not** `ContDiff ℝ 1` for `f ≠ 0`.
  `ERRATUM 48`: a criterion that produces no member it could not produce before is a criterion whose
  usefulness is asserted.

## What this is NOT

**The uniformity is the constant's, and no more** — the caveat `LatticeUniformStein` wrote about
itself is inherited verbatim and is not weakened here. The constant `m⁻²` mentions no graph. That
does **not** make an application uniform: the right-hand side still integrates the gradient, and how
*that* grows with the box is a separate question this file does not touch.

**`OS4` does not move.** A bound whose constant does not blow up is an ingredient of a tightness
argument and not one. No sequence of measures, no limit and no compactness appears here.

**Nothing here is a new estimate.** Both halves existed; this is the composition, and the reason it
is worth a name is that `LatticeUniformStein`'s own header said the `C¹` corollary was the shape the
family had to keep, and that is no longer true.

**No spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeUniformDifferentiable

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeUniformStein LatticeCorrelatedStein LatticeSmearedFromGeneral
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}
variable {Φ : EuclideanSpace ℝ W → ℝ}

/-! ## 1. The bound, on the differentiable class -/

/-- **THE VOLUME-UNIFORM VARIANCE BOUND, WITHOUT `C¹`.**

```
∫Φ² − (∫Φ)²  ≤  m⁻² · ∫ ∑ⱼ (∂ⱼΦ)²
```

against `gaussianField K m`, at every finite vertex type, for any **differentiable** `Φ` whose value
and partial derivatives obey a common polynomial bound. The constant is `m⁻²` and mentions no graph;
**the gradient is nowhere required to be continuous.** -/
theorem poincare_uniform_differentiable (hm : m ≠ 0) (hΦd : Differentiable ℝ Φ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Φ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (j : W) (x), |fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ∫ ω, ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2
          ∂(gaussianField K m) :=
  poincare_uniform_stein hm
    (LatticeFieldDifferentiable.steinPairField_of_differentiable hΦd hb hb')

/-- **AND THE FORM WITH NO INTEGRAL LEFT.** A differentiable observable of polynomial growth whose
gradient is bounded in `ℓ²` by `L` pointwise has variance at most `m⁻²·L²` — no graph, no dimension,
no integral, and no continuity of the gradient. -/
theorem poincare_uniform_differentiable_of_bounded (hm : m ≠ 0) (hΦd : Differentiable ℝ Φ)
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Φ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (j : W) (x), |fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    {L : ℝ} (hL : ∀ ω, ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2 ≤ L ^ 2) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * L ^ 2 :=
  poincare_uniform_stein_of_bounded hm
    (LatticeFieldDifferentiable.steinPairField_of_differentiable hΦd hb hb') hL

/-! ## 2. Exercised on an observable the `C¹` corollary cannot reach

`ERRATUM 48`. `LatticeSmearedFromGeneral.not_contDiff_wig_smear` proves `ω ↦ wig ⟪f,ω⟫` is not
`ContDiff ℝ 1` for any `f ≠ 0`, so `LatticeUniformStein.poincare_uniform_of_stein` does not apply to
it and `LatticeUniformPoincare.poincare_uniform` cannot state it. The bound holds anyway. -/

/-- **THE VOLUME-UNIFORM BOUND ON A NON-`C¹` OBSERVABLE.** -/
theorem poincare_uniform_wigSmear (hm : m ≠ 0) (f : EuclideanSpace ℝ W) :
    (∫ ω, wigSmear f ω * wigSmear f ω ∂(gaussianField K m))
        - (∫ ω, wigSmear f ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ∫ ω, ∑ j, (fderiv ℝ (wigSmear f) ω
          (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2 ∂(gaussianField K m) :=
  poincare_uniform_differentiable hm (differentiable_wigSmear f) (wigSmear_bound f)
    (fun j ω => fderiv_wigSmear_bound f j ω)

end LatticeUniformDifferentiable
