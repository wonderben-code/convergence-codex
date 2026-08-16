import LatticeSteinPoincarePi
import LatticeCorrelatedPoincare

/-!
# The correlated Poincaré inequality without differentiability

`LatticeCorrelatedPoincare.poincare_correlated_general` proved

```
∫Φ² dμ − (∫Φ dμ)²  ≤  ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ) dμ
```

against `gaussianField K m` for **continuously differentiable** observables.
`LatticeSteinPoincarePi` removed that restriction against a *product* measure, and its header named
carrying the result through `√G` as the step that would remove it here. This is that step.

The inequality now holds for `Φ` in the **Stein pair class against the field**, with `γ` in the
role of the gradient — and `γ` is not required to be a derivative of anything.

## The shape of the argument, which is entirely inherited

`gaussianField K m` **is** the product Gaussian pushed through `√G`
(`LatticeFieldProduct.gaussianField_eq_map_pi`, an equality of measures). So:

* the hypothesis is the product-measure Stein condition on `Φ ∘ √G` with the tuple
  `i ↦ ∑ⱼ γⱼ(√G ·)·(√G eᵢ)ⱼ` — the chain rule's answer, **written down rather than derived**,
  because there is no derivative to differentiate;
* `LatticeSteinPoincarePi.poincare_steinPi_of` supplies the inequality;
* `LatticeGradientForm.sum_sq_col_eq_quadForm` turns `∑ᵢ (…)²` into `γ ⬝ᵥ G *ᵥ γ`, which is where
  `√G·√G = G` is used and the only place the propagator's identity enters.

**Nothing here is a new analytic idea.** Every ingredient existed; the content is that they compose,
and that the composition never needs smoothness.

## What is proved

* `SteinPairField` — the class, at every finite vertex type and every nonzero mass;
* **`poincare_correlated_stein`** — the displayed inequality on that class;
* `steinPairField_of_contDiff` — a `C¹` observable with square-integrable value and coordinate
  derivatives is in the class, with `γ` its own partial derivatives;
* **`poincare_correlated_general_of_stein`** — and therefore `poincare_correlated_general` follows
  in one line. **The subsumption is a theorem, not a remark in a header.**

## What is honest to flag

**Two measurability side conditions are carried.** `poincare_correlated_stein` asks for `Φ` and each
`γ j` to be a.e.-strongly-measurable *against the field*. They are needed to move integrals across
the change of variables and they are **not** implied by the class, which only constrains the
composed functions against the product measure. Deriving them instead would need `y ↦ √G y` to be a
measurable embedding — true at `m ≠ 0`, since `green` is positive definite — and that is **not
proved here and not costed** (`ERRATUM 183`). They are weaker than the `MemLp` hypotheses
`poincare_correlated_general` already carries, so the bridge in §3 supplies them for free.

**`SteinPairField` is DEFINED BY TRANSPORT**, twice: through `√G` here, and through the canonical
relabelling inside `SteinPairOf`. An intrinsic characterisation — a Stein identity stated against
`gaussianField K m` itself — is **not here and not costed**.

**NO NON-SMOOTH WITNESS IS EXHIBITED AT THE FIELD.** `LatticeSteinPoincarePi` exhibits one against
the product measure (`|x v|`), which is what makes the class *there* provably wider than `C¹`.
Transporting it through `√G` would give one here; **it is not done**. So this file proves the class
**contains** `C¹` and does **not** prove it strictly larger. Claiming otherwise would be asserting
the corollary of a theorem nobody has written.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeCorrelatedStein

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GaussianProductMeasure
open LatticeFieldProduct LatticeGradientForm LatticeCorrelatedPoincare
open LatticeSteinPoincarePi LatticePoincarePi
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The class -/

/-- **The Stein pair class against `gaussianField K m`.**

`Φ` is paired with `γ` exactly when `Φ ∘ √G` is paired, against the product measure, with the tuple
the chain rule would produce — `i ↦ ∑ⱼ γⱼ(√G ·)·(√G eᵢ)ⱼ`. Written down rather than differentiated,
since `γ` is not assumed to be anyone's derivative. -/
def SteinPairField (K : SimpleGraph W) [DecidableRel K.Adj] (m : ℝ)
    (Φ : EuclideanSpace ℝ W → ℝ) (γ : W → EuclideanSpace ℝ W → ℝ) : Prop :=
  SteinPairOf W
    (fun y => Φ (sqrtMapOf (CFC.sqrt (green K m)) y))
    (fun i y => ∑ j, γ j (sqrtMapOf (CFC.sqrt (green K m)) y)
      * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j)

/-! ## 2. The inequality -/

/-- **THE CORRELATED POINCARÉ INEQUALITY, WITHOUT DIFFERENTIABILITY.**

`∫Φ² − (∫Φ)² ≤ ∫ γ ⬝ᵥ G *ᵥ γ` against `gaussianField K m`, at every finite vertex type and every
nonzero mass, for any Stein pair `(Φ, γ)` against the field. -/
theorem poincare_correlated_stein (hm : m ≠ 0)
    {Φ : EuclideanSpace ℝ W → ℝ} {γ : W → EuclideanSpace ℝ W → ℝ}
    (hΦm : AEStronglyMeasurable Φ (gaussianField K m))
    (hγm : ∀ j, AEStronglyMeasurable (γ j) (gaussianField K m))
    (h : SteinPairField K m Φ γ) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => γ j ω) ⬝ᵥ green K m *ᵥ (fun j => γ j ω) ∂(gaussianField K m) := by
  classical
  have hmap : Measure.map (fun y => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
      (gaussPiOf W) = gaussianField K m :=
    (LatticeFieldProduct.gaussianField_eq_map_pi (H := K) (m := m)).symm
  have htrans : ∀ u : EuclideanSpace ℝ W → ℝ, AEStronglyMeasurable u (gaussianField K m) →
      ∫ ω, u ω ∂(gaussianField K m)
        = ∫ y, u (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)) ∂(gaussPiOf W) := by
    intro u hu
    rw [← hmap] at hu ⊢
    rw [integral_map (by fun_prop) hu]
  have hquad : AEStronglyMeasurable
      (fun ω => (fun j => γ j ω) ⬝ᵥ green K m *ᵥ (fun j => γ j ω)) (gaussianField K m) := by
    have hEq : (fun ω => (fun j => γ j ω) ⬝ᵥ green K m *ᵥ (fun j => γ j ω))
        = ∑ i : W, ∑ j : W, (fun ω => γ i ω * (green K m i j * γ j ω)) := by
      funext ω
      simp [dotProduct, Matrix.mulVec, Finset.sum_apply, Finset.mul_sum]
    rw [hEq]
    exact Finset.aestronglyMeasurable_sum _ fun i _ =>
      Finset.aestronglyMeasurable_sum _ fun j _ =>
        (hγm i).mul (aestronglyMeasurable_const.mul (hγm j))
  have hint : ∀ i : W, Integrable (fun y : W → ℝ =>
      (∑ j, γ j (sqrtMapOf (CFC.sqrt (green K m)) y)
        * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j)
      * ∑ j, γ j (sqrtMapOf (CFC.sqrt (green K m)) y)
        * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j) (gaussPiOf W) :=
    fun i => (h.memLp_grad i).integrable_mul (h.memLp_grad i)
  have key := poincare_steinPi_of h
  rw [htrans (fun ω => Φ ω * Φ ω) (hΦm.mul hΦm), htrans Φ hΦm]
  refine key.trans (le_of_eq ?_)
  rw [htrans (fun ω => (fun j => γ j ω) ⬝ᵥ green K m *ᵥ (fun j => γ j ω)) hquad]
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hq := sum_sq_col_eq_quadForm (CFC.sqrt (green K m)) (green K m)
    (isSymm_sqrt_green (G := K) (m := m)) (sqrt_green_mul_self_general (H := K) hm)
    (fun j => γ j (sqrtMapOf (CFC.sqrt (green K m)) y))
  simpa [sq] using hq

/-! ## 3. The smooth side is inside the class -/

/-- A `C¹` observable of the field, with square-integrable value and coordinate derivatives, is a
Stein pair against the field with `γ` its own partial derivatives. -/
theorem steinPairField_of_contDiff {Φ : EuclideanSpace ℝ W → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m)) :
    SteinPairField K m Φ
      (fun j ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) := by
  classical
  have hΦd : Differentiable ℝ Φ := hΦc.differentiable (by norm_num)
  have hmap : Measure.map (fun y => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
      (gaussPiOf W) = gaussianField K m :=
    (LatticeFieldProduct.gaussianField_eq_map_pi (H := K) (m := m)).symm
  have hmemc : ∀ u : EuclideanSpace ℝ W → ℝ, MemLp u 2 (gaussianField K m) →
      MemLp (fun y => u (sqrtMapOf (CFC.sqrt (green K m)) y)) 2 (gaussPiOf W) := by
    intro u hu
    have := (memLp_map_measure_iff (μ := gaussPiOf W)
      (f := fun y => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
      (by rw [hmap]; exact hu.1) (by fun_prop)).mp (by rw [hmap]; exact hu)
    simpa [Function.comp_def] using this
  have hcomp : ContDiff ℝ 1 (fun y => Φ (sqrtMapOf (CFC.sqrt (green K m)) y)) :=
    hΦc.comp (sqrtMapOf (CFC.sqrt (green K m))).contDiff
  have hchain : ∀ (y : W → ℝ) (i : W),
      fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))
        = ∑ j, fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
            (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
            * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j := by
    intro y i
    rw [fderiv_comp_sqrtMapOf _ hΦd y (Pi.single i (1 : ℝ)), sqrtMapOf_apply,
      LatticeGradientForm.apply_eq_sum_coords]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hgrad' : ∀ i, MemLp (fun y => fderiv ℝ
      (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y (Pi.single i (1 : ℝ))) 2
        (gaussPiOf W) := by
    intro i
    have hrw : (fun y => fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y
        (Pi.single i (1 : ℝ)))
        = fun y => ∑ j, fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
            (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
            * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j := funext fun y => hchain y i
    rw [hrw]
    exact memLp_finset_sum _ (fun j _ => (hmemc _ (hgrad j)).mul_const _)
  have hst := steinPairOf_of_contDiff (V := W) hcomp (hmemc Φ hmem) hgrad'
  have hfun : (fun i y => fderiv ℝ (fun z => Φ (sqrtMapOf (CFC.sqrt (green K m)) z)) y
      (Pi.single i (1 : ℝ)))
      = fun i (y : W → ℝ) => ∑ j, fderiv ℝ Φ (sqrtMapOf (CFC.sqrt (green K m)) y)
          (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
          * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j := by
    funext i y; exact hchain y i
  rw [hfun] at hst
  exact hst

/-! ## 4. And therefore the `C¹` theorem, in one line -/

/-- **THE SUBSUMPTION, PROVED.** `LatticeCorrelatedPoincare.poincare_correlated_general` falls out
of §2 and §3 — same statement, same constant, no extra hypothesis. -/
theorem poincare_correlated_general_of_stein (hm : m ≠ 0) {Φ : EuclideanSpace ℝ W → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green K m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField K m) :=
  poincare_correlated_stein hm hmem.1 (fun j => (hgrad j).1)
    (steinPairField_of_contDiff hΦc hmem hgrad)

/-- **AND THE SUBSUMPTION IS MACHINE-CHECKED, NOT EYEBALLED.**

It is not enough that §4 *looks like* `poincare_correlated_general`; a transcription slip would
make this file claim more than it proves. At the same arguments the two conclusions are the **same
proposition** — proof irrelevance closes `A = B` by `rfl` exactly when the types coincide, and it
does. So `LatticeCorrelatedStein` genuinely contains `LatticeCorrelatedPoincare`'s theorem rather
than a near neighbour of it.

*Written after the adversarial review of this file observed that "same statement" had been asserted
in the header on the strength of my having copied it.* -/
example {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {μ : ℝ}
    (hμ : μ ≠ 0) {Φ : EuclideanSpace ℝ V → ℝ} (h1 : ContDiff ℝ 1 Φ)
    (h2 : MemLp Φ 2 (gaussianField G μ))
    (h3 : ∀ j : V, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField G μ)) : True := by
  have A := LatticeCorrelatedPoincare.poincare_correlated_general hμ h1 h2 h3
  have B := poincare_correlated_general_of_stein hμ h1 h2 h3
  have : A = B := rfl
  trivial

end LatticeCorrelatedStein
