import GreenQuadFormSharp
import LatticeOSPackage

/-!
# OS0's finite-volume constant is the smallest that works, at every fixed graph

`LatticeOSPackage.RegularFinVol` names finite-volume regularity — `∫ exp ⟪f, ω⟫ ≤ exp(‖f‖²/(2m²))`
— and `LatticeRegularity.generatingFunctional_le` proves it, with a constant **naming no graph**.
Both files say what the bound is and neither says whether `(2m²)⁻¹` can be lowered. **It cannot, and
not merely for the class**: at *each fixed graph* the bound is an **equality** at one test function.

`GreenQuadFormSharp` did exactly this one level down, for the quadratic form: `quadForm_green_one`
is the equality case at every graph and `le_of_quadForm_green_le` turns it into optimality of `m⁻²`.
**This file carries that step through the exponential**, where the statement is about the OS axiom's
constant rather than about a matrix.

## What is proved

**`generatingFunctional_at_one`** — at the all-ones test function the generating functional is
exactly `exp(|V| / (2m²))`, on every finite graph. The constant vector is an eigenvector of `green`
at `m⁻²` (`GreenExpansion.green_mulVec_one`), which is the same witness `GreenNormExact` uses for
the operator norm and `GreenQuadFormSharp` for the form.

**`le_of_generatingFunctional_le`** — so any `c` with `∫ exp ⟪f, ω⟫ ≤ exp(c‖f‖²)` for all `f`
satisfies `(2m²)⁻¹ ≤ c`. **`regularFinVol_optimal`** states the consequence in the package's own
vocabulary: `RegularFinVol`'s constant is the least one for which the property can hold.

## What is NOT here

**No new bound and no new axiom.** Everything above the equality is quoted:
`LatticeGeneratingFunctional.generatingFunctional`, `GreenQuadFormSharp.quadForm_green_one`,
`LatticeRegularity.sum_sq_eq_norm_sq`. **The one new fact is the equality case at the exponential
level**, and the file is short because that is all it adds.

**`OS0` in the continuum sense is untouched**, as `LatticeOSPackage`'s own table says in the column
headed *"the continuum statement it is NOT"*: a bound on Schwartz test functions yielding a
distribution-valued measure. Optimality of a finite-volume constant says nothing about it.

**`OS4` is untouched.** The watchlist's other open axiom is clustering, and this file neither uses
nor states `LatticeFieldFactorises.generatingFunctional_add_of_separated`.

**Nothing about `m = 0`**, and nothing about an empty vertex type — `Nonempty V` is what makes the
witness a nonzero test function, exactly as in `GreenQuadFormSharp.le_of_quadForm_green_le`.

**No wall moves.**

> **WHY THIS FILE IS SHORT, AND IT IS THE UNIT'S REAL FINDING** (`ERRATUM 450`). Its first draft was
> a file called `LatticeOS0` that stated `RegularFinVol`, proved `generatingFunctional_le` and
> bounded the quadratic form — **four declarations that already existed**, in `LatticeOSPackage`,
> `LatticeRegularity` and `LatticeUniformPoincare`. The absence claim behind it came from a `grep`
> whose output was piped through `head`: the ten lines shown were all `CascadeFoundation` and `F*`
> commentary, and **the `paper_f` hits were below the cut**. `newnames_scan` caught all four before
> the commit. What survived the audit is this file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeRegularitySharp

open Matrix GraphLaplacian MeasureTheory
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The bound is attained -/

/-- **THE GENERATING FUNCTIONAL AT THE ALL-ONES TEST FUNCTION**, exactly, on every finite graph:
`exp(|V| / (2m²))` — which is `LatticeRegularity.generatingFunctional_le`'s bound with no slack.
The witness is the constant eigenvector, `GreenExpansion.green_mulVec_one`. -/
theorem generatingFunctional_at_one (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0) :
    ∫ ω, Real.exp ⟪(WithLp.toLp 2 (fun _ : V => (1 : ℝ)) : EuclideanSpace ℝ V), ω⟫
        ∂(gaussianField G m)
      = Real.exp (Fintype.card V / (2 * m ^ 2)) := by
  rw [LatticeGeneratingFunctional.generatingFunctional (G := G) (m := m) hm]
  congr 1
  have hq : (fun _ : V => (1 : ℝ)) ⬝ᵥ green G m *ᵥ (fun _ : V => (1 : ℝ))
      = (m ^ 2)⁻¹ * ∑ _j : V, (1 : ℝ) ^ 2 := GreenQuadFormSharp.quadForm_green_one G hm
  rw [hq]
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-! ## 2. So no smaller constant works, at this graph -/

/-- **THE CONSTANT `(2m²)⁻¹` CANNOT BE LOWERED AT ANY FIXED GRAPH.** `GreenQuadFormSharp`'s
`le_of_quadForm_green_le` is this one level down, for the quadratic form. -/
theorem le_of_generatingFunctional_le [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) {c : ℝ} (h : ∀ f : EuclideanSpace ℝ V,
      ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ≤ Real.exp (c * ‖f‖ ^ 2)) :
    (2 * m ^ 2)⁻¹ ≤ c := by
  classical
  set u : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ)) with hu
  have hnorm : ‖u‖ ^ 2 = (Fintype.card V : ℝ) := by
    rw [← LatticeRegularity.sum_sq_eq_norm_sq u, hu]
    simp
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hle := h u
  rw [generatingFunctional_at_one G hm, hnorm, Real.exp_le_exp, div_eq_inv_mul] at hle
  exact le_of_mul_le_mul_right hle hcard

/-- **AND SO `RegularFinVol`'S CONSTANT IS OPTIMAL**, in the package's own vocabulary: the property
holds, and it fails for every smaller constant at every finite nonempty graph. -/
theorem regularFinVol_optimal [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0) :
    LatticeOSPackage.RegularFinVol G m ∧
      ∀ c : ℝ, (∀ f : EuclideanSpace ℝ V,
        ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ≤ Real.exp (c * ‖f‖ ^ 2)) →
        (2 * m ^ 2)⁻¹ ≤ c :=
  ⟨LatticeOSPackage.gaussianField_regularFinVol hm,
    fun _ hc => le_of_generatingFunctional_le G hm hc⟩

end LatticeRegularitySharp
