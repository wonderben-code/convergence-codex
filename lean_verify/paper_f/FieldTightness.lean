import GreenLargeMass
import LatticeGeneratingFunctional
import Mathlib.Probability.Moments.Variance

/-!
# One tail bound on the field, with a radius that does not know the volume

`WALLS` §W2.0's first leg needs a measure on an infinite-dimensional space, and the
`UNLOCK_WATCHLIST` item *"the infinite-volume limit along periodic boxes"* splits that into three
clauses. Clause (ii) reads

> *"uniform correlation bounds plus a tightness argument, **which is where the analysis lives**"*

and the phrase *"the analysis is in the half not supplied"* occurs **five** times inside that one
item, across annotations dated 13 and 15 August. Its `ESTIMATE` field says clause (ii) is *"a
research problem, not a formalisation problem"*.

**This file supplies the analytic content of the second half, and it is Chebyshev applied to a
bound this estate proved weeks ago.** That sentence is the finding, not the theorems. It does not
make the item's `ESTIMATE` wrong about the leg — see the four paragraphs below, which are the point
of the file — but it does make it wrong about *which step* the research is in.

## The statements

`variance_eval` — the variance of the field at one site is the diagonal Green entry.

`variance_eval_le` — **and it is at most `m⁻²`, on every finite simple graph at once**, with no
degree hypothesis, no regularity, no reflection, and no reference to a side length. This is
`GreenLargeMass.green_diag_le` read through the field, and that theorem has been in this estate
since it was written.

`meas_abs_ge_le` — Chebyshev at one site.

`radius` and `meas_abs_ge_radius_le` — **the radius is a function of the mass and the tolerance
alone.** Its signature mentions neither the graph, nor its vertex type, nor the site: for every
`ε > 0`, every finite graph, every nonzero mass and every site,

    (gaussianField G m) {ω | radius m ε ≤ |ω x|}  ≤  ε.

That quantifier order is the one an infinite-volume argument needs, and it is why the radius is a
`def` rather than an existential — an existential would let the witness depend on `G` silently.

## **THIS IS NOT TIGHTNESS, AND MUST NOT BE RECORDED AS TIGHTNESS**

Tightness is a statement about **one** family of measures on **one** space: for every `ε` there is a
**compact** `K` with `μₙ(Kᶜ) ≤ ε` for all `n`. Every measure here lives on its own
`EuclideanSpace ℝ V`, a different space for every graph, and a per-site tail bound is not a
statement about a compact set.

**What is missing is not analysis. It is the carrier**, and naming it is the point of this file:
*(Read with the 23 Aug 2026 supersession inside item 1 below: the carrier now exists, and what is
missing is the author's decision in item 2.)*

1. **A single space** — `Π _ : ℤ^d, ℝ` is the natural one, is Polish and Borel in Mathlib with no
   work, and is not defined anywhere in this estate.
   **^ SUPERSEDED 23 Aug 2026 and kept (`ERRATUM 94`): `ConfigSpace.lean` defines it.** `Config ι`
   is `ι → ℝ`, `cube a` is the configurations bounded site by site, `isCompact_cube` is Tychonoff,
   and `compl_cube` says its complement is `{ω | ∃ x, a x < |ω x|}` — **the set §4 below bounds,
   verbatim**. `isTightMeasureSet_of_site_tail` then takes per-site bounds with a summable weight
   and returns `MeasureTheory.IsTightMeasureSet`, Mathlib's own notion. **So item (1) is done and
   item (3) composes with it; what is left of this list is item (2) alone**, which is an author's
   decision and not a construction.
2. **A pushforward of each finite-volume field into it** — extend a field on a box or a torus to
   all of `ℤ^d`. **This is a choice, not a construction**, and it is `ASSUMPTIONS_LEDGER` 47, an
   author's decision. By zero and by periodic repetition give different limits.
3. **The union bound over sites.** A compact subset of a countable product is contained in a
   product of intervals, so the per-site bounds assemble with radii `aₓ` chosen to make a weight
   `∑ₓ wₓ` converge. **An earlier draft of this header said that step was "unstatable before" (1)
   and (2). That was wrong, and §4 below is the correction** — the union bound is provable in
   finite volume right now, with the weight as a parameter, and §4's constant is `∑ₓ wₓ` and
   mentions nothing else about the graph. **What (1) and (2) are actually needed for is to make
   the weight ONE function on ONE index set** instead of a fresh function per volume.

Only after all three does Mathlib's `isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le`
apply — and that theorem, the step clause (ii) calls the analysis, needs nothing from this project
but the tail bounds.

**And it would still not close the leg.** Compactness produces *a* limit measure; showing it is the
`ℤ^d` free field needs `G_n(x,y) → G(x,y)` for the approximants, which nothing here touches. That
is where the analysis actually lives, and clause (ii) named the wrong step.
-/

namespace FieldTightness

open MeasureTheory ProbabilityTheory GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)

/-! ## 1. The variance at a site -/

/-- **THE VARIANCE OF THE FIELD AT ONE SITE IS THE DIAGONAL GREEN ENTRY.** -/
theorem variance_eval (hm : m ≠ 0) (x : V) :
    Var[fun ω : EuclideanSpace ℝ V => ω x; gaussianField G m] = green G m x x := by
  rw [← covariance_self (by fun_prop)]
  exact covariance_eval_multivariateGaussian (green_posDef G hm).posSemidef x x

/-- **AND IT IS AT MOST `m⁻²`, ON EVERY FINITE SIMPLE GRAPH AT ONCE.** No degree bound, no
regularity, no side length: the right-hand side is a function of the mass alone. -/
theorem variance_eval_le (hm : m ≠ 0) (x : V) :
    Var[fun ω : EuclideanSpace ℝ V => ω x; gaussianField G m] ≤ (m ^ 2)⁻¹ := by
  rw [variance_eval G m hm x]
  exact GreenLargeMass.green_diag_le (G := G) hm x

/-! ## 2. Chebyshev -/

/-- **CHEBYSHEV AT ONE SITE.** -/
theorem meas_abs_ge_le (hm : m ≠ 0) (x : V) {a : ℝ} (ha : 0 < a) :
    gaussianField G m {ω : EuclideanSpace ℝ V | a ≤ |ω x|}
      ≤ ENNReal.ofReal ((m ^ 2 * a ^ 2)⁻¹) := by
  have hc := meas_ge_le_variance_div_sq (μ := gaussianField G m)
    (X := fun ω : EuclideanSpace ℝ V => ω x) (memLp_eval G m x) ha
  rw [GraphLaplacian.integral_eval] at hc
  simp only [sub_zero] at hc
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  rw [mul_inv, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (variance_eval_le G m hm x) (le_of_lt ha2)

/-! ## 3. A radius produced from the mass and the tolerance, before any graph -/

/-- The radius beyond which the field at a site is `ε`-improbable. **It is a function of `m` and
`ε` only** — that is the whole content of the definition, and the reason it is a `def`. -/
noncomputable def radius (m ε : ℝ) : ℝ := Real.sqrt ((m ^ 2 * ε)⁻¹)

theorem radius_pos (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) : 0 < radius m ε := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  exact Real.sqrt_pos.mpr (by positivity)

theorem radius_sq (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    radius m ε ^ 2 = (m ^ 2 * ε)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  exact Real.sq_sqrt (by positivity)

/-- **THE TAIL BOUND, WITH THE QUANTIFIERS IN THE ORDER AN INFINITE-VOLUME ARGUMENT NEEDS.**
`radius m ε` mentions neither `G`, nor `V`, nor `x`. -/
theorem meas_abs_ge_radius_le (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) (x : V) :
    gaussianField G m {ω : EuclideanSpace ℝ V | radius m ε ≤ |ω x|} ≤ ENNReal.ofReal ε := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have h := meas_abs_ge_le G m hm x (radius_pos m hm hε)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [radius_sq m hm hε]
  have hcalc : m ^ 2 * (m ^ 2 * ε)⁻¹ = ε⁻¹ := by
    field_simp
  rw [hcalc, inv_inv]

/-! ## 4. The union bound over sites, with the weight as a parameter

**Written as the adversarial review of §§1–3**, which is why it corrects this file's own header
rather than a different file's. §3 above claimed the assembly step was "unstatable before" the
carrier existed. It is statable now: the only thing a fresh index set would change is whether the
weight is one function or one per volume.
-/

/-- **THE UNION BOUND**, with a radius chosen independently at each site. -/
theorem meas_exists_abs_ge_le (hm : m ≠ 0) (a : V → ℝ) (ha : ∀ x, 0 < a x) :
    gaussianField G m {ω : EuclideanSpace ℝ V | ∃ x, a x ≤ |ω x|}
      ≤ ∑ x, ENNReal.ofReal ((m ^ 2 * (a x) ^ 2)⁻¹) := by
  have hset : {ω : EuclideanSpace ℝ V | ∃ x, a x ≤ |ω x|}
      = ⋃ x, {ω : EuclideanSpace ℝ V | a x ≤ |ω x|} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  exact Finset.sum_le_sum fun x _ => meas_abs_ge_le G m hm x (ha x)

/-- **AND WITH THE RADII READ OFF A WEIGHT.** The bound is the weight's total mass and **says
nothing else about the graph**: for any `w`, the field leaves the box `∏ₓ [−radius m (w x),
radius m (w x)]` with probability at most `∑ₓ w x`.

**This is the assembly step, in finite volume.** What a fixed index set would buy is that `w` is
**one** function rather than one per volume — which is the whole of what `ASSUMPTIONS_LEDGER` 47
decides, and is why that decision, and not this inequality, is where the leg stops. -/
theorem meas_exists_abs_ge_radius_le (hm : m ≠ 0) (w : V → ℝ) (hw : ∀ x, 0 < w x) :
    gaussianField G m {ω : EuclideanSpace ℝ V | ∃ x, radius m (w x) ≤ |ω x|}
      ≤ ENNReal.ofReal (∑ x, w x) := by
  refine (meas_exists_abs_ge_le G m hm (fun x => radius m (w x))
    (fun x => radius_pos m hm (hw x))).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => le_of_lt (hw x))]
  refine Finset.sum_le_sum fun x _ => ENNReal.ofReal_le_ofReal ?_
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  rw [radius_sq m hm (hw x)]
  have hcalc : m ^ 2 * (m ^ 2 * w x)⁻¹ = (w x)⁻¹ := by field_simp
  rw [hcalc, inv_inv]

/-- **THE TOLERANCE FORM**, which is the shape a tightness argument quotes: any weight whose total
is at most `ε` gives an `ε`-bound, and the box it names is a product of intervals. -/
theorem meas_exists_abs_ge_radius_le_of_sum_le (hm : m ≠ 0) (w : V → ℝ) (hw : ∀ x, 0 < w x)
    {ε : ℝ} (hsum : ∑ x, w x ≤ ε) :
    gaussianField G m {ω : EuclideanSpace ℝ V | ∃ x, radius m (w x) ≤ |ω x|}
      ≤ ENNReal.ofReal ε :=
  (meas_exists_abs_ge_radius_le G m hm w hw).trans (ENNReal.ofReal_le_ofReal hsum)

end FieldTightness
