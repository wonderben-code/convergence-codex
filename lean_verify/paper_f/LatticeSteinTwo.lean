import LatticeSteinIdentity

/-!
# Two linear factors against an exponential — and a route the records do not have

`LatticeSteinIdentity.stein_identity` is Gaussian integration by parts for this estate's
correlated field, at the **exponential** observable:

```
∫ ⟪a,ω⟫·exp⟪f,ω⟫ dμ = ⟨f,Ga⟩·exp(½⟨f,Gf⟩).
```

This pulls out a **second** linear factor, by one differentiation of exactly the kind the file
above does:

```
∫ ⟪a,ω⟫⟪b,ω⟫·exp⟪f,ω⟫ dμ = (⟨b,Ga⟩ + ⟨f,Ga⟩⟨f,Gb⟩)·exp(½⟨f,Gf⟩).
```

## Why this is more than one more rung

The `UNLOCK_WATCHLIST` records the blocker on general-order Isserlis as

> Gaussian integration by parts for the CORRELATED field at a **product** observable, which this
> estate has only for the exponential and for a power of one test function.

**The exponential observable carries the same information, and this file is the second rung of a
ladder that reaches the product observable without ever needing one.** Write
`T_k(a₁,…,a_k; f) = ∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫`. Then:

* `T_0` is the generating functional, `exp(½⟨f,Gf⟩)` — known;
* `T_1` is `stein_identity` — known;
* `T_2` is this file;
* and `T_{k+1}` is **one differentiation of `T_k`**: replace `f` by `f + s·a_{k+1}`, differentiate
  at `s = 0`, and the integral reading gains the factor `⟪a_{k+1},ω⟫` while the closed reading is
  a polynomial in `s` times `exp` of a quadratic in `s`, so its derivative is a product rule.

**And `T_k(a₁,…,a_k; 0)` is `∫∏ᵢ⟪aᵢ,ω⟫`**, because `exp⟪0,ω⟫ = 1`. That is general-order Isserlis
at `k` arbitrary test functions — `WickPairings.IsserlisGeneral` — reached with **no product
observable anywhere in the argument**.

**WHAT IS AND IS NOT CLAIMED.** The ladder is derived here and its second rung is built. **The
general `k` is NOT proved**, and the honest statement of what stands between is: each rung is one
differentiation, and the closed form at rung `k` is a sum over the partial pairings of
`{a₁,…,a_k}` — the object `Involutions` supplies — so the induction needs that sum written as a
term and differentiated, which is not done here and is **not costed** (`ERRATUM 194`). What this
file does establish is that **the blocker the watchlist names is not the only road**, which is a
different thing from removing it, and the watchlist clause is amended to say so rather than
rewritten.

**⚠ SUPERSEDED 2026-08-27, and the paragraph above is kept as written (`ERRATUM 94`).** *"The
general `k` is NOT proved"* was true for eleven days and is now false. `LadderStep.ladder` builds
every rung of the ladder derived above, by exactly the route the paragraph prescribes — the sum
over partial pairings written as a term (`SteinSumRecursion.steinTerm`) and differentiated
(`LatticeSteinLadder.hasDerivAt_steinSum`) — and `IsserlisAll.isserlisGeneral_all` is its `f = 0`
corollary. **What is NOT superseded is the sentence after it**: this file establishes that the
blocker the watchlist names is not the only road, which stays a different claim from removing it.
`LatticeSteinMajorant` and `LadderStep` removed it, by that road rather than this one.

## What is proved

* `deriv_bound_two` — `‖y·z·exp(x + s·z)‖` bounded, for `|s| ≤ 1`, by six terms each of the form
  `exp(x ± y ± 2z)`, from `abs_le_exp_add_exp_neg` and the file above's `deriv_bound`;
* `integrable_deriv_bound_two` — and each of those six is `exp⟪g,ω⟫` at a test function, so
  `LatticeGeneratingFunctional.integrable_exp_inner` covers them all;
* `hasDerivAt_stein_two_ray`, `hasDerivAt_stein_two_closed` — the two readings;
* **`stein_two`** — the identity;
* `stein_two_zero` — at `f = 0` it degenerates to `∫⟪a,ω⟫⟪b,ω⟫ = ⟨b,Ga⟩`, which
  `LatticeIsserlisSmeared.smeared_twoPoint` proved by polarising a second moment. **A new identity
  that disagreed with an old one at a shared point would be worth knowing about; this one agrees.**

And **the third rung, `T_3`**, because one rung is thin evidence for a ladder:

* `deriv_bound_three`, `integrable_deriv_bound_three` — the same split once more, twelve terms
  `exp(x ± y ± z ± 2w)`, each of them `exp⟪g,ω⟫` at `g = f ± a ± b ± 2c`;
* `hasDerivAt_stein_three_ray`, `hasDerivAt_stein_three_closed`, and **`stein_three`**:
  `∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫exp⟪f,ω⟫ = (⟨c,Ga⟩⟨f,Gb⟩ + ⟨c,Gb⟩⟨f,Ga⟩ + ⟨b,Ga⟩⟨f,Gc⟩ +
  ⟨f,Ga⟩⟨f,Gb⟩⟨f,Gc⟩)·exp(½⟨f,Gf⟩)`. **FOUR TERMS, AND
  `Involutions.card_involutions_fin_three` IS `4`** — the partial pairings of a three-element set,
  three of which pair two of `a, b, c` and contract the third, one of which contracts all three.
  This is the first identity in the estate exhibiting that structure rather than one or two
  special cases of it;
* `stein_three_zero` — and at `f = 0` it vanishes, which is
  `LatticeOddVanishing.integral_prod_odd_eq_zero` at three factors, the first odd order above one.
  **The two statements genuinely meet there**, by routes with no step in common.

Finite volume throughout. **No wall moves. No published tag moves.**
-/

namespace LatticeSteinTwo

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeSteinIdentity

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The majorant, one factor deeper -/

/-- `deriv_bound` with a second linear factor split off by `|y| ≤ eʸ + e⁻ʸ`. Six terms, each an
exponential of an affine function of `x`, `y`, `z`. -/
theorem deriv_bound_two (x y z s : ℝ) (hs : |s| ≤ 1) :
    ‖y * z * Real.exp (x + s * z)‖
      ≤ Real.exp (x + y + 2 * z) + 2 * Real.exp (x + y) + Real.exp (x + y - 2 * z)
        + (Real.exp (x - y + 2 * z) + 2 * Real.exp (x - y) + Real.exp (x - y - 2 * z)) := by
  have hz := deriv_bound x z s hs
  have hy := abs_le_exp_add_exp_neg y
  have hregroup : ‖y * z * Real.exp (x + s * z)‖ = |y| * ‖z * Real.exp (x + s * z)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul]
  rw [hregroup]
  have hstep : |y| * ‖z * Real.exp (x + s * z)‖
      ≤ (Real.exp y + Real.exp (-y))
        * (Real.exp (x + 2 * z) + 2 * Real.exp x + Real.exp (x - 2 * z)) :=
    mul_le_mul hy hz (norm_nonneg _) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
  field_simp

/-- Each of the six is `exp⟪g,ω⟫` at `g = f ± a ± 2b` or `f ± a`, and `integrable_exp_inner` is
stated for **every** test function. -/
theorem integrable_deriv_bound_two (hm : m ≠ 0) (f a b : EuclideanSpace ℝ V) :
    Integrable (fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + 2 * (inner ℝ b ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - 2 * (inner ℝ b ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + 2 * (inner ℝ b ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - 2 * (inner ℝ b ω : ℝ))))
      (gaussianField G m) := by
  have key : ∀ (c d : ℝ), Integrable (fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + c * (inner ℝ a ω : ℝ) + d * (inner ℝ b ω : ℝ)))
      (gaussianField G m) := by
    intro c d
    refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm
      (f + c • a + d • b)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [inner_add_left, real_inner_smul_left]
  have h1 := key 1 2
  have h2 := key 1 0
  have h3 := key 1 (-2)
  have h4 := key (-1) 2
  have h5 := key (-1) 0
  have h6 := key (-1) (-2)
  refine (((h1.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
    (((h2.congr (Filter.Eventually.of_forall fun ω => by ring_nf))).const_mul 2)).add
      (h3.congr (Filter.Eventually.of_forall fun ω => by ring_nf))).add
    (((h4.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
      (((h5.congr (Filter.Eventually.of_forall fun ω => by ring_nf))).const_mul 2)).add
        (h6.congr (Filter.Eventually.of_forall fun ω => by ring_nf)))

/-! ## 2. The two readings of the derivative -/

/-- **THE INTEGRAL READING**, by the same parametric-integral lemma as `stein_identity`, with the
majorant of §1. -/
theorem hasDerivAt_stein_two_ray (hm : m ≠ 0) (f a b : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ)) ∂(gaussianField G m))
      (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (inner ℝ a ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ)) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (inner ℝ a ω : ℝ) * ((inner ℝ b ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ))) with hF'
  have hbase : ∀ s : ℝ, Continuous
      (fun ω : EuclideanSpace ℝ V =>
        Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ))) := fun s =>
    Real.continuous_exp.comp ((continuous_pair f).add (continuous_const.mul (continuous_pair b)))
  have hcont : ∀ s : ℝ, Continuous (F s) := fun s => (continuous_pair a).mul (hbase s)
  have hcont' : ∀ s : ℝ, Continuous (F' s) := fun s =>
    (continuous_pair a).mul ((continuous_pair b).mul (hbase s))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (s : ℝ), HasDerivAt (F · ω) (F' s ω) s := by
    intro ω s
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ b ω : ℝ)) (inner ℝ b ω : ℝ) s := by
      simpa using ((hasDerivAt_id s).mul_const (inner ℝ b ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := hlin.exp.const_mul (inner ℝ a ω : ℝ)
    simp only [hF, hF']
    convert hp using 1
    ring
  have hint0 : Integrable (F 0) μ := by
    have hb : Integrable (fun ω : EuclideanSpace ℝ V =>
        Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ))
          + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ))) μ := by
      have k1 : Integrable (fun ω : EuclideanSpace ℝ V =>
          Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ))) μ := by
        refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm
          (f + (1 : ℝ) • a)).congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only [inner_add_left, real_inner_smul_left]
        ring_nf
      have k2 : Integrable (fun ω : EuclideanSpace ℝ V =>
          Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ))) μ := by
        refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm
          (f + (-1 : ℝ) • a)).congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only [inner_add_left, real_inner_smul_left]
        ring_nf
      exact k1.add k2
    refine Integrable.mono' hb ((hcont 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have habs : ‖F 0 ω‖ = |(inner ℝ a ω : ℝ)| * Real.exp (inner ℝ f ω : ℝ) := by
      simp only [hF, Real.norm_eq_abs, zero_mul, add_zero]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [habs]
    have hy := abs_le_exp_add_exp_neg (inner ℝ a ω : ℝ)
    have hpos : (0 : ℝ) < Real.exp (inner ℝ f ω : ℝ) := Real.exp_pos _
    calc |(inner ℝ a ω : ℝ)| * Real.exp (inner ℝ f ω : ℝ)
        ≤ (Real.exp (inner ℝ a ω : ℝ) + Real.exp (-(inner ℝ a ω : ℝ)))
            * Real.exp (inner ℝ f ω : ℝ) := by
          exact mul_le_mul_of_nonneg_right hy hpos.le
      _ = _ := by
          simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
          field_simp
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + 2 * (inner ℝ b ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - 2 * (inner ℝ b ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + 2 * (inner ℝ b ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - 2 * (inner ℝ b ω : ℝ))))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    hint0
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω s hsm => by
      have hs : |s| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hsm)
      have h := deriv_bound_two (inner ℝ f ω : ℝ) (inner ℝ a ω : ℝ) (inner ℝ b ω : ℝ) s hs
      simpa [hF', mul_assoc] using h)
    (integrable_deriv_bound_two hm f a b)
    (Filter.Eventually.of_forall fun ω s _ => hderiv ω s)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * Real.exp (inner ℝ f ω : ℝ) ∂μ := by
    simp only [hF', zero_mul, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [← hval]
  simpa [hF] using hres.2

/-- **THE CLOSED READING**, and this is where `stein_identity` is spent: the integral is not to be
estimated but evaluated, as a linear factor times `exp` of a quadratic in `s`. One product rule. -/
theorem hasDerivAt_stein_two_closed (hm : m ≠ 0) (f a b : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ)) ∂(gaussianField G m))
      ((dotG G m b a + dotG G m f a * dotG G m f b)
        * Real.exp (linVar G m f / 2)) 0 := by
  have hfun : (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ)) ∂(gaussianField G m))
      = fun s : ℝ => (dotG G m f a + s * dotG G m b a)
          * Real.exp (linVar G m (f + s • b) / 2) := by
    funext s
    have h1 : ∀ ω : EuclideanSpace ℝ V, ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ))
        = (inner ℝ (f + s • b) ω : ℝ) := fun ω => (inner_add_smul f b s ω).symm
    simp only [h1]
    rw [stein_identity hm (f + s • b) a, dotG_add_left, dotG_smul_left]
  rw [hfun]
  have hu : HasDerivAt (fun s : ℝ => dotG G m f a + s * dotG G m b a) (dotG G m b a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m b a)).const_add (dotG G m f a)
  have hv := hasDerivAt_gf_ray (G := G) hm f b
  have hres := hu.mul hv
  convert hres using 1
  simp only [zero_smul, add_zero]
  ring

/-! ## 3. The identity -/

/-- **TWO LINEAR FACTORS AGAINST AN EXPONENTIAL.**

`∫ ⟪a,ω⟫⟪b,ω⟫·exp⟪f,ω⟫ = (⟨b,Ga⟩ + ⟨f,Ga⟩⟨f,Gb⟩)·exp(½⟨f,Gf⟩)`.

Read combinatorially: `⟪a,·⟫` contracts either with `⟪b,·⟫` — leaving `exp` alone — or with the
exponential's argument, after which `⟪b,·⟫` must do the same. **Both terms of the two-element
pairing sum are visible in the statement.** -/
theorem stein_two (hm : m ≠ 0) (f a b : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = (dotG G m b a + dotG G m f a * dotG G m f b) * Real.exp (linVar G m f / 2) :=
  (hasDerivAt_stein_two_ray (G := G) hm f a b).unique (hasDerivAt_stein_two_closed hm f a b)

/-- **AND AT `f = 0` IT DEGENERATES TO `∫⟪a,ω⟫⟪b,ω⟫ = ⟨b,Ga⟩`**, which
`LatticeIsserlisSmeared.smeared_twoPoint` proved by polarising a second moment. A new identity
that disagreed with an old one at a shared point would be worth knowing about; this one agrees. -/
theorem stein_two_zero (hm : m ≠ 0) (a b : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) ∂(gaussianField G m) = dotG G m b a := by
  have h := stein_two (G := G) hm 0 a b
  have hz : dotG G m 0 a = 0 := by simp [dotG]
  have hv : linVar G m 0 = 0 := by simp [linVar_eq_dotG, dotG]
  simp only [inner_zero_left, Real.exp_zero, mul_one, hz, hv, zero_mul, add_zero,
    zero_div] at h
  simpa using h

/-! ## 4. The third rung, where the pairing sum becomes visible

`T_3` is one more differentiation, and what comes out has **four** terms — which is
`Involutions.card_involutions_fin_three`, the number of ways to pair up three things partially.
Three of them pair two of `a, b, c` and contract the third with the exponential's argument; the
fourth contracts all three. **That is the first place in this estate where a Stein-type identity
exhibits the partial-pairing structure rather than one or two special cases of it.** -/

/-- The majorant one factor deeper again: `deriv_bound_two` with a third linear factor split off
by `|y| ≤ eʸ + e⁻ʸ`. Twelve terms, each `exp(x ± y ± z ± 2w)`. -/
theorem deriv_bound_three (x y z w s : ℝ) (hs : |s| ≤ 1) :
    ‖y * z * w * Real.exp (x + s * w)‖
      ≤ Real.exp (x + y + z + 2 * w) + 2 * Real.exp (x + y + z)
          + Real.exp (x + y + z - 2 * w)
        + (Real.exp (x + y - z + 2 * w) + 2 * Real.exp (x + y - z)
          + Real.exp (x + y - z - 2 * w))
      + (Real.exp (x - y + z + 2 * w) + 2 * Real.exp (x - y + z)
          + Real.exp (x - y + z - 2 * w)
        + (Real.exp (x - y - z + 2 * w) + 2 * Real.exp (x - y - z)
          + Real.exp (x - y - z - 2 * w))) := by
  have hzw := deriv_bound_two x z w s hs
  have hy := abs_le_exp_add_exp_neg y
  have hregroup : ‖y * z * w * Real.exp (x + s * w)‖
      = |y| * ‖z * w * Real.exp (x + s * w)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, mul_assoc, ← mul_assoc z, abs_mul]
  rw [hregroup]
  have hstep : |y| * ‖z * w * Real.exp (x + s * w)‖
      ≤ (Real.exp y + Real.exp (-y))
        * (Real.exp (x + z + 2 * w) + 2 * Real.exp (x + z) + Real.exp (x + z - 2 * w)
          + (Real.exp (x - z + 2 * w) + 2 * Real.exp (x - z)
            + Real.exp (x - z - 2 * w))) :=
    mul_le_mul hy hzw (norm_nonneg _) (by positivity)
  refine hstep.trans (le_of_eq ?_)
  simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
  field_simp

/-- Each of the twelve is `exp⟪g,ω⟫` at `g = f ± a ± b ± 2c`. -/
theorem integrable_deriv_bound_three (hm : m ≠ 0) (f a b c : EuclideanSpace ℝ V) :
    Integrable (fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ)))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))))) (gaussianField G m) := by
  have key : ∀ (p q r : ℝ), Integrable (fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + p * (inner ℝ a ω : ℝ) + q * (inner ℝ b ω : ℝ)
        + r * (inner ℝ c ω : ℝ))) (gaussianField G m) := by
    intro p q r
    refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm
      (f + p • a + q • b + r • c)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [inner_add_left, real_inner_smul_left]
  have mk : ∀ (p q : ℝ), Integrable (fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + p * (inner ℝ a ω : ℝ) + q * (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + p * (inner ℝ a ω : ℝ) + q * (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + p * (inner ℝ a ω : ℝ) + q * (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))) (gaussianField G m) := by
    intro p q
    have h1 := key p q 2
    have h2 := key p q 0
    have h3 := key p q (-2)
    exact ((h1.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
      ((h2.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).const_mul 2)).add
        (h3.congr (Filter.Eventually.of_forall fun ω => by ring_nf))
  have m1 := mk 1 1
  have m2 := mk 1 (-1)
  have m3 := mk (-1) 1
  have m4 := mk (-1) (-1)
  refine ((m1.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
    (m2.congr (Filter.Eventually.of_forall fun ω => by ring_nf))).add
      ((m3.congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
        (m4.congr (Filter.Eventually.of_forall fun ω => by ring_nf)))

/-- **THE INTEGRAL READING** at the third rung. -/
theorem hasDerivAt_stein_three_ray (hm : m ≠ 0) (f a b c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * ((inner ℝ c ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))) with hF'
  have hbase : ∀ s : ℝ, Continuous
      (fun ω : EuclideanSpace ℝ V =>
        Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))) := fun s =>
    Real.continuous_exp.comp ((continuous_pair f).add (continuous_const.mul (continuous_pair c)))
  have hcont : ∀ s : ℝ, Continuous (F s) := fun s =>
    ((continuous_pair a).mul (continuous_pair b)).mul (hbase s)
  have hcont' : ∀ s : ℝ, Continuous (F' s) := fun s =>
    ((continuous_pair a).mul (continuous_pair b)).mul ((continuous_pair c).mul (hbase s))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (s : ℝ), HasDerivAt (F · ω) (F' s ω) s := by
    intro ω s
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ c ω : ℝ)) (inner ℝ c ω : ℝ) s := by
      simpa using ((hasDerivAt_id s).mul_const (inner ℝ c ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := hlin.exp.const_mul ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ))
    simp only [hF, hF']
    convert hp using 1
    ring
  have hint0 : Integrable (F 0) μ := by
    have key : ∀ (p q : ℝ), Integrable (fun ω : EuclideanSpace ℝ V =>
        Real.exp ((inner ℝ f ω : ℝ) + p * (inner ℝ a ω : ℝ) + q * (inner ℝ b ω : ℝ))) μ := by
      intro p q
      refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm
        (f + p • a + q • b)).congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [inner_add_left, real_inner_smul_left]
    have hb : Integrable (fun ω : EuclideanSpace ℝ V =>
        Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
          + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ))
        + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
          + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)))) μ :=
      (((key 1 1).congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
        ((key 1 (-1)).congr (Filter.Eventually.of_forall fun ω => by ring_nf))).add
          (((key (-1) 1).congr (Filter.Eventually.of_forall fun ω => by ring_nf)).add
            ((key (-1) (-1)).congr (Filter.Eventually.of_forall fun ω => by ring_nf)))
    refine Integrable.mono' hb ((hcont 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have habs : ‖F 0 ω‖
        = |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * Real.exp (inner ℝ f ω : ℝ) := by
      simp only [hF, Real.norm_eq_abs, zero_mul, add_zero]
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [habs]
    have hya := abs_le_exp_add_exp_neg (inner ℝ a ω : ℝ)
    have hyb := abs_le_exp_add_exp_neg (inner ℝ b ω : ℝ)
    have hpos : (0 : ℝ) < Real.exp (inner ℝ f ω : ℝ) := Real.exp_pos _
    have hprod : |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)|
        ≤ (Real.exp (inner ℝ a ω : ℝ) + Real.exp (-(inner ℝ a ω : ℝ)))
          * (Real.exp (inner ℝ b ω : ℝ) + Real.exp (-(inner ℝ b ω : ℝ))) :=
      mul_le_mul hya hyb (abs_nonneg _) (by positivity)
    calc |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * Real.exp (inner ℝ f ω : ℝ)
        ≤ (Real.exp (inner ℝ a ω : ℝ) + Real.exp (-(inner ℝ a ω : ℝ)))
            * (Real.exp (inner ℝ b ω : ℝ) + Real.exp (-(inner ℝ b ω : ℝ)))
            * Real.exp (inner ℝ f ω : ℝ) := mul_le_mul_of_nonneg_right hprod hpos.le
      _ = _ := by
          simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
          field_simp
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) + (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ)))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ))
      + (Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ))
        + Real.exp ((inner ℝ f ω : ℝ) - (inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)
          - 2 * (inner ℝ c ω : ℝ)))))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    hint0
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω s hsm => by
      have hs : |s| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hsm)
      have h := deriv_bound_three (inner ℝ f ω : ℝ) (inner ℝ a ω : ℝ) (inner ℝ b ω : ℝ)
        (inner ℝ c ω : ℝ) s hs
      simpa [hF', mul_assoc] using h)
    (integrable_deriv_bound_three hm f a b c)
    (Filter.Eventually.of_forall fun ω s _ => hderiv ω s)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
          * Real.exp (inner ℝ f ω : ℝ) ∂μ := by
    simp only [hF', zero_mul, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [← hval]
  simpa [hF] using hres.2

/-- **THE CLOSED READING** at the third rung: `stein_two` at `f + s•c`, one product rule. -/
theorem hasDerivAt_stein_three_closed (hm : m ≠ 0) (f a b c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      ((dotG G m c a * dotG G m f b + dotG G m f a * dotG G m c b) * Real.exp (linVar G m f / 2)
        + (dotG G m b a + dotG G m f a * dotG G m f b)
            * (dotG G m f c * Real.exp (linVar G m f / 2))) 0 := by
  have hfun : (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      = fun s : ℝ => (dotG G m b a
          + (dotG G m f a + s * dotG G m c a) * (dotG G m f b + s * dotG G m c b))
          * Real.exp (linVar G m (f + s • c) / 2) := by
    funext s
    have h1 : ∀ ω : EuclideanSpace ℝ V, ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))
        = (inner ℝ (f + s • c) ω : ℝ) := fun ω => (inner_add_smul f c s ω).symm
    simp only [h1]
    rw [stein_two hm (f + s • c) a b, dotG_add_left, dotG_add_left, dotG_smul_left,
      dotG_smul_left]
  rw [hfun]
  have hu : HasDerivAt (fun s : ℝ => dotG G m b a
      + (dotG G m f a + s * dotG G m c a) * (dotG G m f b + s * dotG G m c b))
      (dotG G m c a * dotG G m f b + dotG G m f a * dotG G m c b) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => dotG G m f a + s * dotG G m c a) (dotG G m c a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m c a)).const_add (dotG G m f a)
    have h2 : HasDerivAt (fun s : ℝ => dotG G m f b + s * dotG G m c b) (dotG G m c b) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m c b)).const_add (dotG G m f b)
    have h3 := (h1.mul h2).const_add (dotG G m b a)
    convert h3 using 1
    simp
  have hv := hasDerivAt_gf_ray (G := G) hm f c
  have hres := hu.mul hv
  convert hres using 1
  simp only [zero_mul, add_zero, zero_smul]

/-- **THREE LINEAR FACTORS AGAINST AN EXPONENTIAL, AND THE PARTIAL-PAIRING SUM IS VISIBLE.**

`∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫exp⟪f,ω⟫ = (⟨c,Ga⟩⟨f,Gb⟩ + ⟨c,Gb⟩⟨f,Ga⟩ + ⟨b,Ga⟩⟨f,Gc⟩ +
⟨f,Ga⟩⟨f,Gb⟩⟨f,Gc⟩)·exp(½⟨f,Gf⟩)`.

**FOUR TERMS, AND `Involutions.card_involutions_fin_three` IS `4`** — the number of ways to pair
three things partially. Three of them pair two of `a, b, c` and contract the third with `f`; the
fourth contracts all three. This is the first identity in the estate that exhibits that structure
rather than one or two special cases of it. -/
theorem stein_three (hm : m ≠ 0) (f a b c : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = (dotG G m c a * dotG G m f b + dotG G m c b * dotG G m f a
          + dotG G m b a * dotG G m f c
          + dotG G m f a * dotG G m f b * dotG G m f c) * Real.exp (linVar G m f / 2) := by
  have h := (hasDerivAt_stein_three_ray (G := G) hm f a b c).unique
    (hasDerivAt_stein_three_closed hm f a b c)
  rw [h]
  ring

/-- **AND AT `f = 0` IT VANISHES**, which `LatticeOddVanishing.integral_prod_odd_eq_zero` says at
every odd order and this estate previously had only for an odd power of one test function. Three
factors is the first odd order above one, so the two statements genuinely meet here. -/
theorem stein_three_zero (hm : m ≠ 0) (a b c : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        ∂(gaussianField G m) = 0 := by
  have h := stein_three (G := G) hm 0 a b c
  have hz : ∀ g : EuclideanSpace ℝ V, dotG G m 0 g = 0 := fun g => by simp [dotG]
  simp only [inner_zero_left, Real.exp_zero, mul_one, hz, zero_mul, mul_zero, add_zero] at h
  simpa using h

end LatticeSteinTwo
