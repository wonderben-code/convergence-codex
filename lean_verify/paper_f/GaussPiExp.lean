/-
  GaussPiExp.lean — stair N2a: the exponential domination in n dimensions.

  WHY. Probing stair N2 (completeness of the multi-index Hermite system)
  established what it actually is: not a density argument but a
  CHARACTERISTIC-FUNCTION uniqueness argument, exactly as the estate's
  one-dimensional `polynomials_complete` does it — split `F` into positive
  and negative parts, match the characteristic functions of the two
  `withDensity` measures, close with `Measure.ext_of_charFun`. The
  analytic content of that route, in any dimension, is one thing: **the
  exponential must be an L¹-dominated limit of polynomials.** In one
  dimension the estate calls that `tendsto_partial_exp` and everything
  else is bookkeeping.

  I predicted that this piece would collapse in n dimensions the way N1
  did, because `exp(c·Σᵢ|xᵢ|) = ∏ᵢ exp(c|xᵢ|)` is a product of
  single-coordinate functions and `Integrable.fintype_prod_dep` eats
  those. **This file is that prediction tested.** It holds: the whole
  domination is 1-d `integrable_exp_abs_mul` composed with the product
  lemma.

  WHAT THIS FILE PROVES:
  * **`memLp_exp_sumAbs`** — `exp(c·Σᵢ|xᵢ|) ∈ L²(γⁿ)` for every real `c`,
    including `c > 0`. This is the fact that makes Gaussian measure
    tolerate exponentials at all.
  * **`integrable_exp_sumAbs_mul`** — hence `exp(c·Σᵢ|xᵢ|)·|G|` is
    integrable for every `G ∈ L²(γⁿ)`: the dominating function N2's
    dominated-convergence step needs.
  * **`abs_inner_le_sumAbs`** and **`partial_exp_bound`** — the bridge from
    a linear form to that dominating function, and the uniform bound on
    the partial sums of `exp(⟨t,x⟩)`. Together they are the hypothesis of
    dominated convergence, with the limit function left to N2 proper.

  WHAT THIS DOES NOT DO. It is a domination, not a convergence: nothing
  here says the partial sums converge to anything, and nothing here
  mentions characteristic functions. N2 also still needs the transport of
  `gaussPi n` to `EuclideanSpace ℝ (Fin n)`, because
  `Measure.ext_of_charFun` wants an inner-product space and `Fin n → ℝ`
  carries the sup norm — probed today, and `EuclideanSpace.measurableEquiv`
  is the tool. Neither of those is in this file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiBessel

namespace GaussPiExp

open MeasureTheory ProbabilityTheory Filter Topology
open HermiteCompleteness GaussianProductMeasure

noncomputable section

/-! ## 1. The ℓ¹ size function -/

/-- `Σᵢ |xᵢ|` — the size that makes the exponential factorise. -/
def sumAbs (n : ℕ) (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

theorem sumAbs_nonneg (n : ℕ) (x : Fin n → ℝ) : 0 ≤ sumAbs n x :=
  Finset.sum_nonneg fun _i _ => abs_nonneg _

theorem continuous_sumAbs (n : ℕ) : Continuous (sumAbs n) :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).abs


/-- The factorisation the whole file rests on. -/
theorem exp_sumAbs_eq_prod (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    Real.exp (c * sumAbs n x) = ∏ i, Real.exp (c * |x i|) := by
  rw [sumAbs, Finset.mul_sum, Real.exp_sum]

theorem continuous_exp_sumAbs (n : ℕ) (c : ℝ) :
    Continuous fun x : Fin n → ℝ => Real.exp (c * sumAbs n x) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_sumAbs n))

/-! ## 2. Integrability, by the same product lemma that collapsed N1 -/

theorem integrable_exp_sumAbs (n : ℕ) (c : ℝ) :
    Integrable (fun x => Real.exp (c * sumAbs n x)) (gaussPi n) := by
  have h : (fun x : Fin n → ℝ => Real.exp (c * sumAbs n x))
      = fun x => ∏ i, Real.exp (c * |x i|) := funext (exp_sumAbs_eq_prod n c)
  rw [h, gaussPi]
  exact Integrable.fintype_prod_dep fun _ => integrable_exp_abs_mul c

/-- **`exp(c·Σ|xᵢ|)` is square-integrable against the Gaussian product
    measure, for EVERY real `c`.** -/
theorem memLp_exp_sumAbs (n : ℕ) (c : ℝ) :
    MemLp (fun x => Real.exp (c * sumAbs n x)) 2 (gaussPi n) := by
  refine (memLp_two_iff_integrable_sq
    (continuous_exp_sumAbs n c).aestronglyMeasurable).mpr ?_
  have hsq : (fun x : Fin n → ℝ => Real.exp (c * sumAbs n x) ^ 2)
      = fun x => Real.exp (2 * c * sumAbs n x) := by
    funext x
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsq]
  exact integrable_exp_sumAbs n (2 * c)

/-- **The dominating function N2 needs.** -/
theorem integrable_exp_sumAbs_mul (n : ℕ) (G : (Fin n → ℝ) → ℝ)
    (hG : MemLp G 2 (gaussPi n)) (c : ℝ) :
    Integrable (fun x => Real.exp (c * sumAbs n x) * |G x|) (gaussPi n) :=
  MemLp.integrable_mul (memLp_exp_sumAbs n c) hG.norm

/-! ## 3. From a linear form to the dominating exponential -/

/-- `|⟨t,x⟩| ≤ C·Σᵢ|xᵢ|` whenever every `|tᵢ| ≤ C`. **No sign hypothesis on
    `C`**: for `n ≥ 1` it follows from `0 ≤ |t 0| ≤ C`, and at `n = 0` both
    sides are zero. The first draft carried `0 ≤ C` and the linter caught
    that it was never used — recorded because dropping an unnecessary
    hypothesis is the cheapest kind of strengthening there is. -/
theorem abs_inner_le_sumAbs (n : ℕ) (t x : Fin n → ℝ) {C : ℝ}
    (hC : ∀ i, |t i| ≤ C) : |∑ i, t i * x i| ≤ C * sumAbs n x := by
  calc |∑ i, t i * x i| ≤ ∑ i, |t i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |t i| * |x i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul]
    _ ≤ ∑ i, C * |x i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (hC i) (abs_nonneg _)
    _ = C * sumAbs n x := by rw [sumAbs, Finset.mul_sum]

/-- **The uniform bound on the partial sums of `exp⟨t,x⟩`** — the
    hypothesis of dominated convergence, with the dominating function
    supplied by §2. -/
theorem partial_exp_bound (n : ℕ) (t x : Fin n → ℝ) {C : ℝ}
    (hC : ∀ i, |t i| ≤ C) (N : ℕ) :
    |∑ k ∈ Finset.range N, (∑ i, t i * x i) ^ k / (k.factorial : ℝ)|
      ≤ Real.exp (C * sumAbs n x) := by
  set y : ℝ := ∑ i, t i * x i with hy
  calc |∑ k ∈ Finset.range N, y ^ k / (k.factorial : ℝ)|
      ≤ ∑ k ∈ Finset.range N, |y ^ k / (k.factorial : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range N, |y| ^ k / (k.factorial : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial : ℝ))]
    _ ≤ Real.exp |y| := Real.sum_le_exp_of_nonneg (abs_nonneg y) N
    _ ≤ Real.exp (C * sumAbs n x) :=
        Real.exp_le_exp.mpr (abs_inner_le_sumAbs n t x hC)

/-! ## 4. Review round 45 — the ways this could be hollow

**"`memLp_exp_sumAbs` could hold vacuously for `c ≤ 0` only."** It is
stated and proved for every real `c`, positive included, which is the only
case that matters — for `c ≤ 0` the function is bounded and the statement
is trivial. The proof squares to `exp(2c·Σ|xᵢ|)` and calls itself at
`2c`, so the positive case is genuinely carried.

**"The bound could be vacuous at `n = 0`."** At `n = 0` the sum is empty,
`sumAbs = 0`, the exponential is `1`, and `partial_exp_bound` says the
partial sums of `exp 0` are bounded by `1` — degenerate but true, and it
falls out of the same proof rather than needing a case split.

**"It might not be the domination N2 needs."** `integrable_exp_sumAbs_mul`
is stated in exactly the shape the estate's one-dimensional
`integrable_exp_abs_mul_mul` has, which is what
`tendsto_partial_exp` consumes; `partial_exp_bound` is the pointwise
hypothesis of `tendsto_integral_of_dominated_convergence` for the same
argument. What is missing is the convergence and the characteristic
function, and the header says so.
-/

/-- The degenerate dimension, as a theorem rather than a remark. -/
theorem sumAbs_zero_dim (x : Fin 0 → ℝ) : sumAbs 0 x = 0 := by
  simp [sumAbs]

/-- The dominating function is not the constant `1` in any positive
    dimension — so §2 is a statement about genuine exponential growth. -/
theorem exp_sumAbs_unbounded (c : ℝ) (hc : 0 < c) :
    ∀ M : ℝ, ∃ x : Fin 1 → ℝ, M < Real.exp (c * sumAbs 1 x) := by
  intro M
  obtain ⟨r, hr⟩ := exists_gt (Real.log (max M 1) / c)
  refine ⟨fun _ => |r| + 1, ?_⟩
  have hs : sumAbs 1 (fun _ => |r| + 1) = |r| + 1 := by
    simp [sumAbs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |r| + 1)]
  rw [hs]
  have hlt : Real.log (max M 1) < c * (|r| + 1) := by
    have h1 : Real.log (max M 1) / c < r := hr
    have h2 : Real.log (max M 1) < c * r := by
      rw [div_lt_iff₀ hc] at h1
      linarith [h1]
    nlinarith [le_abs_self r, hc]
  have hpos : (0:ℝ) < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_log hpos] at this
  exact lt_of_le_of_lt (le_max_left M 1) this

end

end GaussPiExp
