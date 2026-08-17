import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# A differentiable function of polynomial growth that is not `C¹`

`LatticeSmearedFromGeneral`'s header states that the estate's two Poincaré theorems separate in
both directions, and after §5 one of those directions is a theorem and the other is still a
sentence. The unproved half, quoted from that header:

> a differentiable `F` with discontinuous derivative and polynomial growth is inside
> `poincare_smeared` and **outside** `poincare_correlated_general`. **STILL ASSERTED, NOT PROVED.**
> The classical witness is `x² sin(1/x)` extended by `0` … **it is not built here**.

This file builds it. **Mathlib does not have this example** — searched by shape across
`Analysis/`, not by name (`ERRATUM 179`) — so it is constructed from the derivative rules.

## What is proved

* `wig`, `wig'` — the function `x ↦ x²·sin(1/x)` extended by `0`, and its derivative;
* `hasDerivAt_wig` — **`wig` is differentiable at every real point**, including the origin, where
  the difference quotient is `x·sin(1/x)` and is squeezed by `|x|`;
* `wig_bound`, `wig'_bound` — **both** have polynomial growth: `|wig x| ≤ 1·(1+x²)` and
  `|wig' x| ≤ 2·(1+x²)`;
* `wig'_bound_sharp` — `|wig' x| ≤ 2|x| + 1`, which is the bound `LatticeSmearedFromGeneral`'s
  header names, proved rather than left as prose;
* **`not_continuous_wig'`** — the derivative is **not** continuous, along `spike n = 1/(2π(n+1))`
  where the cosine term is pinned at `1` while the sine term vanishes;
* **`not_contDiff_wig`** — hence `wig` is not `ContDiff ℝ 1`;
* **`exists_differentiable_polyGrowth_not_contDiff`** — the three facts as one existence statement,
  which is the form `LatticeSmearedFromGeneral`'s header needs.

## What this is NOT

**It does not instantiate the Poincaré inequality at `wig`.** `poincare_smeared` would accept it;
that is the point of the growth bounds. But actually applying that theorem here would require the
lattice imports and this file deliberately has none — it is a statement about `ℝ → ℝ`, and keeping
it that way is what makes it checkable in isolation.

**It says nothing about whether the general theorem could be extended to cover `wig`.** It
establishes that the general theorem *as stated* does not, and nothing more.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace DifferentiableNotC1

open Real Filter Topology
open scoped Real

/-! ## 1. The function and its derivative -/

/-- `x ↦ x²·sin(1/x)`, extended by `0` at the origin. -/
noncomputable def wig (x : ℝ) : ℝ := if x = 0 then 0 else x ^ 2 * Real.sin x⁻¹

/-- Its derivative: `2x·sin(1/x) − cos(1/x)` away from the origin, and `0` at it. -/
noncomputable def wig' (x : ℝ) : ℝ :=
  if x = 0 then 0 else 2 * x * Real.sin x⁻¹ - Real.cos x⁻¹

@[simp] theorem wig_zero : wig 0 = 0 := by simp [wig]

@[simp] theorem wig'_zero : wig' 0 = 0 := by simp [wig']

theorem wig_of_ne {x : ℝ} (hx : x ≠ 0) : wig x = x ^ 2 * Real.sin x⁻¹ := by simp [wig, hx]

theorem wig'_of_ne {x : ℝ} (hx : x ≠ 0) :
    wig' x = 2 * x * Real.sin x⁻¹ - Real.cos x⁻¹ := by simp [wig', hx]

/-! ## 2. Differentiability away from the origin -/

theorem hasDerivAt_wig_of_ne {x : ℝ} (hx : x ≠ 0) : HasDerivAt wig (wig' x) x := by
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx
  have hsin : HasDerivAt (fun y : ℝ => Real.sin y⁻¹) (Real.cos x⁻¹ * -(x ^ 2)⁻¹) x :=
    (Real.hasDerivAt_sin x⁻¹).comp x hinv
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hprod : HasDerivAt (fun y : ℝ => y ^ 2 * Real.sin y⁻¹)
      (2 * x * Real.sin x⁻¹ + x ^ 2 * (Real.cos x⁻¹ * -(x ^ 2)⁻¹)) x := hsq.mul hsin
  have hval : 2 * x * Real.sin x⁻¹ + x ^ 2 * (Real.cos x⁻¹ * -(x ^ 2)⁻¹) = wig' x := by
    rw [wig'_of_ne hx]
    field_simp
    ring
  rw [← hval]
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  exact wig_of_ne hy

/-! ## 3. Differentiability at the origin, where the quotient is squeezed -/

theorem hasDerivAt_wig_zero : HasDerivAt wig (wig' 0) 0 := by
  rw [wig'_zero, hasDerivAt_iff_tendsto_slope]
  have hbd : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ‖slope wig 0 x‖ ≤ ‖x‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have hs : slope wig 0 x = x * Real.sin x⁻¹ := by
      have hnum : wig x - wig 0 = x * (x * Real.sin x⁻¹) := by
        rw [wig_zero, wig_of_ne hx0, sub_zero, sq, mul_assoc]
      rw [slope_def_field, hnum, sub_zero]
      exact mul_div_cancel_left₀ _ hx0
    rw [hs, norm_mul]
    have : ‖Real.sin x⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
    nlinarith [norm_nonneg x, this, norm_nonneg (Real.sin x⁻¹)]
  refine squeeze_zero_norm' hbd ?_
  exact (continuous_norm.tendsto' 0 0 (by simp)).comp nhdsWithin_le_nhds

theorem hasDerivAt_wig (x : ℝ) : HasDerivAt wig (wig' x) x := by
  by_cases hx : x = 0
  · subst hx; exact hasDerivAt_wig_zero
  · exact hasDerivAt_wig_of_ne hx

theorem differentiable_wig : Differentiable ℝ wig := fun x => (hasDerivAt_wig x).differentiableAt

/-! ## 4. Both have polynomial growth -/

theorem wig_bound (x : ℝ) : |wig x| ≤ 1 * (1 + x ^ 2) ^ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [wig_of_ne hx, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2)]
    have h1 : |Real.sin x⁻¹| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [sq_nonneg x, abs_nonneg (Real.sin x⁻¹)]

/-- **The sharp derivative bound, which is the one `LatticeSmearedFromGeneral`'s header names.**
`|wig′ x| ≤ 2|x| + 1`, at every real point including the origin. -/
theorem wig'_bound_sharp (x : ℝ) : |wig' x| ≤ 2 * |x| + 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [wig'_of_ne hx]
    have hs : |Real.sin x⁻¹| ≤ 1 := Real.abs_sin_le_one _
    have hc : |Real.cos x⁻¹| ≤ 1 := Real.abs_cos_le_one _
    have hstep : |2 * x * Real.sin x⁻¹ - Real.cos x⁻¹|
        ≤ |2 * x * Real.sin x⁻¹| + |Real.cos x⁻¹| := abs_sub _ _
    have h2 : |2 * x * Real.sin x⁻¹| ≤ 2 * |x| := by
      rw [abs_mul, abs_mul]
      simp only [abs_two]
      nlinarith [abs_nonneg x, hs, abs_nonneg (Real.sin x⁻¹)]
    linarith

theorem wig'_bound (x : ℝ) : |wig' x| ≤ 2 * (1 + x ^ 2) ^ 1 := by
  have h3 : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have h4 : (0:ℝ) ≤ x ^ 2 := sq_nonneg x
  have := wig'_bound_sharp x
  simp only [pow_one]
  linarith

/-! ## 5. The derivative is not continuous -/

/-- The sample points `1/(2π(n+1))`, on which the cosine term is pinned at `1`. -/
noncomputable def spike (n : ℕ) : ℝ := (2 * π * (n + 1))⁻¹

theorem spike_ne_zero (n : ℕ) : spike n ≠ 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have : (0:ℝ) < 2 * π * (n + 1) := by positivity
  simp only [spike]
  exact inv_ne_zero (ne_of_gt this)

theorem wig'_spike (n : ℕ) : wig' (spike n) = -1 := by
  have hne := spike_ne_zero n
  have hinv : (spike n)⁻¹ = 2 * π * (n + 1) := by
    simp only [spike]
    rw [inv_inv]
  rw [wig'_of_ne hne, hinv]
  have hs : Real.sin (2 * π * (n + 1)) = 0 := by
    have he : (2 : ℝ) * π * (n + 1) = ((2 * (n + 1) : ℤ) : ℝ) * π := by push_cast; ring
    rw [he]
    exact Real.sin_int_mul_pi _
  have hc : Real.cos (2 * π * (n + 1)) = 1 := by
    have he : (2 : ℝ) * π * (n + 1) = ((n + 1 : ℕ) : ℝ) * (2 * π) := by push_cast; ring
    rw [he]
    exact Real.cos_nat_mul_two_pi _
  rw [hs, hc]
  ring

theorem tendsto_spike : Tendsto spike atTop (𝓝 0) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => 2 * π * ((n : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) h1
  simpa [spike] using tendsto_inv_atTop_zero.comp h2

/-- **THE DERIVATIVE IS NOT CONTINUOUS.** Along `spike`, which tends to `0`, it is constantly
`-1`, while at `0` it is `0`. -/
theorem not_continuous_wig' : ¬ Continuous wig' := by
  intro hc
  have h1 : Tendsto (fun n => wig' (spike n)) atTop (𝓝 (wig' 0)) :=
    (hc.tendsto 0).comp tendsto_spike
  rw [wig'_zero] at h1
  have h2 : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 0) := by
    simp only [wig'_spike] at h1
    exact h1
  have := tendsto_nhds_unique h2 tendsto_const_nhds
  norm_num at this

/-- **AND SO `wig` IS NOT `ContDiff ℝ 1`.** -/
theorem not_contDiff_wig : ¬ ContDiff ℝ 1 wig := by
  intro h
  have hderiv : deriv wig = wig' := funext fun x => (hasDerivAt_wig x).deriv
  exact not_continuous_wig' (hderiv ▸ h.continuous_deriv le_rfl)

/-! ## 6. The three facts as one statement -/

/-- **THE WITNESS `LatticeSmearedFromGeneral`'S HEADER NAMED.**

There is a function `ℝ → ℝ` that is differentiable everywhere, whose derivative has polynomial
growth alongside it, and which is **not** `ContDiff ℝ 1`. That is exactly
`LatticePoincare.poincare_smeared`'s hypothesis pattern together with the failure of
`LatticeCorrelatedPoincare.poincare_correlated_general`'s. -/
theorem exists_differentiable_polyGrowth_not_contDiff :
    ∃ (F F' : ℝ → ℝ) (C : ℝ) (k : ℕ),
      (∀ x, HasDerivAt F (F' x) x)
      ∧ (∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k)
      ∧ (∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k)
      ∧ ¬ ContDiff ℝ 1 F :=
  ⟨wig, wig', 2, 1, hasDerivAt_wig,
    fun x => (wig_bound x).trans (by nlinarith [sq_nonneg x]),
    wig'_bound, not_contDiff_wig⟩

end DifferentiableNotC1
