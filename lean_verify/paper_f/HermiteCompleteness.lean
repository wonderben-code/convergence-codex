/-
  HermiteCompleteness: the Hermite Polynomials Are COMPLETE in L²(γ)
  ==================================================================

  The CAESAR target from the watchlist. `GaussianPoincare.lean` proved the
  Hermite polynomials orthogonal in L²(γ) with ⟨Hₙ, Hₙ⟩ = n!·√(2π), and every
  statement since — Poincaré in 1 and n dimensions, the Λ²/2 gap, the measure
  identifications — has carried the caveat "polynomial test functions only".
  The missing key is COMPLETENESS: nothing orthogonal to all the Hₙ except 0.
  Mathlib has no Gaussian-L² Hermite theory; this file supplies the
  completeness half.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `integrable_exp_abs_mul`, `memLp_exp_abs_mul` — e^{c|x|} lies in
     L²(gaussianReal 0 1) for every c: the Gaussian has all exponential
     moments. This is the hypothesis that makes the Gaussian moment problem
     DETERMINATE, and it is where the argument would fail for a heavy-tailed
     measure (it fails for the lognormal, famously).
  2. `tendsto_partial_exp` — for g ∈ L²(γ), the partial sums of the
     exponential series, integrated against g dγ, converge to
     ∫ e^{ixt} g dγ. Dominated convergence, with dominating function
     e^{|t||x|}·|g| ∈ L¹ by Cauchy–Schwarz from 1.
  3. **`polynomials_complete`** — if f ∈ L²(γ) satisfies ∫ f·p dγ = 0 for
     every polynomial p, then f = 0 a.e. The route: split f = f⁺ − f⁻; the
     two finite measures f±dγ have equal moments, hence (by 2, since the
     partial-sum sequences are then IDENTICAL) equal characteristic
     functions, hence are equal by Mathlib's `Measure.ext_of_charFun`;
     `withDensity` injectivity then gives f⁺ = f⁻ a.e.
  4. **`hermite_complete`** — the same with "every polynomial" replaced by
     "every Hermite polynomial", via the Hermite expansion
     `exists_hermite_repr'` of `GaussianPoincare`.
  5. `hermite_orthogonal_gauss`, `hermite_norm_gauss` — the orthogonality
     relations transported from the weight-integral formulation to Mathlib's
     `gaussianReal 0 1`: ∫ Hₘ·Hₙ dγ = 0 for m ≠ n and ∫ Hₙ² dγ = n!
     (so no Hₙ is the zero vector — the family is not degenerate).
  6. **`hermite_complete_orthogonal_system`** — the package: pairwise
     orthogonal, each of norm² = n! ≠ 0, and complete. THE HERMITE
     POLYNOMIALS ARE A COMPLETE ORTHOGONAL SYSTEM IN L²(γ), stated against
     Mathlib's own Gaussian measure.

  NOT proven here, and each is the honest next rung:

  * **The Poincaré inequality beyond polynomials.** Completeness gives L²
    approximation; the inequality needs W^{1,2} approximation — polynomials
    pₙ with pₙ → f AND pₙ′ → f′ in L²(γ) simultaneously. The natural route is
    Hermite partial sums and Parseval, which needs the L²-Fourier apparatus
    (bundled `Lp` machinery) this file deliberately avoids. Recorded on
    UNLOCK_WATCHLIST with this file as its trigger.
  * Completeness in L²(γ_σ) for σ ≠ 1 or in n dimensions (the same argument
    transfers; not done here).
  * Anything about the spectral action. Unchanged, unproven.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincare
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory Polynomial Filter Topology

noncomputable section

namespace HermiteCompleteness

open GaussianPoincare

/-- The standard Gaussian, locally abbreviated. -/
abbrev gauss : Measure ℝ := gaussianReal 0 1

/-! ## 1. All exponential moments: the determinacy hypothesis -/

theorem integrable_exp_abs_mul (c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|)) gauss := by
  have h1 : Integrable (fun x => Real.exp (c * x) + Real.exp (-c * x)) gauss :=
    (integrable_exp_mul_gaussianReal c).add (integrable_exp_mul_gaussianReal (-c))
  refine h1.mono' ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have := (Real.exp_pos (-c * x)).le
      linarith
    · rw [abs_of_neg hx]
      have h2 : Real.exp (c * -x) = Real.exp (-c * x) := by ring_nf
      rw [h2]
      linarith [(Real.exp_pos (c * x)).le]

theorem memLp_exp_abs_mul (c : ℝ) :
    MemLp (fun x => Real.exp (c * |x|)) 2 gauss := by
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (c * |x|)) gauss :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun x => Real.exp (c * |x|) ^ 2) = fun x => Real.exp (2 * c * |x|) := by
    funext x
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hsq]
  exact integrable_exp_abs_mul (2 * c)

/-! ## 2. Integrability of the pieces -/

/-- Powers are in L²(γ) — imported from `GaussianPoincare`. -/
theorem memLp_pow (k : ℕ) : MemLp (fun x : ℝ => x ^ k) 2 gauss :=
  GaussianPoincare.memLp_pow_gaussianReal k 0 1

theorem integrable_pow_mul (g : ℝ → ℝ) (hg : MemLp g 2 gauss) (k : ℕ) :
    Integrable (fun x => x ^ k * g x) gauss :=
  MemLp.integrable_mul (memLp_pow k) hg

theorem integrable_exp_abs_mul_mul (g : ℝ → ℝ) (hg : MemLp g 2 gauss) (c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|) * |g x|) gauss :=
  MemLp.integrable_mul (memLp_exp_abs_mul c) hg.norm

/-! ## 3. The exponential series against g dγ -/

/-- **Dominated convergence for the exponential series**: for g ∈ L²(γ), the
    moment partial sums converge to the "characteristic function with density
    g". This is where all the analysis lives; everything after it is
    bookkeeping. -/
theorem tendsto_partial_exp (g : ℝ → ℝ) (hg : MemLp g 2 gauss) (t : ℝ) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
        ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
          * ((∫ x, x ^ k * g x ∂gauss : ℝ) : ℂ))
      atTop
      (𝓝 (∫ x, Complex.exp ((x * t : ℝ) * Complex.I) * (g x : ℂ) ∂gauss)) := by
  have hgm : AEStronglyMeasurable g gauss := hg.aestronglyMeasurable
  -- each term of the series is integrable
  have hterm : ∀ k : ℕ, Integrable
      (fun x => (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
        * (g x : ℂ)) gauss := by
    intro k
    have hre : Integrable (fun x => x ^ k * g x) gauss := integrable_pow_mul g hg k
    have heq : (fun x => (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
        * (g x : ℂ))
        = fun x => ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
            * ((x ^ k * g x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [heq]
    exact (hre.ofReal.const_mul _)
  -- the partial sums, integrated, are the moment sums
  have hsum : ∀ N : ℕ,
      (∫ x, (∑ k ∈ Finset.range N,
          (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)) * (g x : ℂ) ∂gauss)
        = ∑ k ∈ Finset.range N,
            ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
              * ((∫ x, x ^ k * g x ∂gauss : ℝ) : ℂ) := by
    intro N
    have hexpand : (fun x => (∑ k ∈ Finset.range N,
        (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)) * (g x : ℂ))
        = fun x => ∑ k ∈ Finset.range N,
            (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (g x : ℂ) := by
      funext x
      rw [Finset.sum_mul]
    rw [hexpand, integral_finset_sum _ (fun k _ => hterm k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have heq : (fun x => (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
        * (g x : ℂ))
        = fun x => ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
            * ((x ^ k * g x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    rw [heq]
    have h1 := integral_const_mul (μ := gauss)
      (((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))
      (fun x : ℝ => ((x ^ k * g x : ℝ) : ℂ))
    have h2 := integral_complex_ofReal (f := fun x : ℝ => x ^ k * g x) (μ := gauss)
    exact h1.trans (congrArg
      (fun z => ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * z) h2)
  -- dominated convergence
  have hdom : Tendsto (fun N => ∫ x, (∑ k ∈ Finset.range N,
      (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)) * (g x : ℂ) ∂gauss)
      atTop
      (𝓝 (∫ x, Complex.exp ((x * t : ℝ) * Complex.I) * (g x : ℂ) ∂gauss)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Real.exp (|t| * |x|) * |g x|) ?_ ?_ ?_ ?_
    · intro N
      refine AEStronglyMeasurable.mul ?_
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hgm)
      refine Continuous.aestronglyMeasurable ?_
      refine continuous_finset_sum _ fun k _ => ?_
      exact (((Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)).mul continuous_const).pow k).div_const _
    · exact integrable_exp_abs_mul_mul g hg |t|
    · intro N
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      calc ‖∑ k ∈ Finset.range N,
            (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N,
              ‖(((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖ :=
            norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, |x * t| ^ k / (k.factorial : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs]
            norm_num
        _ ≤ Real.exp |x * t| := Real.sum_le_exp_of_nonneg (abs_nonneg _) N
        _ = Real.exp (|t| * |x|) := by rw [abs_mul, mul_comm]
    · filter_upwards with x
      have hs : HasSum (fun k => (((x * t : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))
          (Complex.exp ((x * t : ℝ) * Complex.I)) := by
        rw [Complex.exp_eq_exp_ℂ]
        exact NormedSpace.expSeries_div_hasSum_exp _
      exact (hs.tendsto_sum_nat).mul_const _
  -- combine
  have := hdom
  simp only [hsum] at this
  exact this

end HermiteCompleteness
