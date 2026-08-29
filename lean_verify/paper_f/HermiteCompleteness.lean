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
     measure (classically it fails for the lognormal; that classical fact is
     motivation here, not something formalised).
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
  5. `hermite_orthogonal_gauss`, `hermite_norm_sq_gauss` — the orthogonality
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

    ⚠ BOTH HALVES ARE NOW DONE, AND BY DIFFERENT FILES. The n-dimensional
    half is `HermitePiComplete`, which reduces to the one-dimensional
    `hermite_complete` twice. The variance half is
    `HermiteScaledComplete.polynomials_complete_scaled` and
    `hermite_complete_scaled`, added 2026-08-29 — and the sentence above was
    right that "the same argument transfers", with one wrinkle it did not
    foresee: the transported object is an L² function rather than a
    differentiable one, so it is only AEStronglyMeasurable, and
    `PoincareScaledBeyond.integral_scaled` asks for Measurable.
    `HermiteScaledComplete.integral_scaled_ae` is that change of variables
    with the hypothesis weakened. The scaled file also proves the
    orthogonality and the norms, so
    `hermite_complete_orthogonal_system_scaled` is the full analogue of item
    6 below. The polynomial completeness holds at EVERY σ including σ = 0,
    where the measure is δ₀ and orthogonality to the constant polynomial
    already forces f 0 = 0; the Hermite form needs σ ≠ 0, where σ⁻¹ means
    something. THE SENTENCE IS KEPT AS WRITTEN (ERRATUM 94): it is the
    record of what was open, and it stays true of THIS file.

    ⚠ STILL OPEN, AND NOT TO BE READ AS CLOSED BY THE ABOVE: the two
    generalisations are independent and only one of them has been combined
    with the other. The `HermitePi*` line is at variance one, and
    `HermiteScaledComplete` is one-dimensional. **n dimensions at variance σ
    is proved nowhere in this estate as of 2026-08-29.**
  * Anything about the spectral action. Unchanged, unproven.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincare
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

/- Mathlib's own CharacteristicFunction file sets this option around the
   charFun lemmas; without it, `rw`/`simp` fail to match visibly-identical
   integral, `inner` and `smul` patterns in this measure-theoretic context
   (instance-path mismatches under transparency-respecting unification). -/
set_option backward.isDefEq.respectTransparency false

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

/-! ## 4. Completeness against all polynomials -/

theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **COMPLETENESS OF THE POLYNOMIALS IN L²(γ)**, in dual form: an L²
    function orthogonal to every polynomial vanishes a.e. The Gaussian
    moment problem is determinate, and this is its Lean form. -/
theorem polynomials_complete (f : ℝ → ℝ) (hf : MemLp f 2 gauss)
    (horth : ∀ p : ℝ[X], ∫ x, f x * p.eval x ∂gauss = 0) :
    f =ᵐ[gauss] 0 := by
  classical
  have hfmeas : AEStronglyMeasurable f gauss := hf.aestronglyMeasurable
  set fp : ℝ → ℝ := fun x => max (f x) 0 with hfp_def
  set fm : ℝ → ℝ := fun x => max (-f x) 0 with hfm_def
  have hfpm : AEStronglyMeasurable fp gauss := hfmeas.sup aestronglyMeasurable_const
  have hfmm : AEStronglyMeasurable fm gauss :=
    hfmeas.neg.sup aestronglyMeasurable_const
  have hfp2 : MemLp fp 2 gauss := by
    refine hf.of_le hfpm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hfm2 : MemLp fm 2 gauss := by
    refine hf.of_le hfmm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hsub : ∀ x, fp x - fm x = f x := fun x => max_sub_max_neg (f x)
  -- the moments of the two halves agree
  have hmom : ∀ k : ℕ,
      (∫ x, x ^ k * fp x ∂gauss) = ∫ x, x ^ k * fm x ∂gauss := by
    intro k
    have h0 := horth (X ^ k)
    have hsplit : (∫ x, x ^ k * fp x ∂gauss) - ∫ x, x ^ k * fm x ∂gauss
        = ∫ x, f x * (X ^ k : ℝ[X]).eval x ∂gauss := by
      rw [← integral_sub (integrable_pow_mul fp hfp2 k)
        (integrable_pow_mul fm hfm2 k)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hx := hsub x
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      linear_combination (x : ℝ) ^ k * hx
    rw [h0] at hsplit
    linarith [hsplit]
  -- the two finite measures with densities f⁺ and f⁻
  set dp : ℝ → ℝ≥0 := fun x => (f x).toNNReal with hdp_def
  set dm : ℝ → ℝ≥0 := fun x => (-f x).toNNReal with hdm_def
  have hdp_coe : ∀ x, ((dp x : ℝ)) = fp x := fun x => Real.coe_toNNReal' _
  have hdm_coe : ∀ x, ((dm x : ℝ)) = fm x := fun x => Real.coe_toNNReal' _
  have hdp_meas : AEMeasurable dp gauss :=
    measurable_real_toNNReal.comp_aemeasurable hfmeas.aemeasurable
  have hdm_meas : AEMeasurable dm gauss :=
    measurable_real_toNNReal.comp_aemeasurable hfmeas.aemeasurable.neg
  have hdp_ofReal : (fun x => ((dp x : ℝ≥0∞))) = fun x => ENNReal.ofReal (f x) := rfl
  have hdm_ofReal : (fun x => ((dm x : ℝ≥0∞))) = fun x => ENNReal.ofReal (-f x) := rfl
  have hfin_p : (∫⁻ x, (dp x : ℝ≥0∞) ∂gauss) ≠ ⊤ := by
    rw [hdp_ofReal]
    exact (hf.integrable one_le_two).lintegral_lt_top.ne
  have hfin_m : (∫⁻ x, (dm x : ℝ≥0∞) ∂gauss) ≠ ⊤ := by
    rw [hdm_ofReal]
    exact ((hf.integrable one_le_two).neg.lintegral_lt_top).ne
  set mup : Measure ℝ := gauss.withDensity (fun x => (dp x : ℝ≥0∞)) with hmup
  set mum : Measure ℝ := gauss.withDensity (fun x => (dm x : ℝ≥0∞)) with hmum
  haveI : IsFiniteMeasure mup := isFiniteMeasure_withDensity hfin_p
  haveI : IsFiniteMeasure mum := isFiniteMeasure_withDensity hfin_m
  -- equal characteristic functions, via the moment series
  have hchar : charFun mup = charFun mum := by
    funext t
    have hip : ∀ x : ℝ, ((inner ℝ x t : ℝ) : ℂ) = ((x * t : ℝ) : ℂ) := by
      intro x
      norm_cast
      rw [RCLike.inner_apply]
      simp [mul_comm]
    have hpull : ∀ (d : ℝ → ℝ≥0) (fd : ℝ → ℝ), AEMeasurable d gauss →
        (∀ x, ((d x : ℝ)) = fd x) →
        charFun (gauss.withDensity (fun x => (d x : ℝ≥0∞))) t
          = ∫ x, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) * ((fd x : ℝ) : ℂ)
              ∂gauss := by
      intro d fd hd hcoe
      rw [charFun_apply,
        integral_withDensity_eq_integral_smul₀ hd
          (fun x => Complex.exp ((inner ℝ x t : ℝ) * Complex.I))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [NNReal.smul_def, Complex.real_smul, hcoe x, hip x, mul_comm]
    rw [hpull dp fp hdp_meas hdp_coe, hpull dm fm hdm_meas hdm_coe]
    -- the two integrals are limits of IDENTICAL moment sequences
    have h1 := tendsto_partial_exp fp hfp2 t
    have h2 := tendsto_partial_exp fm hfm2 t
    have heqseq : (fun N => ∑ k ∈ Finset.range N,
        ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
          * ((∫ x, x ^ k * fp x ∂gauss : ℝ) : ℂ))
        = fun N => ∑ k ∈ Finset.range N,
            ((t : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
              * ((∫ x, x ^ k * fm x ∂gauss : ℝ) : ℂ) := by
      funext N
      exact Finset.sum_congr rfl fun k _ => by rw [hmom k]
    rw [heqseq] at h1
    exact tendsto_nhds_unique h1 h2
  -- hence the measures agree, hence the densities, hence f = 0
  have hmeq : mup = mum := Measure.ext_of_charFun hchar
  have hdens : (fun x => (dp x : ℝ≥0∞)) =ᵐ[gauss] fun x => (dm x : ℝ≥0∞) :=
    (withDensity_eq_iff hdp_meas.coe_nnreal_ennreal hdm_meas.coe_nnreal_ennreal
      hfin_p).mp hmeq
  filter_upwards [hdens] with x hx
  have hnn : dp x = dm x := by exact_mod_cast hx
  have hfp_eq : fp x = fm x := by
    rw [← hdp_coe x, ← hdm_coe x, hnn]
  have := hsub x
  simp only [Pi.zero_apply]
  linarith

/-! ## 5. Completeness of the HERMITE system -/

/-- **THE HERMITE POLYNOMIALS ARE COMPLETE**: an L² function orthogonal to
    every Hₙ vanishes a.e. Reduction to `polynomials_complete` through the
    Hermite expansion of an arbitrary polynomial. -/
theorem hermite_complete (f : ℝ → ℝ) (hf : MemLp f 2 gauss)
    (horth : ∀ n : ℕ, ∫ x, f x * (H n).eval x ∂gauss = 0) :
    f =ᵐ[gauss] 0 := by
  refine polynomials_complete f hf fun p => ?_
  obtain ⟨N, a, hrep⟩ := exists_hermite_repr' p
  have hpt : (fun x => f x * p.eval x)
      = fun x => ∑ k ∈ Finset.range (N + 1), a k * (f x * (H k).eval x) := by
    funext x
    rw [hrep, Polynomial.eval_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have hik : ∀ k : ℕ, Integrable (fun x => a k * (f x * (H k).eval x)) gauss := by
    intro k
    have h1 : Integrable (fun x => f x * (H k).eval x) gauss :=
      MemLp.integrable_mul hf
        (GaussianPoincare.memLp_polynomial_gaussianReal (H k) 0 1)
    exact h1.const_mul _
  rw [hpt, integral_finset_sum _ (fun k _ => hik k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, horth k, mul_zero]

/-! ## 6. Orthogonality transported to the measure, and the package -/

/-- The orthogonality relations of `GaussianPoincare`, restated against
    Mathlib's `gaussianReal 0 1`: ⟨Hₘ, Hₙ⟩_{L²(γ)} = δₘₙ · m!. -/
theorem hermite_orthogonal_gauss (m n : ℕ) :
    ∫ x, (H m).eval x * (H n).eval x ∂gauss
      = if m = n then (m.factorial : ℝ) else 0 := by
  have hZ : Z ≠ 0 := ne_of_gt Z_pos
  have h1 := gmean_eq_integral (H m * H n)
  have h2 : (∫ x, (H m * H n).eval x ∂gauss)
      = ∫ x, (H m).eval x * (H n).eval x ∂gauss :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [Polynomial.eval_mul])
  have h3 : gmean (H m * H n) = (if m = n then (m.factorial : ℝ) * Z else 0) / Z := by
    rw [show gmean (H m * H n) = ip (H m) (H n) / Z from rfl, ip_H]
  rw [← h2, ← h1, h3]
  split_ifs
  · field_simp
  · simp

/-- No Hₙ is the zero vector of L²(γ): its norm² is n! > 0. -/
theorem hermite_norm_sq_gauss (n : ℕ) :
    ∫ x, (H n).eval x * (H n).eval x ∂gauss = (n.factorial : ℝ) := by
  rw [hermite_orthogonal_gauss n n, if_pos rfl]

/-- **THE HERMITE POLYNOMIALS ARE A COMPLETE ORTHOGONAL SYSTEM IN L²(γ)**:
    pairwise orthogonal, each of norm² = n! ≠ 0, and nothing in L² is
    orthogonal to all of them except 0 — stated entirely against Mathlib's
    own Gaussian measure. This was the CAESAR key on the watchlist: it is
    what "expand in Hermite modes" needs in order to mean something. -/
theorem hermite_complete_orthogonal_system :
    (∀ m n : ℕ, m ≠ n →
        ∫ x, (H m).eval x * (H n).eval x ∂gauss = 0)
      ∧ (∀ n : ℕ,
          ∫ x, (H n).eval x * (H n).eval x ∂gauss = (n.factorial : ℝ))
      ∧ (∀ n : ℕ, (n.factorial : ℝ) ≠ 0)
      ∧ (∀ f : ℝ → ℝ, MemLp f 2 gauss →
          (∀ n : ℕ, ∫ x, f x * (H n).eval x ∂gauss = 0) → f =ᵐ[gauss] 0) :=
  ⟨fun m n hmn => by rw [hermite_orthogonal_gauss, if_neg hmn],
    hermite_norm_sq_gauss,
    fun n => Nat.cast_ne_zero.mpr n.factorial_ne_zero,
    hermite_complete⟩

end HermiteCompleteness
