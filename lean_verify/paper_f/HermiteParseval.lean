/-
  HermiteParseval: Riesz–Fischer for the Hermite Series — Parseval Lands
  ======================================================================

  The limit-taking rung. `HermiteCompleteness` proved the system total;
  `HermiteBessel` proved the partial sums are the exact orthogonal
  projections and are L²-Cauchy. This file supplies the one ingredient
  neither could: COMPLETENESS OF THE SPACE, through Mathlib's `Lp`, and
  harvests the limits.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `inner_toLp` — the dictionary: the L² inner product of two `toLp`
     images is the integral of the product. Everything else is this
     dictionary applied.
  2. `cauchySeq_SL` — the partial sums, as elements of L²(γ), form a Cauchy
     sequence (from `sn_cauchy` + convergence of the coefficient series).
  3. **`tendsto_SN_L2`** — RIESZ–FISCHER FOR THE HERMITE SERIES: the partial
     sums converge in L²(γ) to f itself,

         ∫ (f − S_N f)² dγ → 0.

     The limit exists by completeness of L²; it EQUALS f because the
     difference is orthogonal to every Hₙ and the system is complete
     (`hermite_complete`). This is the statement "every L² function IS its
     Hermite expansion".
  4. **`parseval`** — ‖f‖² = Σ n!·cₙ², as a `HasSum`. The Bessel inequality
     of the previous file is now an equality in the limit.
  5. **`polynomial_dense_L2`** — density of polynomials in L²(γ) in NORM
     form: for every ε > 0 there is a polynomial p with ∫ (f − p)² < ε.
     The completeness of the previous file was the dual form; this is the
     approximation form, and it is the one an approximation argument can
     actually consume.

  NOT proven here — the remaining legs to Poincaré on W^{1,2}(γ):

  * The derivative recursion: for f in a Sobolev class, cₙ(f′) relates to
    cₙ₊₁(f) via Hₙ′ = n·Hₙ₋₁ (which `GaussianPoincare.derivative_H_succ`
    already provides at the polynomial level). Needs a definition of the
    weak derivative class first — that definitional choice is the next
    unit's first job.
  * The termwise limit assembling Poincaré for non-polynomial f.
  * Everything upstream files disclaim (no spectral action, one dimension
    only here).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import HermiteBessel

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HermiteParseval

open GaussianPoincare HermiteCompleteness HermiteBessel

/-! ## 1. The dictionary -/

theorem inner_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 gauss) (hg : MemLp g 2 gauss) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂gauss := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp [mul_comm]

/-- MemLp of the partial-sum evaluation. -/
theorem memLp_SN (f : ℝ → ℝ) (N : ℕ) :
    MemLp (fun x => (SNpoly N f).eval x) 2 gauss :=
  GaussianPoincare.memLp_polynomial_gaussianReal (SNpoly N f) 0 1

/-- The partial sum as an element of L²(γ). -/
def SL (f : ℝ → ℝ) (N : ℕ) : Lp ℝ 2 gauss := (memLp_SN f N).toLp _

/-- The norm² of a difference of partial sums is the Ico block of the
    coefficient series. -/
theorem norm_SL_sub_sq (f : ℝ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    ‖SL f M - SL f N‖ ^ 2
      = (∑ n ∈ Finset.range M, (n.factorial : ℝ) * coeff n f ^ 2)
        - ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2 := by
  have hsub : SL f M - SL f N
      = ((memLp_SN f M).sub (memLp_SN f N)).toLp
          ((fun x => (SNpoly M f).eval x) - fun x => (SNpoly N f).eval x) := by
    rw [MemLp.toLp_sub]
    rfl
  rw [← real_inner_self_eq_norm_sq, hsub, inner_toLp]
  have := sn_cauchy f hNM
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  ring

/-! ## 2. The Cauchy sequence and its limit -/

theorem cauchySeq_SL (f : ℝ → ℝ) (hf : MemLp f 2 gauss) : CauchySeq (SL f) := by
  set T := ∑' n, (n.factorial : ℝ) * coeff n f ^ 2 with hT
  have hsummable := summable_coeff_sq f hf
  have hnonneg : ∀ n : ℕ, 0 ≤ (n.factorial : ℝ) * coeff n f ^ 2 :=
    fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hpartial_le : ∀ M : ℕ,
      (∑ n ∈ Finset.range M, (n.factorial : ℝ) * coeff n f ^ 2) ≤ T := by
    intro M
    exact hsummable.sum_le_tsum _ (fun n _ => hnonneg n)
  refine cauchySeq_of_le_tendsto_0
    (fun N => Real.sqrt (T - ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2))
    ?_ ?_
  · intro n m N hn hm
    wlog hnm : m ≤ n generalizing n m
    · rw [dist_comm]
      exact this m n hm hn (le_of_not_ge hnm)
    rw [dist_eq_norm]
    have hnorm := norm_SL_sub_sq f hnm
    have h1 : ‖SL f n - SL f m‖
        = Real.sqrt ((∑ k ∈ Finset.range n, (k.factorial : ℝ) * coeff k f ^ 2)
          - ∑ k ∈ Finset.range m, (k.factorial : ℝ) * coeff k f ^ 2) := by
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    rw [h1]
    refine Real.sqrt_le_sqrt ?_
    have hmono : (∑ k ∈ Finset.range m, (k.factorial : ℝ) * coeff k f ^ 2)
        ≥ ∑ k ∈ Finset.range N, (k.factorial : ℝ) * coeff k f ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) hm))
        (fun k _ _ => hnonneg k)
    linarith [hpartial_le n]
  · have htend : Tendsto
        (fun N => ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2)
        atTop (𝓝 T) := hsummable.hasSum.tendsto_sum_nat
    have : Tendsto
        (fun N => T - ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2)
        atTop (𝓝 (T - T)) := tendsto_const_nhds.sub htend
    rw [sub_self] at this
    have hcont : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
      have := Real.continuous_sqrt.tendsto 0
      rwa [Real.sqrt_zero] at this
    exact hcont.comp this

/-! ## 3. Riesz–Fischer: the limit is f -/

/-- **THE HERMITE SERIES OF AN L² FUNCTION CONVERGES TO IT IN L²(γ)** —
    Riesz–Fischer plus completeness of the system. -/
theorem tendsto_SN_L2 (f : ℝ → ℝ) (hf : MemLp f 2 gauss) :
    Tendsto (fun N => ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss)
      atTop (𝓝 0) := by
  obtain ⟨gL, hgL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_SL f hf)
  set fL : Lp ℝ 2 gauss := hf.toLp f with hfL
  -- the limit is orthogonal to every mode…
  have horthlim : ∀ n : ℕ,
      inner ℝ (fL - gL)
        ((GaussianPoincare.memLp_polynomial_gaussianReal (H n) 0 1).toLp
          (fun x => (H n).eval x)) = 0 := by
    intro n
    set eL : Lp ℝ 2 gauss :=
      (GaussianPoincare.memLp_polynomial_gaussianReal (H n) 0 1).toLp
        (fun x => (H n).eval x) with heL
    have hcont : Tendsto (fun N => inner ℝ (fL - SL f N) eL) atTop
        (𝓝 (inner ℝ (fL - gL) eL)) :=
      Filter.Tendsto.inner (tendsto_const_nhds.sub hgL) tendsto_const_nhds
    have hval : ∀ N : ℕ, n < N → inner ℝ (fL - SL f N) eL = 0 := by
      intro N hn
      have hsub : fL - SL f N
          = (hf.sub (memLp_SN f N)).toLp
              (f - fun x => (SNpoly N f).eval x) := by
        rw [MemLp.toLp_sub]
        rfl
      rw [hsub, inner_toLp]
      have := remainder_orthogonal f hf N n hn
      rw [← this]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Pi.sub_apply])
    have hev : (fun N => inner ℝ (fL - SL f N) eL) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_gt_atTop n] with N hN
      exact hval N hN
    have hzero : Tendsto (fun N => inner ℝ (fL - SL f N) eL) atTop (𝓝 (0 : ℝ)) :=
      Tendsto.congr' hev.symm tendsto_const_nhds
    exact tendsto_nhds_unique hcont hzero
  -- …so by completeness of the system the limit IS f
  have hfeq : fL = gL := by
    have hdiff : MemLp (fun x => f x - gL x) 2 gauss := hf.sub (Lp.memLp gL)
    have horthfun : ∀ n : ℕ,
        ∫ x, (f x - gL x) * (H n).eval x ∂gauss = 0 := by
      intro n
      have h1 := horthlim n
      have hsub2 : fL - gL = hdiff.toLp (fun x => f x - gL x) := by
        have hgLcoe : (Lp.memLp gL).toLp ⇑gL = gL := Lp.toLp_coeFn gL (Lp.memLp gL)
        calc fL - gL = fL - (Lp.memLp gL).toLp ⇑gL := by rw [hgLcoe]
          _ = (hf.sub (Lp.memLp gL)).toLp (f - ⇑gL) := by
              rw [MemLp.toLp_sub]
          _ = hdiff.toLp (fun x => f x - gL x) := rfl
      rw [hsub2, inner_toLp] at h1
      exact h1
    have hzero := hermite_complete _ hdiff horthfun
    have hfg : f =ᵐ[gauss] ⇑gL := by
      filter_upwards [hzero] with x hx
      have : f x - gL x = 0 := hx
      linarith
    calc fL = (Lp.memLp gL).toLp ⇑gL := MemLp.toLp_congr hf (Lp.memLp gL) hfg
      _ = gL := Lp.toLp_coeFn gL (Lp.memLp gL)
  rw [← hfeq] at hgL
  -- translate norm convergence back to the integral
  have hnorm : Tendsto (fun N => ‖fL - SL f N‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ‖SL f N - fL‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hgL
    refine h1.congr fun N => ?_
    rw [norm_sub_rev]
  have hsq : Tendsto (fun N => ‖fL - SL f N‖ ^ 2) atTop (𝓝 0) := by
    have := hnorm.mul hnorm
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    ring
  refine hsq.congr fun N => ?_
  have hsub : fL - SL f N
      = (hf.sub (memLp_SN f N)).toLp (f - fun x => (SNpoly N f).eval x) := by
    rw [MemLp.toLp_sub]
    rfl
  rw [← real_inner_self_eq_norm_sq, hsub, inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  ring

/-! ## 4. Parseval, and density in norm form -/

/-- **PARSEVAL**: ‖f‖² = Σ n!·cₙ². Bessel is an equality in the limit. -/
theorem parseval (f : ℝ → ℝ) (hf : MemLp f 2 gauss) :
    HasSum (fun n => (n.factorial : ℝ) * coeff n f ^ 2)
      (∫ x, f x ^ 2 ∂gauss) := by
  have hsummable := summable_coeff_sq f hf
  have h1 : Tendsto
      (fun N => ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2)
      atTop (𝓝 (∫ x, f x ^ 2 ∂gauss)) := by
    have h2 := tendsto_SN_L2 f hf
    have h3 : (fun N => ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2)
        = fun N => (∫ x, f x ^ 2 ∂gauss)
            - ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss := by
      funext N
      have := remainder_expansion f hf N
      linarith
    rw [h3]
    have h4 : Tendsto (fun N => (∫ x, f x ^ 2 ∂gauss)
        - ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss) atTop
        (𝓝 ((∫ x, f x ^ 2 ∂gauss) - 0)) := tendsto_const_nhds.sub h2
    rwa [sub_zero] at h4
  have h5 := hsummable.hasSum.tendsto_sum_nat
  have h6 := tendsto_nhds_unique h5 h1
  exact h6 ▸ hsummable.hasSum

/-- **Density of the polynomials in L²(γ), in NORM form**: the approximation
    statement that downstream limit arguments can consume. The dual form was
    `HermiteCompleteness.polynomials_complete`; this is its quantitative
    counterpart, with the approximant explicit — the Hermite partial sum. -/
theorem polynomial_dense_L2 (f : ℝ → ℝ) (hf : MemLp f 2 gauss)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∫ x, (f x - p.eval x) ^ 2 ∂gauss < ε := by
  have h := tendsto_SN_L2 f hf
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨SNpoly N f, ?_⟩
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  calc ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss
      ≤ |∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss| := le_abs_self _
    _ < ε := this

end HermiteParseval
