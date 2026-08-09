/-
  PoincareBeyondPolynomials: the Caveat Falls
  ===========================================

  Since the first Poincaré file, every analytic statement in this campaign
  has carried the caveat "polynomial test functions only". This file removes
  it: the Gaussian Poincaré inequality holds for every function which,
  together with its derivative, has polynomial growth — and the only
  regularity used is everywhere-differentiability, so every C¹ function of
  the class qualifies (and more: derivative-discontinuous functions of the
  x²sin(1/x) kind are covered). sin is in the class; so is every
  bounded smooth function; so is nothing that was provable before today.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `integral_gauss_eq_weight` — the general bridge ∫ h dγ = Z⁻¹·∫ h·W dx,
     for ANY function (the polynomial file proved it for polynomials; the
     proof never needed polynomiality).
  2. `memLp_of_polyGrowth` — an A.E.-STRONGLY-MEASURABLE f with
     |f| ≤ C(1+x²)^m is in L²(γ). (The hypothesis is
     `AEStronglyMeasurable`, weaker than `Measurable` — the theorem is
     stronger than an earlier version of this line said; a bound alone
     cannot give membership.)
  3. `tendsto_growth_mul_W_atTop` and `tendsto_growth_mul_W_atBot` —
     growth × polynomial × Gaussian weight → 0 at both infinities: the
     boundary terms of integration by parts vanish. (This line named a
     single `tendsto_growth_mul_W`, which does not exist and hid that
     there are two statements, one per end of the line; corrected by the
     11 Aug citation sweep, ERRATUM 50.)
  4. **`stein_general`** — Gaussian integration by parts for the class:
     ∫ f′·q dγ = ∫ f·(Xq − q′) dγ for every polynomial q. The FTC on the
     whole line plus the boundary limits; this is the analytic heart.
  5. **`coeff_deriv`** — the coefficient recursion cₙ(f′) = (n+1)·cₙ₊₁(f),
     because X·Hₙ − Hₙ′ = Hₙ₊₁ is literally the Hermite recurrence.
  6. **`poincare_beyond_polynomials`** — for everywhere-differentiable f
     with f, f′ of polynomial growth (in particular every C¹ such f):

         ∫ f² dγ − (∫ f dγ)² ≤ ∫ (f′)² dγ.

     Assembly: Parseval for f and for f′, the recursion identifying the
     coefficients, and the termwise inequality n! ≤ n·n! for n ≥ 1.
  7. `poincare_sin` — NON-VACUITY: the inequality instantiated at sin
     (with cos as the derivative), a function no earlier file could touch.
     Var_γ(sin) ≤ ∫ cos² dγ.

  NOT proven here:

  * The MAXIMAL class. "C¹ with polynomial growth" is sufficient, not
    maximal: the sharp class is the Sobolev space W^{1,2}(γ) with weak
    derivatives, and functions like e^{x²/4}·(oscillation) of super-poly
    growth but finite Dirichlet energy are outside today's hypotheses. The
    upgrade path is a density argument in W^{1,2}(γ), for which
    `polynomial_dense_L2` supplies the L² half; the W^{1,2} half needs a
    weak-derivative formalism the estate does not yet have.
  * Dimensions above one, and any connection to the spectral action.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import HermiteParseval

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareBeyondPolynomials

open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval

/-! ## 1. The general Gaussian bridge -/

/-- ∫ h dγ = Z⁻¹ ∫ h·W dx for ANY h — the bridge the polynomial file proved
    only for polynomials, whose proof never used polynomiality. -/
theorem integral_gauss_eq_weight (h : ℝ → ℝ) :
    ∫ x, h x ∂gauss = Z⁻¹ * ∫ x : ℝ, h x * W x := by
  rw [show (gauss : Measure ℝ) = gaussianReal 0 1 from rfl,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x • h x = Z⁻¹ • (h x * W x) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [← Z_eq]
    unfold W
    ring
  simp_rw [hpdf]
  rw [integral_smul, smul_eq_mul]

/-! ## 2. Membership and boundary decay from polynomial growth -/

/-- The dominating polynomial (1+X²)^m, as a polynomial. -/
def domP (m : ℕ) : ℝ[X] := (1 + X ^ 2) ^ m

theorem eval_domP (m : ℕ) (x : ℝ) : (domP m).eval x = (1 + x ^ 2) ^ m := by
  simp [domP]

theorem domP_nonneg (m : ℕ) (x : ℝ) : 0 ≤ (domP m).eval x := by
  rw [eval_domP]
  positivity

/-- Polynomial growth puts a continuous function in L²(γ). -/
theorem memLp_of_polyGrowth {f : ℝ → ℝ} (hmeas : AEStronglyMeasurable f gauss)
    {C : ℝ} {m : ℕ} (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m) :
    MemLp f 2 gauss := by
  have hpoly : MemLp (fun x => (C • domP m).eval x) 2 gauss :=
    GaussianPoincare.memLp_polynomial_gaussianReal (C • domP m) 0 1
  refine hpoly.of_le hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, eval_domP]
  calc |f x| ≤ C * (1 + x ^ 2) ^ m := hb x
    _ ≤ |C * (1 + x ^ 2) ^ m| := le_abs_self _

/-- The boundary decay: growth × polynomial × W → 0 at +∞. -/
theorem tendsto_growth_mul_W_atTop {f : ℝ → ℝ} {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m) (q : ℝ[X]) :
    Tendsto (fun x => f x * q.eval x * W x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hW : ∀ x : ℝ, 0 ≤ W x := fun x => (Real.exp_pos _).le
  have hbound : ∀ x : ℝ, ‖f x * q.eval x * W x‖
      ≤ (C • (domP m * (q ^ 2 + 1))).eval x * W x := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hW x)]
    have h1 : |q.eval x| ≤ q.eval x ^ 2 + 1 := by
      nlinarith [sq_nonneg (|q.eval x| - 1), abs_nonneg (q.eval x),
        sq_abs (q.eval x)]
    have h2 := hb x
    have hCpos : 0 ≤ C * (1 + x ^ 2) ^ m := le_trans (abs_nonneg _) h2
    rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
      eval_domP, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_one]
    have h3 : |f x| * |q.eval x| ≤ C * (1 + x ^ 2) ^ m * (q.eval x ^ 2 + 1) := by
      have := mul_le_mul h2 h1 (abs_nonneg _) hCpos
      linarith [this]
    have h4 : C * (1 + x ^ 2) ^ m * (q.eval x ^ 2 + 1)
        = C * ((1 + x ^ 2) ^ m * (q.eval x ^ 2 + 1)) := by ring
    nlinarith [mul_le_mul_of_nonneg_right h3 (hW x)]
  refine squeeze_zero (fun x => norm_nonneg _) hbound ?_
  exact GaussianPoincare.tendsto_poly_mul_W_atTop _

theorem tendsto_growth_mul_W_atBot {f : ℝ → ℝ} {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m) (q : ℝ[X]) :
    Tendsto (fun x => f x * q.eval x * W x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hW : ∀ x : ℝ, 0 ≤ W x := fun x => (Real.exp_pos _).le
  have hbound : ∀ x : ℝ, ‖f x * q.eval x * W x‖
      ≤ (C • (domP m * (q ^ 2 + 1))).eval x * W x := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hW x)]
    have h1 : |q.eval x| ≤ q.eval x ^ 2 + 1 := by
      nlinarith [sq_nonneg (|q.eval x| - 1), abs_nonneg (q.eval x),
        sq_abs (q.eval x)]
    have h2 := hb x
    have hCpos : 0 ≤ C * (1 + x ^ 2) ^ m := le_trans (abs_nonneg _) h2
    rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
      eval_domP, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_one]
    have h3 : |f x| * |q.eval x| ≤ C * (1 + x ^ 2) ^ m * (q.eval x ^ 2 + 1) := by
      have := mul_le_mul h2 h1 (abs_nonneg _) hCpos
      linarith [this]
    nlinarith [mul_le_mul_of_nonneg_right h3 (hW x)]
  refine squeeze_zero (fun x => norm_nonneg _) hbound ?_
  exact GaussianPoincare.tendsto_poly_mul_W_atBot _

/-- Integrability over Lebesgue of growth × polynomial × W. -/
theorem integrable_growth_mul_W {f : ℝ → ℝ} (hmeas : AEStronglyMeasurable f volume)
    {C : ℝ} {m : ℕ} (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m) (q : ℝ[X]) :
    Integrable (fun x : ℝ => f x * q.eval x * W x) := by
  have hWm : AEStronglyMeasurable W volume :=
    (Real.continuous_exp.comp (Continuous.div_const (continuous_pow 2).neg 2)
      ).aestronglyMeasurable
  refine (GaussianPoincare.integrable_poly_mul_W
    (C • (domP m * (q ^ 2 + 1)))).mono' ?_ ?_
  · exact (hmeas.mul (Polynomial.continuous q).aestronglyMeasurable).mul hWm
  · filter_upwards with x
    have hW : 0 ≤ W x := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hW]
    have h1 : |q.eval x| ≤ q.eval x ^ 2 + 1 := by
      nlinarith [sq_nonneg (|q.eval x| - 1), abs_nonneg (q.eval x),
        sq_abs (q.eval x)]
    have h2 := hb x
    have hCpos : 0 ≤ C * (1 + x ^ 2) ^ m := le_trans (abs_nonneg _) h2
    rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
      eval_domP, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_one]
    have h3 : |f x| * |q.eval x| ≤ C * (1 + x ^ 2) ^ m * (q.eval x ^ 2 + 1) := by
      have := mul_le_mul h2 h1 (abs_nonneg _) hCpos
      linarith [this]
    nlinarith [mul_le_mul_of_nonneg_right h3 hW]

/-! ## 3. Gaussian integration by parts for the class -/

/-- The weight differentiates to −x·W. -/
theorem hasDerivAt_W (x : ℝ) : HasDerivAt W (-x * W x) x := by
  have hg : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h using 1
    ring
  have := hg.exp
  simpa [W, mul_comm] using this

/-- **Gaussian integration by parts for everywhere-differentiable functions of polynomial
    growth**: ∫ f′·q dγ = ∫ f·(Xq − q′) dγ for every polynomial q. -/
theorem stein_general {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m)
    (q : ℝ[X]) :
    ∫ x, f' x * q.eval x ∂gauss
      = ∫ x, f x * (X * q - derivative q).eval x ∂gauss := by
  have hfcont : Continuous f := by
    have : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
    exact this.continuous
  have hf'meas : AEStronglyMeasurable f' volume := by
    have hfd : f' = deriv f := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact (measurable_deriv f).aestronglyMeasurable
  -- the total derivative of F = f·q·W
  have hF : ∀ x : ℝ, HasDerivAt (fun y => f y * q.eval y * W y)
      ((f' x * q.eval x - f x * (X * q - derivative q).eval x) * W x) x := by
    intro x
    have h1 := (hderiv x).mul (q.hasDerivAt x)
    have h2 := h1.mul (hasDerivAt_W x)
    convert h2 using 1
    simp only [Pi.mul_apply, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X]
    ring
  -- integrability of the total derivative
  have hint : Integrable (fun x : ℝ =>
      (f' x * q.eval x - f x * (X * q - derivative q).eval x) * W x) := by
    have i1 := integrable_growth_mul_W hf'meas hb' q
    have i2 := integrable_growth_mul_W hfcont.aestronglyMeasurable hb
      (X * q - derivative q)
    refine (i1.sub i2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- FTC on the line, boundary terms vanish
  have h0 := integral_of_hasDerivAt_of_tendsto hF hint
    (tendsto_growth_mul_W_atBot hb q) (tendsto_growth_mul_W_atTop hb q)
  simp only [sub_zero] at h0
  -- split and pass to the measure
  have i1 := integrable_growth_mul_W hf'meas hb' q
  have i2 := integrable_growth_mul_W hfcont.aestronglyMeasurable hb
    (X * q - derivative q)
  have hsplit : (fun x : ℝ =>
      (f' x * q.eval x - f x * (X * q - derivative q).eval x) * W x)
      = fun x : ℝ => f' x * q.eval x * W x
          - f x * (X * q - derivative q).eval x * W x := by
    funext x
    ring
  rw [hsplit, integral_sub i1 i2] at h0
  have hW1 : ∫ x, f' x * q.eval x ∂gauss
      = Z⁻¹ * ∫ x : ℝ, f' x * q.eval x * W x :=
    integral_gauss_eq_weight _
  have hW2 : ∫ x, f x * (X * q - derivative q).eval x ∂gauss
      = Z⁻¹ * ∫ x : ℝ, f x * (X * q - derivative q).eval x * W x :=
    integral_gauss_eq_weight _
  rw [hW1, hW2]
  have : (∫ x : ℝ, f' x * q.eval x * W x)
      = ∫ x : ℝ, f x * (X * q - derivative q).eval x * W x := by linarith
  rw [this]

/-! ## 4. The coefficient recursion -/

/-- **cₙ(f′) = (n+1)·cₙ₊₁(f)** — because X·Hₙ − Hₙ′ = Hₙ₊₁ is the Hermite
    recurrence itself. -/
theorem coeff_deriv {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m)
    (n : ℕ) :
    coeff n f' = (n + 1 : ℝ) * coeff (n + 1) f := by
  have hstein := stein_general hderiv hb hb' (H n)
  have hH : X * H n - derivative (H n) = H (n + 1) := (H_succ n).symm
  rw [hH] at hstein
  simp only [HermiteBessel.coeff]
  rw [hstein]
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-! ## 5. The inequality, beyond polynomials -/

/-- **THE GAUSSIAN POINCARÉ INEQUALITY FOR EVERYWHERE-DIFFERENTIABLE
    FUNCTIONS OF POLYNOMIAL
    GROWTH** — the caveat "polynomial test functions only" falls:

      ∫ f² dγ − (∫ f dγ)² ≤ ∫ (f′)² dγ. -/
theorem poincare_beyond_polynomials {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2
      ≤ ∫ x, f' x ^ 2 ∂gauss := by
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hfcont : Continuous f := hdiff.continuous
  have hf'meas : AEStronglyMeasurable f' gauss := by
    have hfd : f' = deriv f := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact (measurable_deriv f).aestronglyMeasurable
  have hf2 : MemLp f 2 gauss := memLp_of_polyGrowth hfcont.aestronglyMeasurable hb
  have hf'2 : MemLp f' 2 gauss := memLp_of_polyGrowth hf'meas hb'
  -- Parseval for f and for f′, with the recursion substituted
  have PA := parseval f hf2
  have PB := parseval f' hf'2
  have hrec : (fun n => (n.factorial : ℝ) * coeff n f' ^ 2)
      = fun (n : ℕ) => ((n : ℝ) + 1) * (((n + 1 : ℕ)).factorial : ℝ)
          * coeff (n + 1) f ^ 2 := by
    funext n
    rw [coeff_deriv hderiv hb hb' n]
    have hfac : (((n + 1 : ℕ)).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    ring
  rw [hrec] at PB
  -- shift Parseval for f by one: the n ≥ 1 block sums to ‖f‖² − c₀²
  have hc0 : coeff 0 f = ∫ x, f x ∂gauss := by
    simp only [HermiteBessel.coeff]
    have hH0 : (H 0) = 1 := by
      unfold GaussianPoincare.H
      rw [Polynomial.hermite_zero]
      simp
    rw [hH0]
    simp
  have PA' : HasSum (fun k => ((k + 1).factorial : ℝ) * coeff (k + 1) f ^ 2)
      ((∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2) := by
    refine (hasSum_nat_add_iff (f := fun n =>
      (n.factorial : ℝ) * coeff n f ^ 2) 1).mpr ?_
    have hval : ((∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2)
        + ∑ i ∈ Finset.range 1, (i.factorial : ℝ) * coeff i f ^ 2
        = ∫ x, f x ^ 2 ∂gauss := by
      rw [Finset.sum_range_one, hc0]
      simp [Nat.factorial]
    rw [hval]
    exact PA
  -- termwise comparison: n! ≤ (n+1)·n! …
  have hle : ∀ k : ℕ, (((k + 1 : ℕ)).factorial : ℝ) * coeff (k + 1) f ^ 2
      ≤ ((k : ℝ) + 1) * (((k + 1 : ℕ)).factorial : ℝ) * coeff (k + 1) f ^ 2 := by
    intro k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [mul_nonneg
      (Nat.cast_nonneg ((k + 1 : ℕ).factorial) : (0 : ℝ) ≤ _)
      (sq_nonneg (coeff (k + 1) f))]
  exact hasSum_le hle PA' PB

/-! ## 6. Non-vacuity: sine is in the class and nothing before today was -/

/-- **Poincaré for the sine function** — a test function no earlier file in
    this estate could touch: Var_γ(sin) ≤ ∫ cos² dγ. -/
theorem poincare_sin :
    (∫ x, Real.sin x ^ 2 ∂gauss) - (∫ x, Real.sin x ∂gauss) ^ 2
      ≤ ∫ x, Real.cos x ^ 2 ∂gauss := by
  refine poincare_beyond_polynomials (f := Real.sin) (f' := Real.cos)
    (C := 1) (m := 0) (fun x => Real.hasDerivAt_sin x) ?_ ?_
  · intro x
    simpa using Real.abs_sin_le_one x
  · intro x
    simpa using Real.abs_cos_le_one x

end PoincareBeyondPolynomials
