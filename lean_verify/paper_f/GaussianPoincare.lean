/-
  GaussianPoincare: The 1-d Gaussian Poincaré Inequality
  ======================================================

  Frontier unit (tree §11.6, the rigorous-QFT branch where the
  `BakryEmeryGap.lean` row lives; link L23 of
  `codex-internal/formalisation/SPINE.md`; wall #1 of the honest wall map). What the estate had
  before this file: the spec doc tags
  "Bakry-Émery spectral gap (gap = 2/Λ²)" as PROVED ★, but in Lean the gap
  was a DEFINITION and the criterion field was discharged by `le_refl` — no
  measure, no variance, no test function appeared anywhere (Phase 0 audit).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  **The Gaussian Poincaré inequality for polynomial test functions**, stated
  against Mathlib's own `gaussianReal 0 1`:

      ∫ p² dγ − (∫ p dγ)² ≤ ∫ (p′)² dγ        (`poincare_gaussianReal`)

  with the constant 1 SHARP — and sharpness is EXPORTED, not remarked:
  `gvar_X_eq_one` and `dirichlet_X_eq_one` compute both sides at p = X, and
  `no_better_constant` concludes that any constant c for which the inequality
  holds universally satisfies c ≥ 1. The route
  is Chernoff's: expand in Hermite polynomials, where both sides are exactly
  computable and the inequality becomes the index comparison 1 ≤ k.

  The stairs, each of which is new work. Mathlib has the algebraic Hermite
  polynomials with their coefficient, degree and monicity facts and the
  Rodrigues formula — two of which (`hermite_monic`, `natDegree_hermite`) are
  imported and used below — but no derivative identity and no L² theory
  whatsoever:

  1. §1–3 ALGEBRA. `derivative_H_succ`: Hₙ₊₁′ = (n+1)·Hₙ, which Mathlib does
     NOT have (a search for `derivative (hermite …)` across Mathlib returns
     only the two occurrences inside `hermite_succ` itself); the three-term
     recurrence; and `exists_hermite_repr`
     — every real polynomial is a finite Hermite combination with an
     explicit degree bound.
  2. §4 ANALYSIS. `stein_weight`: Gaussian integration by parts,
     ∫ x·p(x)·W = ∫ p′(x)·W, for the weight W = e^{−x²/2}. Proven from the
     fundamental theorem of calculus on the whole line
     (`integral_of_hasDerivAt_of_tendsto`) plus integrability of polynomial ×
     Gaussian and decay at both ends. This is the only genuinely analytic
     input; everything above it is algebra over this identity.
  3. §5 ORTHOGONALITY. `ip_H`: ⟪Hₘ, Hₙ⟫ = m!·Z·δₘₙ in L²(W), with
     Z = ∫ W = √(2π) computed (`Z_eq`). Mathlib has no Gaussian-L² theory of
     the Hermite family at all; the engine is `ip_H_succ`, the adjunction
     ⟪Hₘ₊₁, Hₙ⟫ = ⟪Hₘ, Hₙ′⟫, which is integration by parts in Hermite
     coordinates.
  4. §6 THE INEQUALITY. The variance is Σ_{k≥1} aₖ²·k! and the Dirichlet
     form is Σ_{k≥1} k·aₖ²·k!, so the inequality is termwise 1 ≤ k.
  5. §7 TRANSFER. `gmean_eq_integral`: the normalised weight functional is
     literally the expectation under `gaussianReal 0 1`, so the final
     statement rests on Mathlib's measure, not on our conventions.
  6. §8 MATHLIB VOCABULARY AND CROSS-CHECK. Polynomials are in L²(γ)
     (`memLp_polynomial_gaussianReal`), so the left-hand side really is
     Mathlib's `variance`, and the inequality is restated as
     `Var[p; γ] ≤ ∫(p′)²dγ` (`variance_le_integral_derivative_sq`).
     `gvar_X_eq_one` then closes the loop against Mathlib's own
     `variance_fun_id_gaussianReal`, which is proven from the moment
     generating function — a completely different route. If the
     orthogonality constant or Z = √(2π) were wrong, that equation would
     fail.

  CONVENTIONS, so the numbers can be compared with the estate's: the
  constant proven here is 1, for γ = N(0,1). The estate's `BakryEmeryGap.lean`
  works with the potential a·|x|², where it DEFINES gap := 2a and
  covariance := 1/(2a), i.e. gap × covariance = 1. At covariance 1 — which is
  our measure — that formula gives gap 1, so the two agree. (Theirs is a
  definition, ours is a theorem; the agreement is a consistency check, not a
  derivation of theirs.)

  NOT proven here — and the published Bakry-Émery tags must NOT move on the
  strength of this file:

  * **Test functions beyond polynomials** — IN THIS FILE. When written this
    was open; it has since been closed downstream: Hermite completeness is
    `HermiteCompleteness.lean`, the L²-Fourier apparatus is
    `HermiteBessel.lean` + `HermiteParseval.lean`, and the inequality for C¹
    functions of polynomial growth is
    `PoincareBeyondPolynomials.poincare_beyond_polynomials` (the maximal
    W^{1,2}(γ) class remains open there, and says so).
  * **Dimension > 1** — IN THIS FILE. Closed downstream:
    `GaussianPoincareProduct.poincare_MV` (all n, unit variance) and
    `GaussianProductMeasure.poincare_R16_measure` (n = 16, against the
    product measure).
  * **A DIFFERENT MEASURE.** This is the STANDARD Gaussian γ = N(0,1). The
    Λ-parametrised Gaussian family is treated downstream
    (`SpectralGaussianGap`, `GaussianProductMeasure`,
    `PoincareScaledBeyond`); what remains genuinely open everywhere is any
    connection to a SPECTRAL-ACTION measure — no file derives the Gaussian
    from Tr f(D/Λ), and no theorem anywhere says it does.
  * Ornstein-Uhlenbeck semigroups, log-Sobolev, hypercontractivity.
    (An earlier revision of this list also named "the
    `ProbabilityTheory.variance` phrasing" as missing — stale even then,
    since §8 proves `variance_le_integral_derivative_sq` in exactly that
    phrasing; caught by an adversarial review, recorded in ERRATA.)

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Linarith

open Polynomial

noncomputable section

namespace GaussianPoincare

/-! ## 1. The Hermite polynomials over ℝ

    Mathlib defines `Polynomial.hermite : ℕ → ℤ[X]` (probabilists'
    convention, monic) by the recurrence Hₙ₊₁ = X·Hₙ − Hₙ′. We work over ℝ,
    where the test functions live. -/

/-- The n-th probabilists' Hermite polynomial with real coefficients. -/
def H (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

@[simp] theorem H_zero : H 0 = 1 := by
  simp [H, hermite_zero]

@[simp] theorem H_one : H 1 = X := by
  simp [H]

/-- The defining recurrence, transported to ℝ. -/
theorem H_succ (n : ℕ) : H (n + 1) = X * H n - derivative (H n) := by
  unfold H
  rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    derivative_map]

theorem H_monic (n : ℕ) : (H n).Monic :=
  (hermite_monic n).map _

@[simp] theorem natDegree_H (n : ℕ) : (H n).natDegree = n := by
  unfold H
  rw [natDegree_map_eq_of_injective (Int.cast_injective) _, natDegree_hermite]

@[simp] theorem degree_H (n : ℕ) : (H n).degree = n := by
  have := (H_monic n).ne_zero
  rw [degree_eq_natDegree this, natDegree_H]

/-- Evaluation agrees with Mathlib's `aeval` on the integral Hermite
    polynomials, so the Rodrigues-type lemmas in
    `Mathlib.RingTheory.Polynomial.Hermite.Gaussian` apply verbatim to `H`. -/
theorem eval_H (n : ℕ) (x : ℝ) : (H n).eval x = aeval x (hermite n) := by
  simp [H, aeval_def, eval_map]

/-! ## 2. The derivative identity Hₙ′ = n·Hₙ₋₁

    This is the fact that makes Hermite polynomials the eigenbasis of the
    Ornstein-Uhlenbeck operator, and it is **not** in Mathlib: Mathlib has
    the recurrence and the Rodrigues formula only. It is what will turn the
    Poincaré inequality into a statement about the coefficient index. -/

/-- **The derivative identity**: Hₙ₊₁′ = (n+1)·Hₙ. Proven by induction from
    the recurrence alone (no Rodrigues formula, no analysis). -/
theorem derivative_H_succ (n : ℕ) :
    derivative (H (n + 1)) = ((n : ℝ) + 1) • H n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [H_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul,
        ih, derivative_smul, mul_smul_comm, add_sub_assoc, ← smul_sub,
        ← H_succ n]
      push_cast
      module

/-- The derivative identity in the form Hₙ′ = n·Hₙ₋₁ (for n ≥ 1). -/
theorem derivative_H (n : ℕ) (hn : 0 < n) :
    derivative (H n) = (n : ℝ) • H (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using derivative_H_succ m

/-- The derivative lowers the index, so it lowers the degree by exactly one
    (non-vacuity of the identity above). -/
theorem natDegree_derivative_H_succ (n : ℕ) :
    (derivative (H (n + 1))).natDegree = n := by
  have hc : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [derivative_H_succ, smul_eq_C_mul,
    natDegree_mul (C_ne_zero.mpr hc) (H_monic n).ne_zero, natDegree_C,
    natDegree_H, zero_add]

/-- **The three-term recurrence** X·Hₙ₊₁ = Hₙ₊₂ + (n+1)·Hₙ, obtained by
    feeding the derivative identity into the defining recurrence. This is the
    form in which the Hermite family will drive the orthogonality induction:
    multiplication by X raises the index by one and adds a multiple of the
    index below. -/
theorem X_mul_H_succ (n : ℕ) :
    X * H (n + 1) = H (n + 2) + ((n : ℝ) + 1) • H n := by
  rw [H_succ (n + 1), derivative_H_succ]
  ring

/-- The base case of the three-term recurrence: X·H₀ = H₁. -/
theorem X_mul_H_zero : X * H 0 = H 1 := by
  simp

theorem H_ne_zero (n : ℕ) : H n ≠ 0 := (H_monic n).ne_zero

/-! ## 3. The Hermite polynomials are a basis

    Every real polynomial of degree ≤ N is a finite ℝ-combination of
    H₀, …, H_N. This is pure algebra (the Hₙ are monic of degree n), but it
    is what lets a Poincaré statement about "all polynomials" be reduced to
    a statement about coefficients. -/

/-- **Hermite expansion with a degree bound**: any polynomial of degree ≤ N
    is Σ_{k ≤ N} aₖ·Hₖ for real coefficients aₖ. -/
theorem exists_hermite_repr :
    ∀ (N : ℕ) (p : ℝ[X]), p.natDegree ≤ N →
      ∃ a : ℕ → ℝ, p = ∑ k ∈ Finset.range (N + 1), a k • H k := by
  intro N
  induction N with
  | zero =>
      intro p hp
      refine ⟨fun _ => p.coeff 0, ?_⟩
      simpa [smul_eq_C_mul] using eq_C_of_natDegree_le_zero hp
  | succ N ih =>
      intro p hp
      by_cases hdeg : p.natDegree ≤ N
      · obtain ⟨a, ha⟩ := ih p hdeg
        refine ⟨fun k => if k = N + 1 then 0 else a k, ?_⟩
        have hcong : ∀ k ∈ Finset.range (N + 1),
            (if k = N + 1 then (0 : ℝ) else a k) • H k = a k • H k := by
          intro k hk
          simp only [Finset.mem_range] at hk
          rw [if_neg (by omega : k ≠ N + 1)]
        rw [Finset.sum_range_succ, Finset.sum_congr rfl hcong, ← ha]
        simp
      · rw [not_le] at hdeg
        have hpdeg : p.natDegree = N + 1 := le_antisymm hp hdeg
        have hp0 : p ≠ 0 := by
          intro h
          rw [h, natDegree_zero] at hpdeg
          omega
        have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
        have hdegq : (C p.leadingCoeff * H (N + 1)).degree = p.degree := by
          rw [degree_mul, degree_C hc0, degree_H, zero_add,
            degree_eq_natDegree hp0, hpdeg]
        have hlc : (C p.leadingCoeff * H (N + 1)).leadingCoeff = p.leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_C, (H_monic (N + 1)).leadingCoeff,
            mul_one]
        have hsub : (p - C p.leadingCoeff * H (N + 1)).natDegree ≤ N := by
          by_cases hz : p - C p.leadingCoeff * H (N + 1) = 0
          · simp [hz]
          · have hlt : (p - C p.leadingCoeff * H (N + 1)).degree < p.degree :=
              degree_sub_lt hdegq.symm hp0 hlc.symm
            have hnd := natDegree_lt_natDegree hz hlt
            omega
        obtain ⟨a, ha⟩ := ih _ hsub
        refine ⟨fun k => if k = N + 1 then p.leadingCoeff else a k, ?_⟩
        have hcong : ∀ k ∈ Finset.range (N + 1),
            (if k = N + 1 then p.leadingCoeff else a k) • H k = a k • H k := by
          intro k hk
          simp only [Finset.mem_range] at hk
          rw [if_neg (by omega : k ≠ N + 1)]
        rw [Finset.sum_range_succ, Finset.sum_congr rfl hcong, ← ha]
        simp [smul_eq_C_mul]

/-- Every real polynomial has a Hermite expansion. -/
theorem exists_hermite_repr' (p : ℝ[X]) :
    ∃ (N : ℕ) (a : ℕ → ℝ), p = ∑ k ∈ Finset.range (N + 1), a k • H k :=
  ⟨p.natDegree, (exists_hermite_repr p.natDegree p le_rfl).choose,
    (exists_hermite_repr p.natDegree p le_rfl).choose_spec⟩

/-! ## 4. Gaussian integration by parts (Stein's identity) for polynomials

    The first analytic stair. Everything here is stated against the
    UNNORMALISED Gaussian weight W(x) = e^{−x²/2} and the Lebesgue integral;
    the normalised measure `gaussianReal` enters at the next stair. The
    identity proven is

      ∫ x·p(x)·W(x) dx = ∫ p′(x)·W(x) dx,

    which is Stein's identity / Gaussian integration by parts for polynomial
    test functions. It is the engine for everything above it: orthogonality
    of the Hermite family follows from it by induction. -/

open MeasureTheory Filter Topology

/-- The unnormalised standard Gaussian weight e^{−x²/2}. -/
def W (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2)

theorem W_pos (x : ℝ) : 0 < W x := Real.exp_pos _

@[simp] theorem W_neg (x : ℝ) : W (-x) = W x := by
  unfold W
  congr 1
  ring

/-- Monomials are integrable against the Gaussian weight. -/
theorem integrable_pow_mul_W (n : ℕ) : Integrable (fun x : ℝ => x ^ n * W x) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq hb hs
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [W, Real.rpow_natCast]
  rw [show (-(1 / 2 : ℝ) * x ^ 2) = -x ^ 2 / 2 by ring]

/-- Every polynomial is integrable against the Gaussian weight. -/
theorem integrable_poly_mul_W (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * W x) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      have h := (integrable_pow_mul_W n).const_mul c
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp [Polynomial.eval_monomial, mul_assoc]
  | add p q hp hq =>
      have h := hp.add hq
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp [add_mul]

/-- p(x)·e^{−x²/2} → 0 as x → +∞: the Gaussian beats every polynomial. -/
theorem tendsto_poly_mul_W_atTop (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * W x) atTop (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => ‖p.eval x / Real.exp x‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp p.tendsto_div_exp_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ habs
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos (W_pos x), abs_of_pos (Real.exp_pos x), div_eq_mul_inv,
    ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold W
  apply Real.exp_le_exp.mpr
  nlinarith

/-- p(x)·e^{−x²/2} → 0 as x → −∞, by reflection. -/
theorem tendsto_poly_mul_W_atBot (p : ℝ[X]) :
    Tendsto (fun x : ℝ => p.eval x * W x) atBot (𝓝 0) := by
  have h := (tendsto_poly_mul_W_atTop (p.comp (-X))).comp tendsto_neg_atBot_atTop
  refine Tendsto.congr (fun x => ?_) h
  simp [Polynomial.eval_comp]

/-- **The total derivative integrates to zero**: because p·W vanishes at both
    ends of the line and its derivative is integrable, the fundamental
    theorem of calculus on ℝ gives ∫ (p·W)′ = 0. -/
theorem integral_deriv_poly_mul_W (p : ℝ[X]) :
    ∫ x : ℝ, ((derivative p).eval x - x * p.eval x) * W x = 0 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => p.eval y * W y)
      (((derivative p).eval x - x * p.eval x) * W x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => p.eval y) ((derivative p).eval x) x :=
      p.hasDerivAt x
    have h2 : HasDerivAt (fun y : ℝ => W y) (W x * (-x)) x := by
      have hg : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
        have h := ((hasDerivAt_pow 2 x).neg).div_const 2
        convert h using 1
        ring
      simpa [W] using hg.exp
    have h := h1.mul h2
    convert h using 1
    ring
  have hint : Integrable
      (fun x : ℝ => ((derivative p).eval x - x * p.eval x) * W x) := by
    have h := integrable_poly_mul_W (derivative p - X * p)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [sub_mul]
  have h := integral_of_hasDerivAt_of_tendsto hderiv hint
    (tendsto_poly_mul_W_atBot p) (tendsto_poly_mul_W_atTop p)
  simpa using h

/-- **Stein's identity / Gaussian integration by parts** for polynomial test
    functions: ∫ x·p(x)·W = ∫ p′(x)·W. This is the one genuinely analytic
    input to everything that follows. -/
theorem stein_weight (p : ℝ[X]) :
    ∫ x : ℝ, (x * p.eval x) * W x = ∫ x : ℝ, (derivative p).eval x * W x := by
  have h0 := integral_deriv_poly_mul_W p
  have hi1 : Integrable (fun x : ℝ => (derivative p).eval x * W x) :=
    integrable_poly_mul_W _
  have hi2 : Integrable (fun x : ℝ => (x * p.eval x) * W x) := by
    have h := integrable_poly_mul_W (X * p)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp
  have hsplit : (fun x : ℝ => ((derivative p).eval x - x * p.eval x) * W x)
      = fun x : ℝ => (derivative p).eval x * W x - (x * p.eval x) * W x := by
    funext x
    ring
  rw [hsplit, integral_sub hi1 hi2] at h0
  linarith

/-! ## 5. The Gaussian pairing and Hermite orthogonality

    With Stein's identity in hand the Hermite family can be shown orthogonal
    in L²(W). Everything is phrased through the linear functional
    I(p) = ∫ p·W and the pairing ⟪p,q⟫ = I(p·q). The normalisation constant
    Z = ∫ W is computed exactly (`Z_eq : Z = √(2π)`) and IS used twice, so
    the value is load-bearing and not decoration: `Z_pos` derives Z ≠ 0 from
    it (which every division below needs), and §7 rewrites through it to
    identify Z⁻¹·W with Mathlib's `gaussianPDFReal 0 1`. What the inequality
    does not depend on is the SCALE of the weight — but that is a property of
    the statement, not of these proofs. -/

/-- The Gaussian functional I(p) = ∫ p(x)·e^{−x²/2} dx. -/
def I (p : ℝ[X]) : ℝ := ∫ x : ℝ, p.eval x * W x

@[simp] theorem I_zero : I 0 = 0 := by
  unfold I
  simp

theorem I_add (p q : ℝ[X]) : I (p + q) = I p + I q := by
  unfold I
  rw [← integral_add (integrable_poly_mul_W p) (integrable_poly_mul_W q)]
  congr 1
  funext x
  simp [add_mul]

theorem I_sub (p q : ℝ[X]) : I (p - q) = I p - I q := by
  unfold I
  rw [← integral_sub (integrable_poly_mul_W p) (integrable_poly_mul_W q)]
  congr 1
  funext x
  simp [sub_mul]

theorem I_smul (c : ℝ) (p : ℝ[X]) : I (c • p) = c * I p := by
  unfold I
  have h : ∀ x : ℝ, (c • p).eval x * W x = c • (p.eval x * W x) := by
    intro x
    rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
    ring
  simp_rw [h]
  rw [integral_smul]
  simp

/-- **Stein's identity in functional form**: I(X·p) = I(p′). -/
theorem I_X_mul (p : ℝ[X]) : I (X * p) = I (derivative p) := by
  unfold I
  rw [← stein_weight p]
  congr 1
  funext x
  simp

/-- The Gaussian pairing ⟪p,q⟫ = ∫ p·q·W. -/
def ip (p q : ℝ[X]) : ℝ := I (p * q)

/-- The normalisation constant Z = ∫ e^{−x²/2} dx. -/
def Z : ℝ := I 1

theorem Z_eq : Z = Real.sqrt (2 * Real.pi) := by
  unfold Z I W
  have h : ∀ x : ℝ, (1 : ℝ[X]).eval x * Real.exp (-x ^ 2 / 2)
      = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    intro x
    rw [Polynomial.eval_one, one_mul]
    congr 1
    ring
  simp_rw [h]
  rw [integral_gaussian]
  congr 1
  ring

theorem Z_pos : 0 < Z := by
  rw [Z_eq]
  positivity

/-- Linearity of the pairing in its second argument. -/
theorem ip_smul_right (p q : ℝ[X]) (c : ℝ) : ip p (c • q) = c * ip p q := by
  unfold ip
  rw [mul_smul_comm, I_smul]

@[simp] theorem ip_zero_right (p : ℝ[X]) : ip p 0 = 0 := by
  unfold ip
  simp

/-- **The raising/lowering adjunction**: ⟪Hₘ₊₁, Hₙ⟫ = ⟪Hₘ, Hₙ′⟫. Multiplying
    by X on one side is differentiating on the other — this is the whole
    content of Gaussian integration by parts, in Hermite coordinates. -/
theorem ip_H_succ (m n : ℕ) :
    ip (H (m + 1)) (H n) = ip (H m) (derivative (H n)) := by
  unfold ip
  rw [H_succ m]
  have e1 : (X * H m - derivative (H m)) * H n
      = X * (H m * H n) - derivative (H m) * H n := by ring
  rw [e1, I_sub, I_X_mul, derivative_mul, I_add]
  ring

/-- Every Hermite polynomial of positive index has zero Gaussian mean. -/
theorem I_H_succ (n : ℕ) : I (H (n + 1)) = 0 := by
  rw [H_succ n, I_sub, I_X_mul]
  ring

/-- **Hermite orthogonality in L²(W)**: ⟪Hₘ, Hₙ⟫ = m!·Z·δₘₙ. Mathlib has no
    Gaussian-L² theory of the Hermite family at all; this is the statement
    that makes the family a coordinate system for the Gaussian. -/
theorem ip_H (m n : ℕ) :
    ip (H m) (H n) = if m = n then (m.factorial : ℝ) * Z else 0 := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => simp [ip, Z]
      | succ k =>
          have h : ip (H 0) (H (k + 1)) = I (H (k + 1)) := by
            unfold ip
            rw [H_zero, one_mul]
          rw [h, I_H_succ]
          simp
  | succ m ih =>
      cases n with
      | zero =>
          rw [ip_H_succ, H_zero]
          simp
      | succ k =>
          rw [ip_H_succ, derivative_H_succ, ip_smul_right, ih k]
          by_cases hmk : m = k
          · subst hmk
            rw [if_pos rfl, if_pos rfl, Nat.factorial_succ]
            push_cast
            ring
          · rw [if_neg hmk, if_neg (by omega : m + 1 ≠ k + 1)]
            ring

/-! ## 6. The variance identity and the Poincaré inequality

    With orthogonality proven, the Gaussian variance and the Dirichlet form
    become sums over Hermite coefficients, and the inequality reduces to
    k! ≤ k·k! for k ≥ 1. -/

/-- I is additive over finite sums. -/
theorem I_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    I (∑ i ∈ s, f i) = ∑ i ∈ s, I (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, I_add, ih, Finset.sum_insert hi]

/-- **The pairing of two Hermite expansions** collapses to a single sum, by
    orthogonality. -/
theorem ip_sum (M : ℕ) (a b : ℕ → ℝ) :
    ip (∑ j ∈ Finset.range M, a j • H j) (∑ k ∈ Finset.range M, b k • H k)
      = ∑ k ∈ Finset.range M, a k * b k * (k.factorial : ℝ) * Z := by
  unfold ip
  rw [Finset.sum_mul_sum, I_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [I_sum]
  have hterm : ∀ k, I ((a j • H j) * (b k • H k))
      = a j * b k * (if j = k then (j.factorial : ℝ) * Z else 0) := by
    intro k
    have he : (a j • H j) * (b k • H k) = (a j * b k) • (H j * H k) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [he, I_smul]
    congr 1
    exact ip_H j k
  simp only [hterm, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range M) j
    (fun k => a j * b k * ((j.factorial : ℝ) * Z))]
  rw [if_pos hj]
  ring

/-- The Gaussian mean of an expansion is its zeroth coefficient. -/
theorem I_expansion (N : ℕ) (a : ℕ → ℝ) :
    I (∑ k ∈ Finset.range (N + 1), a k • H k) = a 0 * Z := by
  rw [I_sum]
  have hterm : ∀ k, I (a k • H k) = a k * I (H k) := fun k => I_smul _ _
  simp only [hterm]
  rw [Finset.sum_eq_single 0]
  · rw [H_zero]
    rfl
  · intro k _ hk0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    rw [I_H_succ, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

/-- **The derivative of an expansion**, in Hermite coordinates: the index
    drops by one and the coefficient picks up the index. -/
theorem derivative_expansion (N : ℕ) (a : ℕ → ℝ) :
    derivative (∑ k ∈ Finset.range (N + 1), a k • H k)
      = ∑ j ∈ Finset.range N, (((j : ℝ) + 1) * a (j + 1)) • H j := by
  rw [derivative_sum, Finset.sum_range_succ']
  have h0 : derivative (a 0 • H 0) = 0 := by
    rw [H_zero, derivative_smul]
    simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [derivative_smul, derivative_H_succ, smul_smul, mul_comm]

/-- The Gaussian mean E_γ[p] = ∫p·W / ∫W. -/
def gmean (p : ℝ[X]) : ℝ := I p / Z

/-- The Gaussian variance Var_γ(p) = E_γ[p²] − E_γ[p]². -/
def gvar (p : ℝ[X]) : ℝ := gmean (p * p) - (gmean p) ^ 2

/-- **THE POINCARÉ INEQUALITY for polynomial test functions**:
    Var_γ(p) ≤ E_γ[(p′)²] for the standard Gaussian γ on ℝ.
    Both sides are computed exactly in Hermite coordinates — the variance is
    Σ_{k≥1} aₖ²·k!, the Dirichlet form is Σ_{k≥1} k·aₖ²·k! — so the
    inequality is the index comparison 1 ≤ k. The constant 1 is sharp:
    see `no_better_constant`. -/
theorem poincare_polynomial (p : ℝ[X]) :
    gvar p ≤ gmean (derivative p * derivative p) := by
  obtain ⟨N, a, rfl⟩ := exists_hermite_repr' p
  have hZ : Z ≠ 0 := ne_of_gt Z_pos
  -- the mean is the zeroth coefficient
  have hmean : gmean (∑ k ∈ Finset.range (N + 1), a k • H k) = a 0 := by
    unfold gmean
    rw [I_expansion, mul_div_assoc, div_self hZ, mul_one]
  -- the second moment
  have hsq : gmean ((∑ k ∈ Finset.range (N + 1), a k • H k)
      * (∑ k ∈ Finset.range (N + 1), a k • H k))
      = ∑ k ∈ Finset.range (N + 1), a k * a k * (k.factorial : ℝ) := by
    have h := ip_sum (N + 1) a a
    unfold ip at h
    unfold gmean
    rw [h, ← Finset.sum_mul, mul_div_assoc, div_self hZ, mul_one]
  -- the Dirichlet form
  have hder : gmean (derivative (∑ k ∈ Finset.range (N + 1), a k • H k)
      * derivative (∑ k ∈ Finset.range (N + 1), a k • H k))
      = ∑ j ∈ Finset.range N, (((j : ℝ) + 1) * a (j + 1))
          * (((j : ℝ) + 1) * a (j + 1)) * (j.factorial : ℝ) := by
    rw [derivative_expansion]
    have h := ip_sum N (fun j => ((j : ℝ) + 1) * a (j + 1))
      (fun j => ((j : ℝ) + 1) * a (j + 1))
    unfold ip at h
    unfold gmean
    rw [h, ← Finset.sum_mul, mul_div_assoc, div_self hZ, mul_one]
  -- assemble
  unfold gvar
  rw [hmean, hsq, hder, Finset.sum_range_succ'
    (fun k => a k * a k * (k.factorial : ℝ)) N]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  have hterm : ∀ j ∈ Finset.range N,
      a (j + 1) * a (j + 1) * (((j + 1).factorial : ℕ) : ℝ)
        ≤ (((j : ℝ) + 1) * a (j + 1)) * (((j : ℝ) + 1) * a (j + 1))
            * ((j.factorial : ℕ) : ℝ) := by
    intro j _
    have hF : (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
    have hfact : (((j + 1).factorial : ℕ) : ℝ)
        = ((j : ℝ) + 1) * ((j.factorial : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfact]
    have hd : (((j : ℝ) + 1) * a (j + 1)) * (((j : ℝ) + 1) * a (j + 1))
          * ((j.factorial : ℕ) : ℝ)
        - a (j + 1) * a (j + 1) * (((j : ℝ) + 1) * ((j.factorial : ℕ) : ℝ))
        = ((j : ℝ) * ((j : ℝ) + 1)) * (a (j + 1) * a (j + 1)
            * ((j.factorial : ℕ) : ℝ)) := by
      ring
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hnn : 0 ≤ ((j : ℝ) * ((j : ℝ) + 1)) * (a (j + 1) * a (j + 1)
        * ((j.factorial : ℕ) : ℝ)) := by
      apply mul_nonneg
      · nlinarith
      · exact mul_nonneg (mul_self_nonneg _) hF
    linarith
  have hsum := Finset.sum_le_sum hterm
  nlinarith [hsum]

/-- For p = H₁ = X the Poincaré inequality is an equality. (The two sides are
    each equal to 1 — see `gvar_X_eq_one` and `dirichlet_X_eq_one`; the
    statement that no smaller constant works is `no_better_constant`.) -/
theorem poincare_sharp : gvar X = gmean (derivative X * derivative X) := by
  have h1 : (X : ℝ[X]) = ∑ k ∈ Finset.range 2,
      (fun j => if j = 1 then (1 : ℝ) else 0) k • H k := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
  have hZ : Z ≠ 0 := ne_of_gt Z_pos
  rw [h1]
  have hmean : gmean (∑ k ∈ Finset.range 2,
      (fun j => if j = 1 then (1 : ℝ) else 0) k • H k) = 0 := by
    unfold gmean
    rw [I_expansion]
    simp
  have hsq : gmean ((∑ k ∈ Finset.range 2,
        (fun j => if j = 1 then (1 : ℝ) else 0) k • H k)
      * ∑ k ∈ Finset.range 2, (fun j => if j = 1 then (1 : ℝ) else 0) k • H k)
      = 1 := by
    have h := ip_sum 2 (fun j => if j = 1 then (1 : ℝ) else 0)
      (fun j => if j = 1 then (1 : ℝ) else 0)
    unfold ip at h
    unfold gmean
    rw [h, ← Finset.sum_mul, mul_div_assoc, div_self hZ, mul_one]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hder : gmean (derivative (∑ k ∈ Finset.range 2,
        (fun j => if j = 1 then (1 : ℝ) else 0) k • H k)
      * derivative (∑ k ∈ Finset.range 2,
        (fun j => if j = 1 then (1 : ℝ) else 0) k • H k)) = 1 := by
    rw [derivative_expansion]
    have h := ip_sum 1 (fun j => ((j : ℝ) + 1) * (if j + 1 = 1 then (1 : ℝ) else 0))
      (fun j => ((j : ℝ) + 1) * (if j + 1 = 1 then (1 : ℝ) else 0))
    unfold ip at h
    unfold gmean
    rw [h, ← Finset.sum_mul, mul_div_assoc, div_self hZ, mul_one]
    rw [Finset.sum_range_one]
    norm_num
  unfold gvar
  rw [hmean, hsq, hder]
  ring

/-! ## 7. The same statement against Mathlib's Gaussian measure

    Everything above is phrased through the normalised weight functional
    `gmean`. This section proves that `gmean` IS the expectation under
    Mathlib's `gaussianReal 0 1`, and restates the inequality in a form that
    mentions only that measure — so nothing rests on our own normalisation
    conventions. -/

open ProbabilityTheory

/-- The normalised weight functional is the expectation under Mathlib's
    standard Gaussian measure. -/
theorem gmean_eq_integral (p : ℝ[X]) :
    gmean p = ∫ x : ℝ, p.eval x ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x • p.eval x
      = Z⁻¹ • (p.eval x * W x) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [← Z_eq]
    unfold W
    ring
  simp_rw [hpdf]
  rw [integral_smul]
  unfold gmean I
  rw [smul_eq_mul, inv_mul_eq_div]

/-- **THE GAUSSIAN POINCARÉ INEQUALITY, stated for Mathlib's `gaussianReal`**:
    for every polynomial p and the standard Gaussian measure γ on ℝ,

      ∫ p² dγ − (∫ p dγ)² ≤ ∫ (p′)² dγ.

    The left-hand side is the variance of p under γ written out; the
    right-hand side is the Dirichlet energy. Equality holds at p = X
    (`poincare_sharp`), so the constant 1 is sharp. -/
theorem poincare_gaussianReal (p : ℝ[X]) :
    (∫ x : ℝ, (p.eval x) ^ 2 ∂(gaussianReal 0 1))
        - (∫ x : ℝ, p.eval x ∂(gaussianReal 0 1)) ^ 2
      ≤ ∫ x : ℝ, ((derivative p).eval x) ^ 2 ∂(gaussianReal 0 1) := by
  have hpp : (∫ x : ℝ, (p.eval x) ^ 2 ∂(gaussianReal 0 1)) = gmean (p * p) := by
    rw [gmean_eq_integral]
    congr 1
    funext x
    rw [Polynomial.eval_mul, sq]
  have hdd : (∫ x : ℝ, ((derivative p).eval x) ^ 2 ∂(gaussianReal 0 1))
      = gmean (derivative p * derivative p) := by
    rw [gmean_eq_integral]
    congr 1
    funext x
    rw [Polynomial.eval_mul, sq]
  rw [hpp, hdd, ← gmean_eq_integral]
  have h := poincare_polynomial p
  unfold gvar at h
  exact h

/-! ## 8. Mathlib's own vocabulary, and an independent cross-check

    Two things are worth having beyond §7. First, the left-hand side of the
    inequality is the VARIANCE, and Mathlib has a `variance`; saying so
    requires knowing that polynomials are in L²(γ), which is proven here.
    Second — and this is the point of the section — the whole chain
    (Hermite orthogonality, the constant Z, Stein's identity) can be checked
    against a Mathlib theorem proven by a completely different route: for the
    identity function, Mathlib computes the Gaussian variance from the moment
    generating function. `gvar_X_eq_one` closes that loop. If our
    normalisation were wrong anywhere, this is where it would show. -/

theorem gmean_one : gmean (1 : ℝ[X]) = 1 := by
  unfold gmean
  exact div_self (ne_of_gt Z_pos)

theorem gmean_add (p q : ℝ[X]) : gmean (p + q) = gmean p + gmean q := by
  unfold gmean
  rw [I_add, add_div]

theorem gmean_smul (c : ℝ) (p : ℝ[X]) : gmean (c • p) = c * gmean p := by
  unfold gmean
  rw [I_smul, mul_div_assoc]

/-- Monomials are in L²(γ) — the non-vacuity certificate for the variance. -/
theorem memLp_pow_gaussianReal (n : ℕ) (m : ℝ) (v : NNReal) :
    MemLp (fun x : ℝ ↦ x ^ n) 2 (gaussianReal m v) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have h : MemLp id ((2 * n : ℕ) : NNReal) (gaussianReal m v) := memLp_id_gaussianReal _
  have h2 := h.integrable_norm_rpow'
  simp only [id_eq, Real.norm_eq_abs, ENNReal.coe_toReal, NNReal.coe_natCast,
    Real.rpow_natCast] at h2
  refine h2.congr' (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [← pow_mul, ← abs_pow, mul_comm]
  simp

/-- Polynomials are in L²(γ), so `ProbabilityTheory.variance` is not a junk
    value on them. -/
theorem memLp_polynomial_gaussianReal (p : ℝ[X]) (m : ℝ) (v : NNReal) :
    MemLp (fun x : ℝ ↦ p.eval x) 2 (gaussianReal m v) := by
  have key : (fun x : ℝ ↦ p.eval x)
      = ∑ i ∈ Finset.range (p.natDegree + 1), (fun x : ℝ ↦ p.coeff i * x ^ i) := by
    ext x
    rw [Finset.sum_apply, Polynomial.eval_eq_sum_range]
  rw [key]
  exact memLp_finset_sum' _ fun i _ ↦ (memLp_pow_gaussianReal i m v).const_mul _

/-- Our `gvar` IS Mathlib's `variance` under `gaussianReal 0 1`. -/
theorem variance_eq_gvar (p : ℝ[X]) :
    Var[fun x => p.eval x; gaussianReal 0 1] = gvar p := by
  rw [variance_eq_sub (memLp_polynomial_gaussianReal p 0 1)]
  unfold gvar
  congr 1
  · rw [gmean_eq_integral]
    congr 1
    funext x
    simp [Polynomial.eval_mul, sq]
  · rw [gmean_eq_integral]

/-- **THE POINCARÉ INEQUALITY IN MATHLIB'S VOCABULARY**:
    Var[p; γ] ≤ ∫ (p′)² dγ for the standard Gaussian γ. -/
theorem variance_le_integral_derivative_sq (p : ℝ[X]) :
    Var[fun x => p.eval x; gaussianReal 0 1]
      ≤ ∫ x : ℝ, ((derivative p).eval x) ^ 2 ∂(gaussianReal 0 1) := by
  rw [variance_eq_gvar]
  have hd : (∫ x : ℝ, ((derivative p).eval x) ^ 2 ∂(gaussianReal 0 1))
      = gmean (derivative p * derivative p) := by
    rw [gmean_eq_integral]
    congr 1
    funext x
    rw [Polynomial.eval_mul, sq]
  rw [hd]
  exact poincare_polynomial p

/-- Cross-check 1: the Gaussian mean of x is 0, via Mathlib's
    `integral_id_gaussianReal`. -/
theorem gmean_X_eq_zero : gmean (X : ℝ[X]) = 0 := by
  rw [gmean_eq_integral]
  simp

/-- **Cross-check 2 — the independent confirmation.** Our Hermite machinery
    gives Var(X) = 1! · Z / Z = 1; Mathlib gets the same number from the
    moment generating function (`variance_fun_id_gaussianReal`). The two
    routes share nothing but the measure, so this equation is a genuine test
    of the orthogonality constant and of `Z = √(2π)`. -/
theorem gvar_X_eq_one : gvar (X : ℝ[X]) = 1 := by
  have h := variance_eq_gvar (X : ℝ[X])
  simp only [Polynomial.eval_X] at h
  rw [← h]
  simp

/-- The Dirichlet energy of X is 1. -/
theorem dirichlet_X_eq_one :
    gmean (derivative (X : ℝ[X]) * derivative X) = 1 := by
  rw [Polynomial.derivative_X, one_mul, gmean_one]

/-- **THE CONSTANT 1 CANNOT BE IMPROVED**, as an exported statement rather
    than a remark: if Var_γ(p) ≤ c·E_γ[(p′)²] holds for every polynomial,
    then c ≥ 1. (Proof: test on p = X, where the variance and the Dirichlet
    energy are both exactly 1.) -/
theorem no_better_constant (c : ℝ)
    (h : ∀ p : ℝ[X], gvar p ≤ c * gmean (derivative p * derivative p)) :
    1 ≤ c := by
  have hX := h X
  rw [gvar_X_eq_one, dirichlet_X_eq_one, mul_one] at hX
  exact hX

/-- Sharpness in the measure-theoretic vocabulary, matching the language of
    `poincare_gaussianReal`: at p = X both sides equal 1. -/
theorem poincare_sharp_gaussianReal :
    Var[fun x => (X : ℝ[X]).eval x; gaussianReal 0 1] = 1 ∧
      (∫ x : ℝ, ((derivative (X : ℝ[X])).eval x) ^ 2 ∂(gaussianReal 0 1)) = 1 := by
  refine ⟨by rw [variance_eq_gvar, gvar_X_eq_one], ?_⟩
  have hd : (∫ x : ℝ, ((derivative (X : ℝ[X])).eval x) ^ 2 ∂(gaussianReal 0 1))
      = gmean (derivative X * derivative X) := by
    rw [gmean_eq_integral]
    congr 1
    funext x
    rw [Polynomial.eval_mul, sq]
  rw [hd, dirichlet_X_eq_one]

/-! ## 9. The stairs above this one

    For the record, in dependency order, what a continuation would build:

    1. **Density of polynomials in W^{1,2}(γ)**, so that the inequality
       extends from polynomial test functions to the natural space. This is
       Hermite completeness in L²(γ); Mathlib does not have it.
    2. **Tensorisation** to ℝⁿ: the Poincaré constant of a product measure is
       the minimum of the factors', giving the inequality on ℝ¹⁶ ≅ Herm₄(ℂ),
       which is the space the cascade actually needs.
    3. **A spectral-action measure**: the estate's claimed gap 2/Λ² is about
       a measure built from the spectral action, not about N(0,1). Writing
       that measure down in Lean is a prerequisite for any statement about
       Λ, and it does not exist yet anywhere in the estate.
    4. The Ornstein-Uhlenbeck semigroup and the Bakry-Émery Γ₂ criterion,
       which is the machinery the published narrative invokes. This file
       reaches the conclusion of that machinery in the one case where it can
       be got at by hand; it does not build the machinery. -/

end GaussianPoincare
