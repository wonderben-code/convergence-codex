/-
  PoincareSteinScaled: the Stein-Class Poincaré Inequality at Every Variance
  ==========================================================================

  Review round 7 caught the honest gap this file closes: the Stein-class
  inequality (`PoincareSteinClass`) lived at variance one, PARALLEL to —
  not extending — the σ²-scaled chain (`PoincareScaledBeyond`). This file
  removes the unit-variance hypothesis (the queue's "one restrictive
  hypothesis at a time"): the STEIN CLASS at variance σ² is defined by
  the σ-Gaussian integration-by-parts pairing against polynomials, and
  Poincaré holds on it with the sharp σ² constant. The route is the
  substitution x ↦ σx, transported at the level of the CLASS: a σ-Stein
  pair becomes a standard Stein pair (with the test polynomial composed
  with X/σ), the variance-one theorem fires, and the integrals transport
  back. The scaled C¹-of-polynomial-growth theorem
  (`poincare_scaled_beyond`) is then re-derived as a corollary — the
  subsumption relation the round-7-corrected honesty box promised.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `SteinPairScaled σ f g` — the class at variance σ²: f, g ∈ L²(γ_σ²)
     with ∫ g·q dγ_σ² = ∫ f·(x·q/σ² − q′) dγ_σ² for EVERY polynomial q.
     At σ = 0 the division-by-zero convention (x·q/0 = 0 in Lean) makes
     the pairing a degenerate Dirac condition; the class carries no
     analytic content there, and nothing below pretends it does — the
     σ = 0 case of the inequality is proven separately and trivially.
  2. `steinPairScaled_toStd` (σ ≠ 0) — THE TRANSPORT: (f, g) a σ-Stein
     pair ⟹ (f(σ·), σ·g(σ·)) a standard Stein pair. The test-function
     side composes with C(1/σ)·X; `Polynomial.derivative_comp` does the
     chain rule on the polynomial side.
  3. **`poincare_stein_scaled`** — THE INEQUALITY AT EVERY VARIANCE, no
     σ ≠ 0 hypothesis:

         Var_{γ_σ²}(f) ≤ σ² · ∫ g² dγ_σ²   for every σ-Stein pair.

     σ ≠ 0 by transport + the variance-one theorem; σ = 0 by the Dirac
     degeneration (both sides are 0 — `integral_dirac`).
  4. `steinPairScaled_of_polyGrowth` (σ ≠ 0) — the scaled C¹ class
     embeds: every everywhere-differentiable f of polynomial growth
     (with f′ of polynomial growth) forms a σ-Stein pair with f′ —
     the reverse transport, test side composed with C(σ)·X.
  5. **`poincare_scaled_beyond_subsumed`** — `poincare_scaled_beyond`'s
     statement re-derived: σ ≠ 0 THROUGH the class inequality; σ = 0 by
     the same standalone Dirac computation (necessarily so — at σ = 0
     NOT EVERY C¹ pair lies in the degenerate class: (X, 1) provably
     does not, `not_steinPairScaled_zero_id_one` — so no class route
     exists there). The scaled chain is SUBSUMED, completing
     what the round-7 correction scoped; `poincare_scaled_beyond_original`
     restates it in the original file's literal spelling.
  6. **Sharpness, machine-checked** (review round 8): `var_id_scaled`
     (Var_{γ_σ²}(X) = σ²) and **`no_better_constant_scaled`** — any
     constant serving the whole σ-class at σ ≠ 0 is at least σ². The
     header's "sharp σ² constant" is now a theorem, not a docstring.

  WHAT IS AND IS NOT CLAIMED: exactly the variance-one file's honesty
  box, at every σ — polynomials are the test family (incomparable with
  Cc^∞, no a-priori inclusion either way), one dimension, nothing about
  the spectral action. The fJump strictness witness is variance-one
  and is not re-proven here (its transport is routine but not needed by
  any claim this file makes).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import PoincareSteinClass
import PoincareScaledBeyond

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareSteinScaled

open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
  PoincareBeyondPolynomials PoincareSteinClass PoincareScaledBeyond

/-- The variance-σ² Gaussian. -/
abbrev gaussSc (σ : ℝ) : Measure ℝ :=
  gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)

/-- **The Stein class at variance σ²**: the σ-Gaussian IBP pairing
    against every polynomial. At σ = 0 see the header — the pairing is
    a degenerate Dirac condition and carries no analytic content. -/
def SteinPairScaled (σ : ℝ) (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 (gaussSc σ) ∧ MemLp g 2 (gaussSc σ) ∧
    ∀ q : ℝ[X], ∫ x, g x * q.eval x ∂gaussSc σ
      = ∫ x, f x * (x * q.eval x / σ ^ 2 - (derivative q).eval x) ∂gaussSc σ

/-! ## 1. The change of variables, a.e. version -/

theorem map_scaled (σ : ℝ) :
    (gauss : Measure ℝ).map (fun x => σ * x) = gaussSc σ := by
  rw [show (gauss : Measure ℝ) = gaussianReal 0 1 from rfl,
    gaussianReal_map_const_mul σ]
  congr 1
  · ring
  · ext
    simp

/-- Change of variables needing only a.e. strong measurability (the
    class members carry no more). -/
theorem integral_scaled_ae (σ : ℝ) (h : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable h (gaussSc σ)) :
    ∫ x, h x ∂gaussSc σ = ∫ x, h (σ * x) ∂gauss := by
  rw [← map_scaled σ] at hmeas ⊢
  exact integral_map (by fun_prop) hmeas

theorem memLp_comp_scaled (σ : ℝ) {h : ℝ → ℝ}
    (hh : MemLp h 2 (gaussSc σ)) : MemLp (fun x => h (σ * x)) 2 gauss := by
  rw [← map_scaled σ] at hh
  exact (memLp_map_measure_iff hh.aestronglyMeasurable (by fun_prop)).mp hh

/-! ## 2. The transport of the class -/

/-- **A σ-Stein pair transports to a standard Stein pair** (σ ≠ 0):
    (f, g) ↦ (f(σ·), σ·g(σ·)), with the test polynomial composed with
    C(1/σ)·X on the way through. -/
theorem steinPairScaled_toStd {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (h : SteinPairScaled σ f g) :
    SteinPair (fun x => f (σ * x)) (fun x => σ * g (σ * x)) := by
  obtain ⟨hf, hg, hpair⟩ := h
  refine ⟨memLp_comp_scaled σ hf, (memLp_comp_scaled σ hg).const_mul σ, ?_⟩
  intro q
  set r : ℝ[X] := q.comp (Polynomial.C (1 / σ) * Polynomial.X) with hrdef
  have hreval : ∀ y : ℝ, r.eval y = q.eval (1 / σ * y) := fun y => by
    simp [hrdef, Polynomial.eval_comp]
  have hrderiv : ∀ y : ℝ, (derivative r).eval y
      = 1 / σ * (derivative q).eval (1 / σ * y) := fun y => by
    simp [hrdef, Polynomial.derivative_comp]
  have hL : ∫ x, (σ * g (σ * x)) * q.eval x ∂gauss
      = σ * ∫ x, g x * r.eval x ∂gaussSc σ := by
    rw [integral_scaled_ae σ (fun x => g x * r.eval x)
      (hg.aestronglyMeasurable.mul (Polynomial.continuous r).aestronglyMeasurable),
      ← integral_const_mul]
    congr 1
    funext x
    rw [hreval]
    have : 1 / σ * (σ * x) = x := by field_simp
    rw [this]
    ring
  have hR : ∫ x, f (σ * x) * (x * q.eval x
        - (derivative q).eval x) ∂gauss
      = σ * ∫ x, f x * (x * r.eval x / σ ^ 2
          - (derivative r).eval x) ∂gaussSc σ := by
    rw [integral_scaled_ae σ
      (fun x => f x * (x * r.eval x / σ ^ 2 - (derivative r).eval x))
      (hf.aestronglyMeasurable.mul (by fun_prop)),
      ← integral_const_mul]
    congr 1
    funext x
    rw [hreval, hrderiv]
    have h1 : 1 / σ * (σ * x) = x := by field_simp
    rw [h1]
    field_simp
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  rw [hL, hR, hpair r]

/-! ## 3. The inequality at every variance -/

/-- The Dirac degeneration: at variance 0 the Gaussian is the Dirac
    mass at 0 (a measure equality; the vanishing of both sides of the
    inequality is derived from it downstream, not stated here). -/
theorem gaussSc_zero : gaussSc 0 = Measure.dirac 0 := by
  have h0 : (⟨(0 : ℝ) ^ 2, sq_nonneg 0⟩ : NNReal) = 0 := by
    ext
    norm_num
  rw [show gaussSc 0 = gaussianReal 0 ⟨(0 : ℝ) ^ 2, sq_nonneg 0⟩ from rfl,
    h0, gaussianReal_zero_var]

/-- **THE STEIN-CLASS POINCARÉ INEQUALITY AT EVERY VARIANCE** — no
    σ ≠ 0 hypothesis: Var_{γ_σ²}(f) ≤ σ²·∫g² dγ_σ² for every σ-Stein
    pair. σ = 0 degenerates to 0 ≤ 0 via the Dirac case. -/
theorem poincare_stein_scaled (σ : ℝ) {f g : ℝ → ℝ}
    (h : SteinPairScaled σ f g) :
    (∫ x, f x ^ 2 ∂gaussSc σ) - (∫ x, f x ∂gaussSc σ) ^ 2
      ≤ σ ^ 2 * ∫ x, g x ^ 2 ∂gaussSc σ := by
  by_cases hσ : σ = 0
  · subst hσ
    rw [gaussSc_zero, integral_dirac, integral_dirac]
    simp
  · have h1 : ∫ x, f x ^ 2 ∂gaussSc σ = ∫ x, f (σ * x) ^ 2 ∂gauss :=
      integral_scaled_ae σ (fun y => f y ^ 2)
        (h.1.aestronglyMeasurable.pow 2)
    have h2 : ∫ x, f x ∂gaussSc σ = ∫ x, f (σ * x) ∂gauss :=
      integral_scaled_ae σ f h.1.aestronglyMeasurable
    have h3 : ∫ x, g x ^ 2 ∂gaussSc σ = ∫ x, g (σ * x) ^ 2 ∂gauss :=
      integral_scaled_ae σ (fun y => g y ^ 2)
        (h.2.1.aestronglyMeasurable.pow 2)
    rw [h1, h2, h3]
    have hG : ∫ x, (σ * g (σ * x)) ^ 2 ∂gauss
        = σ ^ 2 * ∫ x, g (σ * x) ^ 2 ∂gauss := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    calc (∫ x, f (σ * x) ^ 2 ∂gauss) - (∫ x, f (σ * x) ∂gauss) ^ 2
        ≤ ∫ x, (σ * g (σ * x)) ^ 2 ∂gauss :=
          poincare_stein (steinPairScaled_toStd hσ h)
      _ = σ ^ 2 * ∫ x, g (σ * x) ^ 2 ∂gauss := hG

/-! ## 4. The scaled C¹ class embeds; the scaled chain is subsumed -/

/-- **The scaled C¹-of-polynomial-growth class embeds in the σ-Stein
    class** (σ ≠ 0): the reverse transport, with the test polynomial
    composed with C(σ)·X. -/
theorem steinPairScaled_of_polyGrowth {σ : ℝ} (hσ : σ ≠ 0) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    SteinPairScaled σ f f' := by
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hfcont : Continuous f := hdiff.continuous
  have hf'meas : Measurable f' := by
    have hfd : f' = deriv f := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact measurable_deriv f
  -- the transported pair, exactly as in `poincare_scaled_beyond`
  have hgderiv : ∀ x, HasDerivAt (fun y => f (σ * y))
      ((fun y => σ * f' (σ * y)) x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => σ * y) σ x := by
      simpa using (hasDerivAt_id x).const_mul σ
    have h2 := (hderiv (σ * x)).comp x h1
    simpa [mul_comm] using h2
  have hgrow : ∀ x : ℝ, (1 + (σ * x) ^ 2) ^ m
      ≤ (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by
    intro x
    rw [← mul_pow]
    have hbase : 1 + (σ * x) ^ 2 ≤ max 1 (σ ^ 2) * (1 + x ^ 2) := by
      have h1 : σ ^ 2 ≤ max 1 (σ ^ 2) := le_max_right _ _
      have h2 : (1 : ℝ) ≤ max 1 (σ ^ 2) := le_max_left _ _
      nlinarith [sq_nonneg x, sq_nonneg σ]
    exact pow_le_pow_left₀ (by positivity) hbase m
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hb 0)
  have hD0 : (0 : ℝ) ≤ (max 1 (σ ^ 2)) ^ m := by positivity
  have hFb : ∀ x, |f (σ * x)| ≤ C * (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by
    intro x
    calc |f (σ * x)| ≤ C * (1 + (σ * x) ^ 2) ^ m := hb (σ * x)
      _ ≤ C * ((max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m) := by
          exact mul_le_mul_of_nonneg_left (hgrow x) hC0
      _ = C * (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by ring
  have hF'b : ∀ x, |f' (σ * x)| ≤ C * (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by
    intro x
    calc |f' (σ * x)| ≤ C * (1 + (σ * x) ^ 2) ^ m := hb' (σ * x)
      _ ≤ C * ((max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m) := by
          exact mul_le_mul_of_nonneg_left (hgrow x) hC0
      _ = C * (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by ring
  -- membership at variance σ², by pulling standard membership back
  have hmemf : MemLp f 2 (gaussSc σ) := by
    rw [← map_scaled σ]
    refine (memLp_map_measure_iff ?_ (by fun_prop)).mpr ?_
    · rw [map_scaled σ]
      exact hfcont.aestronglyMeasurable
    · exact memLp_of_polyGrowth
        (hfcont.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
        hFb
  have hmemf' : MemLp f' 2 (gaussSc σ) := by
    rw [← map_scaled σ]
    refine (memLp_map_measure_iff ?_ (by fun_prop)).mpr ?_
    · rw [map_scaled σ]
      exact hf'meas.aestronglyMeasurable
    · exact memLp_of_polyGrowth
        ((hf'meas.comp (measurable_const_mul σ)).aestronglyMeasurable) hF'b
  refine ⟨hmemf, hmemf', fun q => ?_⟩
  -- the standard pair for the transported functions: one COMMON growth
  -- constant D for both components
  set D : ℝ := (1 + |σ|) * (C * (max 1 (σ ^ 2)) ^ m) with hDdef
  have hKnn : (0 : ℝ) ≤ C * (max 1 (σ ^ 2)) ^ m := mul_nonneg hC0 hD0
  have hDF : ∀ x, |f (σ * x)| ≤ D * (1 + x ^ 2) ^ m := by
    intro x
    refine le_trans (hFb x) (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hDdef]
    nlinarith [mul_nonneg (abs_nonneg σ) hKnn]
  have hDG : ∀ x, |σ * f' (σ * x)| ≤ D * (1 + x ^ 2) ^ m := by
    intro x
    rw [abs_mul]
    calc |σ| * |f' (σ * x)|
        ≤ |σ| * (C * (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left (hF'b x) (abs_nonneg σ)
      _ ≤ D * (1 + x ^ 2) ^ m := by
          rw [hDdef]
          nlinarith [hKnn, sq_nonneg x,
            mul_nonneg hKnn (by positivity : (0:ℝ) ≤ (1 + x ^ 2) ^ m)]
  have hstd : SteinPair (fun x => f (σ * x)) (fun x => σ * f' (σ * x)) :=
    steinPair_of_polyGrowth hgderiv hDF hDG
  -- reverse substitution: test with q̂ = q.comp (C σ · X)
  set r : ℝ[X] := q.comp (Polynomial.C σ * Polynomial.X) with hrdef
  have hreval : ∀ y : ℝ, r.eval y = q.eval (σ * y) := fun y => by
    simp [hrdef, Polynomial.eval_comp]
  have hrderiv : ∀ y : ℝ, (derivative r).eval y
      = σ * (derivative q).eval (σ * y) := fun y => by
    simp [hrdef, Polynomial.derivative_comp]
  have hpair := hstd.2.2 r
  -- transport both sides of hpair down to γ_σ²
  have hLstd : ∫ x, (σ * f' (σ * x)) * r.eval x ∂gauss
      = σ * ∫ x, f' x * q.eval x ∂gaussSc σ := by
    rw [integral_scaled_ae σ (fun x => f' x * q.eval x)
      (hf'meas.aestronglyMeasurable.mul
        (Polynomial.continuous q).aestronglyMeasurable),
      ← integral_const_mul]
    congr 1
    funext x
    rw [hreval]
    ring
  have hRstd : ∫ x, f (σ * x) * (x * r.eval x - (derivative r).eval x) ∂gauss
      = σ * ∫ x, f x * (x * q.eval x / σ ^ 2
          - (derivative q).eval x) ∂gaussSc σ := by
    rw [integral_scaled_ae σ
      (fun x => f x * (x * q.eval x / σ ^ 2 - (derivative q).eval x))
      (hfcont.aestronglyMeasurable.mul (by fun_prop)),
      ← integral_const_mul]
    congr 1
    funext x
    rw [hreval, hrderiv]
    field_simp
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X] at hpair
  rw [hLstd, hRstd] at hpair
  exact mul_left_cancel₀ hσ hpair

/-- **The scaled beyond-polynomials theorem, subsumed**: the statement
    of `poincare_scaled_beyond` re-derived from the class inequality
    (σ = 0 by the Dirac case, σ ≠ 0 through the σ-Stein class). -/
theorem poincare_scaled_beyond_subsumed (σ : ℝ) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂gaussSc σ) - (∫ x, f x ∂gaussSc σ) ^ 2
      ≤ σ ^ 2 * ∫ x, f' x ^ 2 ∂gaussSc σ := by
  by_cases hσ : σ = 0
  · subst hσ
    rw [gaussSc_zero, integral_dirac, integral_dirac]
    simp
  · exact poincare_stein_scaled σ
      (steinPairScaled_of_polyGrowth hσ hderiv hb hb')

/-- Non-vacuity at every variance: (X, 1) is a σ-Stein pair for σ ≠ 0.
    At it the inequality reads σ² ≤ σ²·1 — now MACHINE-CHECKED by
    `var_id_scaled` and `no_better_constant_scaled` below, not merely
    asserted. -/
theorem steinPairScaled_id_one {σ : ℝ} (hσ : σ ≠ 0) :
    SteinPairScaled σ (fun x => x) (fun _ => 1) := by
  refine steinPairScaled_of_polyGrowth (C := 1) (m := 1) hσ
    (fun x => hasDerivAt_id x) (fun x => ?_) (fun x => ?_)
  · have h1 : |x| ≤ 1 + x ^ 2 := by
      nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
    simpa using h1
  · have h0 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    rw [abs_one]
    nlinarith

/-- The σ = 0 exclusion, as a theorem (review round 9): (X, 1) — a C¹
    pair of polynomial growth — does NOT lie in the degenerate σ = 0
    class (the pairing at q = 1 forces g(0) = 0). So the Dirac branch
    of the subsumption cannot be routed through the class. -/
theorem not_steinPairScaled_zero_id_one :
    ¬ SteinPairScaled 0 (fun x => x) (fun _ => 1) := by
  rintro ⟨-, -, hpair⟩
  have h := hpair 1
  rw [gaussSc_zero] at h
  simp at h

/-! ## 5. Sharpness, machine-checked (review round 8) -/

/-- Var_{γ_σ²}(X) = σ² — the variance side of the sharpness identity,
    from Mathlib's `variance_id_gaussianReal`. -/
theorem var_id_scaled (σ : ℝ) :
    (∫ x, x ^ 2 ∂gaussSc σ) - (∫ x, x ∂gaussSc σ) ^ 2 = σ ^ 2 := by
  have hvar : Var[id; gaussSc σ] = ((⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) : ℝ) :=
    variance_id_gaussianReal
  rw [variance_eq_sub (memLp_id_gaussianReal' 2 (by norm_num))] at hvar
  simpa using hvar

/-- **The σ² constant is sharp at every σ ≠ 0**: any constant c that
    serves EVERY σ-Stein pair satisfies σ² ≤ c — witnessed by (X, 1),
    where the left side is exactly σ² and ∫1² = 1. -/
theorem no_better_constant_scaled {σ : ℝ} (hσ : σ ≠ 0) (c : ℝ)
    (h : ∀ f g : ℝ → ℝ, SteinPairScaled σ f g →
      (∫ x, f x ^ 2 ∂gaussSc σ) - (∫ x, f x ∂gaussSc σ) ^ 2
        ≤ c * ∫ x, g x ^ 2 ∂gaussSc σ) :
    σ ^ 2 ≤ c := by
  have hid := h (fun x => x) (fun _ => 1) (steinPairScaled_id_one hσ)
  have h1 : ∫ x, ((fun _ : ℝ => (1 : ℝ)) x) ^ 2 ∂gaussSc σ = 1 := by simp
  rw [h1, mul_one] at hid
  simp only [] at hid
  linarith [var_id_scaled σ]

/-- The subsumption, restated in `poincare_scaled_beyond`'s literal
    spelling (the two are definitionally equal; this closes even the
    cosmetic gap). -/
theorem poincare_scaled_beyond_original (σ : ℝ) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)))
        - (∫ x, f x ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))) ^ 2
      ≤ σ ^ 2 * ∫ x, f' x ^ 2
          ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)) :=
  poincare_scaled_beyond_subsumed σ hderiv hb hb'

end PoincareSteinScaled
