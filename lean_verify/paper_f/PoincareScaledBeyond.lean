/-
  PoincareScaledBeyond: the Λ²/2 Inequality Beyond Polynomials
  ============================================================

  `PoincareBeyondPolynomials` removed the polynomial-only caveat at variance
  one. This file transfers it to every variance σ² — and in particular to
  σ² = Λ²/2, the cutoff-scale Gaussian of `SpectralGaussianGap` — by the
  substitution x ↦ σx. The flagship Bakry–Émery-form inequality of this
  campaign now holds for C¹ test functions of polynomial growth, not just
  polynomials.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `integral_scaled` — the change of variables
     ∫ h dγ_{σ²} = ∫ h(σx) dγ, via Mathlib's `gaussianReal_map_const_mul`
     (which is unconditional in σ, so no σ ≠ 0 hypothesis is needed
     anywhere in this file — at σ = 0 everything degenerates gracefully to
     the Dirac case, where the inequality is 0 ≤ 0).
  2. **`poincare_scaled_beyond`** — for EVERY σ and f ∈ C¹ with f, f′ of
     polynomial growth:

         Var_{γ_{σ²}}(f) ≤ σ² · ∫ (f′)² dγ_{σ²}.

     Proof by substitution: g(x) = f(σx) has g′(x) = σ·f′(σx), the growth
     hypotheses transfer with a new constant, and the variance-one theorem
     applied to g is exactly the claim after the change of variables.
  3. **`poincare_lambda_beyond`** — the cutoff form: at variance Λ²/2,

         Var(f) ≤ (Λ²/2) · E[(f′)²]

     against `gaussianReal 0 (Λ²/2)`, for the same class. The estate's
     quoted gap 2/Λ² now constrains non-polynomial observables.
  4. `poincare_lambda_sin` — non-vacuity at the cutoff scale: the inequality
     instantiated at sin against the Λ-Gaussian.

  NOT proven here:

  * The maximal W^{1,2} class, dimensions above one, the spectral action —
    all exactly as disclaimed upstream.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import PoincareBeyondPolynomials

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareScaledBeyond

open HermiteCompleteness PoincareBeyondPolynomials

/-! ## 1. The change of variables -/

/-- For σ ≠ 0, integration against the variance-σ² Gaussian is integration
    of the rescaled function against the standard one. -/
theorem integral_scaled (σ : ℝ) (h : ℝ → ℝ) (hmeas : Measurable h) :
    ∫ x, h x ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))
      = ∫ x, h (σ * x) ∂gauss := by
  have hmap : (gauss : Measure ℝ).map (fun x => σ * x)
      = gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) := by
    rw [show (gauss : Measure ℝ) = gaussianReal 0 1 from rfl,
      gaussianReal_map_const_mul σ]
    congr 1
    · ring
    · ext
      simp
  rw [← hmap, integral_map (by fun_prop) hmeas.aestronglyMeasurable]

/-! ## 2. The scaled inequality for the class -/

/-- **The Gaussian Poincaré inequality at variance σ², beyond polynomials**:
    for σ ≠ 0 and C¹ f with f, f′ of polynomial growth,
    Var(f) ≤ σ²·E[(f′)²] against `gaussianReal 0 σ²`. -/
theorem poincare_scaled_beyond (σ : ℝ) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)))
        - (∫ x, f x ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))) ^ 2
      ≤ σ ^ 2 * ∫ x, f' x ^ 2 ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)) := by
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hfcont : Continuous f := hdiff.continuous
  have hf'meas : Measurable f' := by
    have hfd : f' = deriv f := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact measurable_deriv f
  -- the substituted function and its data
  set g : ℝ → ℝ := fun x => f (σ * x) with hg
  set g' : ℝ → ℝ := fun x => σ * f' (σ * x) with hg'
  have hgderiv : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => σ * y) σ x := by
      simpa using (hasDerivAt_id x).const_mul σ
    have h2 := (hderiv (σ * x)).comp x h1
    simpa [hg, hg', mul_comm] using h2
  -- growth transfers with constant C·max(1,σ²)^m
  set D : ℝ := C * (max 1 (σ ^ 2)) ^ m with hD
  have hgrow : ∀ x : ℝ, (1 + (σ * x) ^ 2) ^ m
      ≤ (max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m := by
    intro x
    rw [← mul_pow]
    have h1 : σ ^ 2 ≤ max 1 (σ ^ 2) := le_max_right _ _
    have h2 : (1 : ℝ) ≤ max 1 (σ ^ 2) := le_max_left _ _
    have hbase : 1 + (σ * x) ^ 2 ≤ max 1 (σ ^ 2) * (1 + x ^ 2) := by
      nlinarith [sq_nonneg x, sq_nonneg σ]
    exact pow_le_pow_left₀ (by positivity) hbase m
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hb 0)
  have hgb : ∀ x, |g x| ≤ D * (1 + x ^ 2) ^ m := by
    intro x
    calc |g x| ≤ C * (1 + (σ * x) ^ 2) ^ m := hb (σ * x)
      _ ≤ C * ((max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left (hgrow x) hC0
      _ = D * (1 + x ^ 2) ^ m := by rw [hD]; ring
  have hgb' : ∀ x, |g' x| ≤ (|σ| * D) * (1 + x ^ 2) ^ m := by
    intro x
    rw [hg']
    calc |σ * f' (σ * x)| = |σ| * |f' (σ * x)| := abs_mul _ _
      _ ≤ |σ| * (C * (1 + (σ * x) ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left (hb' (σ * x)) (abs_nonneg σ)
      _ ≤ |σ| * (C * ((max 1 (σ ^ 2)) ^ m * (1 + x ^ 2) ^ m)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg σ)
          exact mul_le_mul_of_nonneg_left (hgrow x) hC0
      _ = (|σ| * D) * (1 + x ^ 2) ^ m := by rw [hD]; ring
  -- a single constant dominating both
  set E : ℝ := max D (|σ| * D) with hE
  have hgbE : ∀ x, |g x| ≤ E * (1 + x ^ 2) ^ m := by
    intro x
    refine le_trans (hgb x) (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity))
  have hgbE' : ∀ x, |g' x| ≤ E * (1 + x ^ 2) ^ m := by
    intro x
    refine le_trans (hgb' x) (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity))
  -- the variance-one theorem for g
  have hpoincare := poincare_beyond_polynomials hgderiv hgbE hgbE'
  -- transfer every integral
  have hI1 : ∫ x, f x ^ 2 ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))
      = ∫ x, g x ^ 2 ∂gauss := by
    rw [integral_scaled σ (fun x => f x ^ 2) (by fun_prop)]
  have hI2 : ∫ x, f x ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))
      = ∫ x, g x ∂gauss := by
    rw [integral_scaled σ f (by fun_prop)]
  have hI3 : ∫ x, f' x ^ 2 ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))
      = ∫ x, f' (σ * x) ^ 2 ∂gauss := by
    rw [integral_scaled σ (fun x => f' x ^ 2) (by fun_prop)]
  have hI4 : ∫ x, g' x ^ 2 ∂gauss
      = σ ^ 2 * ∫ x, f' (σ * x) ^ 2 ∂gauss := by
    rw [show (fun x => g' x ^ 2) = fun x => σ ^ 2 * f' (σ * x) ^ 2 by
      funext x; rw [hg']; ring]
    exact integral_const_mul _ _
  rw [hI1, hI2, hI3]
  calc (∫ x, g x ^ 2 ∂gauss) - (∫ x, g x ∂gauss) ^ 2
      ≤ ∫ x, g' x ^ 2 ∂gauss := hpoincare
    _ = σ ^ 2 * ∫ x, f' (σ * x) ^ 2 ∂gauss := hI4

/-! ## 3. The cutoff form -/

/-- **The Λ²/2 inequality beyond polynomials**: at the cutoff-scale variance
    Λ²/2, for C¹ test functions of polynomial growth,
    Var(f) ≤ (Λ²/2)·E[(f′)²]. The estate's quoted Bakry-Émery gap 2/Λ² now
    constrains non-polynomial observables. Still NOT the spectral action:
    the measure is assumed Gaussian, exactly as everywhere upstream. -/
theorem poincare_lambda_beyond (Λ : ℝ) {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩))
        - (∫ x, f x ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩)) ^ 2
      ≤ (Λ ^ 2 / 2) * ∫ x, f' x ^ 2 ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩) := by
  have hs2 : Real.sqrt (Λ ^ 2 / 2) ^ 2 = Λ ^ 2 / 2 :=
    Real.sq_sqrt (by positivity)
  have h := poincare_scaled_beyond (Real.sqrt (Λ ^ 2 / 2)) hderiv hb hb'
  have hmeas : (⟨Real.sqrt (Λ ^ 2 / 2) ^ 2,
      sq_nonneg (Real.sqrt (Λ ^ 2 / 2))⟩ : NNReal)
      = (⟨Λ ^ 2 / 2, by positivity⟩ : NNReal) := by
    ext
    simpa using hs2
  rw [hmeas, hs2] at h
  exact h

/-- Non-vacuity at the cutoff scale: sin against the Λ-Gaussian. -/
theorem poincare_lambda_sin (Λ : ℝ) :
    (∫ x, Real.sin x ^ 2 ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩))
        - (∫ x, Real.sin x ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩)) ^ 2
      ≤ (Λ ^ 2 / 2)
          * ∫ x, Real.cos x ^ 2 ∂(gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩) := by
  refine poincare_lambda_beyond Λ (f := Real.sin) (f' := Real.cos)
    (C := 1) (m := 0) (fun x => Real.hasDerivAt_sin x) ?_ ?_
  · intro x
    simpa using Real.abs_sin_le_one x
  · intro x
    simpa using Real.abs_cos_le_one x

end PoincareScaledBeyond
