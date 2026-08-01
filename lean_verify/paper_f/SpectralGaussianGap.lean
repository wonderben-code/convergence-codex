/-
  SpectralGaussianGap: A Poincaré Constant of Λ²/2, for a Real Measure
  ====================================================================

  Campaign-3 unit 3, and a CAESAR target: the estate's whole Bakry-Émery
  family is blocked behind an object — a measure with a Λ in it — that has
  never existed in Lean. `BakryEmeryGap.lean` DEFINES `spectral_gap := 2·a`
  and `covariance := 1/(2a)`; no measure, integral, variance or test function
  appears there (Phase 0 audit, re-confirmed twice).

  This file supplies the missing object in the one case where it can be
  supplied honestly, and connects it to the number the estate quotes.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `gaussScaled` — the expectation against the centred Gaussian of variance
     σ², defined by composing with x ↦ σ·x, and `gaussScaled_eq_integral`,
     which proves it IS the integral against Mathlib's
     `gaussianReal 0 ⟨σ², _⟩` (via Mathlib's own pushforward lemma). So the
     object is Mathlib's Gaussian, not a convention of ours.
  2. `poincare_scaled` — **the Poincaré inequality with the σ² constant**:

         Var_{N(0,σ²)}(p) ≤ σ² · E_{N(0,σ²)}[(p′)²]

     for polynomial test functions, obtained from the unit-variance theorem
     by the scaling x ↦ σx (the derivative picks up exactly one factor of σ,
     which is where the constant comes from).
  3. `poincare_lambda`, `poincare_in_gap_form` — the same inequality at
     **σ² = Λ²/2**, where the constant is Λ²/2 and its reciprocal — the
     spectral gap in the Bakry-Émery normalisation — is exactly **2/Λ²**.
     That is the number the estate has been quoting, and here it appears
     INSIDE a functional inequality about a real measure. There is
     deliberately no standalone theorem `(Λ²/2)⁻¹ = 2/Λ²`: a bare numeral
     identity in physical costume is the pattern this project removes.

  WHAT THIS DOES NOT DO, and it is the whole point of saying it:

  * **This is a Gaussian measure, not the spectral action.** The
    Chamseddine–Connes spectral action is Tr f(D/Λ); nothing here computes
    it, and no theorem in this file mentions D, f, or a Dirac operator. What
    is proven is that IF the fluctuation measure is Gaussian with variance
    Λ²/2, THEN the Poincaré constant is Λ²/2 and the gap is 2/Λ². The
    estate's claim that the spectral action *yields* such a measure is
    exactly as unproven as it was before this file.
  * Polynomial test functions only, in one dimension. The n-dimensional
    unit-variance case is `GaussianPoincareProduct.poincare_MV`; scaling it
    is mechanical and is recorded as the next stair.
  * Therefore **no published Bakry-Émery tag moves on this file either.**
    What changes is that the claim is now falsifiable: the object exists, the
    constant is derived rather than defined, and what remains is one specific
    question — whether the spectral action produces this measure.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincare

open Polynomial MeasureTheory ProbabilityTheory

noncomputable section

namespace SpectralGaussianGap

open GaussianPoincare

/-! ## 1. The scaled Gaussian expectation -/

/-- The rescaling polynomial x ↦ σ·x. -/
def scaleX (σ : ℝ) : ℝ[X] := C σ * X

@[simp] theorem eval_scaleX (σ x : ℝ) : (scaleX σ).eval x = σ * x := by
  simp [scaleX]

/-- The expectation against the centred Gaussian of variance σ², defined by
    composing the test polynomial with x ↦ σ·x. -/
def gaussScaled (σ : ℝ) (p : ℝ[X]) : ℝ := gmean (p.comp (scaleX σ))

/-- **It is Mathlib's Gaussian.** The scaled expectation is the integral
    against `gaussianReal 0 σ²`, by Mathlib's own pushforward lemma for
    scalar multiples of a Gaussian. -/
theorem gaussScaled_eq_integral (σ : ℝ) (p : ℝ[X]) :
    gaussScaled σ p
      = ∫ x : ℝ, p.eval x ∂(gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => σ * x)
      = gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) := by
    rw [gaussianReal_map_const_mul σ]
    congr 1
    · simp
    · ext
      simp [sq]
  rw [gaussScaled, gmean_eq_integral, ← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [Polynomial.eval_comp]

/-! ## 2. The inequality with the σ² constant -/

/-- **The Poincaré inequality for the Gaussian of variance σ²**:
    Var(p) ≤ σ²·E[(p′)²]. The constant is exactly the variance, and it comes
    from the single factor of σ that the derivative picks up under the
    rescaling. -/
theorem poincare_scaled (σ : ℝ) (p : ℝ[X]) :
    gaussScaled σ (p * p) - (gaussScaled σ p) ^ 2
      ≤ σ ^ 2 * gaussScaled σ (derivative p * derivative p) := by
  have hcomp := poincare_polynomial (p.comp (scaleX σ))
  unfold gvar at hcomp
  have hd : derivative (p.comp (scaleX σ))
      = C σ * (derivative p).comp (scaleX σ) := by
    rw [Polynomial.derivative_comp, scaleX]
    simp
  rw [hd] at hcomp
  have hsq : (C σ * (derivative p).comp (scaleX σ))
      * (C σ * (derivative p).comp (scaleX σ))
      = (σ ^ 2) • ((derivative p * derivative p).comp (scaleX σ)) := by
    rw [Polynomial.mul_comp, smul_eq_C_mul]
    push_cast [C_mul, C_pow]
    ring
  rw [hsq, gmean_smul] at hcomp
  unfold gaussScaled
  rw [Polynomial.mul_comp]
  exact hcomp

/-! ## 3. At the cutoff scale: the constant is Λ²/2 and the gap is 2/Λ² -/

/-- **The Poincaré inequality at variance Λ²/2**: the constant is Λ²/2. -/
theorem poincare_lambda (Λ : ℝ) (p : ℝ[X]) :
    gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (p * p)
        - (gaussScaled (Real.sqrt (Λ ^ 2 / 2)) p) ^ 2
      ≤ (Λ ^ 2 / 2)
        * gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (derivative p * derivative p) := by
  have h := poincare_scaled (Real.sqrt (Λ ^ 2 / 2)) p
  rwa [Real.sq_sqrt (by positivity)] at h

/-- **THE GAP IS 2/Λ², INSIDE A REAL INEQUALITY.** In the Bakry-Émery
    normalisation the spectral gap is the reciprocal of the Poincaré
    constant, so this states the inequality with the gap written explicitly:

      Var(p) ≤ (2/Λ²)⁻¹ · E[(p′)²].

    It is deliberately phrased this way rather than as a standalone identity
    `(Λ²/2)⁻¹ = 2/Λ²`, because a bare numeral identity dressed in physical
    vocabulary is precisely the pattern this project exists to remove — the
    estate contains dozens of them. Here 2/Λ² occurs inside a functional
    inequality about an actual measure, or not at all.

    The modelling step — that the spectral action produces a Gaussian
    fluctuation measure of variance Λ²/2 — is NOT proven anywhere in the
    estate and is not proven here. -/
theorem poincare_in_gap_form (Λ : ℝ) (p : ℝ[X]) :
    gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (p * p)
        - (gaussScaled (Real.sqrt (Λ ^ 2 / 2)) p) ^ 2
      ≤ (2 / Λ ^ 2)⁻¹
        * gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (derivative p * derivative p) := by
  have h := poincare_lambda Λ p
  rwa [show ((2 : ℝ) / Λ ^ 2)⁻¹ = Λ ^ 2 / 2 from by rw [inv_div]]

/-- Non-vacuity: the constant is positive, so the inequality has content. -/
theorem lambda_constant_pos (Λ : ℝ) (hΛ : Λ ≠ 0) : 0 < Λ ^ 2 / 2 := by
  have : 0 < Λ ^ 2 := by positivity
  linarith

end SpectralGaussianGap
