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
  3. `poincare_lambda` — the same inequality at **σ² = Λ²/2**, so the
     Poincaré constant is Λ²/2. `poincare_in_gap_form` restates it with the
     reciprocal written out; its entire content over `poincare_lambda` is the
     rewrite `(2/Λ²)⁻¹ = Λ²/2`, and it is kept only because that is the shape
     the estate quotes.
  4. `no_better_constant_scaled`, `lambda_constant_least` — **the constant is
     SHARP**: σ² (resp. Λ²/2) is the LEAST constant for which the inequality
     holds, because p = X attains it (`sigma_sq_attained`). This is what
     licenses saying "the gap IS 2/Λ²" rather than "at most". Without it,
     `poincare_in_gap_form` alone is equally true of 1/Λ², 1/(2Λ²) and 0 —
     an upper bound on the constant says nothing about which one it is.
  5. `poincare_MV_scaled`, `poincare_R16_lambda` (§4) — the same constant in
     n dimensions, and at n = 16; `no_better_constant_R16_lambda` — sharp
     there too. **Caveat, and it is not small: `ENs` is an iterated moment
     functional, not an integral.** `gaussScaled_eq_integral` ties the
     one-dimensional object to `gaussianReal`; nothing here ties the
     16-dimensional one to `Measure.pi`. See "WHAT THIS DOES NOT DO".

  WHAT THIS DOES NOT DO, and it is the whole point of saying it:

  * **This is a Gaussian measure, not the spectral action.** The
    Chamseddine–Connes spectral action is Tr f(D/Λ); nothing here computes
    it, and no theorem in this file mentions D, f, or a Dirac operator. What
    is proven is that IF the fluctuation measure is Gaussian with variance
    Λ²/2, THEN the Poincaré constant is Λ²/2 and the gap is 2/Λ². The
    estate's claim that the spectral action *yields* such a measure is
    exactly as unproven as it was before this file.
  * Polynomial test functions only.
  * **In n > 1 dimensions there is no measure here.** §4 scales
    `GaussianPoincareProduct.poincare_MV`, whose expectation `EN n` is an
    iterated moment functional; `EN_one_eq_integral` certifies n = 1 against
    `gaussianReal 0 1` and nothing certifies n > 1 against a product measure
    (that needs Fubini for `Measure.pi`, recorded on UNLOCK_WATCHLIST). So
    the sentence "for a Gaussian fluctuation measure of variance Λ²/2" is
    justified at n = 1 and is NOT justified at n = 16 — which is the
    dimension the cascade needs. Read §4 as an inequality about moments.
  * Therefore **no published Bakry-Émery tag moves on this file either.**
    What changes is that the claim is now falsifiable: the object exists, the
    constant is derived rather than defined, and what remains is one specific
    question — whether the spectral action produces this measure.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincare
import GaussianPoincareProduct

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

/-! ## 3. At the cutoff scale: the constant is Λ²/2, and (§5) it is sharp -/

/-- **The Poincaré inequality at variance Λ²/2**: the constant is Λ²/2. -/
theorem poincare_lambda (Λ : ℝ) (p : ℝ[X]) :
    gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (p * p)
        - (gaussScaled (Real.sqrt (Λ ^ 2 / 2)) p) ^ 2
      ≤ (Λ ^ 2 / 2)
        * gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (derivative p * derivative p) := by
  have h := poincare_scaled (Real.sqrt (Λ ^ 2 / 2)) p
  rwa [Real.sq_sqrt (by positivity)] at h

/-- **The gap 2/Λ², inside a real inequality.** In the Bakry-Émery
    normalisation the spectral gap is the reciprocal of the Poincaré
    constant, so this states the inequality with the gap written explicitly:

      Var(p) ≤ (2/Λ²)⁻¹ · E[(p′)²].

    Its entire content over `poincare_lambda` is the rewrite
    `(2/Λ²)⁻¹ = Λ²/2` — one application of `inv_div`, and the two statements
    are interderivable by it. It is kept because that is the shape the estate
    quotes, not because it adds mathematics. What makes "the gap IS 2/Λ²" a
    supported claim rather than an upper bound is `lambda_constant_least`
    below; an inequality with constant Λ²/2 is, on its own, equally true with
    any larger constant.

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

/-! ## 4. The same constant in n dimensions — the cascade case -/

/-- The substitution xᵢ ↦ σ·xᵢ in n variables. -/
def scaleSub (σ : ℝ) (n : ℕ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C σ * MvPolynomial.X i)

theorem scaleSub_X (σ : ℝ) (n : ℕ) (j : Fin n) :
    scaleSub σ n (MvPolynomial.X j) = MvPolynomial.C σ * MvPolynomial.X j := by
  simp [scaleSub]

/-- **The chain rule for the rescaling**: each partial derivative picks up
    exactly one factor of σ. This is where the σ² constant comes from in n
    dimensions, exactly as it did in one. -/
theorem pderiv_scaleSub (σ : ℝ) (n : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i (scaleSub σ n p)
      = MvPolynomial.C σ * scaleSub σ n (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [scaleSub]
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p j hp =>
      rw [map_mul, scaleSub_X, MvPolynomial.pderiv_mul, hp,
        MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul, map_add, map_mul,
        map_mul, scaleSub_X]
      by_cases hij : j = i
      · subst hij
        rw [MvPolynomial.pderiv_X_self, map_one, mul_one]
        ring
      · rw [MvPolynomial.pderiv_X_of_ne hij, map_zero]
        ring

/-- The n-fold Gaussian expectation at variance σ². -/
def ENs (σ : ℝ) (n : ℕ) (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  GaussianPoincareProduct.EN n (scaleSub σ n p)

/-- **THE n-DIMENSIONAL POINCARÉ INEQUALITY AT VARIANCE σ²**:
    Var(p) ≤ σ²·Σᵢ E[(∂ᵢp)²]. -/
theorem poincare_MV_scaled (σ : ℝ) (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    ENs σ n (p * p) - (ENs σ n p) ^ 2
      ≤ σ ^ 2 * ∑ i : Fin n,
          ENs σ n (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p) := by
  have h := GaussianPoincareProduct.poincare_MV n (scaleSub σ n p)
  have hterm : ∀ i : Fin n,
      GaussianPoincareProduct.EN n (MvPolynomial.pderiv i (scaleSub σ n p)
        * MvPolynomial.pderiv i (scaleSub σ n p))
      = σ ^ 2 * ENs σ n (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p) := by
    intro i
    rw [pderiv_scaleSub]
    have hsq : (MvPolynomial.C σ * scaleSub σ n (MvPolynomial.pderiv i p))
        * (MvPolynomial.C σ * scaleSub σ n (MvPolynomial.pderiv i p))
        = (σ ^ 2) •
            (scaleSub σ n (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)) := by
      rw [map_mul, MvPolynomial.smul_eq_C_mul, map_pow]
      ring
    rw [hsq, GaussianPoincareProduct.EN_smul, ENs]
  simp only [hterm] at h
  rw [← Finset.mul_sum] at h
  unfold ENs
  rw [map_mul]
  exact h

/-- **The cascade case with the cutoff constant**: on ℝ¹⁶ ≅ Herm₄(ℂ),
    Var(p) ≤ (Λ²/2)·Σᵢ E[(∂ᵢp)²], with the constant sharp
    (`no_better_constant_R16_lambda`).

    TWO caveats, both load-bearing. (a) `ENs σ 16` is the SCALED ITERATED
    MOMENT FUNCTIONAL of `GaussianPoincareProduct`, not an integral: no
    theorem here or there identifies it with `Measure.pi`, so this is not
    yet a statement about a 16-dimensional measure, and the words "Gaussian
    fluctuation measure" do not belong to it. (b) Even at n = 1, where the
    object IS a measure, nothing connects it to the spectral action. -/
theorem poincare_R16_lambda (Λ : ℝ) (p : MvPolynomial (Fin 16) ℝ) :
    ENs (Real.sqrt (Λ ^ 2 / 2)) 16 (p * p)
        - (ENs (Real.sqrt (Λ ^ 2 / 2)) 16 p) ^ 2
      ≤ (Λ ^ 2 / 2) * ∑ i : Fin 16,
          ENs (Real.sqrt (Λ ^ 2 / 2)) 16
            (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p) := by
  have h := poincare_MV_scaled (Real.sqrt (Λ ^ 2 / 2)) 16 p
  rwa [Real.sq_sqrt (by positivity)] at h

/-- The constant is positive for Λ ≠ 0. This is NOT non-vacuity of the
    inequality — `Var ≤ 10¹⁰⁰ · E[(p′)²]` also has a positive constant. Real
    non-vacuity is attainment, and that is `sigma_sq_attained` below. -/
theorem lambda_constant_pos (Λ : ℝ) (hΛ : Λ ≠ 0) : 0 < Λ ^ 2 / 2 := by
  have : 0 < Λ ^ 2 := by positivity
  linarith

/-- The rescaled expectation of a constant. -/
theorem ENs_one (σ : ℝ) (n : ℕ) : ENs σ n (1 : MvPolynomial (Fin n) ℝ) = 1 := by
  rw [ENs, map_one, GaussianPoincareProduct.EN_one]

theorem ENs_zero (σ : ℝ) (n : ℕ) : ENs σ n (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  rw [ENs, map_zero, GaussianPoincareProduct.EN_zero_poly]

/-- The first coordinate still has mean zero after rescaling. -/
theorem ENs_X_zero (σ : ℝ) (n : ℕ) :
    ENs σ (n + 1) (MvPolynomial.X 0) = 0 := by
  rw [ENs, scaleSub_X, ← MvPolynomial.smul_eq_C_mul,
    GaussianPoincareProduct.EN_smul, GaussianPoincareProduct.EN_X_zero, mul_zero]

/-- **The first coordinate has variance σ² after rescaling** — this is what
    makes σ² attained, hence least. -/
theorem ENs_X_zero_sq (σ : ℝ) (n : ℕ) :
    ENs σ (n + 1) (MvPolynomial.X 0 * MvPolynomial.X 0) = σ ^ 2 := by
  rw [ENs, map_mul, scaleSub_X]
  rw [show (MvPolynomial.C σ * MvPolynomial.X (0 : Fin (n + 1)))
      * (MvPolynomial.C σ * MvPolynomial.X 0)
      = (σ ^ 2) • ((MvPolynomial.X (0 : Fin (n + 1))) * MvPolynomial.X 0) by
    rw [MvPolynomial.smul_eq_C_mul, map_pow]; ring]
  rw [GaussianPoincareProduct.EN_smul, GaussianPoincareProduct.EN_X_zero_sq, mul_one]

/-! ## 5. Sharpness: Λ²/2 is the LEAST constant, not merely a valid one

    An inequality `Var ≤ c·E[(p′)²]` is true for every c larger than the
    optimal one, so exhibiting it with c = Λ²/2 does not say the gap is 2/Λ².
    What says that is that no smaller c works. Here it is. -/

theorem gaussScaled_X (σ : ℝ) : gaussScaled σ (X : ℝ[X]) = 0 := by
  rw [gaussScaled, scaleX, X_comp, ← smul_eq_C_mul, gmean_smul,
    GaussianPoincare.gmean_X_eq_zero, mul_zero]

theorem gaussScaled_X_sq (σ : ℝ) :
    gaussScaled σ ((X : ℝ[X]) * X) = σ ^ 2 := by
  have hmean : gmean ((X : ℝ[X]) * X) = 1 := by
    have h := GaussianPoincare.gvar_X_eq_one
    unfold GaussianPoincare.gvar at h
    rw [GaussianPoincare.gmean_X_eq_zero] at h
    simpa using h
  rw [gaussScaled, mul_comp, scaleX, X_comp]
  rw [show (C σ * X : ℝ[X]) * (C σ * X) = (σ * σ) • ((X : ℝ[X]) * X) by
    rw [smul_eq_C_mul, C_mul]; ring]
  rw [gmean_smul, hmean, mul_one, sq]

theorem gaussScaled_derivative_X (σ : ℝ) :
    gaussScaled σ (derivative (X : ℝ[X]) * derivative X) = 1 := by
  rw [derivative_X, one_mul, gaussScaled, one_comp, GaussianPoincare.gmean_one]

/-- **The constant σ² is ATTAINED**, at p = X: the inequality of
    `poincare_scaled` is an equality there. -/
theorem sigma_sq_attained (σ : ℝ) :
    gaussScaled σ ((X : ℝ[X]) * X) - (gaussScaled σ X) ^ 2
      = σ ^ 2 * gaussScaled σ (derivative (X : ℝ[X]) * derivative X) := by
  rw [gaussScaled_X, gaussScaled_X_sq, gaussScaled_derivative_X]
  ring

/-- **No constant smaller than σ² works.** -/
theorem no_better_constant_scaled (σ c : ℝ)
    (h : ∀ p : ℝ[X], gaussScaled σ (p * p) - (gaussScaled σ p) ^ 2
      ≤ c * gaussScaled σ (derivative p * derivative p)) :
    σ ^ 2 ≤ c := by
  have hX := h X
  rw [gaussScaled_X, gaussScaled_X_sq, gaussScaled_derivative_X, mul_one] at hX
  linarith

/-- **THE GAP IS 2/Λ², AND NOT MERELY AT MOST 2/Λ².** Λ²/2 is the least
    constant for which the Poincaré inequality holds at variance Λ²/2, so its
    reciprocal 2/Λ² is the largest valid spectral gap — which is what the
    Bakry-Émery normalisation means by "the gap". This is the theorem that
    the estate's quoted number needed and did not have. -/
theorem lambda_constant_least (Λ c : ℝ)
    (h : ∀ p : ℝ[X],
      gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (p * p)
          - (gaussScaled (Real.sqrt (Λ ^ 2 / 2)) p) ^ 2
        ≤ c * gaussScaled (Real.sqrt (Λ ^ 2 / 2)) (derivative p * derivative p)) :
    Λ ^ 2 / 2 ≤ c := by
  have h2 := no_better_constant_scaled (Real.sqrt (Λ ^ 2 / 2)) c h
  rwa [Real.sq_sqrt (by positivity)] at h2

/-- Sharpness in the cascade dimension too: Λ²/2 is the least constant for
    which the 16-dimensional inequality holds. -/
theorem no_better_constant_R16_lambda (Λ c : ℝ)
    (h : ∀ p : MvPolynomial (Fin 16) ℝ,
      ENs (Real.sqrt (Λ ^ 2 / 2)) 16 (p * p)
          - (ENs (Real.sqrt (Λ ^ 2 / 2)) 16 p) ^ 2
        ≤ c * ∑ i : Fin 16,
            ENs (Real.sqrt (Λ ^ 2 / 2)) 16
              (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)) :
    Λ ^ 2 / 2 ≤ c := by
  have hs : (Real.sqrt (Λ ^ 2 / 2)) ^ 2 = Λ ^ 2 / 2 := Real.sq_sqrt (by positivity)
  have hX := h (MvPolynomial.X 0)
  rw [ENs_X_zero, ENs_X_zero_sq] at hX
  have hsum : ∑ i : Fin 16,
      ENs (Real.sqrt (Λ ^ 2 / 2)) 16
        (MvPolynomial.pderiv i (MvPolynomial.X (0 : Fin 16))
          * MvPolynomial.pderiv i (MvPolynomial.X 0)) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin 16)]
    · rw [MvPolynomial.pderiv_X_self, one_mul, ENs_one]
    · intro b _ hb
      rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hb), zero_mul, ENs_zero]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  rw [hsum, mul_one, hs] at hX
  linarith

end SpectralGaussianGap
