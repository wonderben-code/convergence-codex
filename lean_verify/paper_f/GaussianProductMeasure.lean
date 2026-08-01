/-
  GaussianProductMeasure: the n-Dimensional Expectation IS an Integral
  ===================================================================

  Closes the finding that an adversarial review raised against
  `SpectralGaussianGap.lean` and `GaussianPoincareProduct.lean`, and that is
  recorded as ERRATA 27: in n > 1 dimensions those files' expectation `EN n`
  is an ITERATED MOMENT FUNCTIONAL, built by peeling one variable at a time,
  and nothing identified it with an integral against a measure. The
  16-dimensional Poincaré inequality — the one the cascade needs — was
  therefore not a statement about a Gaussian measure at all, however much its
  docstrings said "measure".

  This file supplies the identification.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `integrable_eval` — every polynomial is integrable against the n-fold
     standard Gaussian product measure `Measure.pi (fun _ => gaussianReal 0 1)`.
     Via `MvPolynomial.eval_eq'` (a polynomial is a finite sum of monomials)
     and Mathlib's `Integrable.fintype_prod` together with
     `GaussianPoincare.memLp_pow_gaussianReal`.
  2. **`EN_eq_integral` — `EN n p = ∫ x, eval x p ∂(Measure.pi γ)`**, for every
     n and every polynomial. The peeling construction and the product measure
     agree. Proved by induction on n: the base case is `Measure.pi_of_empty`,
     and the step is Fubini (`integral_prod_symm`) transported along Mathlib's
     `measurePreserving_piFinSuccAbove`, which is exactly the "peel one
     variable" operation at the level of measures.
  3. `poincare_MV_measure`, `poincare_R16_measure` — hence the n-dimensional
     and 16-dimensional Poincaré inequalities **as statements about a
     measure**:

         ∫ p² dγₙ − (∫ p dγₙ)² ≤ Σᵢ ∫ (∂ᵢp)² dγₙ

     with γₙ = `Measure.pi (fun _ => gaussianReal 0 1)`. Every expectation in
     sight is now an integral against a single Mathlib measure on ℝⁿ.
  4. `no_better_constant_measure` — the constant 1 is sharp in this form too,
     so the statement is not the vacuous one that some constant works.
  5. `measurePreserving_scale`, `ENs_eq_integral` — the same for the SCALED
     functional: xᵢ ↦ σxᵢ is measure preserving from the unit-variance product
     Gaussian to the variance-σ² one (Mathlib's `measurePreserving_pi` plus
     `gaussianReal_map_const_mul`), so `SpectralGaussianGap.ENs σ n` is the
     integral against `Measure.pi (fun _ => gaussianReal 0 σ²)`.
  6. **`poincare_R16_lambda_measure`** — hence the flagship statement, about a
     measure:

         ∫ p² dγ₁₆^{Λ²/2} − (∫ p dγ₁₆^{Λ²/2})² ≤ (Λ²/2) · Σᵢ ∫ (∂ᵢp)² dγ₁₆^{Λ²/2}

     on ℝ¹⁶ ≅ Herm₄(ℂ), against the honest 16-dimensional Gaussian of variance
     Λ²/2. With `SpectralGaussianGap.no_better_constant_R16_lambda` (the
     constant is least), that is the estate's Bakry-Émery gap 2/Λ² as a
     theorem about a measure rather than a definition.

  NOT proven here:

  * **Test functions beyond polynomials.** The inequality is proven for
    polynomials; extending to W^{1,2}(γₙ) needs a density argument.
  * **Any link to the spectral action.** Nothing here produces a Gaussian
    fluctuation measure from Tr f(D/Λ). Unchanged, and unproven.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincareProduct
import SpectralGaussianGap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory GaussianPoincareProduct

noncomputable section

namespace GaussianProductMeasure

/-- The n-fold standard Gaussian measure on ℝⁿ. -/
def gaussPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (gaussPi n) := by
  rw [gaussPi]
  infer_instance

/-! ## 1. Polynomials are integrable against the product Gaussian -/

theorem integrable_pow (v : NNReal) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) :=
  (GaussianPoincare.memLp_pow_gaussianReal k 0 v).integrable (by norm_num)

/-- A monomial is integrable: Mathlib's `Integrable.fintype_prod` plus the
    fact that the Gaussian has all moments. -/
theorem integrable_monomial (v : NNReal) (n : ℕ) (d : Fin n →₀ ℕ) :
    Integrable (fun x : Fin n → ℝ => ∏ i, x i ^ d i)
      (Measure.pi (fun _ => gaussianReal 0 v)) :=
  Integrable.fintype_prod (fun i => integrable_pow v (d i))

/-- **Every polynomial is integrable against the n-fold Gaussian**, at any
    variance. -/
theorem integrable_eval_of (v : NNReal) (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : Fin n → ℝ => MvPolynomial.eval x p)
      (Measure.pi (fun _ => gaussianReal 0 v)) := by
  have hrw : (fun x : Fin n → ℝ => MvPolynomial.eval x p)
      = fun x : Fin n → ℝ =>
          ∑ d ∈ p.support, MvPolynomial.coeff d p * ∏ i, x i ^ d i := by
    funext x
    rw [MvPolynomial.eval_eq']
  rw [hrw]
  exact integrable_finset_sum _ fun d _ => (integrable_monomial v n d).const_mul _

theorem integrable_eval (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : Fin n → ℝ => MvPolynomial.eval x p) (gaussPi n) := by
  rw [gaussPi]
  exact integrable_eval_of 1 n p

/-! ## 2. The peeling construction and the product measure agree -/

/-- The measure-level version of peeling the first variable. -/
theorem measurePreserving_peel (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (gaussPi (n + 1)) ((gaussianReal 0 1).prod (gaussPi n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0

theorem peel_apply (n : ℕ) (z : Fin (n + 1) → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) z
      = (z 0, Fin.tail z) := rfl

/-- **THE IDENTIFICATION**: the n-fold iterated moment functional of
    `GaussianPoincareProduct` is the integral against the n-fold Gaussian
    product measure. Everything downstream that said "expectation" now means
    an integral. -/
theorem EN_eq_integral : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
    EN n p = ∫ x, MvPolynomial.eval x p ∂(gaussPi n) := by
  intro n
  induction n with
  | zero =>
      intro p
      rw [EN_zero, gaussPi, Measure.pi_of_empty (fun _ => gaussianReal 0 1)
        (fun i => Fin.elim0 i), integral_dirac]
  | succ n ih =>
      intro p
      rw [EN_succ, ih]
      have hin : ∀ w : Fin n → ℝ,
          MvPolynomial.eval w (EyM n (MvPolynomial.finSuccEquiv ℝ n p))
            = ∫ x : ℝ, MvPolynomial.eval (Fin.cons x w) p ∂(gaussianReal 0 1) := by
        intro w
        rw [eval_EyM, GaussianPoincare.gmean_eq_integral]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [MvPolynomial.eval_eq_eval_mv_eval' w x p]
      simp_rw [hin]
      have hGint : Integrable (fun y : ℝ × (Fin n → ℝ) =>
          MvPolynomial.eval (Fin.cons y.1 y.2) p) ((gaussianReal 0 1).prod (gaussPi n)) := by
        rw [← (measurePreserving_peel n).integrable_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        have hcomp : ((fun y : ℝ × (Fin n → ℝ) => MvPolynomial.eval (Fin.cons y.1 y.2) p)
            ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
            = fun z : Fin (n + 1) → ℝ => MvPolynomial.eval z p := by
          funext z
          simp only [Function.comp_apply, peel_apply, Fin.cons_self_tail]
        rw [hcomp]
        exact integrable_eval (n + 1) p
      have hprod := integral_prod_symm
        (fun y : ℝ × (Fin n → ℝ) => MvPolynomial.eval (Fin.cons y.1 y.2) p) hGint
      rw [← hprod]
      rw [← (measurePreserving_peel n).integral_comp
        (MeasurableEquiv.measurableEmbedding _)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [peel_apply, Fin.cons_self_tail]

/-! ## 3. The Poincaré inequality as a statement about a measure -/

/-- **THE n-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY, ABOUT A MEASURE**:

      ∫ p² dγₙ − (∫ p dγₙ)² ≤ Σᵢ ∫ (∂ᵢp)² dγₙ,

    with γₙ = `Measure.pi (fun _ => gaussianReal 0 1)` — one Mathlib measure
    on ℝⁿ, not an iterated functional. -/
theorem poincare_MV_measure (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∫ x, MvPolynomial.eval x (p * p) ∂(gaussPi n))
        - (∫ x, MvPolynomial.eval x p ∂(gaussPi n)) ^ 2
      ≤ ∑ i : Fin n, ∫ x,
          MvPolynomial.eval x (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
            ∂(gaussPi n) := by
  have h := poincare_MV n p
  rw [EN_eq_integral, EN_eq_integral] at h
  simp_rw [EN_eq_integral] at h
  exact h

/-- **The cascade case, about a measure**: on ℝ¹⁶ ≅ Herm₄(ℂ). -/
theorem poincare_R16_measure (p : MvPolynomial (Fin 16) ℝ) :
    (∫ x, MvPolynomial.eval x (p * p) ∂(gaussPi 16))
        - (∫ x, MvPolynomial.eval x p ∂(gaussPi 16)) ^ 2
      ≤ ∑ i : Fin 16, ∫ x,
          MvPolynomial.eval x (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
            ∂(gaussPi 16) :=
  poincare_MV_measure 16 p

/-- **Sharpness in measure form**: 1 is the least constant here too, so the
    measure-level statement is not the vacuous "some constant works". -/
theorem no_better_constant_measure (n : ℕ) (c : ℝ)
    (h : ∀ p : MvPolynomial (Fin (n + 1)) ℝ,
      (∫ x, MvPolynomial.eval x (p * p) ∂(gaussPi (n + 1)))
          - (∫ x, MvPolynomial.eval x p ∂(gaussPi (n + 1))) ^ 2
        ≤ c * ∑ i : Fin (n + 1), ∫ x,
            MvPolynomial.eval x (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
              ∂(gaussPi (n + 1))) :
    1 ≤ c := by
  refine no_better_constant_MV n c fun p => ?_
  have hp := h p
  rw [← EN_eq_integral, ← EN_eq_integral] at hp
  simp_rw [← EN_eq_integral] at hp
  exact hp

/-! ## 4. The scaled version: variance σ², and the Λ²/2 constant

    `SpectralGaussianGap.ENs σ n` is `EN n` precomposed with xᵢ ↦ σxᵢ. Under
    the coordinatewise pushforward that is the n-fold Gaussian of variance
    σ², so the Λ-parametrised statements become statements about a measure
    too. -/

/-- The n-fold centred Gaussian of variance σ². -/
def gaussPiVar (σ : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal))

/-- Evaluating the rescaled polynomial is evaluating at the rescaled point. -/
theorem eval_scaleSub (n : ℕ) (σ : ℝ) (x : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval x (SpectralGaussianGap.scaleSub σ n p)
      = MvPolynomial.eval (fun i => σ * x i) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [SpectralGaussianGap.scaleSub]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [map_mul, SpectralGaussianGap.scaleSub_X, map_mul, map_mul, hp]
      simp

/-- **The rescaling is measure preserving**, coordinatewise, by Mathlib's
    `measurePreserving_pi` and its pushforward lemma for scalar multiples of a
    Gaussian. -/
theorem measurePreserving_scale (σ : ℝ) (n : ℕ) :
    MeasurePreserving (fun (x : Fin n → ℝ) (i : Fin n) => σ * x i)
      (gaussPi n) (gaussPiVar σ n) := by
  rw [gaussPi, gaussPiVar]
  refine measurePreserving_pi _ _ fun i => ⟨measurable_const_mul σ, ?_⟩
  rw [gaussianReal_map_const_mul σ, mul_zero, mul_one]

/-- **`ENs` IS an integral too**: the scaled moment functional is the integral
    against the n-fold Gaussian of variance σ². -/
theorem ENs_eq_integral (σ : ℝ) (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    SpectralGaussianGap.ENs σ n p = ∫ x, MvPolynomial.eval x p ∂(gaussPiVar σ n) := by
  have hms := measurePreserving_scale σ n
  have hint : ∫ y, MvPolynomial.eval y p ∂(gaussPiVar σ n)
      = ∫ x, MvPolynomial.eval ((fun (x : Fin n → ℝ) (i : Fin n) => σ * x i) x) p
          ∂(gaussPi n) := by
    conv_lhs => rw [← hms.map_eq]
    exact integral_map hms.measurable.aemeasurable
      (by rw [hms.map_eq, gaussPiVar]; exact (integrable_eval_of _ n p).aestronglyMeasurable)
  rw [hint, SpectralGaussianGap.ENs, EN_eq_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => eval_scaleSub n σ x p)

/-- The variance of the measure the Λ statements use is literally Λ²/2. -/
theorem gaussPiVar_sqrt (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    gaussPiVar (Real.sqrt a) n = Measure.pi (fun _ => gaussianReal 0 ⟨a, ha⟩) := by
  rw [gaussPiVar]
  congr 1
  funext _
  congr 1
  exact NNReal.coe_injective (Real.sq_sqrt ha)

/-- **THE CASCADE STATEMENT, ABOUT A MEASURE.** On ℝ¹⁶ ≅ Herm₄(ℂ), against
    the honest 16-dimensional Gaussian of variance Λ²/2:

      ∫ p² − (∫ p)² ≤ (Λ²/2) · Σᵢ ∫ (∂ᵢp)².

    This is the statement the estate's Bakry-Émery number was quoting, now
    with every expectation an integral against a single Mathlib measure —
    which is exactly what ERRATA 27 said was missing. The constant is sharp
    (`SpectralGaussianGap.no_better_constant_R16_lambda`), so 2/Λ² is the
    gap and not merely a bound on it.

    Still NOT proven, and unchanged: that the spectral action produces this
    measure. -/
theorem poincare_R16_lambda_measure (Λ : ℝ) (p : MvPolynomial (Fin 16) ℝ) :
    (∫ x, MvPolynomial.eval x (p * p)
        ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩))
        - (∫ x, MvPolynomial.eval x p
            ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩)) ^ 2
      ≤ (Λ ^ 2 / 2) * ∑ i : Fin 16, ∫ x,
          MvPolynomial.eval x (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
            ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩) := by
  have h := SpectralGaussianGap.poincare_R16_lambda Λ p
  rw [ENs_eq_integral, ENs_eq_integral] at h
  simp_rw [ENs_eq_integral] at h
  rw [gaussPiVar_sqrt (Λ ^ 2 / 2) (by positivity)] at h
  exact h

/-- **Sharpness of the Λ²/2 constant in MEASURE form**: no smaller constant
    satisfies the 16-dimensional inequality against the Λ-Gaussian. Transfers
    `SpectralGaussianGap.no_better_constant_R16_lambda` through
    `ENs_eq_integral`, so the measure-level statement of
    `poincare_R16_lambda_measure` carries its own sharpness certificate. -/
theorem no_better_constant_R16_lambda_measure (Λ c : ℝ)
    (h : ∀ p : MvPolynomial (Fin 16) ℝ,
      (∫ x, MvPolynomial.eval x (p * p)
          ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩))
          - (∫ x, MvPolynomial.eval x p
              ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩)) ^ 2
        ≤ c * ∑ i : Fin 16, ∫ x,
            MvPolynomial.eval x (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
              ∂(Measure.pi fun _ : Fin 16 => gaussianReal 0 ⟨Λ ^ 2 / 2, by positivity⟩)) :
    Λ ^ 2 / 2 ≤ c := by
  refine SpectralGaussianGap.no_better_constant_R16_lambda Λ c fun p => ?_
  have hp := h p
  rw [← gaussPiVar_sqrt (Λ ^ 2 / 2) (by positivity)] at hp
  rw [ENs_eq_integral, ENs_eq_integral]
  simp_rw [ENs_eq_integral]
  exact hp

end GaussianProductMeasure
