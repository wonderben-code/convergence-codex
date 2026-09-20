/-
  Herm4GaussianMoments.lean — the two things unit 161 said it did not state: the partition function
  as an INTEGRAL, `∫ exp(-‖A‖²/Λ²) dA = (πΛ²)⁸` over `Herm₄(ℂ)`, and the moments transported: the
  Frobenius norm squared averages to `16` under `herm4Gaussian`, to `16 Λ²` under the scaled
  measure, and to `8 Λ²` under the Boltzmann normal form with cutoff `Λ`.

  SPINE L20 (Boltzmann measure exists, PARTIAL) — the second and fourth bullets of
  `Herm4GaussianDensity`'s NOT list, and the moment clause the L40493 watchlist block has called *a
  short corollary … named rather than built* since 14 September. Hardening unit 162, 2026-09-20.

  WHY. Unit 161 wrote `Z = (πΛ²)⁸` as the constant in a density and said `∫ e^{-‖A‖²/Λ²} = (πΛ²)⁸`
  was not stated as an integral identity. It is one line from being one: `herm4Boltzmann Λ` is a
  probability measure, its total mass is `∫⁻ Z⁻¹ · e^{-‖A‖²/Λ²}`, so the integral of the weight is
  `Z`; the Bochner form follows because the integrand is nonnegative and continuous. The moments
  are the other direction of unit 12's pushforward: `∫ ‖A‖² d(herm4Gaussian)` is `∫ ‖herm4Coord x‖²
  dγ¹⁶`, the basis is orthonormal so `‖herm4Coord x‖² = ∑ xᵢ²`, each coordinate is a standard
  Gaussian (`Measure.pi_map_eval`) whose second moment is `1` (`GaussianPoincare.gmean_eq_integral`
  at `X²` and `GaussianPoincareProduct.mom_two`), and there are sixteen of them. Scaling by `Λ`
  multiplies by `Λ²`.

  WHAT IS PROVED.
  * **`lintegral_boltzmann_weight`**, **`integral_boltzmann_weight`** — for `Λ > 0`,
    `∫⁻ ofReal (exp(-‖A‖²/Λ²)) = ofReal ((πΛ²)⁸)` and `∫ exp(-‖A‖²/Λ²) = (πΛ²)⁸`.
  * `norm_herm4Coord_sq`, `integral_sq_gaussianReal` (`∫ t² dγ = 1`), `gaussPi_map_eval`,
    `integral_coord_sq`, `integrable_coord_sq`, `integral_sum_sq_gaussPi` (`∫ ∑ xᵢ² dγ¹⁶ = 16`).
  * **`integral_norm_sq_herm4Gaussian`** — `∫ ‖A‖² d(herm4Gaussian) = 16`.
  * `integral_norm_sq_map_smul` — `∫ ‖A‖² d(herm4Gaussian.map (Λ • ·)) = 16 Λ²`, every real `Λ`.
  * **`integral_norm_sq_herm4Boltzmann`** — `∫ ‖A‖² d(herm4Boltzmann Λ) = 8 Λ²`, every real `Λ`.

  WHAT IS **NOT** PROVED, said exactly.
  * The mean. `∫ A d(herm4Gaussian) = 0` as a vector integral in `Herm₄(ℂ)` is not stated; the
    centring is visible only through the second moment being the dimension.
  * Higher moments and the polynomial moment table. `GaussianProductMeasure`'s `EN` results are
    about `ℝ¹⁶` and are transported here only for `∑ xᵢ²`; the Wick/Isserlis table on `Herm₄(ℂ)`
    and `∫ ‖A‖⁴` are not.
  * The identification with the spectral action — unchanged from units 12 and 161: DECISION 5;
    `herm4Boltzmann` is a Gaussian named for its weight.
  * Anything about the cascade's `D`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import Herm4GaussianDensity

namespace Herm4GaussianMoments

open MeasureTheory ProbabilityTheory Herm4Gaussian Herm4GaussianDensity GaussianProductMeasure
  GaussianPoincare GaussianPoincareProduct
open scoped ENNReal

noncomputable section

/-! ## 1. `Z` as an integral -/

/-- **`Z` AS AN INTEGRAL, LEBESGUE FORM.** `∫⁻ exp(-‖A‖²/Λ²) dA = (πΛ²)⁸` over `Herm₄(ℂ)`, for
`Λ > 0`: `herm4Boltzmann Λ` is a probability measure with density `Z⁻¹ · exp(-‖A‖²/Λ²)`
(`herm4Boltzmann_eq_withDensity`), so the integral of the weight is `Z`. -/
theorem lintegral_boltzmann_weight {Λ : ℝ} (hΛ : 0 < Λ) :
    ∫⁻ A : Herm4, ENNReal.ofReal (Real.exp (-‖A‖ ^ 2 / Λ ^ 2))
      = ENNReal.ofReal ((Real.pi * Λ ^ 2) ^ 8) := by
  have hZ : 0 < (Real.pi * Λ ^ 2) ^ 8 := by positivity
  have h1 : (herm4Boltzmann Λ) Set.univ = 1 := measure_univ
  rw [herm4Boltzmann_eq_withDensity hΛ, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ] at h1
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.2 hZ.le)] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_inv_of_pos hZ] at h1
  have hne : ENNReal.ofReal ((Real.pi * Λ ^ 2) ^ 8) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hZ
  calc ∫⁻ A : Herm4, ENNReal.ofReal (Real.exp (-‖A‖ ^ 2 / Λ ^ 2))
      = ENNReal.ofReal ((Real.pi * Λ ^ 2) ^ 8)
          * ((ENNReal.ofReal ((Real.pi * Λ ^ 2) ^ 8))⁻¹
            * ∫⁻ A : Herm4, ENNReal.ofReal (Real.exp (-‖A‖ ^ 2 / Λ ^ 2))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal ((Real.pi * Λ ^ 2) ^ 8) := by rw [h1, mul_one]

/-- **`Z` AS AN INTEGRAL, BOCHNER FORM.** `∫ exp(-‖A‖²/Λ²) dA = (πΛ²)⁸`, from the Lebesgue form via
`integral_eq_lintegral_of_nonneg_ae` — no integrability hypothesis is needed for a nonnegative
continuous integrand. This is the identity unit 161's NOT list said it did not state. -/
theorem integral_boltzmann_weight {Λ : ℝ} (hΛ : 0 < Λ) :
    ∫ A : Herm4, Real.exp (-‖A‖ ^ 2 / Λ ^ 2) = (Real.pi * Λ ^ 2) ^ 8 := by
  have hc : Continuous fun A : Herm4 => Real.exp (-‖A‖ ^ 2 / Λ ^ 2) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun A => (Real.exp_pos _).le)
    hc.aestronglyMeasurable, lintegral_boltzmann_weight hΛ,
    ENNReal.toReal_ofReal (by positivity)]

/-! ## 2. The second moment -/

/-- `‖∑ xᵢ • bᵢ‖² = ∑ xᵢ²` — the basis is orthonormal. -/
theorem norm_herm4Coord_sq (x : Fin 16 → ℝ) : ‖herm4Coord x‖ ^ 2 = ∑ i, x i ^ 2 := by
  have h : herm4Coord x = herm4Basis.repr.symm (WithLp.toLp 2 x) := rfl
  rw [h, LinearIsometryEquiv.norm_map, EuclideanSpace.real_norm_sq_eq]

/-- The second moment of the standard one-dimensional Gaussian is `1`:
`GaussianPoincare.gmean_eq_integral` at `X²` together with `GaussianPoincareProduct.mom_two`. -/
theorem integral_sq_gaussianReal : ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := gmean_eq_integral ((Polynomial.X : Polynomial ℝ) ^ 2)
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [← h]
  exact mom_two

/-- Each coordinate of the 16-fold product is a standard Gaussian (`Measure.pi_map_eval`, the
other fifteen factors having mass `1`). -/
theorem gaussPi_map_eval (i : Fin 16) : (gaussPi 16).map (Function.eval i) = gaussianReal 0 1 := by
  rw [gaussPi, Measure.pi_map_eval]
  simp

/-- `∫ xᵢ² dγ¹⁶ = 1` for every coordinate `i`. -/
theorem integral_coord_sq (i : Fin 16) : ∫ x : Fin 16 → ℝ, x i ^ 2 ∂(gaussPi 16) = 1 := by
  have h := integral_map (μ := gaussPi 16) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t ^ 2) (by fun_prop)
  rw [gaussPi_map_eval] at h
  exact h.symm.trans integral_sq_gaussianReal

/-- `xᵢ²` is integrable against `gaussPi 16` — `GaussianProductMeasure.integrable_eval` at `Xᵢ²`. -/
theorem integrable_coord_sq (i : Fin 16) :
    Integrable (fun x : Fin 16 → ℝ => x i ^ 2) (gaussPi 16) := by
  have h := integrable_eval 16 (MvPolynomial.X i ^ 2)
  simpa using h

/-- `∫ ‖x‖² dγ¹⁶ = 16`: sixteen coordinates of second moment `1`. -/
theorem integral_sum_sq_gaussPi : ∫ x : Fin 16 → ℝ, ∑ i, x i ^ 2 ∂(gaussPi 16) = 16 := by
  rw [integral_finset_sum _ (fun i _ => integrable_coord_sq i)]
  simp [integral_coord_sq]

/-- **THE SECOND MOMENT ON `Herm₄(ℂ)`**: `∫ ‖A‖² d(herm4Gaussian) = 16`, the Frobenius norm squared
averaging to the dimension — `herm4Gaussian` is the pushforward of `gaussPi 16` along the
volume-preserving `herm4Coord`, and the norm is carried by `norm_herm4Coord_sq`. -/
theorem integral_norm_sq_herm4Gaussian : ∫ A : Herm4, ‖A‖ ^ 2 ∂herm4Gaussian = 16 := by
  rw [herm4Gaussian_eq_map_herm4Coord,
    integral_map herm4Coord.measurable.aemeasurable (by fun_prop)]
  simp_rw [norm_herm4Coord_sq]
  exact integral_sum_sq_gaussPi

/-- The scaled measure of unit 161 has `∫ ‖A‖² = 16 Λ²` — variance `Λ²` per coordinate. Holds for
every real `Λ` (no positivity needed: `‖Λ • A‖² = Λ² ‖A‖²`). -/
theorem integral_norm_sq_map_smul (Λ : ℝ) :
    ∫ A : Herm4, ‖A‖ ^ 2 ∂(herm4Gaussian.map (Λ • ·)) = 16 * Λ ^ 2 := by
  have hm : Measurable fun A : Herm4 => Λ • A := by fun_prop
  rw [integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_norm_sq_herm4Gaussian]
  ring

/-- **THE SECOND MOMENT OF THE BOLTZMANN NORMAL FORM**: `∫ ‖A‖² d(herm4Boltzmann Λ) = 8 Λ²` — the
weight `exp(-‖A‖²/Λ²)` has variance `Λ²/2` per coordinate, sixteen coordinates. For every real
`Λ`. -/
theorem integral_norm_sq_herm4Boltzmann (Λ : ℝ) :
    ∫ A : Herm4, ‖A‖ ^ 2 ∂(herm4Boltzmann Λ) = 8 * Λ ^ 2 := by
  rw [herm4Boltzmann, integral_norm_sq_map_smul, div_pow, Real.sq_sqrt (by norm_num)]
  ring

end

end Herm4GaussianMoments
