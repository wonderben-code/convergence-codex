/-
  Herm4GaussianDensity.lean — the closed form: `herm4Gaussian` has density `(2π)^{-8} · e^{-‖A‖²/2}`
  with respect to the volume of `Herm₄(ℂ)`, the scaled measure has variance `Λ²`, and the Boltzmann
  normal form with cutoff `Λ` has partition function `Z = (πΛ²)⁸`.

  SPINE L20 (Boltzmann measure exists, PARTIAL) — the clause of Caesar item 4 the 20 September
  re-count left standing, and `Herm4Gaussian`'s NOT list, second bullet. Hardening unit 161,
  2026-09-20.

  WHY. Unit 12 (`Herm4Gaussian`) put the Gaussian on the Hermitian slice itself and said what it had
  not done: *no `(2π)^{-8}` and no `Z = (πΛ²)⁸` appears in any statement here … the variance is `1`,
  not `Λ²`*. The L20 row has carried the missing constant since the Phase 2c queue. The pieces were
  in the estate and in Mathlib: `GaussPiDensity.gaussPi_eq_withDensity` writes the 16-fold product
  Gaussian as `volume.withDensity (ofReal ∘ rhoPi 16)`;
  `OrthonormalBasis.measurePreserving_repr_symm` and `PiLp.volume_preserving_toLp` make the
  coordinate map volume-preserving; and a density rides
  along a volume-preserving equivalence. The sixteen `(√(2π))⁻¹` multiply to `(2π)^{-8}`, the
  sixteen exponents add to `-‖A‖²/2` because the basis is orthonormal. Scaling by `Λ` costs the
  Jacobian `Λ⁻¹⁶` (`Measure.map_addHaar_smul`), which turns `(2π)^{-8}` into `(2πΛ²)^{-8}`; at the
  scale `Λ/√2` the weight is `e^{-‖A‖²/Λ²}` and the constant is `(πΛ²)^{-8}` — the `Z` of the queue.

  WHAT IS PROVED.
  * `herm4Coord : (Fin 16 → ℝ) ≃ᵐ Herm4`, `herm4Coord_apply`, `herm4Coord_measurePreserving`;
    `herm4Gaussian_eq_map_herm4Coord`.
  * `map_withDensity_equiv`, `map_withDensity_equiv'` — `(μ.withDensity f).map e = ν.withDensity
    (f ∘ e.symm)` for a measure-preserving (resp. any) measurable equivalence `e`.
  * `rhoPi_herm4Coord_symm` — `rhoPi 16 (herm4Coord.symm A) = ((2π)⁸)⁻¹ · exp(-‖A‖²/2)`.
  * **`herm4Gaussian_eq_withDensity`** — `herm4Gaussian = volume.withDensity
    (A ↦ ofReal (((2π)⁸)⁻¹ · exp(-‖A‖²/2)))`.
  * `volume_map_smul` (the Jacobian `Λ⁻¹⁶`), **`herm4Gaussian_map_smul`** — the pushforward along
    `A ↦ Λ • A`, `Λ > 0`, has density `((2πΛ²)⁸)⁻¹ · exp(-‖A‖²/(2Λ²))`: variance `Λ²`.
  * `herm4Boltzmann Λ := herm4Gaussian.map ((Λ/√2) • ·)`, a probability measure;
    **`herm4Boltzmann_eq_withDensity`** — for `Λ > 0` its density is `((πΛ²)⁸)⁻¹ · exp(-‖A‖²/Λ²)`,
    so **`Z = (πΛ²)⁸`**.

  WHAT IS **NOT** PROVED, said exactly.
  * That any of these is the Boltzmann measure OF THE SPECTRAL ACTION. `herm4Boltzmann` is a
    Gaussian named for its weight `e^{-‖A‖²/Λ²}`; what fluctuates and with what weight is
    `DECISIONS NEEDED` 5 and `ASSUMPTIONS_LEDGER` 8, 26, 27, exactly as unit 12 left it. The word
    *Boltzmann* in the name is the queue's, not a theorem's.
  * `Z` as an integral. `Z = (πΛ²)⁸` appears as the constant in a density that Mathlib's
    `stdGaussian` makes a probability measure; `∫ exp(-‖A‖²/Λ²) dA = (πΛ²)⁸` is not stated as an
    integral identity here.
  * `Λ ≤ 0`. `herm4Boltzmann Λ` is defined for every real `Λ` (at `Λ = 0` it is a Dirac mass);
    the density formula is proved for `Λ > 0` only.
  * Moments, and any connection to the cascade's `D` — unit 12's third and fourth bullets stand.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import Herm4Gaussian
import GaussPiDensity

namespace Herm4GaussianDensity

open MeasureTheory ProbabilityTheory Herm4Gaussian GaussPiDensity GaussianProductMeasure
  TextbookSobolev
open scoped ENNReal

noncomputable section

/-! ## 1. The coordinate equivalence `ℝ¹⁶ ≃ᵐ Herm₄`, volume-preserving -/

/-- **The coordinate equivalence `ℝ¹⁶ ≃ᵐ Herm₄(ℂ)`** along `herm4Basis`: `x ↦ ∑ xᵢ • bᵢ`, as
`toLp` followed by `herm4Basis.repr.symm`. -/
def herm4Coord : (Fin 16 → ℝ) ≃ᵐ Herm4 :=
  (MeasurableEquiv.toLp 2 (Fin 16 → ℝ)).trans herm4Basis.measurableEquiv.symm

/-- `herm4Coord x = ∑ i, x i • herm4Basis i` — the map of `herm4Gaussian_eq_map_pi_std`. -/
theorem herm4Coord_apply (x : Fin 16 → ℝ) : herm4Coord x = ∑ i, x i • herm4Basis i := by
  rw [herm4Basis.sum_repr_symm]
  rfl

/-- The inverse reads off the coordinates in `herm4Basis`. -/
theorem herm4Coord_symm_apply (A : Herm4) (i : Fin 16) :
    herm4Coord.symm A i = herm4Basis.repr A i := rfl

/-- **Volume-preserving**: Lebesgue measure on `ℝ¹⁶` goes to the volume of the inner product
space `Herm₄(ℂ)` (`PiLp.volume_preserving_toLp`, `OrthonormalBasis.measurePreserving_repr_symm`). -/
theorem herm4Coord_measurePreserving : MeasurePreserving herm4Coord volume volume :=
  herm4Basis.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin 16))

/-! ## 2. The measure is the pushforward of the 16-fold product along `herm4Coord` -/

/-- `herm4Gaussian` is the pushforward of `GaussianProductMeasure.gaussPi 16` along `herm4Coord`
— unit 12's `herm4Gaussian_eq_map_pi_std` with the map named. -/
theorem herm4Gaussian_eq_map_herm4Coord : herm4Gaussian = (gaussPi 16).map herm4Coord := by
  rw [herm4Gaussian_eq_map_pi_std]
  congr 1
  funext x
  exact (herm4Coord_apply x).symm

/-! ## 3. A density is carried along a measure-preserving measurable equivalence -/

/-- **A density rides along a measure-preserving measurable equivalence**:
`(μ.withDensity f).map e = ν.withDensity (f ∘ e.symm)`. Proved from `withDensity_apply`,
`Measure.restrict_map` and `lintegral_map_equiv`; no hypothesis on `f`. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [MeasurableEquiv.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← he.map_eq, Measure.restrict_map e.measurable hs, lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

/-! ## 4. The density in closed form -/

/-- **THE DENSITY IN CLOSED FORM.** `GaussPiDensity.rhoPi 16` read back through `herm4Coord` is
`(2π)^{-8} · exp(-‖A‖²/2)`: the sixteen factors `(√(2π))⁻¹` multiply to `((2π)⁸)⁻¹`, and the
sixteen exponents add to `-‖A‖²/2` because `herm4Basis.repr` is an isometry
(`EuclideanSpace.real_norm_sq_eq`). -/
theorem rhoPi_herm4Coord_symm (A : Herm4) :
    rhoPi 16 (herm4Coord.symm A) = ((2 * Real.pi) ^ 8)⁻¹ * Real.exp (-‖A‖ ^ 2 / 2) := by
  have hsum : ∑ i : Fin 16, (herm4Basis.repr A i) ^ 2 = ‖A‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]
  have hconst : ((Real.sqrt (2 * Real.pi))⁻¹) ^ 16 = ((2 * Real.pi) ^ 8)⁻¹ := by
    rw [inv_pow, show (16 : ℕ) = 2 * 8 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  simp only [rhoPi, rho_funext, herm4Coord_symm_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hconst,
    ← Real.exp_sum, ← Finset.sum_div, Finset.sum_neg_distrib, hsum]

/-- **THE CLOSED FORM ON `Herm₄(ℂ)`.**
`herm4Gaussian = volume.withDensity (A ↦ (2π)^{-8} · e^{-‖A‖²/2})` with respect to the volume of
the Frobenius inner product space — the `(2π)^{-8}` that `Herm4Gaussian`'s NOT list and `SPINE`
L20 said appeared in no statement. -/
theorem herm4Gaussian_eq_withDensity :
    herm4Gaussian = volume.withDensity
      (fun A : Herm4 => ENNReal.ofReal (((2 * Real.pi) ^ 8)⁻¹ * Real.exp (-‖A‖ ^ 2 / 2))) := by
  rw [herm4Gaussian_eq_map_herm4Coord, gaussPi_eq_withDensity,
    map_withDensity_equiv _ _ herm4Coord herm4Coord_measurePreserving]
  congr 1
  funext A
  rw [rhoPi_herm4Coord_symm]

/-! ## 5. The cutoff scale: variance `Λ²`, and the partition function `Z = (πΛ²)⁸` -/

/-- The same for any measurable equivalence, with the pushforward on the right. -/
theorem map_withDensity_equiv' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) :=
  map_withDensity_equiv μ (μ.map e) e ⟨e.measurable, rfl⟩ f

/-- The volume of `Herm₄(ℂ)` is a Haar measure (it is a basis' `addHaar`). -/
instance : (volume : Measure Herm4).IsAddHaarMeasure :=
  inferInstanceAs (stdOrthonormalBasis ℝ Herm4).toBasis.addHaar.IsAddHaarMeasure

/-- Scaling by `Λ > 0` multiplies the volume of the 16-dimensional `Herm₄(ℂ)` by `Λ⁻¹⁶`
(`Measure.map_addHaar_smul`, `finrank_herm4`). -/
theorem volume_map_smul {Λ : ℝ} (hΛ : 0 < Λ) :
    (volume : Measure Herm4).map (Λ • ·) = ENNReal.ofReal ((Λ ^ 16)⁻¹) • volume := by
  rw [Measure.map_addHaar_smul (μ := (volume : Measure Herm4)) hΛ.ne', finrank_herm4,
    abs_of_pos (inv_pos.2 (pow_pos hΛ 16))]

/-- `‖Λ⁻¹ • A‖² = ‖A‖²/Λ²` for `Λ > 0`. -/
theorem norm_inv_smul_sq (Λ : ℝ) (hΛ : 0 < Λ) (A : Herm4) :
    ‖Λ⁻¹ • A‖ ^ 2 = ‖A‖ ^ 2 / Λ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hΛ), mul_pow, inv_pow]
  ring

/-- **THE SCALED GAUSSIAN**: pushing `herm4Gaussian` forward along `A ↦ Λ • A` gives the Gaussian
of variance `Λ²`, with density `(2πΛ²)^{-8} · exp(-‖A‖²/(2Λ²))`. -/
theorem herm4Gaussian_map_smul {Λ : ℝ} (hΛ : 0 < Λ) :
    herm4Gaussian.map (Λ • ·) = volume.withDensity
      (fun A : Herm4 =>
        ENNReal.ofReal (((2 * Real.pi * Λ ^ 2) ^ 8)⁻¹ * Real.exp (-‖A‖ ^ 2 / (2 * Λ ^ 2)))) := by
  have hne : Λ ≠ 0 := hΛ.ne'
  have hmap : herm4Gaussian.map (Λ • ·) = herm4Gaussian.map (MeasurableEquiv.smul₀ Λ hne) := rfl
  rw [hmap, herm4Gaussian_eq_withDensity, map_withDensity_equiv', MeasurableEquiv.coe_smul₀,
    volume_map_smul hΛ, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext A
  rw [Pi.smul_apply, smul_eq_mul, MeasurableEquiv.symm_smul₀, MeasurableEquiv.coe_smul₀,
    ← ENNReal.ofReal_mul (by positivity), norm_inv_smul_sq Λ hΛ]
  congr 1
  have h1 : -(‖A‖ ^ 2 / Λ ^ 2) / 2 = -‖A‖ ^ 2 / (2 * Λ ^ 2) := by
    rw [neg_div, neg_div, div_div, mul_comm]
  have h2 : (Λ ^ 16)⁻¹ * ((2 * Real.pi) ^ 8)⁻¹ = ((2 * Real.pi * Λ ^ 2) ^ 8)⁻¹ := by
    rw [← mul_inv]
    congr 1
    ring
  rw [← mul_assoc, h2, h1]

/-- **THE BOLTZMANN NORMAL FORM WITH CUTOFF `Λ`**: the Gaussian of weight `exp(-‖A‖²/Λ²)` on
`Herm₄(ℂ)`, defined as the pushforward of `herm4Gaussian` along `A ↦ (Λ/√2) • A`. A probability
measure for every real `Λ`; its density is computed for `Λ > 0`. -/
def herm4Boltzmann (Λ : ℝ) : Measure Herm4 := herm4Gaussian.map ((Λ / Real.sqrt 2) • ·)

instance (Λ : ℝ) : IsProbabilityMeasure (herm4Boltzmann Λ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- **`Z = (πΛ²)⁸`.** For `Λ > 0`, `herm4Boltzmann Λ = volume.withDensity (A ↦ Z⁻¹ · e^{-‖A‖²/Λ²})`
with `Z = (πΛ²)⁸` — the partition function `SPINE` L20 has carried as *not stated* since the
Phase 2c queue. -/
theorem herm4Boltzmann_eq_withDensity {Λ : ℝ} (hΛ : 0 < Λ) :
    herm4Boltzmann Λ = volume.withDensity
      (fun A : Herm4 =>
        ENNReal.ofReal (((Real.pi * Λ ^ 2) ^ 8)⁻¹ * Real.exp (-‖A‖ ^ 2 / Λ ^ 2))) := by
  have hs : 0 < Λ / Real.sqrt 2 := div_pos hΛ (Real.sqrt_pos.2 (by norm_num))
  rw [herm4Boltzmann, herm4Gaussian_map_smul hs]
  congr 1
  funext A
  have hsq : (Λ / Real.sqrt 2) ^ 2 = Λ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have h1 : 2 * Real.pi * (Λ ^ 2 / 2) = Real.pi * Λ ^ 2 := by ring
  have h2 : 2 * (Λ ^ 2 / 2) = Λ ^ 2 := by ring
  rw [hsq, h1, h2]

end

end Herm4GaussianDensity
