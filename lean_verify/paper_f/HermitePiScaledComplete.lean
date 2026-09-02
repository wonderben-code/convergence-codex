import HermitePiComplete
import GaussianProductMeasure
import TextbookSobolevPiScaled

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-!
# `n` dimensions **and** variance `σ²` at once — the combination neither half had

`HermiteCompleteness` fenced two generalisations of its completeness theorem in one sentence:
*"completeness in `L²(γ_σ)` for `σ ≠ 1` or in `n` dimensions (the same argument transfers; not
done here)."* Both halves are now done and **they were done separately**:
`HermitePiComplete.hpi_complete` is `n` dimensions **at variance one**, and
`HermiteScaledComplete` is variance `σ` **in one dimension**. A note added to
`HermiteCompleteness` on 2026-08-29 says in as many words that the combination —
`n` dimensions at variance `σ` — **is proved nowhere in this estate**.

**This file is that combination**, and it is the note's own sentence discharged the day after it
was written.

The route is the one-dimensional route again, with one difference that makes it shorter rather
than longer: the estate already has the scaling as a **`MeasurePreserving` map**,
`GaussianProductMeasure.measurePreserving_scale`, so the pushforward identity does not have to
be built here. Everything below is transport across it.

## What is proved

> **`polynomials_complete_pi_scaled`** — if `F ∈ L²(γ_σⁿ)` is orthogonal against `γ_σⁿ` to every
> **rescaled** product Hermite function `x ↦ Hpi n m (σ⁻¹ • x)`, then `F = 0` almost everywhere.
> At every `σ ≠ 0` and every `n`.
>
> **`hermitePi_orthogonal_scaled`**, **`hermitePi_norm_sq_scaled`** — the rescaled family is
> orthogonal against `γ_σⁿ` with the **same** inner products as at variance one: `0` off the
> diagonal and `∏ᵢ (mᵢ)!` on it. The variance does not appear in the answer, in any dimension.
>
> **`hermitePi_complete_orthogonal_system_scaled`** — the package, the `n`-dimensional
> variance-`σ` analogue of `HermiteCompleteness.hermite_complete_orthogonal_system`.
>
> **`memLp_scaled_pi_iff`**, **`ae_eq_zero_pi_iff`** — the transport lemmas, stated separately
> because they are what the argument is, and because `ae_map_iff` is again unusable: it wants a
> measurable set and an `L²` function supplies only an a.e.-measurable one, so vanishing moves
> across through `eLpNorm` as it did in one dimension.

## What is NOT claimed

**`σ = 0` is excluded here, and that is a real difference from one dimension.**
`HermiteScaledComplete.polynomials_complete_scaled` covers `σ = 0` because at variance zero the
one-dimensional measure is `δ₀` and orthogonality to the constant polynomial already forces
`f 0 = 0`. The same is true of `γ_0ⁿ = δ₀ⁿ`, but **it is not proved below**: every statement here
carries `σ ≠ 0`, which is what the rescaled family `Hpi n m (σ⁻¹ • ·)` needs to mean anything.
The degenerate case is not claimed in either direction.

> **⚠ Closed the same day, by §4 of this file.** `complete_pi_zero` proves it: `γ_0ⁿ` is the Dirac
> mass at the origin (`TextbookSobolevPiScaled.gaussPiVar_zero`, over the estate's own `pi_dirac`,
> which Mathlib does not have), and orthogonality to `Hpi n 0 = 1` alone forces `F 0 = 0`.
> **^ THE CLAUSE *"which Mathlib does not have"* IS FALSE AND IS KEPT** (`ERRATUM 419`, 2026-09-02,
> on `ERRATUM 94`'s rule). Mathlib has it: `Measure.infinitePi_dirac` composed with
> `Measure.infinitePi_eq_pi`, two lines (`ERRATUM 413`, 2026-09-01). **That correction reached
> `TextbookSobolevPiScaled` and not this file** — the estate's `pi_dirac` is kept there only to
> avoid a 53-job import, which is a convenience and not an absence. Nothing else here changes. **The
> paragraph is kept (`ERRATUM 94`) and its reason is still the right reason**: the statement is
> about the **plain** family, because the rescaled one is meaningless at `σ = 0` — so this is not
> the `σ ≠ 0` theorem extended, it is a different statement about a degenerate measure. **No
> integrability hypothesis is needed or assumed**, as in one dimension.

**No Poincaré inequality.** This is completeness only. The `W^{1,2}` approximation that the
inequality beyond polynomials needs is untouched here, exactly as `HermiteCompleteness` records.

**Nothing about `MvPolynomial`s.** The orthogonality is stated against the product Hermite
family `Hpi`, which is what `HermitePiComplete` proves completeness for. There is no
`MvPolynomial` version below and none is claimed.

**Nothing is withdrawn.** `HermitePiComplete.hpi_complete` and
`HermiteScaledComplete.polynomials_complete_scaled` keep their proofs; this file uses the first
and stands beside the second.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermitePiScaledComplete

open HermitePi HermitePiComplete GaussianProductMeasure GaussianPoincare

variable {n : ℕ} {σ : ℝ}

/-- The coordinatewise rescaling, as a function. -/
def scalePi (σ : ℝ) (n : ℕ) : (Fin n → ℝ) → (Fin n → ℝ) := fun x i => σ * x i

theorem map_gaussPi_eq (σ : ℝ) (n : ℕ) :
    (gaussPi n).map (scalePi σ n) = gaussPiVar σ n :=
  (measurePreserving_scale σ n).map_eq

theorem aemeasurable_scalePi (σ : ℝ) (n : ℕ) :
    AEMeasurable (scalePi σ n) (gaussPi n) :=
  (measurePreserving_scale σ n).measurable.aemeasurable

/-! ## 1. Transport across the rescaling -/

theorem integral_scaled_pi (σ : ℝ) (n : ℕ) (h : (Fin n → ℝ) → ℝ)
    (hmeas : AEStronglyMeasurable h (gaussPiVar σ n)) :
    ∫ x, h x ∂(gaussPiVar σ n) = ∫ x, h (scalePi σ n x) ∂(gaussPi n) := by
  rw [← map_gaussPi_eq σ n] at hmeas ⊢
  exact integral_map (aemeasurable_scalePi σ n) hmeas

theorem memLp_scaled_pi_iff (σ : ℝ) (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (gaussPiVar σ n)) :
    MemLp F 2 (gaussPiVar σ n) ↔ MemLp (fun x => F (scalePi σ n x)) 2 (gaussPi n) := by
  rw [← map_gaussPi_eq σ n] at hF ⊢
  exact memLp_map_measure_iff hF (aemeasurable_scalePi σ n)

/-- Vanishing transfers both ways. Through `eLpNorm`, because `ae_map_iff` wants a measurable
set and an `L²` function supplies only an a.e.-measurable one. -/
theorem ae_eq_zero_pi_iff (σ : ℝ) (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (gaussPiVar σ n)) :
    F =ᵐ[gaussPiVar σ n] 0 ↔ (fun x => F (scalePi σ n x)) =ᵐ[gaussPi n] 0 := by
  have hF' : AEStronglyMeasurable F ((gaussPi n).map (scalePi σ n)) := by
    rwa [map_gaussPi_eq σ n]
  have hcomp : AEStronglyMeasurable (fun x => F (scalePi σ n x)) (gaussPi n) :=
    hF'.comp_aemeasurable (aemeasurable_scalePi σ n)
  have hnorm : eLpNorm F 2 (gaussPiVar σ n)
      = eLpNorm (fun x => F (scalePi σ n x)) 2 (gaussPi n) := by
    rw [← map_gaussPi_eq σ n]
    exact eLpNorm_map_measure hF' (aemeasurable_scalePi σ n)
  have h1 : F =ᵐ[gaussPiVar σ n] 0 ↔ eLpNorm F 2 (gaussPiVar σ n) = 0 :=
    (eLpNorm_eq_zero_iff hF (by norm_num)).symm
  have h2 : (fun x => F (scalePi σ n x)) =ᵐ[gaussPi n] 0
      ↔ eLpNorm (fun x => F (scalePi σ n x)) 2 (gaussPi n) = 0 :=
    (eLpNorm_eq_zero_iff hcomp (by norm_num)).symm
  rw [h1, h2, hnorm]

/-- The rescaling undoes the rescaled argument: this is the one computation the whole file
turns on. -/
theorem scalePi_inv (hσ : σ ≠ 0) (n : ℕ) (x : Fin n → ℝ) :
    (fun i => σ⁻¹ * scalePi σ n x i) = x := by
  funext i
  simp only [scalePi]
  rw [← mul_assoc, inv_mul_cancel₀ hσ, one_mul]

/-! ## 2. Completeness in `n` dimensions at variance `σ²` -/

/-- **COMPLETENESS OF THE RESCALED PRODUCT HERMITE FAMILY IN `L²(γ_σⁿ)`.** The combination the
one-dimensional and the variance-one results did not have between them. -/
theorem polynomials_complete_pi_scaled (hσ : σ ≠ 0) (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : MemLp F 2 (gaussPiVar σ n))
    (horth : ∀ m : Fin n → ℕ,
      ∫ x, F x * Hpi n m (fun i => σ⁻¹ * x i) ∂(gaussPiVar σ n) = 0) :
    F =ᵐ[gaussPiVar σ n] 0 := by
  have hFm : AEStronglyMeasurable F (gaussPiVar σ n) := hF.aestronglyMeasurable
  set G : (Fin n → ℝ) → ℝ := fun x => F (scalePi σ n x) with hG
  have hGL : MemLp G 2 (gaussPi n) := (memLp_scaled_pi_iff σ n F hFm).mp hF
  have hGorth : ∀ m : Fin n → ℕ, ∫ x, G x * Hpi n m x ∂(gaussPi n) = 0 := by
    intro m
    have hint : AEStronglyMeasurable
        (fun x => F x * Hpi n m (fun i => σ⁻¹ * x i)) (gaussPiVar σ n) :=
      hFm.mul (((Hpi_continuous n m).comp
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).aestronglyMeasurable)
    have hcv := integral_scaled_pi σ n _ hint
    rw [horth m] at hcv
    calc ∫ x, G x * Hpi n m x ∂(gaussPi n)
        = ∫ x, F (scalePi σ n x) * Hpi n m (fun i => σ⁻¹ * scalePi σ n x i) ∂(gaussPi n) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hG, scalePi_inv hσ n x]
      _ = 0 := hcv.symm
  exact (ae_eq_zero_pi_iff σ n F hFm).mpr (hpi_complete n G hGL hGorth)

/-! ## 3. Orthogonality and norms, by the same transport -/

theorem hermitePi_orthogonal_scaled (hσ : σ ≠ 0) (n : ℕ) (m m' : Fin n → ℕ) (hmm : m ≠ m') :
    ∫ x, Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m' (fun i => σ⁻¹ * x i) ∂(gaussPiVar σ n) = 0 := by
  have hint : AEStronglyMeasurable
      (fun x => Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m' (fun i => σ⁻¹ * x i))
        (gaussPiVar σ n) := by
    refine AEStronglyMeasurable.mul ?_ ?_ <;>
      exact ((Hpi_continuous n _).comp
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).aestronglyMeasurable
  rw [integral_scaled_pi σ n _ hint]
  rw [show (fun x : Fin n → ℝ => Hpi n m (fun i => σ⁻¹ * scalePi σ n x i)
        * Hpi n m' (fun i => σ⁻¹ * scalePi σ n x i))
      = fun x : Fin n → ℝ => Hpi n m x * Hpi n m' x by
    funext x; rw [scalePi_inv hσ n x]]
  rw [Hpi_orthogonal n m m', if_neg hmm]

theorem hermitePi_norm_sq_scaled (hσ : σ ≠ 0) (n : ℕ) (m : Fin n → ℕ) :
    ∫ x, Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m (fun i => σ⁻¹ * x i) ∂(gaussPiVar σ n)
      = ∏ i, ((m i).factorial : ℝ) := by
  have hint : AEStronglyMeasurable
      (fun x => Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m (fun i => σ⁻¹ * x i))
        (gaussPiVar σ n) := by
    refine AEStronglyMeasurable.mul ?_ ?_ <;>
      exact ((Hpi_continuous n _).comp
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).aestronglyMeasurable
  rw [integral_scaled_pi σ n _ hint]
  rw [show (fun x : Fin n → ℝ => Hpi n m (fun i => σ⁻¹ * scalePi σ n x i)
        * Hpi n m (fun i => σ⁻¹ * scalePi σ n x i))
      = fun x : Fin n → ℝ => Hpi n m x * Hpi n m x by
    funext x; rw [scalePi_inv hσ n x]]
  exact Hpi_norm_sq n m

/-- **THE RESCALED PRODUCT HERMITE FAMILY IS A COMPLETE ORTHOGONAL SYSTEM IN `L²(γ_σⁿ)`**, in
the same four parts as at variance one and in one dimension. -/
theorem hermitePi_complete_orthogonal_system_scaled (hσ : σ ≠ 0) (n : ℕ) :
    (∀ m m' : Fin n → ℕ, m ≠ m' →
        ∫ x, Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m' (fun i => σ⁻¹ * x i)
          ∂(gaussPiVar σ n) = 0)
      ∧ (∀ m : Fin n → ℕ,
          ∫ x, Hpi n m (fun i => σ⁻¹ * x i) * Hpi n m (fun i => σ⁻¹ * x i)
            ∂(gaussPiVar σ n) = ∏ i, ((m i).factorial : ℝ))
      ∧ (∀ m : Fin n → ℕ, (∏ i, ((m i).factorial : ℝ)) ≠ 0)
      ∧ (∀ F : (Fin n → ℝ) → ℝ, MemLp F 2 (gaussPiVar σ n) →
          (∀ m : Fin n → ℕ,
            ∫ x, F x * Hpi n m (fun i => σ⁻¹ * x i) ∂(gaussPiVar σ n) = 0) →
          F =ᵐ[gaussPiVar σ n] 0) :=
  ⟨fun m m' h => hermitePi_orthogonal_scaled hσ n m m' h,
   fun m => hermitePi_norm_sq_scaled hσ n m,
   fun m => Finset.prod_ne_zero_iff.mpr fun i _ =>
     Nat.cast_ne_zero.mpr (m i).factorial_ne_zero,
   fun F hF horth => polynomials_complete_pi_scaled hσ n F hF horth⟩

/-! ## 4. The degenerate case, `σ = 0` -/

/-- `Hpi n 0` is the constant `1`: every factor is `H 0 = 1`. -/
theorem Hpi_zero_eq_one (n : ℕ) (x : Fin n → ℝ) : Hpi n 0 x = 1 := by
  simp [Hpi]

/-- **COMPLETENESS AT VARIANCE ZERO, IN `n` DIMENSIONS.** The clause this file's header left open
on 2026-08-29, closed the same day. At `σ = 0` the rescaled family `Hpi n m (σ⁻¹ • ·)` is
meaningless, so the statement is about the **plain** product Hermite family — and it needs only
the constant one: `γ_0ⁿ` is the Dirac mass at the origin, and orthogonality to `Hpi n 0 = 1`
already says `F 0 = 0`. **No integrability hypothesis is needed or assumed**, exactly as in one
dimension. -/
theorem complete_pi_zero (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (horth : ∀ m : Fin n → ℕ, ∫ x, F x * Hpi n m x ∂(gaussPiVar 0 n) = 0) :
    F =ᵐ[gaussPiVar 0 n] 0 := by
  have hd : gaussPiVar 0 n = Measure.dirac (0 : Fin n → ℝ) :=
    TextbookSobolevPiScaled.gaussPiVar_zero n
  have h1 := horth 0
  rw [hd] at h1 ⊢
  rw [integral_dirac] at h1
  rw [Hpi_zero_eq_one, mul_one] at h1
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have hsub : {x : Fin n → ℝ | ¬ F x = (0 : (Fin n → ℝ) → ℝ) x}
      ⊆ ({0} : Set (Fin n → ℝ))ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hx (by simpa using h1)
  refine measure_mono_null hsub ?_
  simp

end HermitePiScaledComplete
