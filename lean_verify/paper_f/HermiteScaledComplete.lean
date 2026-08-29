import HermiteCompleteness

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-!
# Completeness at every variance, and at variance zero too

`HermiteCompleteness` proved that nothing in `L²(γ)` is orthogonal to every polynomial except
`0`, at variance **one**, and listed among the things it did not do:

> *"Completeness in `L²(γ_σ)` for `σ ≠ 1` or in `n` dimensions (the same argument transfers; not
> done here)."*

The `n`-dimensional half was closed by the `HermitePi*` line, which reduces to the
one-dimensional `hermite_complete` twice. **The variance half is the one this file closes**, and
it was the clause `ERRATUM 314`'s probe of the fence census recorded as *unresolved by grep* —
neither answered nor attempted, as of 2026-08-28.

The route is the substitution `x ↦ σx`, which `PoincareScaledBeyond` already used to carry the
Poincaré inequality to every variance. What makes completeness a little different is that the
function being transported is an `L²` function rather than a differentiable one, so it is only
`AEStronglyMeasurable`, and the transport has to be done with `Measure.map` lemmas that accept
that. `PoincareScaledBeyond.integral_scaled` asks for `Measurable`, so it is not reusable here;
`integral_scaled_ae` below is the same change of variables under the weaker hypothesis.

## What is proved

> **`map_gauss_eq`** — `γ` pushed forward along `x ↦ σx` **is** Mathlib's `gaussianReal 0 σ²`,
> for every `σ`, from `gaussianReal_map_const_mul`. Everything else is transport across this.
>
> **`integral_scaled_ae`** — the change of variables for any `AEStronglyMeasurable` integrand,
> not just a `Measurable` one. This is `PoincareScaledBeyond.integral_scaled` with a hypothesis
> removed, and removing it is what makes the `L²` argument possible at all.
>
> **`memLp_scaled_iff`** and **`ae_eq_zero_iff`** — `f ∈ L²(γ_σ)` exactly when `f(σ·) ∈ L²(γ)`,
> and `f = 0` a.e. `γ_σ` exactly when `f(σ·) = 0` a.e. `γ`. The second goes through `eLpNorm`
> rather than through `ae_map_iff`, because the latter wants a measurable set and an `L²`
> function supplies only an a.e.-measurable one.
>
> **`polynomials_complete_scaled`** — **the theorem.** If `f ∈ L²(γ_σ)` is orthogonal to every
> polynomial against `γ_σ`, then `f = 0` a.e. **For every `σ`, including `σ = 0`.** The
> substitution argument needs `σ ≠ 0` — it composes polynomials with `x ↦ σ⁻¹x` — so the
> degenerate case is proved separately and directly: at `σ = 0` the measure is `δ₀`, and
> orthogonality to the constant polynomial `1` already says `f 0 = 0`.
>
> **`hermite_complete_scaled`** — the same with the polynomials replaced by the Hermite family
> **rescaled to the measure**, `x ↦ Hₙ(σ⁻¹x)`. Stated at `σ ≠ 0`, where `σ⁻¹` means something.
>
> **`hermite_orthogonal_scaled`** and **`hermite_norm_sq_scaled`** — and the rescaled family is
> orthogonal against `γ_σ`, with the **same** inner products as at variance one, `∫ HₘHₙ = 0`
> for `m ≠ n` and `∫ Hₙ² = n!`. The same change of variables carries the whole relation across;
> the variance does not appear in the answer.
>
> **`hermite_complete_orthogonal_system_scaled`** — the package, in the same four parts as
> `HermiteCompleteness.hermite_complete_orthogonal_system`: pairwise orthogonal, each of norm²
> `n! ≠ 0`, and complete, at every `σ ≠ 0`.

## What is NOT claimed

**No `MemLp` hypothesis is needed at `σ = 0`, and none is assumed** — `complete_zero` takes only
the orthogonality. That is not a strengthening worth much (`δ₀` makes every function square
integrable) but it is what the statement says, and it is said rather than padded.

**Nothing about `n` dimensions at variance `σ`.** The `HermitePi*` line is at variance one. The
two generalisations are independent and only one of them is done below.

**No Poincaré inequality, no `L²`-Fourier apparatus, no Parseval.** `HermiteCompleteness`
records that the inequality beyond polynomials needs `W^{1,2}` approximation rather than `L²`
approximation; that remains true and this file does not touch it.

**`PoincareScaledBeyond.integral_scaled` is not withdrawn.** `integral_scaled_ae` is a second
lemma with a weaker hypothesis, not a replacement; the original keeps its proof and its uses.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermiteScaledComplete

open HermiteCompleteness GaussianPoincare

/-- The centred Gaussian of variance `σ²`, as Mathlib's own measure. -/
noncomputable def gaussSc (σ : ℝ) : Measure ℝ :=
  gaussianReal 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)

instance isProbabilityMeasure_gaussSc (σ : ℝ) : IsProbabilityMeasure (gaussSc σ) := by
  unfold gaussSc; infer_instance

/-! ## 1. The scaling is a pushforward -/

/-- `γ` pushed along `x ↦ σx` is the variance-`σ²` Gaussian, for **every** `σ`. -/
theorem map_gauss_eq (σ : ℝ) :
    (gauss : Measure ℝ).map (fun x => σ * x) = gaussSc σ := by
  rw [show (gauss : Measure ℝ) = gaussianReal 0 1 from rfl, gaussianReal_map_const_mul σ]
  unfold gaussSc
  congr 1
  · ring
  · ext
    simp

theorem aemeasurable_scale (σ : ℝ) : AEMeasurable (fun x => σ * x) (gauss : Measure ℝ) :=
  (measurable_const_mul σ).aemeasurable

/-- **The change of variables without the `Measurable` hypothesis.**
`PoincareScaledBeyond.integral_scaled` asks for `Measurable h`; an `L²` function supplies only
`AEStronglyMeasurable`, so that version is not usable on the class this file is about. -/
theorem integral_scaled_ae (σ : ℝ) (h : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable h (gaussSc σ)) :
    ∫ x, h x ∂(gaussSc σ) = ∫ x, h (σ * x) ∂gauss := by
  rw [← map_gauss_eq σ] at hmeas ⊢
  exact integral_map (aemeasurable_scale σ) hmeas

theorem memLp_scaled_iff (σ : ℝ) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (gaussSc σ)) :
    MemLp f 2 (gaussSc σ) ↔ MemLp (fun x => f (σ * x)) 2 gauss := by
  rw [← map_gauss_eq σ] at hf ⊢
  exact memLp_map_measure_iff hf (aemeasurable_scale σ)

/-- Vanishing a.e. transfers both ways across the scaling. Proved through `eLpNorm`, because
`ae_map_iff` wants a measurable set and an `L²` function gives only an a.e.-measurable one. -/
theorem ae_eq_zero_iff (σ : ℝ) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (gaussSc σ)) :
    f =ᵐ[gaussSc σ] 0 ↔ (fun x => f (σ * x)) =ᵐ[gauss] 0 := by
  have hf' : AEStronglyMeasurable f ((gauss : Measure ℝ).map (fun x => σ * x)) := by
    rwa [map_gauss_eq σ]
  have hcomp : AEStronglyMeasurable (fun x => f (σ * x)) (gauss : Measure ℝ) :=
    hf'.comp_aemeasurable (aemeasurable_scale σ)
  have hnorm : eLpNorm f 2 (gaussSc σ) = eLpNorm (fun x => f (σ * x)) 2 gauss := by
    rw [← map_gauss_eq σ]
    exact eLpNorm_map_measure hf' (aemeasurable_scale σ)
  have h1 : f =ᵐ[gaussSc σ] 0 ↔ eLpNorm f 2 (gaussSc σ) = 0 :=
    (eLpNorm_eq_zero_iff hf (by norm_num)).symm
  have h2 : (fun x => f (σ * x)) =ᵐ[gauss] 0
      ↔ eLpNorm (fun x => f (σ * x)) 2 gauss = 0 :=
    (eLpNorm_eq_zero_iff hcomp (by norm_num)).symm
  rw [h1, h2, hnorm]

/-! ## 2. Completeness at every variance -/

/-- The degenerate case, proved directly rather than by the substitution: at `σ = 0` the measure
is `δ₀`, and orthogonality to the constant polynomial `1` already forces `f 0 = 0`. -/
theorem complete_zero (f : ℝ → ℝ)
    (horth : ∀ p : ℝ[X], ∫ x, f x * p.eval x ∂(gaussSc 0) = 0) :
    f =ᵐ[gaussSc 0] 0 := by
  have hv : (⟨(0:ℝ) ^ 2, sq_nonneg (0:ℝ)⟩ : NNReal) = 0 := by
    apply NNReal.coe_injective
    simp
  have hdirac : gaussSc 0 = Measure.dirac (0 : ℝ) := by
    unfold gaussSc
    rw [hv]
    exact gaussianReal_zero_var 0
  have h1 := horth 1
  rw [hdirac] at h1 ⊢
  rw [integral_dirac] at h1
  simp only [Polynomial.eval_one, mul_one] at h1
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬ f x = (0 : ℝ → ℝ) x} ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hx (by simpa using h1)
  refine measure_mono_null hsub ?_
  simp

/-- **COMPLETENESS OF THE POLYNOMIALS IN `L²(γ_σ)`, AT EVERY VARIANCE.** If `f` is square
integrable against the centred Gaussian of variance `σ²` and orthogonal there to every
polynomial, then `f = 0` almost everywhere. `σ = 0` is included, by `complete_zero`. -/
theorem polynomials_complete_scaled (σ : ℝ) (f : ℝ → ℝ) (hf : MemLp f 2 (gaussSc σ))
    (horth : ∀ p : ℝ[X], ∫ x, f x * p.eval x ∂(gaussSc σ) = 0) :
    f =ᵐ[gaussSc σ] 0 := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · exact complete_zero f horth
  have hfm : AEStronglyMeasurable f (gaussSc σ) := hf.aestronglyMeasurable
  set g : ℝ → ℝ := fun x => f (σ * x) with hg
  have hgL : MemLp g 2 gauss := (memLp_scaled_iff σ f hfm).mp hf
  have hgorth : ∀ q : ℝ[X], ∫ x, g x * q.eval x ∂gauss = 0 := by
    intro q
    set p : ℝ[X] := q.comp (C σ⁻¹ * X) with hp
    have hkey : ∀ x : ℝ, p.eval (σ * x) = q.eval x := by
      intro x
      rw [hp, Polynomial.eval_comp]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    have hint : AEStronglyMeasurable (fun x => f x * p.eval x) (gaussSc σ) :=
      hfm.mul (Polynomial.continuous p).aestronglyMeasurable
    have := integral_scaled_ae σ (fun x => f x * p.eval x) hint
    rw [horth p] at this
    calc ∫ x, g x * q.eval x ∂gauss
        = ∫ x, f (σ * x) * p.eval (σ * x) ∂gauss := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hg, hkey]
      _ = 0 := this.symm
  have hz : g =ᵐ[gauss] 0 := polynomials_complete g hgL hgorth
  exact (ae_eq_zero_iff σ f hfm).mpr hz

/-- **THE HERMITE FAMILY, RESCALED TO THE MEASURE, IS COMPLETE IN `L²(γ_σ)`.** The polynomials
orthogonal against variance `σ²` are `x ↦ Hₙ(σ⁻¹x)`, and nothing but `0` is orthogonal to all of
them. Stated at `σ ≠ 0`, where `σ⁻¹` means something. -/
theorem hermite_complete_scaled {σ : ℝ} (hσ : σ ≠ 0) (f : ℝ → ℝ) (hf : MemLp f 2 (gaussSc σ))
    (horth : ∀ n : ℕ, ∫ x, f x * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ) = 0) :
    f =ᵐ[gaussSc σ] 0 := by
  have hfm : AEStronglyMeasurable f (gaussSc σ) := hf.aestronglyMeasurable
  set g : ℝ → ℝ := fun x => f (σ * x) with hg
  have hgL : MemLp g 2 gauss := (memLp_scaled_iff σ f hfm).mp hf
  have hgorth : ∀ n : ℕ, ∫ x, g x * (H n).eval x ∂gauss = 0 := by
    intro n
    have hint : AEStronglyMeasurable (fun x => f x * (H n).eval (σ⁻¹ * x)) (gaussSc σ) :=
      hfm.mul (((Polynomial.continuous (H n)).comp (continuous_const.mul continuous_id))
        |>.aestronglyMeasurable)
    have hcv := integral_scaled_ae σ (fun x => f x * (H n).eval (σ⁻¹ * x)) hint
    rw [horth n] at hcv
    calc ∫ x, g x * (H n).eval x ∂gauss
        = ∫ x, f (σ * x) * (H n).eval (σ⁻¹ * (σ * x)) ∂gauss := by
          have hx : ∀ x : ℝ, σ⁻¹ * (σ * x) = x := by
            intro x
            rw [← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hg, hx]
      _ = 0 := hcv.symm
  have hz : g =ᵐ[gauss] 0 := hermite_complete g hgL hgorth
  exact (ae_eq_zero_iff σ f hfm).mpr hz

/-! ## 3. Orthogonality and norms at variance `σ`, by the same change of variables -/

/-- The rescaled Hermite polynomials are pairwise orthogonal against `γ_σ`, with the **same**
inner products as at variance one: the substitution carries the whole relation across. -/
theorem hermite_orthogonal_scaled {σ : ℝ} (hσ : σ ≠ 0) (m n : ℕ) :
    ∫ x, (H m).eval (σ⁻¹ * x) * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ)
      = if m = n then (m.factorial : ℝ) else 0 := by
  have hx : ∀ x : ℝ, σ⁻¹ * (σ * x) = x := by
    intro x
    rw [← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
  have hmeas : AEStronglyMeasurable
      (fun x => (H m).eval (σ⁻¹ * x) * (H n).eval (σ⁻¹ * x)) (gaussSc σ) := by
    fun_prop
  rw [integral_scaled_ae σ _ hmeas]
  rw [show (fun x : ℝ => (H m).eval (σ⁻¹ * (σ * x)) * (H n).eval (σ⁻¹ * (σ * x)))
      = fun x : ℝ => (H m).eval x * (H n).eval x by
    funext x; rw [hx x]]
  exact hermite_orthogonal_gauss m n

theorem hermite_norm_sq_scaled {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    ∫ x, (H n).eval (σ⁻¹ * x) * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ) = (n.factorial : ℝ) := by
  rw [hermite_orthogonal_scaled hσ n n, if_pos rfl]

/-- **THE RESCALED HERMITE POLYNOMIALS ARE A COMPLETE ORTHOGONAL SYSTEM IN `L²(γ_σ)`.** The
variance-`σ²` analogue of `HermiteCompleteness.hermite_complete_orthogonal_system`, in the same
four parts: pairwise orthogonal, each of norm² `n! ≠ 0`, and complete. -/
theorem hermite_complete_orthogonal_system_scaled {σ : ℝ} (hσ : σ ≠ 0) :
    (∀ m n : ℕ, m ≠ n →
        ∫ x, (H m).eval (σ⁻¹ * x) * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ) = 0)
      ∧ (∀ n : ℕ,
          ∫ x, (H n).eval (σ⁻¹ * x) * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ) = (n.factorial : ℝ))
      ∧ (∀ n : ℕ, (n.factorial : ℝ) ≠ 0)
      ∧ (∀ f : ℝ → ℝ, MemLp f 2 (gaussSc σ) →
          (∀ n : ℕ, ∫ x, f x * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ) = 0) →
          f =ᵐ[gaussSc σ] 0) :=
  ⟨fun m n hmn => by rw [hermite_orthogonal_scaled hσ m n, if_neg hmn],
   fun n => hermite_norm_sq_scaled hσ n,
   fun n => Nat.cast_ne_zero.mpr n.factorial_ne_zero,
   fun f hf horth => hermite_complete_scaled hσ f hf horth⟩

end HermiteScaledComplete
