import HermiteScaledComplete
import HermiteHilbertBasis

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

/-!
# A Hilbert basis of `L²(γ_σ)`, at every nonzero variance

`HermiteHilbertBasis` bundled the estate's orthogonality and completeness into a Mathlib
`HilbertBasis ℕ ℝ (Lp ℝ 2 γ)` — **at variance one**. `HermiteScaledComplete` then proved the
orthogonality, the norms and the completeness at every variance. **The bundling was never
repeated there**, and the gap shows: `TextbookSobolevScaled` reaches a scaled conclusion by
transporting each function back to variance one and invoking the variance-one basis, because
there is no scaled basis to invoke.

This file supplies it. Everything below is the variance-one construction with `γ` replaced by
`γ_σ` and the three inputs replaced by their scaled versions; no new analysis happens here, which
is the point of a bundling file.

## What is proved

> **`memLp_Hsc`** — `x ↦ Hₙ(σ⁻¹x)` is in `L²(γ_σ)`, and **not by transport**: it is a polynomial,
> and `GaussianPoincare.memLp_polynomial_gaussianReal` is already stated at every mean and every
> variance. The rescaled Hermite function is `(H n).comp (C σ⁻¹ * X)` evaluated.
>
> **`inner_toLp_of`** — the `L²` inner product of two `toLp`s is the integral of the product, at
> **any** measure on `ℝ`. This is `HermiteParseval.inner_toLp` with `gauss` generalised away; its
> proof never used the measure, and the original is not withdrawn.
>
> **`orthonormal_eHs`** — the normalised rescaled family `Hₙ(σ⁻¹·)/√(n!)` is orthonormal in
> `L²(γ_σ)`, from `HermiteScaledComplete.hermite_orthogonal_scaled`. The normalisation is the
> variance-one one, because the inner products are the variance-one ones.
>
> **`orthogonal_eq_bot`** — its span has trivial orthogonal complement, from
> `HermiteScaledComplete.hermite_complete_scaled`.
>
> **`hermiteBasisScaled`** — **the `HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussSc σ))`**, for every `σ ≠ 0`,
> with `hermiteBasisScaled_apply` naming its vectors.

## What is NOT claimed

**`σ = 0` is excluded**, as it must be: at variance zero the measure is `δ₀`, `L²(δ₀)` is
one-dimensional, and an `ℕ`-indexed orthonormal family cannot exist in it. This is not a gap to
be filled later — the statement is false there, and saying which is which matters.
`HermiteScaledComplete.polynomials_complete_scaled` still covers `σ = 0`; **completeness and a
basis are different statements**, and only the first survives the degeneration.

**No coefficient dictionary.** `HermiteHilbertBasis` goes on to identify `repr` with
`HermiteBessel.coeff` and re-derive Parseval. That dictionary is defined at variance one and is
**not** transported here, so there is no scaled `repr_apply` and no scaled Parseval below.

> **⚠ Superseded within the hour, 2026-08-29, by §4 of this same file.** `coeffSc` is the scaled
> coefficient — **a different function from `HermiteBessel.coeff`, not a transport of it**, since
> its integral is against `γ_σ` — and `repr_apply_scaled` and `parseval_scaled` are the dictionary
> and the identity. The paragraph is kept (`ERRATUM 94`) because it was true of the file as first
> written and because the reason it gives is still the right one: the variance-one dictionary is
> **not** transported, and nothing below reuses it. **One asymmetry with the variance-one file is
> worth naming**: there, Parseval off the basis is a *consistency check*, because
> `HermiteParseval.parseval` proves it by hand as well. Here there is no hand proof to agree with,
> so `parseval_scaled` rests on the bundling alone.

**Nothing in `n` dimensions.** `HermitePiScaledComplete` has the completeness; the `HermitePi*`
basis line is at variance one, and the scaled `n`-dimensional basis is not built here.

**Nothing is withdrawn.** `HermiteHilbertBasis.hermiteBasis` and `HermiteParseval.inner_toLp`
keep their proofs and their uses.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermiteScaledHilbertBasis

open HermiteCompleteness GaussianPoincare HermiteScaledComplete HermiteHilbertBasis

variable {σ : ℝ}

/-! ## 1. The rescaled Hermite function is a polynomial, so `L²` membership is free -/

/-- `Hₙ(σ⁻¹ ·)`, as a polynomial rather than as a composition of functions. -/
noncomputable def Hsc (σ : ℝ) (n : ℕ) : ℝ[X] := (H n).comp (C σ⁻¹ * X)

theorem eval_Hsc (σ : ℝ) (n : ℕ) (x : ℝ) : (Hsc σ n).eval x = (H n).eval (σ⁻¹ * x) := by
  rw [Hsc, Polynomial.eval_comp]
  simp

theorem memLp_Hsc (σ : ℝ) (n : ℕ) :
    MemLp (fun x => (H n).eval (σ⁻¹ * x)) 2 (gaussSc σ) := by
  have h := memLp_polynomial_gaussianReal (Hsc σ n) 0 (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal)
  simpa only [eval_Hsc] using h

/-- `Hₙ(σ⁻¹ ·)` as an element of `L²(γ_σ)`. -/
noncomputable def HLs (σ : ℝ) (n : ℕ) : Lp ℝ 2 (gaussSc σ) :=
  (memLp_Hsc σ n).toLp _

/-- The inner product of two `toLp`s is the integral of the product, **at any measure**. This is
`HermiteParseval.inner_toLp` with `gauss` generalised away — its proof never looked at the
measure. The original keeps its proof and its uses. -/
theorem inner_toLp_of {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  exact mul_comm (g x) (f x)

theorem inner_HLs_HLs (hσ : σ ≠ 0) (m n : ℕ) :
    inner ℝ (HLs σ m) (HLs σ n) = if m = n then (m.factorial : ℝ) else 0 := by
  simp only [HLs]
  rw [inner_toLp_of]
  exact hermite_orthogonal_scaled hσ m n

/-! ## 2. Orthonormal, and complete -/

/-- The normalised rescaled Hermite system. The normalisation is the variance-one one, because
the inner products are the variance-one ones. -/
noncomputable def eHs (σ : ℝ) (n : ℕ) : Lp ℝ 2 (gaussSc σ) :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • HLs σ n

theorem orthonormal_eHs (hσ : σ ≠ 0) : Orthonormal ℝ (eHs σ) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [eHs, eHs, real_inner_smul_left, real_inner_smul_right, inner_HLs_HLs hσ]
  split_ifs with h
  · subst h
    have hne := sqrt_factorial_ne_zero m
    field_simp
    exact (Real.sq_sqrt (Nat.cast_nonneg (m.factorial))).symm
  · ring

theorem orthogonal_eq_bot (hσ : σ ≠ 0) :
    (Submodule.span ℝ (Set.range (eHs σ)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  have hmem : ∀ n : ℕ, eHs σ n ∈ Submodule.span ℝ (Set.range (eHs σ)) := fun n =>
    Submodule.subset_span ⟨n, rfl⟩
  have hz : ∀ n : ℕ, inner ℝ (HLs σ n) F = 0 := by
    intro n
    have h1 : inner ℝ (eHs σ n) F = 0 := (Submodule.mem_orthogonal _ _).mp hF _ (hmem n)
    rw [eHs, real_inner_smul_left] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (inv_eq_zero.mp h) (sqrt_factorial_ne_zero n)
    · exact h
  have hae : (F : ℝ → ℝ) =ᵐ[gaussSc σ] 0 := by
    refine hermite_complete_scaled hσ _ (Lp.memLp F) fun n => ?_
    have hFeq : (Lp.memLp F).toLp (F : ℝ → ℝ) = F := Lp.toLp_coeFn F (Lp.memLp F)
    have h2 : inner ℝ (HLs σ n) F
        = ∫ x, (H n).eval (σ⁻¹ * x) * (F : ℝ → ℝ) x ∂(gaussSc σ) := by
      conv_lhs => rw [← hFeq]
      simp only [HLs]
      rw [inner_toLp_of]
    rw [hz n] at h2
    calc ∫ x, (F : ℝ → ℝ) x * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ)
        = ∫ x, (H n).eval (σ⁻¹ * x) * (F : ℝ → ℝ) x ∂(gaussSc σ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      _ = 0 := h2.symm
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae

/-! ## 3. The basis -/

/-- **THE RESCALED HERMITE FUNCTIONS ARE A HILBERT BASIS OF `L²(γ_σ)`**, at every `σ ≠ 0`. The
variance-one bundling, with the three scaled inputs in place of the standard ones. -/
noncomputable def hermiteBasisScaled (hσ : σ ≠ 0) : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussSc σ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eHs hσ) (orthogonal_eq_bot hσ)

theorem hermiteBasisScaled_apply (hσ : σ ≠ 0) (n : ℕ) :
    hermiteBasisScaled hσ n = eHs σ n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (orthonormal_eHs hσ)
    (orthogonal_eq_bot hσ)) n

/-- Density in norm form, kept as an export exactly as the variance-one file keeps it: it is not
on the critical path, `mkOfOrthogonalEqBot` consuming `orthogonal_eq_bot` directly. -/
theorem span_dense (hσ : σ ≠ 0) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (eHs σ))).topologicalClosure :=
  le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr (orthogonal_eq_bot hσ)).symm

/-! ## 4. The coefficient dictionary and Parseval, at variance `σ` -/

/-- The `n`-th **scaled** Hermite coefficient: the pairing against `Hₙ(σ⁻¹·)` in `L²(γ_σ)`,
normalised by `n!`. The variance-one `HermiteBessel.coeff` is this at `σ = 1`, but it is a
different function and is not reused — its integral is against `γ`, not `γ_σ`. -/
noncomputable def coeffSc (σ : ℝ) (n : ℕ) (F : ℝ → ℝ) : ℝ :=
  (∫ x, F x * (H n).eval (σ⁻¹ * x) ∂(gaussSc σ)) / (n.factorial : ℝ)

theorem inner_HLs (σ : ℝ) (n : ℕ) (F : Lp ℝ 2 (gaussSc σ)) :
    inner ℝ (HLs σ n) F = (n.factorial : ℝ) * coeffSc σ n (F : ℝ → ℝ) := by
  have hFeq : (Lp.memLp F).toLp (F : ℝ → ℝ) = F := Lp.toLp_coeFn F (Lp.memLp F)
  have h1 : inner ℝ (HLs σ n) F
      = ∫ x, (H n).eval (σ⁻¹ * x) * (F : ℝ → ℝ) x ∂(gaussSc σ) := by
    conv_lhs => rw [← hFeq]
    simp only [HLs]
    rw [inner_toLp_of]
  rw [h1, coeffSc, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem repr_apply_scaled (hσ : σ ≠ 0) (F : Lp ℝ 2 (gaussSc σ)) (n : ℕ) :
    ((hermiteBasisScaled hσ).repr F : ℕ → ℝ) n
      = Real.sqrt (n.factorial : ℝ) * coeffSc σ n (F : ℝ → ℝ) := by
  have hne := sqrt_factorial_ne_zero n
  have key : (Real.sqrt (n.factorial : ℝ))⁻¹ * (n.factorial : ℝ)
      = Real.sqrt (n.factorial : ℝ) := by
    refine mul_left_cancel₀ hne ?_
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul, sqrt_factorial_mul_self]
  rw [HilbertBasis.repr_apply_apply, hermiteBasisScaled_apply, eHs, real_inner_smul_left,
    inner_HLs, ← mul_assoc, key]

/-- **PARSEVAL AT VARIANCE `σ²`.** Read off the basis, exactly as the variance-one file reads its
Parseval off `hermiteBasis` — and unlike that one this is **not** a re-derivation of anything:
the estate has no hand proof of the scaled identity to check it against. -/
theorem parseval_scaled (hσ : σ ≠ 0) (F : Lp ℝ 2 (gaussSc σ)) :
    ‖F‖ ^ 2 = ∑' n : ℕ, (n.factorial : ℝ) * coeffSc σ n (F : ℝ → ℝ) ^ 2 := by
  have h0 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (by rw [h0]; norm_num) ((hermiteBasisScaled hσ).repr F)
  rw [h0] at hnorm
  simp only [Real.rpow_natCast] at hnorm
  rw [← (hermiteBasisScaled hσ).repr.norm_map F, hnorm]
  refine tsum_congr fun n => ?_
  rw [repr_apply_scaled hσ, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

end HermiteScaledHilbertBasis
