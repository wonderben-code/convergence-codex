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

end HermiteScaledHilbertBasis
