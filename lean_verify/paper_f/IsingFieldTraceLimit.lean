/-
  IsingFieldTraceLimit.lean — the magnetisation at the top eigenvector is a limit
  of trace ratios, at any cross-section, with no eigenvector anywhere.

  WHY. `IsingFieldNonzero` settled, at ONE site, that the magnetisation in a field
  is not zero — by pinning it with two traces, which works because two indices and
  two equations are the same number. Its closing note says what that argument does
  not reach: at `2^k` indices the same two traces constrain a SUM rather than
  pinning a number.

  THIS IS THE RUNG THAT DOES REACH IT, AND IT USES ALL THE POWERS INSTEAD OF TWO.
  `B_{p₀p₀}` is the limit of `trace (D · Tᵐ) / λ_{p₀}ᵐ`. The numerator is
  `∑_σ spin (σ v) · (Tᵐ)_{σσ}` — **a sum of matrix entries at every `m`, with no
  spectral quantity in it** — and the denominator is a power of one number. So the
  magnetisation is determined by the diagonal of the powers of the transfer matrix
  and nothing else.

  WHAT IT BUYS AND WHAT IT DOES NOT. It converts *"compute a top eigenvector"* —
  which is what `IsingSlabField`'s item said was needed and what
  `IsingFieldNonzero` avoided by an accident of size — into *"bound a sequence of
  trace ratios from below"*. That is a different kind of question and a more
  tractable-looking one, and **it is not answered here**: nothing below produces
  such a bound for any cross-section of size two or more. The open question is
  unchanged in content and better positioned, which is what a rung is.

  THE ENGINE IS ALREADY GENERAL. `TransferPowerSum.tendsto_weighted_ratio_pow`
  needs the top eigenvalue to be simple and dominant, which holds for any
  Hermitian matrix with strictly positive entries — so all of this is stated for
  `transferG β E` at an arbitrary `E`, field or no field, with no flip hypothesis
  of any kind.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingFieldNonzero

namespace IsingFieldTraceLimit

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingTwoPointSpectral IsingSlabTransfer IsingSlabFlip
open IsingSlabMagnetisation IsingSlabField IsingFieldNonzero

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Conjugation, at every power -/

/-- **THE EIGENVALUE DIAGONAL, AT EVERY POWER.** `conj_transferG` is the case `m = 1`; the rest is
`Units.conj_pow'` with the unitary as the unit. -/
theorem conj_transferG_pow (β : ℝ) (E : Cross V → ℝ) (m : ℕ) :
    (eigU β E)ᴴ * transferG β E ^ m * eigU β E
      = Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q ^ m := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  have hdp : (Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q) ^ m
      = Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q ^ m := by
    rw [Matrix.diagonal_pow]; rfl
  rw [← hdp, ← conj_transferG β E]
  exact (Units.conj_pow' ⟨eigU β E, (eigU β E)ᴴ, hU, hUs⟩ (transferG β E) m).symm

/-- **THE TRACE IDENTITY, FOR ANY MATRIX IN THE MIDDLE.** `trace_spinEigenG_mul_diagonal` is this
at `X = transferG β E`; nothing in the proof cared what `X` was. -/
theorem trace_spinEigenG_mul_conj (β : ℝ) (E : Cross V → ℝ) (v : V)
    (X : Matrix (Cross V) (Cross V) ℝ) :
    (spinEigenG β E v * ((eigU β E)ᴴ * X * eigU β E)).trace
      = ((Matrix.diagonal fun σ : Cross V => spin (σ v)) * X).trace := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [spinEigenG, conj_mul_conj _ _ _ _ hU, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- **SO THE WEIGHTED POWER SUM OF THE EIGENVALUES IS A SUM OF MATRIX ENTRIES.** The left side
carries the eigenbasis; the right side is `∑_σ spin (σ v) · (Tᵐ)_{σσ}` and carries none. -/
theorem sum_spinEigenG_mul_eigenvalues_pow (β : ℝ) (E : Cross V → ℝ) (v : V) (m : ℕ) :
    (∑ p, spinEigenG β E v p p * (transferG_isHermitian β E).eigenvalues p ^ m)
      = ∑ σ : Cross V, spin (σ v) * (transferG β E ^ m) σ σ := by
  have h := trace_spinEigenG_mul_conj β E v (transferG β E ^ m)
  rw [conj_transferG_pow β E m] at h
  have hl : (spinEigenG β E v
        * Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q ^ m).trace
      = ∑ p, spinEigenG β E v p p * (transferG_isHermitian β E).eigenvalues p ^ m := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  have hr : ((Matrix.diagonal fun σ : Cross V => spin (σ v)) * transferG β E ^ m).trace
      = ∑ σ : Cross V, spin (σ v) * (transferG β E ^ m) σ σ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  rw [← hl, ← hr, h]

/-! ## 2. The magnetisation as a limit of trace ratios -/

/-- **THE MAGNETISATION AT THE TOP EIGENVECTOR IS A LIMIT OF TRACE RATIOS.**

`spinEigenG β E v p₀ p₀ = lim_m (∑_σ spin (σ v) · (Tᵐ)_{σσ}) / λ_{p₀}ᵐ`, at every finite
cross-section, for every energy `E`, with **no flip hypothesis and no eigenvector**. The numerator
is a sum of diagonal entries of powers of the transfer matrix.

**What this does not do.** It gives no lower bound on the limit, so it settles nothing about
whether the magnetisation vanishes at a cross-section of size two or more. What it does is replace
the question *"what is the top eigenvector"* by *"how do the diagonal entries of `Tᵐ` grow"*, which
is a question about the matrix and not about its spectral decomposition. -/
theorem spinEigenG_top_eq_limit [Nonempty V] (β : ℝ) (E : Cross V → ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun m : ℕ =>
        (∑ σ : Cross V, spin (σ v) * (transferG β E ^ (m + 1)) σ σ)
          / (transferG_isHermitian β E).eigenvalues p₀ ^ (m + 1))
      atTop (𝓝 (spinEigenG β E v p₀ p₀)) := by
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hlim := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => spinEigenG β E v p p)
  refine Tendsto.congr (fun m => ?_) hlim
  rw [← sum_spinEigenG_mul_eigenvalues_pow β E v (m + 1), Finset.sum_div]
  exact Finset.sum_congr rfl fun p _ => by rw [div_pow, ← mul_div_assoc]

/-! ## 3. The one-site case, recovered

`ERRATUM 201`: the general statement is instantiated where the estate can already evaluate it, so
that the limit is known to be computing the right number. -/

/-- **AT ONE SITE IN A UNIT FIELD THE LIMIT IS NOT ZERO**, because `IsingFieldNonzero` says the
number it converges to is not. Stated so that the two arguments are visibly about one quantity and
not two: the two-trace argument names it, this one exhibits it as a limit of entry sums. -/
theorem field_limit_ne_zero {p₀ : Cross (Fin 1)}
    (hp₀ : ∀ j, (transferG_isHermitian 1 (fieldE (V := Fin 1) 1)).eigenvalues j
      ≤ (transferG_isHermitian 1 (fieldE (V := Fin 1) 1)).eigenvalues p₀) :
    Tendsto (fun m : ℕ =>
        (∑ σ : Cross (Fin 1),
            spin (σ 0) * (transferG 1 (fieldE (V := Fin 1) 1) ^ (m + 1)) σ σ)
          / (transferG_isHermitian 1 (fieldE (V := Fin 1) 1)).eigenvalues p₀ ^ (m + 1))
      atTop (𝓝 (spinEigenG 1 (fieldE (V := Fin 1) 1) 0 p₀ p₀))
    ∧ spinEigenG 1 (fieldE (V := Fin 1) 1) 0 p₀ p₀ ≠ 0 :=
  ⟨spinEigenG_top_eq_limit 1 (fieldE (V := Fin 1) 1) 0 hp₀, field_spinEigen_diag_ne_zero p₀⟩

end IsingFieldTraceLimit
