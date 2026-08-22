import TransferPowerSum

/-!
# The spectral form of a two-point trace

`IsingTwoPoint.corr2Sep_eq_trace_div` puts the strip's two-point function in the shape the
classical account uses — `tr (D · Tᵏ · D · Tᴹ⁺¹⁻ᵏ) / tr (Tᴹ⁺¹)` — and every textbook then does the
same next thing: **diagonalise `T` and read the `k`-dependence off the eigenvalues.** That step is
what this file supplies, for an arbitrary Hermitian matrix and arbitrary insertions.

`TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` is the one-matrix case, `tr (Aᵏ) = ∑ λᵢᵏ`.
This is the case with two insertions, where the answer is a **double** sum and the two exponents
sit on different eigenvalues — which is precisely why a two-point function decays and a partition
function does not.

## What is proved

* **`trace_mul_pow_mul_pow`** — for Hermitian `A` with eigenvector unitary `U`,
  `tr (D · Aᵏ · E · Aᵐ) = ∑ₚ ∑_q Bₚq · λ_qᵏ · C_qₚ · λₚᵐ`, where `B = U* D U` and `C = U* E U`
  are the insertions read in the eigenbasis;
* **`isHermitian_conj`** — that change of basis preserves Hermitian-ness, so at `E = D` the
  coefficient `Bₚq · B_qₚ` is `Bₚq · conj Bₚq`;
* **`trace_mul_pow_mul_pow_self`** — hence at `E = D` the coefficients are `‖Bₚq‖²`, **real and
  non-negative**. That is the fact a decay estimate needs: the double sum has no cancellation
  between terms, so it is controlled by its largest eigenvalue ratio.

**Absent from Mathlib by name**, probed 2026-08-22 against the environment dump:
`Matrix.trace_mul_pow`, `Matrix.IsHermitian.trace_mul_pow`, `trace_conj_pow`,
`Matrix.trace_mul_pow_mul_pow` — zero each.

## What this does NOT do

**It is not a decay statement and not a mass gap.** It is the identity a decay statement is proved
from; turning it into decay needs the top eigenvalue's simplicity and dominance, and for the strip
it needs those **uniformly in the width**, which is `WALLS` §W4 §6 item 2's open sentence. And
`IsingTwoPoint.corr2Sep_neg` already shows what the eventual statement can look like: symmetric
about the midpoint, so decay only up to it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermitianTwoPointTrace

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. The insertions, read in the eigenbasis -/

omit [DecidableEq n] in
/-- **CONJUGATING BY A MATRIX PRESERVES HERMITIAN-NESS.** -/
theorem isHermitian_conj {D : Matrix n n 𝕜} (hD : D.IsHermitian) (U : Matrix n n 𝕜) :
    (Uᴴ * D * U).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
    Matrix.mul_assoc]

/-! ## 2. A trace of two diagonal insertions, before any spectral theory -/

/-- **THE DOUBLE SUM, FOR ARBITRARY MATRICES AND ARBITRARY DIAGONALS.** No Hermitian hypothesis
and no eigenvalues: this is the shape, and §3 supplies the diagonals. -/
theorem trace_mul_diagonal_mul_diagonal (X Y : Matrix n n 𝕜) (d e : n → 𝕜) :
    (X * Matrix.diagonal d * Y * Matrix.diagonal e).trace
      = ∑ p, ∑ q, X p q * d q * (Y q p * e p) := by
  have h : X * Matrix.diagonal d * Y * Matrix.diagonal e
      = (X * Matrix.diagonal d) * (Y * Matrix.diagonal e) := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun q _ => by rw [Matrix.mul_diagonal, Matrix.mul_diagonal]

/-! ## 3. The two-point trace, diagonalised -/

/-- **THE SPECTRAL FORM OF A TWO-POINT TRACE.** The two exponents land on **different**
eigenvalues, which is the whole reason a two-point function carries a ratio and a partition
function does not. -/
theorem trace_mul_pow_mul_pow {A : Matrix n n 𝕜} (hA : A.IsHermitian) (D E : Matrix n n 𝕜)
    (k m : ℕ) :
    (D * A ^ k * E * A ^ m).trace
      = ∑ p, ∑ q, ((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ * D
              * (hA.eigenvectorUnitary : Matrix n n 𝕜)) p q
            * ((hA.eigenvalues q : ℝ) : 𝕜) ^ k
            * (((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ * E
              * (hA.eigenvectorUnitary : Matrix n n 𝕜)) q p
            * ((hA.eigenvalues p : ℝ) : 𝕜) ^ m) := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜) with hU
  have hpow : ∀ j : ℕ,
      A ^ j = U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ j) * Uᴴ := by
    intro j
    have h : A ^ j = (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜)) hA.eigenvectorUnitary
        (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) ^ j)) := by
      rw [← Matrix.diagonal_pow, map_pow, ← hA.spectral_theorem]
    rw [h, Unitary.conjStarAlgAut_apply]
    rfl
  rw [hpow k, hpow m]
  have hgroup : D * (U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ k) * Uᴴ) * E
        * (U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ m) * Uᴴ)
      = (D * U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ k) * Uᴴ * E * U
          * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ m)) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [hgroup, Matrix.trace_mul_comm]
  have hre : Uᴴ * (D * U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ k) * Uᴴ * E
        * U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ m))
      = (Uᴴ * D * U) * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ k)
          * (Uᴴ * E * U) * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜) ^ m) := by
    simp only [Matrix.mul_assoc]
  rw [hre, trace_mul_diagonal_mul_diagonal]

/-- **AND AT `E = D` THE COEFFICIENTS ARE `‖Bₚq‖²`** — real, non-negative, and therefore giving a
double sum with no cancellation between its terms. That is what a decay estimate needs. -/
theorem trace_mul_pow_mul_pow_self {A : Matrix n n 𝕜} (hA : A.IsHermitian) {D : Matrix n n 𝕜}
    (hD : D.IsHermitian) (k m : ℕ) :
    (D * A ^ k * D * A ^ m).trace
      = ∑ p, ∑ q, ((‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ * D
              * (hA.eigenvectorUnitary : Matrix n n 𝕜)) p q‖ : 𝕜)) ^ 2
            * (((hA.eigenvalues q : ℝ) : 𝕜) ^ k * ((hA.eigenvalues p : ℝ) : 𝕜) ^ m) := by
  rw [trace_mul_pow_mul_pow hA D D k m]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have hB := isHermitian_conj hD (hA.eigenvectorUnitary : Matrix n n 𝕜)
  set B := (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ * D * (hA.eigenvectorUnitary : Matrix n n 𝕜)
    with hBdef
  have hqp : B q p = (starRingEnd 𝕜) (B p q) := (hB.apply q p).symm
  have hmc : B p q * (starRingEnd 𝕜) (B p q) = ((‖B p q‖ : 𝕜)) ^ 2 := RCLike.mul_conj _
  rw [hqp]
  linear_combination (((hA.eigenvalues q : ℝ) : 𝕜) ^ k * ((hA.eigenvalues p : ℝ) : 𝕜) ^ m) * hmc

end HermitianTwoPointTrace
