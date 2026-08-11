import IsingTransfer2D
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The symmetrised two-dimensional transfer matrix

`WALLS.md` §W4.0's item 2 is *separating the top eigenvalue* of the two-dimensional transfer
matrix, and it is the wall's remaining hard step. `IsingTransfer2D` built the matrix, and reading
it back shows the first obstacle is not the hard one at all:

**`transfer2` is not symmetric.** Its entry `exp (β (intra σ + inter σ τ))` carries the *source*
column's own bonds and not the target's, so `T σ τ ≠ T τ σ`. Every piece of finite-dimensional
spectral theory in Mathlib — `IsHermitian.eigenvalues`, `spectral_theorem`, real eigenvalues at all
— is out of reach for it, and that is a fact about the presentation rather than about the model.

This file applies the textbook remedy.

> **`transferSym β n = D · W · D`**, with `D` diagonal carrying `exp (β · intra σ / 2)` — half of
> each column's own weight, given to each side — and `W σ τ = exp (β · inter σ τ)` the horizontal
> weight, which is symmetric because `inter` is.
>
> **`transferSym_isHermitian`** — so the spectrum is real and Mathlib's spectral theorem applies.
>
> **`trace_pow_mul_comm`** — `tr ((AB)ᵏ) = tr ((BA)ᵏ)` for any two square matrices. Not in Mathlib
> under any name probed; proved here from `A · (BA)ᵏ = (AB)ᵏ · A` and `trace_mul_comm`.
>
> **`partition2_eq_trace_sym`** — and therefore **the partition function is the trace of a power of
> a symmetric matrix**. Nothing about the model changed; what changed is that the object carrying it
> now has a spectrum one is allowed to talk about.

## What this does NOT do

**It does not separate the top eigenvalue, and so it does not close item 2.** Having a real spectrum
is not having a gap. What remains is exactly Perron–Frobenius — that a strictly positive matrix has
a simple largest eigenvalue strictly dominating the rest — and that theorem is **absent from
Mathlib** (`PerronFrobenius`/`perronFrobenius`: zero files, probed 2026-08-11) and is not proved
here. `IsingTransfer2D.transfer2_pos` records the positivity it would consume; `transferSym_pos`
below records that symmetrising does not destroy it.

**No eigenvalue is computed, no gap is bounded, and no limit in the width is taken.** The free
energy does not appear.

**And this is a change of presentation, not of content.** `transferSym` and `transfer2` are
conjugate by a diagonal matrix, which is why their trace powers agree; the file proves that rather
than assuming it.
-/

namespace IsingTransferSym

open Finset Real IsingTransfer2D

variable {n : ℕ}

/-! ## 1. A general trace fact, absent from Mathlib -/

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommRing R]

/-- `A · (B·A)ᵏ = (A·B)ᵏ · A`. The bookkeeping behind every "trace is cyclic" argument about
powers. -/
theorem mul_pow_swap (A B : Matrix α α R) :
    ∀ k : ℕ, A * (B * A) ^ k = (A * B) ^ k * A
  | 0 => by simp
  | k + 1 => by
    calc A * (B * A) ^ (k + 1) = A * ((B * A) * (B * A) ^ k) := by rw [pow_succ']
      _ = (A * B) * (A * (B * A) ^ k) := by simp [Matrix.mul_assoc]
      _ = (A * B) * ((A * B) ^ k * A) := by rw [mul_pow_swap A B k]
      _ = (A * B) ^ (k + 1) * A := by rw [pow_succ']; simp [Matrix.mul_assoc]

/-- **`tr ((AB)ᵏ) = tr ((BA)ᵏ)`.** Probed 2026-08-11 and absent from Mathlib: `trace_pow_mul_comm`,
`Matrix.trace_pow` and `Matrix.pow_apply` all return nothing. `Matrix.trace_mul_comm` is the `k = 1`
case and is what this is built from. -/
theorem trace_pow_mul_comm (A B : Matrix α α R) :
    ∀ k : ℕ, Matrix.trace ((A * B) ^ k) = Matrix.trace ((B * A) ^ k)
  | 0 => by simp
  | k + 1 => by
    calc Matrix.trace ((A * B) ^ (k + 1))
        = Matrix.trace (((A * B) ^ k * A) * B) := by rw [pow_succ]; simp [Matrix.mul_assoc]
      _ = Matrix.trace ((A * (B * A) ^ k) * B) := by rw [mul_pow_swap]
      _ = Matrix.trace (B * (A * (B * A) ^ k)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B * A) ^ (k + 1)) := by rw [pow_succ']; simp [Matrix.mul_assoc]

/-! ## 2. The symmetrised matrix -/

/-- `inter` is symmetric, which is what lets the horizontal weight be split evenly. -/
theorem inter_comm (σ τ : Col n) : inter σ τ = inter τ σ := by
  simp only [inter]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Half of each column's own weight. -/
noncomputable def halfIntra (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  Matrix.diagonal fun σ => exp (β * intra σ / 2)

/-- The horizontal weight, symmetric. -/
noncomputable def horiz (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  fun σ τ => exp (β * inter σ τ)

/-- **THE SYMMETRISED TRANSFER MATRIX.** Each column's own weight is split in half and given to
both sides, which is the standard way to make a transfer matrix Hermitian without changing what it
computes. -/
noncomputable def transferSym (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  halfIntra β n * horiz β n * halfIntra β n

theorem horiz_pos (β : ℝ) (σ τ : Col n) : 0 < horiz β n σ τ := exp_pos _

/-- Its entries, written out: half the source column's weight, the horizontal weight, half the
target column's. -/
theorem transferSym_apply (β : ℝ) (σ τ : Col n) :
    transferSym β n σ τ
      = exp (β * intra σ / 2) * exp (β * inter σ τ) * exp (β * intra τ / 2) := by
  simp [transferSym, halfIntra, horiz, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Symmetrising does not destroy positivity — the hypothesis Perron–Frobenius would consume. -/
theorem transferSym_pos (β : ℝ) (σ τ : Col n) : 0 < transferSym β n σ τ := by
  rw [transferSym_apply]
  positivity

/-- **AND IT IS HERMITIAN**, so its eigenvalues are real and Mathlib's spectral theorem applies.
Over `ℝ` this is transpose-invariance: the diagonal factors are their own transposes and `horiz` is
symmetric by `inter_comm`. -/
theorem transferSym_isHermitian (β : ℝ) (n : ℕ) :
    Matrix.IsHermitian (transferSym β n) := by
  ext σ τ
  simp only [Matrix.conjTranspose_apply, star_trivial, transferSym_apply, inter_comm τ σ]
  ring

/-! ## 3. The trace powers agree, so the partition function is unchanged -/

/-- `transfer2` is the diagonal weight applied on one side only. -/
theorem transfer2_eq (β : ℝ) (n : ℕ) :
    transfer2 β n = (halfIntra β n * halfIntra β n) * horiz β n := by
  ext σ τ
  simp only [transfer2, halfIntra, horiz, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
    ← Real.exp_add]
  ring_nf

/-- **THE TRACE POWERS AGREE.** Both matrices are `D·W·D` and `D²·W` for the same `D` and `W`, and
`trace_pow_mul_comm` moves the leading factor to the back. So symmetrising changes the matrix and
not one number this file cares about. -/
theorem trace_transferSym_pow (β : ℝ) (n k : ℕ) :
    Matrix.trace (transferSym β n ^ k) = Matrix.trace (transfer2 β n ^ k) := by
  rw [transfer2_eq, transferSym, Matrix.mul_assoc]
  rw [trace_pow_mul_comm (halfIntra β n) (horiz β n * halfIntra β n) k,
    trace_pow_mul_comm (halfIntra β n * halfIntra β n) (horiz β n) k]
  rw [Matrix.mul_assoc]

/-- **THE PARTITION FUNCTION IS THE TRACE OF A POWER OF A SYMMETRIC MATRIX.** The physics is
`IsingTransfer2D.partition2_eq_trace`; what this adds is that the operator carrying it may now be
handed to spectral theory.

**It is still not a gap.** See the header: what remains is Perron–Frobenius, which Mathlib does not
have and this file does not prove. -/
theorem partition2_eq_trace_sym (β : ℝ) (n M : ℕ) :
    partition2 β n M = Matrix.trace (transferSym β n ^ (M + 1)) := by
  rw [trace_transferSym_pow, partition2_eq_trace]

/-- **AND THEREFORE THE PARTITION FUNCTION IS A SUM OF REAL EIGENVALUES.** This is what
symmetrising buys, stated: `transfer2` is not Hermitian, so nothing in Mathlib's spectral theory
applies to it, and `partition2` was a trace of a matrix with no accessible spectrum. It is now a sum
over an eigenvalue family of a Hermitian matrix.

**Read the statement carefully — these are the eigenvalues of `T^{M+1}`, not the `(M+1)`-st
powers of the eigenvalues of `T`.** Getting from one to the other is the spectral mapping theorem,
which is **not applied here**; the honest content is that the partition function is a sum of real
numbers each of which is an eigenvalue of a Hermitian matrix, which it was not before. -/
theorem partition2_eq_sum_eigenvalues (β : ℝ) (n M : ℕ) :
    partition2 β n M
      = ∑ i, ((transferSym_isHermitian β n).pow (M + 1)).eigenvalues i := by
  rw [partition2_eq_trace_sym]
  exact Matrix.IsHermitian.trace_eq_sum_eigenvalues
    ((transferSym_isHermitian β n).pow (M + 1))

end IsingTransferSym
