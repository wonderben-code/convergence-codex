import IsingTransfer2D
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Quaternion

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
> **`trace_pow_mul_comm`** — `tr ((AB)ᵏ) = tr ((BA)ᵏ)` for any two square matrices. Absent from
> Mathlib by name and, re-probed 2026-08-11, by shape: nothing in Mathlib puts `trace` of a power on
> both sides of an equation. Proved here from `A · (BA)ᵏ = (AB)ᵏ · A` and `trace_mul_comm`.
>
> **And stated over `CommSemiring`, not `CommRing`** — see §1, where the first draft's hypotheses
> were both too strong and where its hand proof of `A · (BA)ᵏ = (AB)ᵏ · A` turned out to duplicate
> a Mathlib lemma living outside the `Matrix` namespace.
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

⚠ **«WHAT REMAINS IS EXACTLY PERRON–FROBENIUS» IS SUPERSEDED, 22 AUGUST; THE PARAGRAPH IS KEPT PER
`ERRATUM 94`.** Every sentence of it remains true **of this file** — nothing below separates
anything — and the Mathlib probe is not withdrawn. What is no longer true is the implied statement
about what the estate lacks: `PerronGap.transferSym_gap` proves `|λ| < λ_top` off the argmax **for
this file's own matrix**, and it does so without proving general Perron–Frobenius, because the
symmetric strictly-positive case has a variational proof the general case does not.
`transferSym_pos`, recorded above as *"the positivity it would consume"*, is what that chain
consumed.

**AND `trace_transferSym_pow` TURNED OUT TO BE THE RUNG IT LOOKED LIKE.**
`TransferPowerSum.partition2_eq_sum_eigenvalues_pow` puts the partition function in this matrix's
own eigenvalues, and `IsingTwoPointSpectral.corr2Sep_eq_spectral` and
`IsingTwoPointLimit.corr2SepInf_connected_le` put the strip's two-point function there too, the
second with an exponential clustering bound. **All of it at fixed width**, which is `WALLS` §W4 §6
item 3's open sentence and is untouched by any of it.

**No eigenvalue is computed, no gap is bounded, and no limit in the width is taken.** The free
energy does not appear.

**And this is a change of presentation, not of content.** `transferSym` and `transfer2` are
conjugate by a diagonal matrix, which is why their trace powers agree; the file proves that rather
than assuming it.
-/

namespace IsingTransferSym

open Finset Real IsingTransfer2D

variable {n : ℕ}

/-! ## 1. A general trace fact, absent from Mathlib

**Each of the two theorems below is stated over the weakest hypotheses that carry it, and they are
not the same hypotheses.** A first draft of this file asked for `[CommRing R]` in both, having
copied the context from the concrete `ℝ` setting downstream rather than reading off what the proofs
consume. What they actually consume:

* `mul_pow_swap` is a fact about a **monoid**. No commutativity, no subtraction, no addition.
* `trace_pow_mul_comm` needs commutativity, because `Matrix.trace_mul_comm` does
  (`[AddCommMonoid R] [CommMagma R]`), but it does **not** need subtraction. The least coherent
  context that also has matrix powers is `CommSemiring`.

This is not tidying. `CommRing` excluded matrices over `ℕ` — the walk-counting case `TracePathSum`
exists to serve — and, for `mul_pow_swap`, matrices over `ℍ`, which is what
`CliffordRealMinkowski` produces. Both are now covered. -/

section GeneralTrace

variable {α : Type*} [Fintype α] [DecidableEq α]

section

variable {R : Type*} [Semiring R]

/-- `A · (B·A)ᵏ = (A·B)ᵏ · A`, the bookkeeping behind every "trace is cyclic" argument about powers.

**MATHLIB ALREADY HAS THIS AND A FIRST DRAFT OF THIS FILE PROVED IT BY HAND.** It is
`SemiconjBy.pow_right`: `A * (B * A) = (A * B) * A` is associativity, so `A` semiconjugates `B * A`
to `A * B`, and semiconjugation passes to powers in any monoid. The duplicate arose from probing
the `Matrix` namespace for a `Matrix`-shaped name, when the fact is general and lives in
`Algebra.Group.Semiconj`. `ERRATUM 42` is the rule this broke — probe by shape, not by the name you
expect — and the shape to have probed was `a * x = y * a`, not `Matrix.*`.

**Holds over any semiring**, hence for matrices over `ℕ` and over `ℍ`. -/
theorem mul_pow_swap (A B : Matrix α α R) (k : ℕ) : A * (B * A) ^ k = (A * B) ^ k * A :=
  (show SemiconjBy A (B * A) (A * B) from (mul_assoc A B A).symm).pow_right k

end

section

variable {R : Type*} [CommSemiring R]

/-- **`tr ((AB)ᵏ) = tr ((BA)ᵏ)`.** Absent from Mathlib by name — `trace_pow_mul_comm`,
`Matrix.trace_pow`, `Matrix.pow_apply` all return nothing — and, re-probed 2026-08-11, absent by
**shape**: no statement anywhere in Mathlib applies `trace` to a power on both sides of an equation.
The name probe alone would not have settled it, because the ingredient `mul_pow_swap` was in Mathlib
all along under a name no `Matrix` probe reaches. `Matrix.trace_mul_comm` is the `k = 1` case and is
what this is built from.

**Commutativity is needed and subtraction is not**, so this is stated over `CommSemiring`; the case
that buys is `ℕ`-valued matrices, which are the ones that count walks.

**And there is no induction on `k`.** The first draft recursed and never used the recursive call —
`mul_pow_swap` has already done the induction. -/
theorem trace_pow_mul_comm (A B : Matrix α α R) (k : ℕ) :
    Matrix.trace ((A * B) ^ k) = Matrix.trace ((B * A) ^ k) := by
  cases k with
  | zero => simp
  | succ k =>
    calc Matrix.trace ((A * B) ^ (k + 1))
        = Matrix.trace (((A * B) ^ k * A) * B) := by rw [pow_succ]; simp [Matrix.mul_assoc]
      _ = Matrix.trace ((A * (B * A) ^ k) * B) := by rw [mul_pow_swap]
      _ = Matrix.trace (B * (A * (B * A) ^ k)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((B * A) ^ (k + 1)) := by rw [pow_succ']; simp [Matrix.mul_assoc]

end

/-! ### 1.1 The weakening is real, and it is checked rather than announced

A hypothesis weakened on paper is not thereby weakened: the test is whether something the old
hypothesis **refused** now goes through. So the two instantiations below are recorded as theorems
rather than as a remark, and the refusal was **observed rather than predicted** — probed
2026-08-11, against a copy of this section carrying the first draft's `[CommRing R]`:

* `#synth CommSemiring ℕ` succeeds (`Nat.instCommSemiring`) and `#synth CommRing ℕ` fails.
* `#synth Semiring ℍ[ℝ]` succeeds (via `DivisionRing`) and `#synth CommRing ℍ[ℝ]` fails.
* Neither witness below elaborates against `[CommRing R]`. The observed failure mode is a
  heartbeat timeout inside instance search rather than a clean rejection, which is a scruffier
  signal than one would like; the two `#synth` lines above are the crisp form of the same fact and
  are why the timeouts are read as absence rather than as slowness. -/

open scoped Quaternion

/-- **`mul_pow_swap` OVER A NON-COMMUTATIVE COEFFICIENT RING.** `ℍ[ℝ]` is not commutative
(`quaternion_mul_not_comm` below, proved rather than cited), so `[CommRing R]` refused this
outright. `M₂(ℍ[ℝ])` is not a curiosity in this estate: it is `CliffordRealMinkowski`'s target
algebra, the `M₂(ℍ)` in `Cl(1,3;ℝ) ≃ₐ M₂(ℍ)`. -/
theorem mul_pow_swap_quaternion (A B : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) (k : ℕ) :
    A * (B * A) ^ k = (A * B) ^ k * A :=
  mul_pow_swap A B k

/-- The non-commutativity that gives the witness above its point, `i · j = k` against
`j · i = −k`. -/
theorem quaternion_mul_not_comm : ∃ a b : ℍ[ℝ], a * b ≠ b * a := by
  refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, fun h => ?_⟩
  have hk := congrArg QuaternionAlgebra.imK h
  simp at hk
  norm_num at hk

/-- **`trace_pow_mul_comm` OVER `ℕ`.** `ℕ` is a `CommSemiring` and not a ring — there is nothing to
subtract — so `[CommRing R]` refused this too. And `ℕ` is not an exotic instantiation here: matrices
over `ℕ` are the adjacency matrices whose powers count walks, which is the entire subject of
`TracePathSum`. The over-strong hypothesis had excluded the identity's own home ground. -/
theorem trace_pow_mul_comm_nat (A B : Matrix (Fin 3) (Fin 3) ℕ) (k : ℕ) :
    Matrix.trace ((A * B) ^ k) = Matrix.trace ((B * A) ^ k) :=
  trace_pow_mul_comm A B k

end GeneralTrace

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
