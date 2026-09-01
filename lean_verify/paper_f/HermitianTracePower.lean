import TracePowerSpectrum

/-!
# The trace of a power is the power sum of the eigenvalues — lifted out of the Ising chain

**This file contains no new mathematics.** It holds two theorems that were written in
`TransferPowerSum.lean` on 22 August, **under the same namespace and with the same names**, so that
every existing citation of `TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` and
`TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow` — there are eleven, across seven files —
resolves exactly as before. `TransferPowerSum` now imports this file rather than containing them.

## Why the move, and it is a move rather than a copy

`TransferPowerSum` imports `PerronGap`, which imports `IsingTransfer2D`. So a **general statement
about Hermitian matrices over any `RCLike` field** sat underneath the two-dimensional Ising transfer
matrix, and anything wanting it inherited that. `HermitianTraceMoments` recorded the cost on
1 September: `SpectralActionDetermines.trace_pow_eq_of_eigenvalues_multiset_eq` is exactly
`HermitianTraceMoments.trace_pow_eq_of_multiset_eq` at `A = M * Mᴴ` over `ℂ`, so that file could
drop a hand proof and cite the general one — **except that doing so would have put the Ising chain
underneath a spectral-action file.**

`TracePowerSpectrum`, where the same argument's `ℂ` case already lives as `herm_trace_pow`, imports
**only Mathlib**. That is this file's only import, and it is all the proof needs: the spectral
theorem in `Unitary.conjStarAlgAut` form, `Matrix.diagonal_pow`, and cyclicity of the trace.

**Copying rather than moving would have been `ERRATUM 373`'s defect.** The declarations are
deleted from `TransferPowerSum`, not duplicated; `--decls` and `dupname_scan` are the checks
that this is so.

## What this is NOT

* **Not a generalisation.** The statements are byte-for-byte what they were. `PROOF_STRATEGY` §7's
  *"deepen, don't broaden"* is about removing hypotheses; nothing here removes one.
* **Not a claim that `TransferPowerSum` should not exist.** That file's subject — the partition
  function as a power sum of its own transfer matrix's spectrum, and the free energy that follows —
  is unchanged and still lives there. Only the two general lemmas moved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TransferPowerSum

open Matrix Finset

/-- **THE TRACE OF A POWER IS THE POWER SUM OF THE EIGENVALUES.** Mathlib has
`IsHermitian.trace_eq_sum_eigenvalues` (the case `k = 1`) and `IsHermitian.pow` (a power of a
Hermitian matrix is Hermitian, which is what lets the partition function be stated in the *wrong*
eigenvalue family), and nothing joining them. -/
theorem trace_pow_eq_sum_eigenvalues_pow {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℝ) : 𝕜) ^ k := by
  have hpow : A ^ k
      = (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜)) hA.eigenvectorUnitary
          (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) ^ k)) := by
    rw [← Matrix.diagonal_pow, map_pow, ← hA.spectral_theorem]
  rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **THE REAL CASE, WITH NO COERCION IN THE STATEMENT.** This is the rung the watchlist item of
22 August names. `RCLike ℝ` makes it an instance of the theorem above rather than a second proof;
what it buys is that the statement can be *used* against a real symmetric matrix without carrying
`RCLike.ofReal` through every rewrite. -/
theorem real_trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  simpa using trace_pow_eq_sum_eigenvalues_pow hA k

end TransferPowerSum
