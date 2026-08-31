import AdjMatrixWalkTrace
import TransferPowerSum

/-!
# Closed walks are the power sums of the adjacency spectrum

`AdjMatrixWalkTrace` reads `tr(Aⁿ)` as a **count of closed walks**;
`TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` reads `tr(Aᵏ)` as a **power sum of
eigenvalues**, for a Hermitian matrix over any `RCLike` field. Both have been in this estate — the
second since 22 August, the first since this morning — and **nothing joined them**.

> **`adjMatrix_isHermitian`** — the real adjacency matrix is symmetric, hence Hermitian. Neither
> finiteness nor decidable equality on the vertices is used.
>
> **`closed_walks_eq_power_sum`** — for any finite simple graph, the number of closed walks of
> length `n`, summed over basepoints, **is `∑ᵢ λᵢⁿ`** with `λ` the adjacency spectrum.

## THIS FILE IS THE SECOND HALF OF A UNIT WHOSE FIRST HALF WAS A DUPLICATE (`ERRATUM 373`)

The unit that produced it set out to prove the spectral mapping itself, on the strength of a
re-sweep that named it as an open rung. **It was closed on 22 August**, by
`TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` — same name, same statement, same four-rewrite
proof through `spectral_theorem`, `diagonal_pow` and `trace_mul_cycle` — with **six consumers across
five files**. The watchlist block records that closure fourteen lines below the text the sweep read.
The duplicate was written, built green, and deleted; what survives is the composition below, which
is genuinely new and is what the sweep was right about.

## What is NOT here

**No bound, in either direction.** The identity is exact. Turning it into an entropy estimate needs
a bound on `λ`, and **none is proved or cited below** (`ERRATUM 246`).

**Nothing about eigenvectors**, and no claim that `A^k`'s eigenvalue family *is* the `k`-th power of
`A`'s — a statement about two sorted families, strictly stronger than the trace identity, which the
trace identity does not need and which is **not proved anywhere in this estate**.

**No consumer.** Nothing in this estate reads a closed-walk count spectrally as of this file, and
`WalkCount`'s combinatorial bounds are untouched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjSpectrumWalks

open Matrix

/-- The real adjacency matrix is symmetric, hence Hermitian. `IsHermitian` is `Aᴴ = A`, and over
`ℝ` the conjugate transpose is the transpose. -/
theorem adjMatrix_isHermitian {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext i j
  simp [SimpleGraph.adjMatrix_apply]

/-- **THE NUMBER OF CLOSED WALKS OF LENGTH `n` IS THE `n`-TH POWER SUM OF THE ADJACENCY SPECTRUM.**
`AdjMatrixWalkTrace.trace_adjMatrix_pow` reads the trace as a walk count and
`TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow` reads it as a power sum. -/
theorem closed_walks_eq_power_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    ∑ v : V, (Fintype.card {p : G.Walk v v | p.length = n} : ℝ)
      = ∑ i, ((adjMatrix_isHermitian G).eigenvalues i) ^ n := by
  rw [← AdjMatrixWalkTrace.trace_adjMatrix_pow G ℝ n,
    TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow]

end AdjSpectrumWalks
