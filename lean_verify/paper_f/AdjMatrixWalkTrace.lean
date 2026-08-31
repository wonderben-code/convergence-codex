import TracePathSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# The closed-walk trace identity, and the Mathlib neighbour an absence probe could not reach

`TracePathSum` proves the sum-over-walks identity for an **arbitrary** matrix over an arbitrary
commutative semiring, and its header records the probe that justified writing it:

> *"Re-probed 2026-08-11 against the pinned environment: **`Matrix.pow_apply` does not exist**, and
> of the 71 declarations whose names contain `Matrix` and `pow`, none is a sum over walks."*

**The claim is right and the search report is not** (`ERRATUM 366`). `71` is the number of names in
the `Matrix` namespace that contain `pow`; names *containing* `Matrix` and `pow` number **76**, and
one of the five the namespace restriction dropped is
**`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`** — *each entry of the `n`-th power of a graph's
adjacency matrix is the number of walks of that length between the two vertices*. That is a
statement about entries of a matrix power and walks, in the population the sentence names.

**`TracePathSum` is still the general case and is not made redundant.** Mathlib's theorem is
about the **adjacency** matrix, whose entries are `0` and `1`, and its right-hand side is a
**cardinality**;
`pow_succ_apply` is about an arbitrary `M` and its right-hand side is a sum of **products of
entries**. The adjacency matrix is the case where every product is `0` or `1` and the sum counts.

## What is proved here, which is what the missed neighbour makes possible

> **`trace_adjMatrix_pow`** — `tr (A^n) = ∑ᵥ #{closed walks at `v` of length `n`}`, for the
> adjacency matrix of any graph on a finite vertex type. **Mathlib does not have this**: it has the
> entrywise statement and `SimpleGraph.trace_adjMatrix`, which is the `n = 1` case `tr A = 0`.
>
> **`sum_cyc_adjMatrix`** — and hence `TracePathSum.sum_cyc_eq_trace`'s cyclic sum, at the adjacency
> matrix, **is** the closed-walk count: `∑_s ∏ᵢ A (s i) (s (i+1)) = ∑ᵥ #{closed walks at v}`. The
> estate's general identity and Mathlib's counting theorem are two readings of one equation, and
> nothing in this estate had joined them because the probe never saw the second.
>
> **`card_closedWalk_eq_zero_of_isEmpty_adj`** — the sanity check that the identity is not vacuous
> in the direction that matters: on a graph with no edges every closed walk of positive length is
> impossible, so both sides are `0`, and the identity does not hold only because both sides are
> uncomputable.

## What is NOT here

**No new counting theorem.** Every walk fact used is Mathlib's; the content is the trace, which is a
sum over the diagonal, and the identification of the estate's cyclic sum with it.

**Nothing about eigenvalues.** `tr (A^n)` is the `n`-th power sum of the adjacency spectrum, and
composing that with this would say the closed-walk counts are the power sums — a classical
statement. `TracePowerSpectrum.trace_pow_eq_sum_roots_charpoly` is the estate's power-sum theorem
and **it is not applied below**; the composition is one rewrite and is deliberately left for a unit
that wants it, rather than claimed here.

**No cost is offered for the `d = 2` transfer matrix** (`ERRATUM 246`). `WALLS` §W4.0's remaining
items are untouched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjMatrixWalkTrace

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The trace of an adjacency power counts closed walks -/

/-- **`tr (Aⁿ) = ∑ᵥ #{closed walks at `v` of length `n`}`.** The trace is the sum of the diagonal
and `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` reads each diagonal entry as a walk count.
Mathlib has the entrywise statement and `SimpleGraph.trace_adjMatrix` (`tr A = 0`, the `n = 1`
case); it does not have this. -/
theorem trace_adjMatrix_pow (R : Type*) [Semiring R] (n : ℕ) :
    Matrix.trace (G.adjMatrix R ^ n)
      = ∑ v : V, (Fintype.card {p : G.Walk v v | p.length = n} : R) := by
  simp only [Matrix.trace, Matrix.diag, adjMatrix_pow_apply_eq_card_walk]

/-! ## 2. So the estate's cyclic sum is that count -/

/-- **THE ESTATE'S CYCLIC IDENTITY, AT THE ADJACENCY MATRIX, IS THE CLOSED-WALK COUNT.**
`TracePathSum.sum_cyc_eq_trace` holds for an arbitrary matrix over an arbitrary commutative
semiring; §1 reads its right-hand side. The two theorems had sat unconnected because the probe
that justified `TracePathSum` restricted itself to the `Matrix` namespace. -/
theorem sum_cyc_adjMatrix (R : Type*) [CommSemiring R] (N : ℕ) :
    ∑ s : Fin (N + 1) → V, ∏ i : Fin (N + 1), G.adjMatrix R (s i) (s (i + 1))
      = ∑ v : V, (Fintype.card {p : G.Walk v v | p.length = N + 1} : R) := by
  rw [TracePathSum.sum_cyc_eq_trace, trace_adjMatrix_pow]

/-! ## 3. The identity is not vacuous -/

/-- **ON A GRAPH WITH NO EDGES BOTH SIDES VANISH AT POSITIVE LENGTH.** A closed walk of length
`n + 1` starts with an edge, so there are none; the check is that §2 is an identity between two
things that are actually computed, not between two undefined quantities. -/
theorem card_closedWalk_eq_zero_of_isEmpty_adj (hG : ∀ u v : V, ¬ G.Adj u v) (v : V) (n : ℕ) :
    Fintype.card {p : G.Walk v v | p.length = n + 1} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun p => ?_⟩
  obtain ⟨p, hp⟩ := p
  cases p with
  | nil => simp at hp
  | cons h _ => exact hG _ _ h

end AdjMatrixWalkTrace
