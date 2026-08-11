import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Matrix powers as sums over walks

`WALLS.md` §W4.0 item 3 is *tie the gap to correlation decay*, and what remains of it is one named
statement, `IsingTransferMatrix.PartitionIsTrace`: the periodic chain's partition function is
`tr Tᴺ`, i.e. the sum-over-paths identity. That file records the probe:

> *"**Not in Mathlib** — probed by NAME (`trace_pow_eq_sum`, `Matrix.trace_pow`, `trace_list_prod`,
> `prod_cycle`: zero each) and by SHAPE (the only sum-over-functions-of-products under
> `LinearAlgebra/Matrix/` is the permutation sum in `Determinant`)."*

Re-probed 2026-08-11 against the pinned environment: **`Matrix.pow_apply` does not exist**, and of
the 71 declarations whose names contain `Matrix` and `pow`, none is a sum over walks. This file
supplies the open case.

> **`walkProd M b n a s`** — the product `M a s₀ · M s₀ s₁ ⋯ M sₙ₋₁ b` along the walk that starts
> at `a`, visits `s`, and ends at `b`.
>
> **`pow_succ_apply`** — `(Mⁿ⁺¹) a b = ∑ over interior walks`. Induction on `n`, with the step
> reindexing `Fin (n+1) → α` as `α × (Fin n → α)` through `Fin.consEquiv`. This is the identity
> Mathlib does not have.
>
> **`trace_pow_succ`** — hence the trace as a sum over **closed** walks, indexed by basepoint and
> interior.

## What this does NOT do, and it is one re-indexing

**It does not discharge `PartitionIsTrace`.** That statement sums over `s : Fin (N+1) → Bool` of
`∏ i, T (s i) (s (i+1))` with `i+1` **cyclic in `Fin (N+1)`**, and `trace_pow_succ` gives the same
number indexed as *(basepoint, interior)* instead. The two are the same sum written differently and
the missing step is the bijection between the two indexings — which is not bookkeeping in the
dismissible sense, because the cyclic successor changes shape with `N` and so does not induct the
way the open walk does. **Named here, not attempted here**, which is `PROOF_STRATEGY` §3's condition
for leaving a chain.

**And nothing here is about the Ising model.** `M` is any matrix over any semiring.
-/

namespace TracePathSum

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommSemiring R]

/-! ## 1. The product along an open walk -/

/-- **The product along a walk** from `a` through the interior points `s` to `b`. At length `0`
there is no interior and the product is the single entry `M a b`. -/
def walkProd (M : Matrix α α R) (b : α) : ∀ n, α → (Fin n → α) → R
  | 0, a, _ => M a b
  | n + 1, a, s => M a (s 0) * walkProd M b n (s 0) (Fin.tail s)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem walkProd_zero (M : Matrix α α R) (b a : α) (s : Fin 0 → α) :
    walkProd M b 0 a s = M a b := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem walkProd_succ (M : Matrix α α R) (b a : α) (n : ℕ) (s : Fin (n + 1) → α) :
    walkProd M b (n + 1) a s = M a (s 0) * walkProd M b n (s 0) (Fin.tail s) := rfl

/-! ## 2. A matrix power is the sum over walks -/

/-- **`(Mⁿ⁺¹) a b` IS THE SUM OVER WALKS** of length `n+1` from `a` to `b`. The induction step
rewrites `Mⁿ⁺² = M · Mⁿ⁺¹`, expands the product entry as a sum over the first hop, and then
reindexes `Fin (n+1) → α` as `α × (Fin n → α)` — the first hop and the rest — through
`Fin.consEquiv`.

This is the statement the estate's probe found absent from Mathlib, in the open case. -/
theorem pow_succ_apply (M : Matrix α α R) :
    ∀ (n : ℕ) (a b : α), (M ^ (n + 1)) a b = ∑ s : Fin n → α, walkProd M b n a s
  | 0, a, b => by simp
  | n + 1, a, b => by
    have hstep : (M ^ (n + 2)) a b = ∑ c, M a c * (M ^ (n + 1)) c b := by
      rw [pow_succ' M (n + 1), Matrix.mul_apply]
    rw [hstep]
    have hIH : ∀ c, (M ^ (n + 1)) c b = ∑ t : Fin n → α, walkProd M b n c t :=
      fun c => pow_succ_apply M n c b
    have hleft : (∑ c, M a c * (M ^ (n + 1)) c b)
        = ∑ p : α × (Fin n → α), M a p.1 * walkProd M b n p.1 p.2 := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun c _ => by rw [hIH c, Finset.mul_sum]
    rw [hleft]
    refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => α)
      (fun p => M a p.1 * walkProd M b n p.1 p.2)
      (fun s => walkProd M b (n + 1) a s) fun p => ?_
    simp [Fin.consEquiv, Fin.tail_cons]

/-- **AND THE TRACE IS THE SUM OVER CLOSED WALKS**, indexed by basepoint and interior. -/
theorem trace_pow_succ (M : Matrix α α R) (n : ℕ) :
    Matrix.trace (M ^ (n + 1)) = ∑ a, ∑ s : Fin n → α, walkProd M a n a s := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.sum_congr rfl fun a _ => pow_succ_apply M n a a

end TracePathSum
