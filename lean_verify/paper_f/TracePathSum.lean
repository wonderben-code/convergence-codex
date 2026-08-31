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

**^ THE CLAIM STANDS AND THE SEARCH REPORT DOES NOT, CORRECTED 2026-08-31 (`ERRATUM 94`,
`ERRATUM 366`), THE SENTENCE KEPT AS WRITTEN.** `71` is the count of names in the `Matrix`
namespace that contain `pow`. Names *containing* `Matrix` and `pow` — the population this
sentence names — number **76**, and among the five the namespace restriction dropped is
**`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`**: each entry of the `n`-th power of a graph's
adjacency matrix is the number of walks of that length between the two vertices. That is a
statement about entries of a matrix power and walks. **`Matrix.pow_apply` really does not exist**,
and `Matrix.pow_apply_pos_iff_nonempty_path`, which is inside the 71, is a positivity criterion
rather than a sum.

**AND THIS ESTATE HAD ALREADY FOUND THAT THEOREM.** `ERRATUM 342`, on 2026-08-30, names it and
draws the same lesson about a probe scoped to `SimpleGraph.Walk.*` that structurally could not see
a theorem in `SimpleGraph.*`. This file was committed 2026-08-11 and its probe was scoped to
the `Matrix` namespace, which could not see it either; the later entry never came back here.
The two probes missed one theorem for one reason, nineteen days apart.

**WHAT THIS FILE PROVES IS UNAFFECTED AND THE REASON IS NOT A TECHNICALITY.** Mathlib's theorem is
about the **adjacency** matrix, whose entries are `0` and `1`, and its right-hand side is a
**cardinality**; `pow_succ_apply` below is about an arbitrary `M` over an arbitrary commutative
semiring and its right-hand side is a sum of **products of entries**. The adjacency matrix is the
case where every product is `0` or `1` and the sum counts. **The two are joined rather than
compared**: `AdjMatrixWalkTrace.sum_cyc_adjMatrix` derives the closed-walk count from
`sum_cyc_eq_trace` below, which is the identity Mathlib does not have.

> **`walkProd M b n a s`** — the product `M a s₀ · M s₀ s₁ ⋯ M sₙ₋₁ b` along the walk that starts
> at `a`, visits `s`, and ends at `b`.
>
> **`pow_succ_apply`** — `(Mⁿ⁺¹) a b = ∑ over interior walks`. Induction on `n`, with the step
> reindexing `Fin (n+1) → α` as `α × (Fin n → α)` through `Fin.consEquiv`. This is the identity
> Mathlib does not have.
>
> **`trace_pow_succ`** — hence the trace as a sum over **closed** walks, indexed by basepoint and
> interior.
>
> **`sum_cyc_eq_trace`** — and **the cyclic form**, which is the one the physics wants:
> `∑_{s : Fin (N+1) → α} ∏_i M (s i) (s (i+1))`, with `i+1` wrapping, `= tr Mᴺ⁺¹`. This is the
> shape `IsingTransferMatrix.PartitionIsTrace` asks for, over an arbitrary matrix and an arbitrary
> commutative semiring.

## How the cyclic form was reached, because the obvious attempt fails

**Peeling the cyclic product does not work, and it is worth saying why** — "it is only re-indexing"
is the wrong intuition and costs an afternoon. Take the first factor off
`∏ i : Fin (N+2), M (s i) (s (i+1))`. What is left is **not** the cyclic product of `Fin.tail s`:
the leftover's last factor is `M (s (N+1)) (s 0)`, ending where the whole loop started, whereas the
tail's own cyclic product ends at `(tail s) 0 = s 1`. The wrap-around points at a place the tail no
longer knows about, so the recursion does not close.

**What works instead**, and it is the route this file's previous version wrote down and this one
takes:

1. **`openProd`** — the product along an *open* path of `n+1` points. It peels cleanly, because
   `castSucc` and `succ` never wrap (`openProd_succ`).
2. **`cyc_eq_openProd`** — the cyclic product over `s` **is** the open product along
   `Fin.snoc s (s 0)`, the path `s` with its own first point appended. Term by term this is
   `Fin.snoc_castSucc`, except at the last index, where it is exactly the statement that the cyclic
   successor of `Fin.last` is `0`. **The wrap-around is discharged there, once, and never appears
   in an induction.**
3. **`openProd_cons_snoc`** — the open product along `a, t, b` is `walkProd M b n a t`. *This*
   inducts, because `walkProd` holds its endpoint `b` fixed while the start moves, which is the
   shape `openProd_succ` peels into.

Then `trace_pow_succ` and one `Fin.consEquiv` reindexing finish it.

## What this does NOT do

**It is not about the Ising model and does not by itself move any tag.** `M` is any matrix over any
commutative semiring. Instantiating it at the estate's `transfer β` is a separate step, in the file
that owns that matrix.

**And it is not a mass gap.** `WALLS` §W4.0's item 3 is *tie the gap to correlation decay*; this
supplies the identity that item names, in one dimension, where the gap never closes. The wall's
other two items — the `2ⁿ × 2ⁿ` matrix for `d = 2`, and separating its top eigenvalue — are
untouched.
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

/-! ## 3. Closing the walk up

The route §2's header set out, taken. The pieces are the open product, which peels because its two
index maps do not wrap, and one identification of the cyclic product with an open product along the
path with its own first point appended. -/

/-- **The product along an OPEN path** of `n+1` points, `n` factors. Unlike the cyclic product this
peels from the front, because `castSucc` and `succ` never wrap. -/
def openProd (M : Matrix α α R) (n : ℕ) (p : Fin (n + 1) → α) : R :=
  ∏ i : Fin n, M (p i.castSucc) (p i.succ)

omit [Fintype α] [DecidableEq α] in
theorem openProd_succ (M : Matrix α α R) (n : ℕ) (p : Fin (n + 2) → α) :
    openProd M (n + 1) p = M (p 0) (p 1) * openProd M n (Fin.tail p) := by
  simp only [openProd, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one]
  congr 1

omit [Fintype α] [DecidableEq α] in
/-- **THE OPEN PRODUCT ALONG `a, t, b` IS THE WALK PRODUCT.** This is the step that inducts, and it
inducts because `walkProd` holds its endpoint `b` fixed while the start moves — exactly the shape
`openProd_succ` peels into. `Fin.cons_snoc_eq_snoc_cons` and `Fin.cons_self_tail` do the one
rearrangement the step needs. -/
theorem openProd_cons_snoc (M : Matrix α α R) (b : α) :
    ∀ (n : ℕ) (a : α) (t : Fin n → α),
      openProd M (n + 1) (Fin.cons a (Fin.snoc t b)) = walkProd M b n a t
  | 0, a, t => by
    have hb : (Fin.snoc t b : Fin 1 → α) 0 = b := by simp [Fin.snoc]
    simp [openProd, hb]
  | n + 1, a, t => by
    rw [openProd_succ, Fin.tail_cons, walkProd_succ]
    have hsnoc : (Fin.snoc t b : Fin (n + 2) → α)
        = Fin.cons (t 0) (Fin.snoc (Fin.tail t) b) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    have h0 : (Fin.cons a (Fin.snoc t b) : Fin (n + 3) → α) 0 = a := Fin.cons_zero _ _
    have h1 : (Fin.cons a (Fin.snoc t b) : Fin (n + 3) → α) 1 = t 0 := by
      rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
      simp
    rw [h0, h1, hsnoc, openProd_cons_snoc M b n (t 0) (Fin.tail t)]

omit [Fintype α] [DecidableEq α] in
/-- In `Fin (n+1)` the successor of a non-last index is its `Fin.succ`, with no wrap. -/
theorem castSucc_add_one {n : ℕ} (j : Fin n) : (j.castSucc : Fin (n + 1)) + 1 = j.succ := by
  apply Fin.ext
  have := j.isLt
  simp [Fin.val_succ]

omit [Fintype α] [DecidableEq α] in
/-- **THE CYCLIC PRODUCT IS AN OPEN PRODUCT** along `s` with its own first point appended. At every
index but the last this is `Fin.snoc_castSucc`; at the last it is the statement that the cyclic
successor of `Fin.last` is `0`, which is where the wrap-around is discharged once and for all. -/
theorem cyc_eq_openProd (M : Matrix α α R) (N : ℕ) (s : Fin (N + 1) → α) :
    ∏ i : Fin (N + 1), M (s i) (s (i + 1)) = openProd M (N + 1) (Fin.snoc s (s 0)) := by
  simp only [openProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.snoc_castSucc]
  refine congrArg (M (s i)) ?_
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · intro j
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, castSucc_add_one]

omit [Fintype α] [DecidableEq α] in
/-- **THE CYCLIC PRODUCT ALONG `s` IS THE CLOSED WALK FROM `s 0` BACK TO `s 0`.** Extracted from
inside `sum_cyc_eq_trace`'s proof on 2026-08-22, when `IsingTwoPoint.sum_cyc_weighted` needed the
same step: the alternative was to copy six lines, which is `ERRATUM 173` written on purpose. -/
theorem cyc_eq_walkProd (M : Matrix α α R) (N : ℕ) (s : Fin (N + 1) → α) :
    (∏ i : Fin (N + 1), M (s i) (s (i + 1))) = walkProd M (s 0) N (s 0) (Fin.tail s) := by
  rw [cyc_eq_openProd]
  have : (Fin.snoc s (s 0) : Fin (N + 2) → α)
      = Fin.cons (s 0) (Fin.snoc (Fin.tail s) (s 0)) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [this, openProd_cons_snoc]

/-- **THE PARTITION-FUNCTION IDENTITY.** The sum over cyclic configurations of the product of
transfer entries around the loop is the trace of the matrix power. Every step is one of the three
above plus the `Fin.consEquiv` reindexing already used in §2.

This is the shape `IsingTransferMatrix.PartitionIsTrace` asks for, for an arbitrary matrix over an
arbitrary commutative semiring. -/
theorem sum_cyc_eq_trace (M : Matrix α α R) (N : ℕ) :
    ∑ s : Fin (N + 1) → α, ∏ i : Fin (N + 1), M (s i) (s (i + 1))
      = Matrix.trace (M ^ (N + 1)) := by
  rw [Finset.sum_congr rfl fun s _ => cyc_eq_walkProd M N s, trace_pow_succ]
  have hprod : (∑ p : α × (Fin N → α), walkProd M p.1 N p.1 p.2)
      = ∑ a, ∑ t : Fin N → α, walkProd M a N a t := Fintype.sum_prod_type _
  rw [← hprod]
  refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (N + 1) => α).symm
    (fun s => walkProd M (s 0) N (s 0) (Fin.tail s))
    (fun p => walkProd M p.1 N p.1 p.2) fun s => ?_
  simp [Fin.consEquiv]

end TracePathSum
