import Involutions

/-!
# Summing over an involution's fixed points, the other way round

`LatticeSteinLadder.hasDerivAt_steinSum` produces a double sum: over the involutions of the index
set, and inside each, over **that involution's fixed points**.
`SteinSumRecursion.sum_steinTerm_option` produces a double sum the other way: over the **index**
`b`, and inside each, over the involutions that **fix `b`**. Matching a ladder rung against the
recursion means turning one into the other, and that is this file.

## Why it is not `Finset.sum_comm`

`Finset.sum_comm` swaps two sums over **fixed** index sets. Here the inner set depends on the
outer variable in both directions — `fix σ` depends on `σ`, and `{g | g b = b}` depends on `b` —
so the swap is over the set of **pairs** `(σ, j)` with `σ j = j`, read once by its first component
and once by its second. `Finset.sum_comm'` is the version that takes that reading as its
hypothesis, and the hypothesis is symmetric here and closes by `simp`.

## What is proved

* **`sum_fixedPoints_comm`** — the swap, over any `AddCommMonoid`;
* `sum_fixedPoints_comm_count` — and it is checked at the weight `1`, where it says that counting
  `(involution, fixed point of it)` pairs by involution and by point give the same number.

**WHAT IS NOT HERE.** No measure, no integral, no test function; and no ladder. Using this to close
the induction step also needs `SteinSumRecursion.sum_steinTerm_option` transported from `Option α`
to `Fin (n+1)`, which is **not done** — see `LatticeSteinLadder`. **Not costed** (`ERRATUM 194`).
-/

namespace InvolutionFixedSum

open Equiv Function Involutions

variable {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]

/-- **THE SWAP.** Summing a weight over each involution's fixed points is the same as summing it
over each index's fixing involutions. Both sides run over the pairs `(σ, j)` with `σ` an
involution and `σ j = j`; they differ only in which component is read first. -/
theorem sum_fixedPoints_comm (w : Equiv.Perm α → α → M) :
    ∑ σ : ↑(involutions α), ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j), w σ.1 j
      = ∑ b : α, ∑ g : {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b}, w g.1 b := by
  classical
  have hL := Finset.sum_subtype (F := Subtype.fintype _)
      (p := fun σ : Equiv.Perm α => σ ∈ involutions α)
      (Finset.univ.filter (fun σ : Equiv.Perm α => σ ∈ involutions α)) (by simp)
      (fun τ : Equiv.Perm α => ∑ j ∈ Finset.univ.filter (fun j => τ j = j), w τ j)
  rw [← hL, Finset.sum_comm' (t' := (Finset.univ : Finset α))
    (s' := fun b => Finset.univ.filter
      (fun σ : Equiv.Perm α => σ ∈ involutions α ∧ σ b = b))
    (by intro x y; simp)]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Finset.sum_subtype (F := Subtype.fintype _) _ (by simp) _

/-- **THE CHECK.** At the constant weight `1` the swap says the pairs `(σ, j)` with `σ j = j` are
counted the same by involution and by index: the total number of fixed points over all
involutions equals the total number of fixing involutions over all indices. Neither side is a
number this estate had; the identity is what makes them the same one. -/
theorem sum_fixedPoints_comm_count :
    ∑ σ : ↑(involutions α), (Finset.univ.filter (fun j => σ.1 j = j)).card
      = ∑ b : α, Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b} := by
  have h := sum_fixedPoints_comm (α := α) (M := ℕ) (fun _ _ => 1)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] using h

end InvolutionFixedSum
