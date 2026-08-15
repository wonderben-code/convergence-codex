import LovelockReflections

/-!
# Step 2's frame change, which was already in the estate

`LovelockReflections` proved step 1 of the elementary route to `RicciProportional` — reflections
force `T` to send a reflection-fixed tensor to a diagonal one — and recorded step 2 as **a guess**:

> **Step 2** runs on permutation matrices, which are orthogonal by the same kind of computation as
> §1, so it *looks* like the next unit and cheap. **That is a sizing judgement, and this file
> exists because a sizing judgement of mine was wrong**; it is recorded as a guess for the next
> unit to test, not as a promise.

`PROOF_STRATEGY` §6's key generator says that when a unit was a B, retry B → C immediately. This
file is that retry.

## ERRATUM 168: the first draft rebuilt the permutation matrices

The first version of this file opened by defining `permMat`, proving `isOrth_permMat`, and
computing `act2_permMat`, and its header reported that "**the guess was half right** — the frame
change is as cheap as predicted". **All three declarations already existed in
`AlgebraicCurvature`**, with the same three names and the same two statements, in a file this one
transitively imports. So the guess was not half right in the way the header claimed: the frame
change was not *cheap*, it was **already done**, and the check that would have found this is one
`grep` against the file the whole route is built on.

Nothing clashed and nothing warned: the duplicates sat inside `namespace LovelockPermutations`, so
the imported names were silently shadowed. `LovelockReflections` had done the same thing one file
earlier with the *reflection* — see its own header — which is what turned a slip into a pattern
worth an erratum number.

**Three declarations went; nothing that was proved here is now unproved.** What is left is the
part that was never in `AlgebraicCurvature`: not that a permutation is an orthogonal frame change,
but what it does to the image of an equivariant `T`.

## What is proved

`AlgebraicCurvature.act2_permMat` says the action on a 2-tensor is a relabelling and nothing else,

    act2 (permMat σ) S b c  =  S (σ b) (σ c)

with no signs and no sums surviving. From that and equivariance:

* `T_act_permMat` — `T (act (permMat σ) R) b c = T R (σ b) (σ c)`. Relabelling the frame relabels
  the answer.
* **`T_ricciPart_permMat`** — the same statement for the Ricci summand, which is the one step 2
  actually consumes: `T (ricciPart (act (permMat σ) R)) b c = T (ricciPart R) (σ b) (σ c)`. It
  needs `act_ricciPart`, that the summand commutes with a frame change, and
  `isAlgCurv_ricciPart`, that it stays inside the symmetry class.
* `T_ricciPart_diagonal_permMat` — a consistency check that step 1 and this file compose, and
  **not new content**: it says the permuted tensor's image is still diagonal, which also follows
  from step 1 alone, because relabelling a diagonal tensor gives a diagonal tensor. It is kept
  because a composition that did *not* typecheck would have meant one of the two steps was stated
  wrongly, and it is labelled so nobody reads it as the permutation argument doing work.

## What is NOT proved here

**Step 2 is not finished in this file.** What is delivered is the *equivariance* of the diagonal
under relabelling. What step 2 needs on top is the **combinatorial** part: that a linear,
relabelling-equivariant assignment from a traceless diagonal tensor to a diagonal tensor is a fixed
multiple of the identity. **That is `LovelockDiagonalWitness`**, and the first draft of this
paragraph asserted it could not be done without "representing `T` restricted to diagonal tensors as
a linear map on `ℝⁿ` and reading off its entries" — a claim about a proof that had not been
attempted. See that file's header for the correction.

**The honest tally on the three-step route, spelled out rather than given as a fraction:** step 1,
done (`LovelockReflections`). Step 2 has two parts — the frame change, which was already in
`AlgebraicCurvature` and is only *applied* here, and the combinatorics, done in
`LovelockDiagonalWitness` on a fixed pair of indices. Step 3 has two parts — the bridge
`isOrth_of_mem_orthogonalGroup`, which already existed and was never the difficulty, and the
diagonalisation itself, **not done and still the refusal**.

**And nothing here bears on `KillsWeyl`**, the harder of `LovelockReduction`'s two `Prop`s. The
watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockPermutations

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. What relabelling the frame does to the answer -/

/-- Relabelling the frame relabels the answer, with nothing else happening. -/
theorem T_act_permMat
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (σ : Equiv.Perm (Fin n)) (b c : Fin n) :
    T (act (permMat σ) R) b c = T R (σ b) (σ c) := by
  rw [hequiv (permMat σ) (isOrth_permMat σ) R hR b c, act2_permMat]

/-- **THE STATEMENT STEP 2 CONSUMES.** The Ricci summand commutes with the frame change
(`act_ricciPart`) and stays inside the symmetry class (`isAlgCurv_ricciPart`), so relabelling the
frame relabels the summand's image. -/
theorem T_ricciPart_permMat
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (σ : Equiv.Perm (Fin n)) (b c : Fin n) :
    T (ricciPart (act (permMat σ) R)) b c = T (ricciPart R) (σ b) (σ c) := by
  have hfun : ricciPart (act (permMat σ) R) = act (permMat σ) (ricciPart R) := by
    funext a b' c' d'
    exact (act_ricciPart (isOrth_permMat σ) R a b' c' d').symm
  rw [hfun]
  exact T_act_permMat hequiv (isAlgCurv_ricciPart hR) σ b c

/-- **A CONSISTENCY CHECK, NOT NEW CONTENT.** On a relabelled tensor whose traceless Ricci part was
diagonal, the image is still diagonal. This also follows from step 1 alone — relabelling a diagonal
tensor gives a diagonal tensor — so the permutation argument is not doing the work here. It is kept
because a composition that failed to typecheck would have meant one of the two steps was stated
wrongly. The relabelling content is `T_ricciPart_permMat`, above. -/
theorem T_ricciPart_diagonal_permMat
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0)
    (σ : Equiv.Perm (Fin n)) {b c : Fin n} (hne : b ≠ c) :
    T (ricciPart (act (permMat σ) R)) b c = 0 := by
  rw [T_ricciPart_permMat hequiv hR σ b c]
  exact T_ricciPart_diagonal hequiv hR hdiag fun h => hne (σ.injective h)

end LovelockPermutations
