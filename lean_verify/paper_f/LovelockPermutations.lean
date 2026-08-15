import LovelockReflections

/-!
# Step 2's frame change: permutations, and what they say about the diagonal

`LovelockReflections` proved step 1 of the elementary route to `RicciProportional` — reflections
force `T` to send a reflection-fixed tensor to a diagonal one — and recorded step 2 as **a guess**:

> **Step 2** runs on permutation matrices, which are orthogonal by the same kind of computation as
> §1, so it *looks* like the next unit and cheap. **That is a sizing judgement, and this file
> exists because a sizing judgement of mine was wrong**; it is recorded as a guess for the next
> unit to test, not as a promise.

`PROOF_STRATEGY` §6's key generator says that when a unit was a B, retry B → C immediately. This
file is that retry, and **the guess was half right**: the frame change is as cheap as predicted,
and the combinatorial argument that consumes it is not delivered here.

## What is proved

`permMat σ` is the orthogonal matrix of a permutation, and its action on a 2-tensor is a
relabelling and nothing else:

    act2 (permMat σ) S b c  =  S (σ b) (σ c)                    (`act2_permMat`)

with no signs and no sums surviving. From that and equivariance:

* `T_act_permMat` — `T (act (permMat σ) R) b c = T R (σ b) (σ c)`. Relabelling the frame relabels
  the answer.
* **`T_ricciPart_permMat`** — the same statement for the Ricci summand, which is the one step 2
  actually consumes: `T (ricciPart (act (permMat σ) R)) b c = T (ricciPart R) (σ b) (σ c)`. It
  needs `act_ricciPart`, that the summand commutes with a frame change, and
  `isAlgCurv_ricciPart`, that it stays inside the symmetry class.
* `T_ricciPart_diagonal_permMat` — a consistency check that step 1 and §2 compose, and **not new
  content**: it says the permuted tensor's image is still diagonal, which also follows from step 1
  alone, because relabelling a diagonal tensor gives a diagonal tensor. It is kept because a
  composition that did *not* typecheck would have meant one of the two steps was stated wrongly,
  and it is labelled so nobody reads it as the permutation argument doing work.

## What is NOT proved, and it is the half the guess got wrong

**Step 2 is not finished.** What is delivered is the *equivariance* of the diagonal under
relabelling. What step 2 needs on top is the **combinatorial** part: that a linear, relabelling-
equivariant assignment from a traceless diagonal tensor to a diagonal tensor is a fixed multiple
of the identity. The argument is standard — expand the assignment in coordinates, note that
equivariance forces the coefficient matrix to depend only on whether two indices agree, so it is
`α·δ + β·(all ones)`, and tracelessness kills the `β` term — but every step of it needs the
coefficient matrix built, which means representing `T` restricted to diagonal tensors as a linear
map on `ℝⁿ` and reading off its entries. **None of that is here.**

**The honest tally on the three-step route, spelled out rather than given as a fraction:** step 1,
done (`LovelockReflections`). Step 2 has two parts — the frame change, done here, and the
combinatorics, **not done**. Step 3 has two parts — the bridge `isOrth_of_mem_orthogonalGroup`,
which already existed and was never the difficulty, and the diagonalisation itself, **not done and
still the refusal**. So of the four parts that were ever work, **two are done**.

**And nothing here bears on `KillsWeyl`**, the harder of `LovelockReduction`'s two `Prop`s. The
watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockPermutations

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections Finset

variable {n : ℕ}

/-! ## 1. The permutation as a frame change -/

/-- The orthogonal matrix of a permutation. -/
def permMat (σ : Equiv.Perm (Fin n)) (a b : Fin n) : ℝ := if b = σ a then 1 else 0

/-- **A PERMUTATION IS AN ORTHOGONAL FRAME CHANGE**, so `hequiv` applies to it. -/
theorem isOrth_permMat (σ : Equiv.Perm (Fin n)) : IsOrth (permMat σ) where
  rows := by
    intro x y
    have h : ∀ a : Fin n, permMat σ x a * permMat σ y a
        = if a = σ x then (if a = σ y then (1 : ℝ) else 0) else 0 := by
      intro a
      by_cases hx : a = σ x <;> by_cases hy : a = σ y <;>
        simp [permMat, hx, hy]
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true, delta]
    by_cases hxy : x = y <;> simp [hxy, σ.injective.eq_iff]
  cols := by
    intro x y
    have h : ∀ a : Fin n, permMat σ a x * permMat σ a y
        = if x = σ a then (if y = σ a then (1 : ℝ) else 0) else 0 := by
      intro a
      by_cases hx : x = σ a <;> by_cases hy : y = σ a <;>
        simp [permMat, hx, hy]
    rw [Finset.sum_eq_single (σ.symm x)]
    · simp only [Equiv.apply_symm_apply, h, delta]
      rcases eq_or_ne x y with hxy | hxy
      · simp [hxy]
      · simp [hxy, Ne.symm hxy]
    · intro a _ ha
      rw [h]
      exact if_neg fun hc => ha (by rw [hc, Equiv.symm_apply_apply])
    · intro hc; exact absurd (Finset.mem_univ (σ.symm x)) hc

/-- **AND ITS ACTION ON A 2-TENSOR IS A RELABELLING**, with no signs and no surviving sum. -/
theorem act2_permMat (σ : Equiv.Perm (Fin n)) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (permMat σ) S b c = S (σ b) (σ c) := by
  simp only [act2, permMat]
  rw [Finset.sum_eq_single (σ b)]
  · rw [Finset.sum_eq_single (σ c)]
    · simp
    · intro d _ hd; simp [hd]
    · intro h; exact absurd (Finset.mem_univ (σ c)) h
  · intro d _ hd
    refine Finset.sum_eq_zero fun e _ => ?_
    simp [hd]
  · intro h; exact absurd (Finset.mem_univ (σ b)) h

/-! ## 2. What relabelling the frame does to the answer -/

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

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
