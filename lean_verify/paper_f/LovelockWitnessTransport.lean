import LovelockWitnessSum

/-!
# The two values do not depend on which pair of axes was chosen

`LovelockWitnessSum` proved that the Weyl parts of the witness family sum to zero, and then said
exactly what stopped that from cutting the two numbers to one:

> collapsing the double sum into a count of those two values needs one more thing: **that the two
> values do not depend on which pair `(i,j)` was chosen.** … constructing the permutation carrying
> an arbitrary pair to another is a step nobody has written.

**It is written here.**

## What is proved

* **`pairMove`** — an explicit permutation carrying any ordered pair of distinct indices to any
  other, built as two transpositions: swap `i` to `i'`, then swap whatever `j` became to `j'`. The
  second transposition leaves `i'` alone, which is `pairMove_fst`'s whole content;
* **`act2_permMat_twoProj`** — `act2 (permMat σ) (twoProj i j) = twoProj (σ⁻¹ i) (σ⁻¹ j)`, and
  **`act_permMat_twoProjCurv'`** the same on the curvature tensor. **This generalises
  `LovelockWeylTwoValues.act_permMat_twoProjCurv`**, which required `σ` to fix `{i,j}` setwise; the
  general statement holds for **every** `σ` and simply relabels the pair. `PROOF_STRATEGY` §7
  item 3 again;
* **`T_weyl_transport`** — so `T` on the witness for one pair is `T` on the witness for the moved
  pair, with the arguments relabelled;
* **`T_weyl_p_indep`** and **`T_weyl_q_indep`** — **the two numbers are the same for every pair of
  distinct axes.**

## What is left, which is now arithmetic

`LovelockWitnessSum.T_sum_weyl_twoProj` says `∑_i ∑_j T W_{ij} b b = 0`. With this file, every term
is one of two numbers: `p` when `b ∈ {i,j}`, `q` when it is not, and the `i = j` terms vanish
because `knSquare (twoProj i i)` is identically zero. **Counting the terms would give
`2(n−1)·p + (n−1)(n−2)·q = 0`** — one linear relation, and the two numbers become one.

**That count is not done here.** It is a `Finset` cardinality computation and nothing more, but it
is not a theorem until it is written, and this file does not claim it.

**And one number would still not be `KillsWeyl`.** Both predecessors say so and it stays true: the
statement quantifies over every algebraic curvature tensor, this is one witness family, and whether
its orbit spans the Weyl summand is `WALLS` §W5.0 §5b's irreducibility question. **The watchlist
item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWitnessTransport

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockPermutations
  WeylNonzeroGeneral LovelockWeylTwoValues Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. Moving one pair of axes to another -/

/-- **A PERMUTATION CARRYING ANY ORDERED PAIR OF DISTINCT INDICES TO ANY OTHER.** -/
def pairMove (i j i' j' : Fin n) : Equiv.Perm (Fin n) :=
  (Equiv.swap i i').trans (Equiv.swap (Equiv.swap i i' j) j')

theorem pairMove_fst (i j i' j' : Fin n) (hij : i ≠ j) (hij' : i' ≠ j') :
    pairMove i j i' j' i = i' := by
  simp only [pairMove, Equiv.trans_apply, Equiv.swap_apply_left]
  have hne : (Equiv.swap i i') j ≠ i' := by
    intro h
    have : j = i := (Equiv.swap i i').injective (by rw [h, Equiv.swap_apply_left])
    exact hij this.symm
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) hij'

theorem pairMove_snd (i j i' j' : Fin n) :
    pairMove i j i' j' j = j' := by
  simp only [pairMove, Equiv.trans_apply, Equiv.swap_apply_left]

/-! ## 2. What that does to the witness -/

theorem act2_permMat_twoProj (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    act2 (permMat σ) (twoProj i j) = twoProj (σ.symm i) (σ.symm j) := by
  funext b c
  rw [act2_permMat]
  simp only [twoProj]
  have e : ∀ x y : Fin n, delta (σ x) y = delta x (σ.symm y) := by
    intro x y
    by_cases h : σ x = y
    · have : x = σ.symm y := by rw [← h, Equiv.symm_apply_apply]
      simp [delta, this]
    · have : x ≠ σ.symm y := by
        intro e
        exact h (by rw [e, Equiv.apply_symm_apply])
      simp [delta, h, this]
  rw [e, e, e, e]

theorem act_permMat_twoProjCurv' (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    act (permMat σ) (knSquare (twoProj i j)) = knSquare (twoProj (σ.symm i) (σ.symm j)) := by
  funext a b c d
  rw [act_knSquare, act2_permMat_twoProj]

theorem T_weyl_transport
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (σ : Equiv.Perm (Fin n)) (i j b c : Fin n) :
    T (weylPart (knSquare (twoProj (σ.symm i) (σ.symm j)))) b c
      = T (weylPart (knSquare (twoProj i j))) (σ b) (σ c) := by
  have hW : act (permMat σ) (weylPart (knSquare (twoProj i j)))
      = weylPart (knSquare (twoProj (σ.symm i) (σ.symm j))) := by
    funext a b' c' d'
    rw [act_weylPart (isOrth_permMat σ), act_permMat_twoProjCurv' σ i j]
  have hkey := T_act_permMat hequiv (isAlgCurv_weylPart (isAlgCurv_twoProjCurv i j)) σ b c
  rw [hW] at hkey
  exact hkey

/-! ## 3. The two numbers are pair-independent -/

theorem T_weyl_p_indep
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') :
    T (weylPart (knSquare (twoProj i' j'))) i' i'
      = T (weylPart (knSquare (twoProj i j))) i i := by
  have h1 : pairMove i' j' i j i' = i := pairMove_fst i' j' i j hij' hij
  have h2 : pairMove i' j' i j j' = j := pairMove_snd i' j' i j
  have e1 : (pairMove i' j' i j).symm i = i' := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have e2 : (pairMove i' j' i j).symm j = j' := by rw [Equiv.symm_apply_eq]; exact h2.symm
  have h := T_weyl_transport hequiv (pairMove i' j' i j) i j i' i'
  rw [e1, e2, h1] at h
  exact h

theorem T_weyl_q_indep
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j i' j' k k' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')
    (hki : k ≠ i) (hkj : k ≠ j) (hk'i' : k' ≠ i') (hk'j' : k' ≠ j') :
    T (weylPart (knSquare (twoProj i' j'))) k' k'
      = T (weylPart (knSquare (twoProj i j))) k k := by
  have h1 : pairMove i' j' i j i' = i := pairMove_fst i' j' i j hij' hij
  have h2 : pairMove i' j' i j j' = j := pairMove_snd i' j' i j
  have e1 : (pairMove i' j' i j).symm i = i' := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have e2 : (pairMove i' j' i j).symm j = j' := by rw [Equiv.symm_apply_eq]; exact h2.symm
  have hni : pairMove i' j' i j k' ≠ i := by
    intro e
    apply hk'i'
    have hc := congrArg (pairMove i' j' i j).symm e
    rw [Equiv.symm_apply_apply, e1] at hc
    exact hc
  have hnj : pairMove i' j' i j k' ≠ j := by
    intro e
    apply hk'j'
    have hc := congrArg (pairMove i' j' i j).symm e
    rw [Equiv.symm_apply_apply, e2] at hc
    exact hc
  have h := T_weyl_transport hequiv (pairMove i' j' i j) i j k' k'
  rw [e1, e2] at h
  rw [h]
  exact T_weyl_twoProj_off hequiv hni hnj hki hkj

end LovelockWitnessTransport
