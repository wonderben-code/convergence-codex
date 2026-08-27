import PairingGlue

/-!
# How many pairings cross a split

`LatticeTruncatedCount` stopped its bound one step earlier than its predecessors and kept the
number of **crossing** pairings in the constant rather than the number of pairings in total. Its
record named what that left undone: **the crossing count was checked by exhaustion at one
instance and was not given as a formula.** This file gives it.

The ingredients were all present. `PairingGlue.splitEquiv` says a pairing respects a split exactly
when it is a pair of pairings of the two sides, and `Involutions` counts the pairings of any even
finite type — `card_perfectMatchings_eq_doubleFactorial`. **What was missing was only the
subtraction**: the crossing pairings are the ones left over.

## What is proved

* `card_filter_respects` — the respecting pairings, counted as a `Finset.filter` on the matchings
  rather than as `PairingGlue.card_respecting`'s subtype of the permutations. A bridge, not a
  result;
* **`card_respecting_add_card_crossing`** — respecting plus crossing is all of them, stated as an
  **addition** rather than a subtraction so that no truncated `ℕ`-subtraction is hiding in it;
* **`card_crossing_doubleFactorial`** — the closed form. At `|ι| = 2n` and `|S| = 2j` the crossing
  pairings number `(2n−1)‼ − (2j−1)‼·(2(n−j)−1)‼`;
* **`card_crossing_lt`** — and it is **always** strictly fewer than the total, at every even split
  of an even index set. **This is stronger than the record that asked for it**, which hedged with
  *"both sides nonempty"*; the empty side has one pairing, not none, so the hedge was unnecessary;
* **`card_crossing_fin_six`, `card_crossing_fin_six_via_formula`** — **the check**, at `Fin 6`
  split `{0, 1, 2, 3}`: `decide` enumerates and gets **12**, the formula gets `15 − 3·1` and gets
  **12**, and neither proof passes through the other. The instance is `Fin 6` rather than the
  `Fin 4` of `LatticeTruncatedCount` because at `Fin 4` the product is `1·1`, where a formula that
  had dropped a factor altogether would still pass. **What this instance catches and what it does
  not is worth stating rather than leaving to be assumed**: the near side contributes `3`, so
  dropping it is caught; the far side contributes `1`, so dropping *that* would not be;
* **`card_crossing_fin_six_odd`, `card_crossing_fin_six_odd_via_formula`** — **a second check, at
  a different number.** An odd-sized side has no pairings at all, so nothing respects the split and
  **every** pairing crosses: at `Fin 6` split `{0}` the count is the full `15`. It reaches where
  the closed form cannot — that theorem asks for an even split — and it lands somewhere else, so a
  proof that had collapsed to a constant would be caught;

Under this formula `LatticeTruncatedCount.crossing_card_fin_four`'s `2` is `3 − 1·1`, which is
worth stating because that file proves it by `decide` and the two routes are independent.

## What is NOT here

**The composed measure-level bound.** `LatticeTruncatedCount.abs_integral_prod_sub_mul_le_count`
still carries the raw `Finset.card` in its statement; substituting the closed form is one `rw`
through `Nat.cast`, and **no file does it**, deliberately — that statement lives in a file about
the measure, and putting a double factorial inside it would move a combinatorial identity somewhere
it cannot be maintained. A `Lattice`-layer file stating the explicit constant is the natural next
step and is **not done, not costed** (`ERRATUM 194`).

**And the other half of the gap against `LatticeFourPointClustering.connected_smeared_le` is
untouched here**, because it is not a counting question: that bound uses `‖f‖₁·‖g‖₁` where the
general route uses a common `ℓ¹` bound `C` on every test function.

No measure, integral or test function appears in this file.
-/

namespace PairingCount

open Equiv Function Involutions PairingSplit PairingGlue

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The filter and the subtype are the same count

`PairingGlue.card_respecting` counts the respecting matchings as a subtype of the PERMUTATIONS,
carrying both clauses as a conjunction. Every consumer downstream — `PairingCluster`,
`LatticeTruncatedCount` — meets them instead as a `Finset.filter` on the matchings. The two are
the same number and `Equiv.subtypeSubtypeEquivSubtypeInter` is why. -/

/-- The respecting matchings as a `Finset.filter`, counted by the product of the two sides. -/
theorem card_filter_respects (S : Finset ι) :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => RespectsSplit S σ.1)).card
      = Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
        * Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _} := by
  classical
  rw [← card_respecting S, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

/-! ## 2. Respecting plus crossing is all of them -/

/-- **THE PARTITION, AS AN ADDITION.** Every pairing either respects the split or crosses it, so
the two counts add to the total. Stated this way on purpose: the subtraction below is derived from
it rather than the other way round, so a truncated `ℕ`-subtraction can never be the reason a
statement in this file is true. -/
theorem card_respecting_add_card_crossing (S : Finset ι) :
    Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
        * Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _}
      + (Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => ¬ RespectsSplit S σ.1)).card
      = Fintype.card ↑(perfectMatchings ι) := by
  classical
  rw [← card_filter_respects S, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- The same fact as a subtraction, which is the shape a caller reading
`LatticeTruncatedCount.count_le_card` will expect. -/
theorem card_crossing_eq (S : Finset ι) :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => ¬ RespectsSplit S σ.1)).card
      = Fintype.card ↑(perfectMatchings ι)
        - Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
          * Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _} := by
  have := card_respecting_add_card_crossing S
  omega

/-! ## 3. The two sides, in closed form -/

omit [Fintype ι] in
/-- The near side of a split of even size has `(|S|−1)‼` pairings. The ambient `Fintype ι` plays
no part: the near side is finite because `S` is a `Finset`, not because `ι` is finite. -/
theorem card_pm_mem {j : ℕ} (S : Finset ι) (hS : S.card = 2 * j) :
    Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
      = Nat.doubleFactorial (2 * j - 1) :=
  card_perfectMatchings_eq_doubleFactorial _ (by rw [Fintype.card_coe]; exact hS)

/-- And the far side has `(|ι|−|S|−1)‼`. The subtraction `n − j` is not truncated: `S` is a subset
of a type of size `2n`, so `2j ≤ 2n`. -/
theorem card_pm_not_mem {n j : ℕ} (S : Finset ι) (hι : Fintype.card ι = 2 * n)
    (hS : S.card = 2 * j) :
    Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _}
      = Nat.doubleFactorial (2 * (n - j) - 1) := by
  have hle : S.card ≤ Fintype.card ι := by
    simpa [Finset.card_univ] using Finset.card_le_univ S
  refine card_perfectMatchings_eq_doubleFactorial _ ?_
  rw [Fintype.card_subtype_compl, Fintype.card_coe, hι, hS]
  omega

/-! ## 4. The count -/

/-- **THE CLOSED FORM.** At `|ι| = 2n` and `|S| = 2j` the pairings that cross the split number
`(2n−1)‼ − (2j−1)‼·(2(n−j)−1)‼`. -/
theorem card_crossing_doubleFactorial {n j : ℕ} (S : Finset ι) (hι : Fintype.card ι = 2 * n)
    (hS : S.card = 2 * j) :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => ¬ RespectsSplit S σ.1)).card
      = Nat.doubleFactorial (2 * n - 1)
        - Nat.doubleFactorial (2 * j - 1) * Nat.doubleFactorial (2 * (n - j) - 1) := by
  rw [card_crossing_eq S, card_pm_mem S hS, card_pm_not_mem S hι hS,
    card_perfectMatchings_eq_doubleFactorial ι hι]

/-- **AND IT IS ALWAYS STRICTLY FEWER THAN THE TOTAL**, at every even split of an even index set —
so `LatticeTruncatedCount.abs_integral_prod_sub_mul_le_count` is strictly sharper than the form it
replaces, everywhere it applies and not just at the instance that was checked. **No non-emptiness
is needed**: the far side may be empty, and the empty type has exactly one pairing. -/
theorem card_crossing_lt {n j : ℕ} (S : Finset ι) (hι : Fintype.card ι = 2 * n)
    (hS : S.card = 2 * j) :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => ¬ RespectsSplit S σ.1)).card
      < Fintype.card ↑(perfectMatchings ι) := by
  have hadd := card_respecting_add_card_crossing S
  have hpos : 0 < Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
      * Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _} := by
    rw [card_pm_mem S hS, card_pm_not_mem S hι hS]
    exact Nat.mul_pos (Nat.doubleFactorial_pos _) (Nat.doubleFactorial_pos _)
  omega

/-! ## 5. The checks

Two instances, each with two routes to its number and neither route passing through the other.
`Fin 6` is chosen over `LatticeTruncatedCount`'s `Fin 4` because at `Fin 4` the product is `1·1`,
where a formula that had lost a factor altogether would still pass. **What the first instance
catches is the near side and not the far one** — the two factors are `3` and `1` — and saying so is
better than implying it exercises both. The second instance is the degenerate one, where the count
is the whole of `Fin 6`'s fifteen pairings. -/

set_option maxRecDepth 10000 in
/-- **THE CHECK, BY ENUMERATION.** `decide` runs over the permutations of `Fin 6`, keeps the
pairings, and counts those that fail to respect `{0, 1, 2, 3}`. -/
theorem card_crossing_fin_six :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings (Fin 6)) =>
      ¬ RespectsSplit ({0, 1, 2, 3} : Finset (Fin 6)) σ.1)).card = 12 := by
  decide

/-- **THE SAME NUMBER FROM THE FORMULA**, which never enumerates anything: `Fin 6` has `5‼ = 15`
pairings, the split's two sides have `3‼ = 3` and `1‼ = 1`, and `15 − 3·1 = 12`. -/
theorem card_crossing_fin_six_via_formula :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings (Fin 6)) =>
      ¬ RespectsSplit ({0, 1, 2, 3} : Finset (Fin 6)) σ.1)).card = 12 := by
  have h := card_crossing_doubleFactorial (n := 3) (j := 2)
    ({0, 1, 2, 3} : Finset (Fin 6)) (by simp) (by decide)
  norm_num [Nat.doubleFactorial] at h
  exact h

set_option maxRecDepth 10000 in
/-- **THE SECOND CHECK, BY ENUMERATION.** Nothing respects a split whose near side has one
element, because a single element cannot be paired with anything inside it. -/
theorem card_crossing_fin_six_odd :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings (Fin 6)) =>
      ¬ RespectsSplit ({0} : Finset (Fin 6)) σ.1)).card = 15 := by
  decide

/-- **THE SAME NUMBER FROM `card_crossing_eq`**, which the closed form cannot reach: that theorem
asks for an even split, and this one is odd. `Involutions.card_perfectMatchings_eq_zero_of_odd`
supplies the missing factor as `0`. **The total is taken from the double-factorial theorem and not
from `Involutions.card_perfectMatchings_fin_six`**, which is itself a `decide` over the
permutations of `Fin 6` — routing through it would have made this proof and the one above share
their enumeration, and then the pair would not be two routes. -/
theorem card_crossing_fin_six_odd_via_formula :
    (Finset.univ.filter (fun σ : ↑(perfectMatchings (Fin 6)) =>
      ¬ RespectsSplit ({0} : Finset (Fin 6)) σ.1)).card = 15 := by
  have htot : Fintype.card ↑(perfectMatchings (Fin 6)) = 15 := by
    rw [card_perfectMatchings_eq_doubleFactorial (Fin 6) (k := 3) (by simp)]
    norm_num [Nat.doubleFactorial]
  rw [card_crossing_eq ({0} : Finset (Fin 6)), htot,
    card_perfectMatchings_eq_zero_of_odd _ (by decide)]
  simp

end PairingCount
