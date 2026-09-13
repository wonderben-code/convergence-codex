import SecularPositivePart

/-!
# The positive-part bound is sufficient, not necessary, and silent wherever a size is unique

The signless frontier item lists, among what is open, *whether entry 198's positive-part bound is
**necessary***. **It is not**, and the way it fails is more informative than the answer.

`SecularPositivePart.secularSum_at_part_value_lt` proves `secularSum (N − nⱼ) < −1` from two
hypotheses: no size exactly half of `nⱼ`, and

```
∑_{2nᵢ < nⱼ} partTerm j i  <  k_j − 1
```

where `k_j` counts the parts of size `nⱼ`. This file says exactly what that hypothesis is doing.

## What is proved

**`secularSum_lt_iff`** — **the condition the estimate is really about, as a biconditional**:

```
secularSum (N − nⱼ) < −1   ↔   ∑_{nᵢ ≠ nⱼ} partTerm j i  <  k_j − 1
```

The same sum, over **every** index of a different size rather than only the small ones. The identity
behind it is `secularSum_at_part_value_eq` split at the indices of size `nⱼ`, each of which
contributes exactly `−1`; the rest is arithmetic. **So the positive-part bound is one sufficient way
to meet a condition that is equivalent to the conclusion**, and asking whether it is necessary is
asking whether the discarded non-positive terms can be spared. They cannot.

**`two_le_card_of_bound`** — **AND THE HYPOTHESIS IS UNSATISFIABLE WHEREVER A SIZE IS UNIQUE.** The
left side of the bound is a sum of **positive** terms, hence `≥ 0`, so the bound forces `k_j ≥ 2`.
`SecularPositivePart`'s estimate therefore says nothing at any part whose size occurs once — a
limitation of that theorem which is stated here for the first time, and which its own example
`P2299` satisfies by having every size twice.

**`P532`, `bound_fails_P532`, `secularSum_lt_P532`, `bound_not_necessary`** — the witness: parts of
sizes `5`, `3`, `2`. At `nⱼ = 5` the three terms are `−1`, `−3` and `+2`, so the positive part is
`2` against `k_j − 1 = 0` and **the bound fails**, while the sum is `−2` and **the conclusion
holds**. At the other two parts the positive part is empty and `k_j − 1 = 0`, so the bound fails
there too — `0 < 0` is false — and the conclusion holds there as well. **So on this family the
hypothesis fails at every part and the conclusion is true at every part.**

**AND THREE PARTS IS THE FEWEST**, which the file explains rather than proves: with `k_j = 1` the
conclusion needs the non-`nⱼ` terms to sum below `0`, and a single small part contributes something
positive, so a negative contributor — a part with `nⱼ < 2nᵢ` and `nᵢ ≠ nⱼ` — must also be present.
⚠ **That is an argument in this header and not a theorem** (`ERRATUM 246`).

## What is NOT here

* **NO WEAKER USABLE HYPOTHESIS.** `secularSum_lt_iff`'s right side is equivalent to the conclusion,
  so it is an identity and not an improvement: it says where to look, not how to get there. **A
  genuinely weaker sufficient condition — one that is easier to check than the conclusion and
  covers the witness — is not proposed.**
* **NOTHING ABOUT THE WITNESS'S SPECTRUM.** `P532` is used to refute a hypothesis's necessity and
  nothing more; `card_spectrum_eq_three_mul'` is **not** applied to it, its other conditions not
  having been checked.
* **NOTHING ABOUT `SignlessSharpBracket`'s THIRD CONDITION**, which `SignlessDoublingFails` already
  separated into a necessary half and a sufficient half. This file is about entry 198's replacement
  for it, not about the original.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype`/`DecidableEq` on the
index and on each part, and `∀ i, Nonempty (V i)` where a part value is formed. The witness
statements take nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularBoundNotNecessary

open Finset SecularPositivePart UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The condition the estimate is really about -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE BICONDITIONAL.** The indices of size `nⱼ` contribute `−1` each; everything else is the
condition. -/
theorem secularSum_lt_iff (hne : ∀ i, Nonempty (V i)) (j : ι) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) < -1
      ↔ ∑ i ∈ Finset.univ.filter (fun i => Fintype.card (V i) ≠ Fintype.card (V j)),
            partTerm V j i
          < (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) - 1 := by
  classical
  have hsplit : ∑ i, partTerm V j i
      = ∑ i ∈ Finset.univ.filter (fun i => Fintype.card (V i) = Fintype.card (V j)),
          partTerm V j i
        + ∑ i ∈ Finset.univ.filter (fun i => Fintype.card (V i) ≠ Fintype.card (V j)),
          partTerm V j i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => Fintype.card (V i) = Fintype.card (V j))]
  have hsame : ∑ i ∈ Finset.univ.filter (fun i => Fintype.card (V i) = Fintype.card (V j)),
      partTerm V j i
      = -(Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) := by
    rw [Finset.sum_congr rfl fun i hi => partTerm_of_eq hne (Finset.mem_filter.mp hi).2]
    rw [Finset.sum_const, Fintype.card_subtype, nsmul_eq_mul]
    ring
  rw [secularSum_at_part_value_eq j, hsplit, hsame]
  constructor <;> intro h <;> linarith

/-! ## 2. The bound is silent wherever a size is unique -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **A SUM OF POSITIVE TERMS IS NON-NEGATIVE**, so the bound forces at least two parts of the
size it is stated at. -/
theorem two_le_card_of_bound (j : ι)
    (hbound : ∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)), partTerm V j i
      < (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) - 1) :
    2 ≤ Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} := by
  classical
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.univ.filter
      (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)), partTerm V j i := by
    refine Finset.sum_nonneg fun i hi => ?_
    have h2 : 2 * Fintype.card (V i) < Fintype.card (V j) := (Finset.mem_filter.mp hi).2
    have hden : (0 : ℝ) < (Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i) := by
      have : (2 * Fintype.card (V i) : ℝ) < (Fintype.card (V j) : ℝ) := by exact_mod_cast h2
      linarith
    have hnum : (0 : ℝ) ≤ (Fintype.card (V i) : ℝ) := Nat.cast_nonneg _
    exact div_nonneg hnum hden.le
  have hgt : (1 : ℝ) < (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) := by
    linarith
  exact_mod_cast hgt

/-! ## 3. The witness: parts of five, three and two -/

/-- Sizes `5`, `3`, `2`. At `nⱼ = 5` the terms are `−1`, `−3`, `+2`. -/
abbrev P532 : Fin 3 → Type := fun i => Fin (![5, 3, 2] i)

theorem card_P532 (i : Fin 3) : Fintype.card (P532 i) = ![5, 3, 2] i := by simp [P532]

theorem nonempty_P532 (i : Fin 3) : Nonempty (P532 i) := by
  fin_cases i <;> exact ⟨⟨0, by norm_num⟩⟩

theorem card_same_P532 (j : Fin 3) :
    Fintype.card {k : Fin 3 // Fintype.card (P532 k) = Fintype.card (P532 j)} = 1 := by
  fin_cases j <;> decide

/-- **THE BOUND FAILS, AT EVERY PART.** At `nⱼ = 5` the positive part is `2` against `0`; at the
other two it is the empty sum, `0`, and `0 < 0` is false. -/
theorem bound_fails_P532 (j : Fin 3) :
    ¬ (∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (P532 i) < Fintype.card (P532 j)), partTerm P532 j i
      < (Fintype.card {k : Fin 3 // Fintype.card (P532 k) = Fintype.card (P532 j)} : ℝ) - 1) := by
  rw [card_same_P532 j, Finset.sum_filter]
  simp only [partTerm, card_P532]
  fin_cases j <;> norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **AND THE CONCLUSION HOLDS, AT EVERY PART.** -/
theorem secularSum_lt_P532 (j : Fin 3) :
    secularSum (V := P532)
      ((Fintype.card (Σ i, P532 i) : ℝ) - Fintype.card (P532 j)) < -1 := by
  rw [secularSum_lt_iff nonempty_P532 j, card_same_P532 j, Finset.sum_filter]
  simp only [partTerm, card_P532]
  fin_cases j <;> norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **SO THE POSITIVE-PART BOUND IS SUFFICIENT AND NOT NECESSARY**, which is the clause the
signless frontier item lists as open. -/
theorem bound_not_necessary :
    ∀ j : Fin 3,
      ¬ (∑ i ∈ Finset.univ.filter
          (fun i => 2 * Fintype.card (P532 i) < Fintype.card (P532 j)), partTerm P532 j i
        < (Fintype.card {k : Fin 3 // Fintype.card (P532 k) = Fintype.card (P532 j)} : ℝ) - 1)
      ∧ secularSum (V := P532)
          ((Fintype.card (Σ i, P532 i) : ℝ) - Fintype.card (P532 j)) < -1 :=
  fun j => ⟨bound_fails_P532 j, secularSum_lt_P532 j⟩

end SecularBoundNotNecessary
