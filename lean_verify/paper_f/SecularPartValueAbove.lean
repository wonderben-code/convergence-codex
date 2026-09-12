import SecularPositivePart

/-!
# The sharpness bound is one side of a two-sided criterion, and a graph needs the other

`SecularPositivePart` proved that a part value `N − nⱼ` is not a secular root when the **positive
part** of the secular sum there is smaller than `k_{nⱼ} − 1`, and fenced its own result: *the
positive-part bound is **sufficient** and there is no claim that it is necessary … whether every
failure of the bound costs sharpness is **open, not attempted***. **It does not, and this file
settles that in the negative with a graph.**

**WHY THE BOUND IS ONE-SIDED.** At `μ = N − nⱼ` the sum is `−k_{nⱼ} + (the terms off that size)`,
so it equals `−1` exactly when the off-size terms sum to `k_{nⱼ} − 1`. The previous file drives
the sum **below** `−1`; a sum driven **above** `−1` misses the root just as well, and the two
conditions between them are the whole criterion. The estate had only the lower half.

## What is proved

**`secularSum_at_part_value_split`** — the identity the previous file's estimate used internally
and did not state: at a part value the sum is `−k_{nⱼ}` plus the terms at indices of a different
size. Extracted rather than re-derived (`ERRATUM 521`'s rule read forwards).

**`part_value_secular_root_iff`** — **the exact criterion, replacing a sufficient condition by an
equivalence**: the part value is a secular root **iff** the off-size terms sum to `k_{nⱼ} − 1`.
Two lines from the split, and it is what makes *necessary* a decidable question rather than a
guess.

**`secularSum_at_part_value_gt`** — **the missing half**: if every index of a different size is
**small** — `2nᵢ < nⱼ`, so the negative class is empty — and the positive part is **larger** than
`k_{nⱼ} − 1, then the sum is `> −1`. The emptiness hypothesis is not decoration: without it the
negative terms are unbounded below and no lower bound on the sum survives.

**`P22299`, `bound_fails_P22299`, `bound_above_P22299`, `bound_below_P22299`,
`card_spectrum_P22299`** — **the witness, and it fails the old bound strictly rather than by
equality.** `K_{2,2,2,9,9}`: at the part value of the nines the positive part is
`2/5 + 2/5 + 2/5 = 6/5` against `k₉ − 1 = 1`, so `SecularPositivePart`'s hypothesis **fails**
(`bound_fails_P22299` gives `≥`, `bound_above_P22299` gives `>`, and the difference is the whole
point — `K_{1,3,3}` fails it by equality and is a genuine counterexample). At the part value of
the twos the positive class is empty and the old bound applies. **So the graph is sharp — exactly
`3s = 6` eigenvalues — and neither half of the criterion settles both of its part values.**

**`secularSum_P22299_nine`, `secularSum_P22299_two`** — and the two sums **exactly**, `−4/5` and
`−33/8`, so the numbers above are theorems rather than arithmetic done in a header
(`ERRATUM 58`'s rule applied to a docstring). They also make the estimates checkable against an
independently computed answer, which is the only reason a concrete graph needs them at all: the
general theorems exist for **families**, where no such computation is available.

**`positivePart_bound_not_necessary`** — the negative answer, stated as one theorem: there is a
family, an index, and a proof that the bound fails there while the spectrum is exactly `3s`.

## What is NOT here

* **THE CRITERION IS EXACT AND THE TWO SUFFICIENT CONDITIONS ARE NOT JOINTLY COMPLETE.** A sum can
  land on `−1` only by the off-size terms hitting `k_{nⱼ} − 1` exactly, but `>` needs the negative
  class **empty** and `<` needs it merely non-positive, so a graph with a non-empty negative class
  and a large positive part is decided by **neither** — `part_value_secular_root_iff` decides it
  and the two estimates do not. No such graph is exhibited. Not attempted (`ERRATUM 246`).
* **NO COUNT OF WHICH GRAPHS ARE SHARP.** The chain now has `K_{2,2}` (spectrum `{0,2,4}`),
  `K_{2,2,3,3}` and `K_{2,2,9,9}` sharp by the strict-spread and positive-part routes,
  `K_{2,2,2,9,9}` sharp by the route added here, `K_{1,3,3}` a counterexample and `K_{1,1,2,2}`
  below the bracket — **six graphs and no characterisation.**
* **NOTHING ABOUT `K_{1,1,2,2}`**, whose exact count `SignlessDoublingFails` still gives only as
  `< 6`.
* **NO MULTIPLICITIES, NO ROOT VALUES, NOTHING OVER `ℂ`, NO WALL MOVES, NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, with **both `DecidableEq`s omitted** on all three general theorems; the criterion takes
only `∀ i, Nonempty (V i)` and an index. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularPartValueAbove

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularPositivePart

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The identity behind the previous file's estimate -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- At a part value the secular sum is `-k` plus the terms at indices of a **different** size. -/
theorem secularSum_at_part_value_split (hne : ∀ i, Nonempty (V i)) (j : ι) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j))
      = -(Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ)
        + ∑ i ∈ Finset.univ.filter
            (fun i => ¬ Fintype.card (V i) = Fintype.card (V j)), partTerm V j i := by
  classical
  set E := Finset.univ.filter (fun i => Fintype.card (V i) = Fintype.card (V j)) with hE
  have hsplit : ∑ i, partTerm V j i
      = ∑ i ∈ E, partTerm V j i
        + ∑ i ∈ Finset.univ.filter
            (fun i => ¬ Fintype.card (V i) = Fintype.card (V j)), partTerm V j i :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hEsum : ∑ i ∈ E, partTerm V j i = -(E.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => partTerm_of_eq hne
      ((Finset.mem_filter.mp hi).2)), Finset.sum_const, nsmul_eq_mul]
    ring
  have hEcard : E.card = Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} := by
    rw [hE, ← Fintype.card_subtype]
  rw [secularSum_at_part_value_eq, hsplit, hEsum, hEcard]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE EXACT CRITERION.** A part value is a secular root precisely when the off-size terms sum
to `k − 1`; `SecularPositivePart`'s bound is the statement that they sum to less. -/
theorem part_value_secular_root_iff (hne : ∀ i, Nonempty (V i)) (j : ι) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) = -1
      ↔ ∑ i ∈ Finset.univ.filter
          (fun i => ¬ Fintype.card (V i) = Fintype.card (V j)), partTerm V j i
        = (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) - 1 := by
  rw [secularSum_at_part_value_split hne j]
  constructor <;> intro h <;> linarith

/-! ## 2. The half the estate did not have -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SUM ABOVE `-1`.** With the negative class empty, a positive part **larger** than
`k − 1` misses the root on the other side. -/
theorem secularSum_at_part_value_gt (hne : ∀ i, Nonempty (V i)) (j : ι)
    (hsmall : ∀ i, ¬ Fintype.card (V i) = Fintype.card (V j) →
      2 * Fintype.card (V i) < Fintype.card (V j))
    (hbound : (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) - 1
      < ∑ i ∈ Finset.univ.filter
          (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)), partTerm V j i) :
    -1 < secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) := by
  classical
  have hjpos : 0 < Fintype.card (V j) := Fintype.card_pos_iff.mpr (hne j)
  have hAeq : Finset.univ.filter (fun i => ¬ Fintype.card (V i) = Fintype.card (V j))
      = Finset.univ.filter (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hsmall i, fun h hcon => by omega⟩
  rw [secularSum_at_part_value_split hne j, hAeq]
  linarith

/-! ## 3. `K_{2,2,2,9,9}`, which the old bound cannot reach -/

/-- Three parts of two and two parts of nine. -/
abbrev P22299 : Fin 5 → Type := fun i => Fin (2 + 7 * (i.1 / 3))

theorem card_P22299 (i : Fin 5) : Fintype.card (P22299 i) = 2 + 7 * (i.1 / 3) := by
  simp [P22299]

theorem card_two_or_nine (j : Fin 5) :
    Fintype.card (P22299 j) = 2 ∨ Fintype.card (P22299 j) = 9 := by
  rw [card_P22299]; omega

theorem sizes_P22299 :
    (Finset.univ.image (fun i : Fin 5 => Fintype.card (P22299 i))).card = 2 := by decide

/-- **`SecularPositivePart`'s HYPOTHESIS FAILS HERE, AND STRICTLY.** At the nines the positive
part is `6/5` against a threshold of `1` — where `K_{1,3,3}` fails it by equality. -/
theorem bound_fails_P22299 (j : Fin 5) (hj : Fintype.card (P22299 j) = 9) :
    ¬ (∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (P22299 i) < Fintype.card (P22299 j)),
        partTerm P22299 j i
      < (Fintype.card {k : Fin 5 //
          Fintype.card (P22299 k) = Fintype.card (P22299 j)} : ℝ) - 1) := by
  rw [hj, show Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = 9} = 2 from by decide,
    Finset.sum_filter]
  simp only [partTerm, hj, card_P22299, Fin.sum_univ_five]
  norm_num

theorem bound_below_P22299 (j : Fin 5) (hj : Fintype.card (P22299 j) = 2) :
    ∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (P22299 i) < Fintype.card (P22299 j)),
        partTerm P22299 j i
      < (Fintype.card {k : Fin 5 //
          Fintype.card (P22299 k) = Fintype.card (P22299 j)} : ℝ) - 1 := by
  rw [hj, show Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = 2} = 3 from by decide,
    Finset.sum_filter]
  simp only [partTerm, hj, card_P22299, Fin.sum_univ_five]
  norm_num

theorem bound_above_P22299 (j : Fin 5) (hj : Fintype.card (P22299 j) = 9) :
    (Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = Fintype.card (P22299 j)} : ℝ) - 1
      < ∑ i ∈ Finset.univ.filter
          (fun i => 2 * Fintype.card (P22299 i) < Fintype.card (P22299 j)),
          partTerm P22299 j i := by
  rw [hj, show Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = 9} = 2 from by decide,
    Finset.sum_filter]
  simp only [partTerm, hj, card_P22299, Fin.sum_univ_five]
  norm_num

/-- **AND THE TWO SUMS, EXACTLY**, so the numbers this file's header quotes are theorems and not
arithmetic done in prose. At the nines `-2 + 6/5`; at the twos `-3 - 9/8`. Both estimates are
confirmed against them, one on each side of `-1`. -/
theorem secularSum_P22299_nine (j : Fin 5) (hj : Fintype.card (P22299 j) = 9) :
    secularSum (V := P22299)
      ((Fintype.card (Σ i, P22299 i) : ℝ) - Fintype.card (P22299 j)) = -(4 / 5) := by
  rw [secularSum_at_part_value_split (fun _ => ⟨0⟩) j,
    show Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = Fintype.card (P22299 j)} = 2 from
      by rw [hj]; decide,
    Finset.sum_filter]
  simp only [partTerm, hj, card_P22299, Fin.sum_univ_five]
  norm_num

theorem secularSum_P22299_two (j : Fin 5) (hj : Fintype.card (P22299 j) = 2) :
    secularSum (V := P22299)
      ((Fintype.card (Σ i, P22299 i) : ℝ) - Fintype.card (P22299 j)) = -(33 / 8) := by
  rw [secularSum_at_part_value_split (fun _ => ⟨0⟩) j,
    show Fintype.card {k : Fin 5 // Fintype.card (P22299 k) = Fintype.card (P22299 j)} = 3 from
      by rw [hj]; decide,
    Finset.sum_filter]
  simp only [partTerm, hj, card_P22299, Fin.sum_univ_five]
  norm_num

/-- **AND NO PART VALUE IS A SECULAR ROOT — ONE ON EACH SIDE.** -/
theorem not_root_P22299 (j : Fin 5) :
    secularSum (V := P22299)
      ((Fintype.card (Σ i, P22299 i) : ℝ) - Fintype.card (P22299 j)) ≠ -1 := by
  rcases card_two_or_nine j with hj | hj
  · have h := secularSum_at_part_value_lt (V := P22299) (fun _ => ⟨0⟩) j
      (by simp only [hj]; decide) (bound_below_P22299 j hj)
    linarith
  · have h := secularSum_at_part_value_gt (V := P22299) (fun _ => ⟨0⟩) j
      (by simp only [hj]; decide) (bound_above_P22299 j hj)
    linarith

/-- **THE SPECTRUM IS EXACTLY `3s = 6`.** -/
theorem card_spectrum_P22299 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P22299 μ) ∧ S.card = 6 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_eq_three_mul' (V := P22299) (fun _ => ⟨0⟩) ⟨0⟩
    (by decide) (by decide) (by decide) not_root_P22299
  rw [sizes_P22299] at hcard
  exact ⟨S, hS, by omega⟩

/-- **THE ANSWER TO THE QUESTION `SecularPositivePart` LEFT OPEN**: the positive-part bound is
sufficient and **not** necessary. -/
theorem positivePart_bound_not_necessary :
    (∃ j : Fin 5, ¬ (∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (P22299 i) < Fintype.card (P22299 j)),
        partTerm P22299 j i
      < (Fintype.card {k : Fin 5 //
          Fintype.card (P22299 k) = Fintype.card (P22299 j)} : ℝ) - 1))
    ∧ ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P22299 μ)
      ∧ S.card = 3 * (Finset.univ.image (fun i : Fin 5 => Fintype.card (P22299 i))).card := by
  refine ⟨⟨3, bound_fails_P22299 3 (by decide)⟩, ?_⟩
  obtain ⟨S, hS, hcard⟩ := card_spectrum_P22299
  exact ⟨S, hS, by rw [sizes_P22299]; omega⟩

end SecularPartValueAbove
