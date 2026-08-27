import PairingSplit

/-!
# How big a crossing pairing can be

`PairingRelabel.integral_prod_split` deletes the crossing pairings, because it assumes the weight
across the split is exactly zero. **Clustering proper does not get to delete them**: the weight
across is small, not absent, and what is wanted is a bound on what the crossing terms contribute.
This file is the per-term half of that bound.

A crossing pairing carries at least one factor from across the split. Bound that factor by `ε`,
bound every other factor by `M`, and the term is at most `ε · M^(r − 1)` where `r` is the number
of pairs. **`r` is the same for every perfect matching** — half the indices — and §1 proves it,
because a bound whose exponent depends on the matching is not a bound on the sum.

## What is proved

* **`two_mul_card_filter_lt`** — a perfect matching's representative set has exactly half the
  indices. The two halves `{i < σ i}` and `{σ i < i}` partition the index type (no fixed point, so
  trichotomy has two cases) and `σ` swaps them;
* **`abs_prod_le_of_not_respects`** — a pairing product over a representative set, at a matching
  that does NOT respect the split, is at most `ε · M^(r − 1)`. **Which index carries the crossing
  factor is not known to the caller**, so the proof locates it rather than being handed it, and
  symmetry of the weight is what lets it use either member of the crossing pair;
* `card_filter_lt_eq` — the count as a number rather than a doubled one;
* **`card_filter_lt_fin_four`, `two_mul_card_filter_lt_fin_four`** — **the check**. At `Fin 4` and
  the matching pairing `0` with `2` and `1` with `3`, `decide` enumerates the representative set
  and finds two elements; §1, which enumerates nothing, says two doubled is four.
  `mem_perfectMatchings_fin_four` establishes the instance rather than assuming it — a first draft
  took it as a hypothesis, which would have made the check conditional on something unproved.

## What is NOT here

The sum, and therefore the estimate. Summing these bounds needs the number of crossing matchings,
which is at most the number of matchings and is `(k−1)‼` — a bound the estate has
(`Involutions.card_perfectMatchings_fin_eq_doubleFactorial`) and which is not consumed here.
**Not costed** (`ERRATUM 194`). No measure, integral or test function appears.
-/

namespace PairingBound

open Equiv Function Involutions PairWeightRep PairingSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-! ## 1. Every perfect matching has the same number of pairs -/

omit [DecidableEq ι] in
/-- **A PERFECT MATCHING PAIRS UP HALF THE INDICES.** `σ` maps `{i < σ i}` bijectively onto
`{σ i < i}` — it is its own inverse and reverses the comparison — and the two sets partition the
index type because `σ` has no fixed point. -/
theorem two_mul_card_filter_lt {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) :
    2 * (Finset.univ.filter (fun i => i < σ i)).card = Fintype.card ι := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hne : ∀ i, σ i ≠ i := hσ.2
  have hswap : (Finset.univ.filter (fun i => i < σ i)).card
      = (Finset.univ.filter (fun i => σ i < i)).card := by
    refine Finset.card_bij' (fun a _ => σ a) (fun b _ => σ b) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hinv a]; exact ha
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [hinv b]; exact hb
    · intro a _; exact hinv a
    · intro b _; exact hinv b
  have hunion : (Finset.univ.filter (fun i => i < σ i))
      ∪ (Finset.univ.filter (fun i => σ i < i)) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy i (σ i) with h | h | h
    · exact Or.inl h
    · exact absurd h.symm (hne i)
    · exact Or.inr h
  have hdisj : Disjoint (Finset.univ.filter (fun i => i < σ i))
      (Finset.univ.filter (fun i => σ i < i)) := by
    refine Finset.disjoint_left.mpr fun i hi hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact absurd hi (not_lt.mpr hj.le)
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ] at this
  omega

/-! ## 2. A crossing term is small -/

omit [Fintype ι] [DecidableEq ι] in
/-- **A CROSSING PAIRING IS AT MOST `ε · M^(r−1)`.** One factor comes from across the split and
is bounded by `ε`; the remaining `r − 1` are bounded by `M`. Which index carries the crossing
factor is not known to the caller, which is why the proof locates it rather than being told. -/
theorem abs_prod_le_of_not_respects {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S R : Finset ι} (hR : IsRepSet σ R)
    {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |w i j| ≤ ε) (hall : ∀ i j, |w i j| ≤ M)
    (hns : ¬ RespectsSplit S σ) :
    |∏ i ∈ R, w i (σ i)| ≤ ε * M ^ (R.card - 1) := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  -- locate an index of `R` whose factor crosses the split
  obtain ⟨i₀, hi₀R, hi₀⟩ : ∃ i ∈ R, |w i (σ i)| ≤ ε := by
    rw [RespectsSplit, not_forall] at hns
    obtain ⟨i, hi⟩ := hns
    have hstep : ∀ a : ι, a ∈ S → σ a ∉ S → ∃ j ∈ R, |w j (σ j)| ≤ ε := by
      intro a ha hσa
      have hane : σ a ≠ a := fun h => hσa (by rw [h]; exact ha)
      by_cases haR : a ∈ R
      · exact ⟨a, haR, hcross a ha (σ a) hσa⟩
      · have : σ a ∈ R := by
          by_contra h; exact haR ((hR.2 a hane).mpr h)
        refine ⟨σ a, this, ?_⟩
        rw [hinv a, hw (σ a) a]
        exact hcross a ha (σ a) hσa
    by_cases him : i ∈ S
    · exact hstep i him fun h => hi (iff_of_true h him)
    · have hσim : σ i ∈ S := by
        by_contra h; exact hi (iff_of_false h him)
      exact hstep (σ i) hσim (by rw [hinv i]; exact him)
  -- split that factor off and bound the rest
  have hrest : |∏ i ∈ R.erase i₀, w i (σ i)| ≤ M ^ (R.card - 1) :=
    calc |∏ i ∈ R.erase i₀, w i (σ i)| = ∏ i ∈ R.erase i₀, |w i (σ i)| := Finset.abs_prod _ _
      _ ≤ ∏ _i ∈ R.erase i₀, M := Finset.prod_le_prod (fun i _ => abs_nonneg _)
          (fun i _ => hall i (σ i))
      _ = M ^ (R.erase i₀).card := by rw [Finset.prod_const]
      _ = M ^ (R.card - 1) := by rw [Finset.card_erase_of_mem hi₀R]
  rw [← Finset.prod_erase_mul R _ hi₀R, abs_mul]
  calc |∏ i ∈ R.erase i₀, w i (σ i)| * |w i₀ (σ i₀)|
      ≤ M ^ (R.card - 1) * ε :=
        mul_le_mul hrest hi₀ (abs_nonneg _) (pow_nonneg hM0 _)
    _ = ε * M ^ (R.card - 1) := mul_comm _ _

/-! ## 3. The count as a number, and the check -/

omit [DecidableEq ι] in
/-- The representative set's size, as a number rather than a doubled one. -/
theorem card_filter_lt_eq {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) :
    (Finset.univ.filter (fun i => i < σ i)).card = Fintype.card ι / 2 := by
  have := two_mul_card_filter_lt hσ
  omega

/-- **THE CHECK.** At `Fin 4` and the matching pairing `0` with `2` and `1` with `3`, the
representative set is `{0, 1}` — computed by `decide`, not by §1 — and §1 says its size doubled is
`4`. Both routes reach `2`, and a lemma that had counted pairs or indices or something else would
not. -/
theorem card_filter_lt_fin_four :
    (Finset.univ.filter
      (fun i : Fin 4 => i < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i)).card
      = 2 := by decide

/-- The instance is a perfect matching, established rather than assumed. -/
theorem mem_perfectMatchings_fin_four :
    (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∈ perfectMatchings (Fin 4) := by
  refine ⟨?_, ?_⟩
  · intro x; revert x; decide
  · intro x; revert x; decide

/-- And §1 agrees with the enumeration, which is the comparison rather than either half alone. -/
theorem two_mul_card_filter_lt_fin_four : 2 * 2 = Fintype.card (Fin 4) := by
  rw [← card_filter_lt_fin_four]
  exact two_mul_card_filter_lt mem_perfectMatchings_fin_four

end PairingBound
