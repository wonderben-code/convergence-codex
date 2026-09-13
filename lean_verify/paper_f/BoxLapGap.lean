import BoxLapExtremes

/-!
# The box's spectral gap, exactly, and its multiplicity is the dimension

`BoxLapExtremes` computed the two extreme fibres of the box's Laplacian and said, in terms, that
this was **not** progress on the open `d ≥ 2` count: the ends are exactly where collisions cannot
happen. **The second-smallest value is the first place that argument has to do any work**, and it
still works — and this time the answer is not `1`.

## What is proved

**`gapVal`** — `2 − 2cos(π/(m+1))`, the value of one coordinate at frequency `1`.

**`gapVal_pos`** — it is positive, which is where `m ≥ 1` enters and is the only place it does.

**`boxLapEig_eq_gap_iff`** — **the fibre, characterised.** A frequency vector's eigenvalue is
`gapVal` exactly when **one coordinate is `1` and the rest are `0`.** Three cases and no more: two
coordinates at `1` or above give at least `2·gapVal`; one coordinate at `2` or above gives more than
`gapVal` by strict monotonicity; everything else is zero.

**`finrank_gap_box`** — **THE FILE'S THEOREM.** In every dimension `d` and at every side length
`m + 1` with `m ≥ 1`,

```
finrank (eigenspace of the box's Laplacian at 2 − 2cos(π/(m+1))) = d
```

**exactly `d`** — one mode per coordinate, and nothing else. So the free-boundary lattice
Laplacian's **spectral gap** is `2 − 2cos(π/(m+1))` and its multiplicity is the dimension.

**`finrank_gap_boxSignless`** — and the same for `Q`, free, the box being two-colourable.

## Why this one is not free the way the ends were

At the bottom the fibre is a singleton because every term is non-negative and vanishes only at
frequency zero — a statement about **one** coordinate. At the gap the argument has to compare
**configurations**: it must rule out two coordinates at `1` as well as one at `2`, and those are
different comparisons. That the two rulings-out happen to be the same inequality — `gapVal ≤
term(k)` for `k ≥ 1`, strict for `k ≥ 2` — is what keeps it short, and is a fact about the cosine
and not about the box.

**IT IS STILL NOT THE OPEN QUESTION.** Collisions are what make the `d ≥ 2` count hard, and at the
gap there are none for the same monotonicity reason as at the ends. **Three fibres are now known
and every interior one is not** (`ERRATUM 246`).

## What is NOT here

* **NO THIRD-SMALLEST.** At the next value the argument genuinely breaks: `2·gapVal` and
  `term(2)` can be compared for a given `m`, but which is smaller **depends on `m`**, so there is no
  uniform answer and a case split on the side length would be the beginning of the real count.
  **Not attempted.**
* **NO SECOND-LARGEST**, which is the mirror image of this file by the same argument with `m − 1`
  in place of `1`. It is **not written**, because nothing wants it and writing it would be a
  transcription rather than a result.
* **NOTHING ABOUT THE MASSIVE OPERATOR.** `FieldBoxRotation` works with `massive` and gives a
  **lower** bound of `2` on a multiplicity when two coordinates differ; that is a different
  statement about a different matrix and neither implies the other.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a dimension `d`, a side length written
`m + 1`, and `1 ≤ m` — that is, at least two sites along each axis, without which there is no second
eigenvalue to speak of. `d = 0` is allowed and the theorem reads `0 = 0`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BoxLapGap

open Real Finset BoxGraph BoxLapSpectrum BoxLapExtremes

/-- The gap value: one coordinate at frequency `1`. -/
noncomputable def gapVal (m : ℕ) : ℝ :=
  2 - 2 * Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))

theorem gapVal_pos {m : ℕ} (hm : 1 ≤ m) : 0 < gapVal m := by
  have h := term_strictMono (m := m) (a := 0) (b := 1) Nat.zero_lt_one hm
  rw [gapVal]
  simpa using h

theorem gapVal_le_term {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    gapVal m ≤ 2 - 2 * Real.cos ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
  rcases eq_or_lt_of_le hk with h | h
  · subst h; rw [gapVal]
  · rw [gapVal]; exact (term_strictMono h hkm).le

theorem gapVal_lt_term {m k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    gapVal m < 2 - 2 * Real.cos ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
  have h1 : (1 : ℕ) < k := hk
  rw [gapVal]
  exact term_strictMono h1 hkm

/-- **THE FIBRE, CHARACTERISED.** -/
theorem boxLapEig_eq_gap_iff {d m : ℕ} (hm : 1 ≤ m) {k : Fin d → ℕ} (hk : ∀ i, k i ≤ m) :
    boxLapEig d (m + 1) k = gapVal m ↔ ∃ i : Fin d, k i = 1 ∧ ∀ j, j ≠ i → k j = 0 := by
  classical
  rw [boxLapEig_eq]
  constructor
  · intro h
    -- some coordinate is nonzero, else the sum is zero
    have hex : ∃ i, k i ≠ 0 := by
      by_contra hno
      push Not at hno
      have : ∑ i, (2 - 2 * Real.cos ((k i : ℝ) * Real.pi / ((m : ℝ) + 1))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hno i]; simp
      rw [this] at h
      exact absurd h.symm (ne_of_gt (gapVal_pos hm))
    obtain ⟨i, hi⟩ := hex
    have hi1 : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr hi
    -- every other coordinate must vanish
    have hrest : ∀ j, j ≠ i → k j = 0 := by
      intro j hj
      by_contra hjne
      have hj1 : 1 ≤ k j := Nat.one_le_iff_ne_zero.mpr hjne
      have hpair : gapVal m + gapVal m
          ≤ ∑ l, (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) := by
        have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun l _ _ => term_nonneg m (k l))
        refine le_trans ?_ hle
        rw [Finset.sum_pair (Ne.symm hj)]
        exact add_le_add (gapVal_le_term hi1 (hk i)) (gapVal_le_term hj1 (hk j))
      rw [h] at hpair
      linarith [gapVal_pos hm]
    -- so the sum is that one term
    have honly : ∑ l, (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1)))
        = 2 - 2 * Real.cos ((k i : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : ∑ l ∈ Finset.univ.erase i,
          (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [hrest l (Finset.mem_erase.mp hl).1]
        simp
      rw [this, add_zero]
    rw [honly] at h
    refine ⟨i, ?_, hrest⟩
    by_contra hne
    have h2 : 2 ≤ k i := by omega
    exact absurd h.symm (ne_of_lt (gapVal_lt_term h2 (hk i)))
  · rintro ⟨i, hi, hrest⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi]
    have : ∑ l ∈ Finset.univ.erase i,
        (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [hrest l (Finset.mem_erase.mp hl).1]
      simp
    rw [this, add_zero, gapVal]

/-! ## 2. The fibre has exactly `d` points -/

/-- **THE FILE'S THEOREM.** The gap's eigenspace has dimension exactly the ambient dimension. -/
theorem finrank_gap_box (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ) - (gapVal m) • LinearMap.id)) = d := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m (gapVal m)]
  set e : Fin d → Site d (m + 1) :=
    fun i j => if j = i then ⟨1, by omega⟩ else ⟨0, by omega⟩ with he
  have hmem : ∀ k : Site d (m + 1),
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = gapVal m ↔ ∃ i, k = e i := by
    intro k
    rw [boxLapEig_eq_gap_iff hm (fun i => Nat.lt_succ_iff.mp (k i).isLt)]
    constructor
    · rintro ⟨i, hi, hrest⟩
      refine ⟨i, funext fun j => ?_⟩
      by_cases hj : j = i
      · subst hj
        refine Fin.ext ?_
        simp only [he, if_pos rfl]
        exact hi
      · refine Fin.ext ?_
        simp only [he, if_neg hj]
        exact hrest j hj
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp [he], fun j hj => by simp [he, hj]⟩
  have hinj : Function.Injective e := by
    intro a b hab
    by_contra hne
    have hax := congrFun hab a
    rw [show e a a = (⟨1, by omega⟩ : Fin (m + 1)) from by simp [he],
      show e b a = (⟨0, by omega⟩ : Fin (m + 1)) from by simp [he, hne]] at hax
    exact absurd (congrArg Fin.val hax) (by simp)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : Finset.univ.filter (fun k : Site d (m + 1) =>
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = gapVal m)
      = Finset.univ.image e := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [hmem k]
    exact exists_congr fun i => eq_comm
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **AND THE SAME FOR `Q`**, the box being two-colourable. -/
theorem finrank_gap_boxSignless (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (LaplacianSignless.signlessLap (boxGraph d (m + 1)))
          - (gapVal m) • LinearMap.id)) = d := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_boxSignlessLap d m (gapVal m),
    ← BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m (gapVal m)]
  exact finrank_gap_box d hm

end BoxLapGap
