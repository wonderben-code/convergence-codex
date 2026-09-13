import BoxLapMultiplicityExact
import SignlessConjugateMultiplicity
import FieldBoxRotation

/-!
# Both ends of the box's spectrum are simple, in every dimension and at every side length

`BoxLapMultiplicityExact` turned the box's Laplacian multiplicities into an **exact fibre count** —
how many frequency vectors give a value — and then closed with the honest fence: **that count is
unknown at `d ≥ 2`.** It is a question about sums of `2 − 2cos(kπ/n)` colliding, which is number
theory this estate has not touched and this file does not touch either.

**But two fibres need no number theory**, and this file computes them: **the smallest and the
largest value each come from exactly one frequency vector**, because each coordinate's contribution
is strictly increasing in its frequency and the extremes are attained coordinatewise. So the box's
ground state and top state are **simple** in every dimension and at every side length — the same
pair of statements `TorusRealMultiplicity` proves for the periodic lattice, now on the box, which
had them only at `d = 1`.

## What is proved

**`term_nonneg`, `term_eq_zero_iff`, `term_strictMono`** — the one-dimensional facts. Each
coordinate contributes `2 − 2cos(kπ/(m+1))`, which is `≥ 0`, is `0` only at `k = 0`, and is
**strictly increasing** for `k ≤ m` because the angle stays inside `[0, π)`. One Mathlib lemma,
`Real.cos_lt_cos_of_nonneg_of_le_pi`, does all three.

**`boxLapEig_eq_zero_iff`** — the sum vanishes exactly at the zero frequency vector. A sum of
non-negative terms.

> ⚠ **AND THE NON-NEGATIVITY IS CITED, NOT PROVED** (`ERRATUM 536`, second instance, same day). A
> draft of this file declared `boxLapEig_nonneg` for side length `m + 1`;
> `FieldBoxRotation.boxLapEig_nonneg` is the same statement **at every side length**, so the draft
> was both a duplicate and weaker. `newnames_scan` flagged it between writing and committing, as it
> did for `mem_of_walk` earlier today — **the second time in a day that a per-unit check caught a
> duplicate before it shipped**, which is the whole argument for that mode. The declaration is
> deleted and the import added; the two files could not see each other before, so this is the
> unknowing-duplicate class and not carelessness about an available name.

**`finrank_ground_state_box`** — hence **the box's Laplacian has a one-dimensional kernel**, in
every dimension and at every side length. (`0` is the ground state: the box is connected, so the
constants are the kernel — and what is new here is not that the kernel is nonzero but that the
**fibre count** says one, from the frequency side rather than the connectivity side.)

**`boxLapEig_le_top`, `boxLapEig_eq_top_iff`, `finrank_top_state_box`** — and the same at the other
end: `boxLapEig ≤ d · (2 − 2cos(mπ/(m+1)))` with equality only at the all-`m` frequency vector, so
the top eigenspace is a line too.

**`finrank_ground_state_boxSignless`, `finrank_top_state_boxSignless`** — **and both transfer to
`Q` for free**, the box being two-colourable:
`SignlessConjugateMultiplicity.finrank_eigenspace_boxSignlessLap` is the same fibre count for the
signless operator, so the two theorems above hold verbatim with `Q` in place of `L`.

## What is NOT here

* **THE FIBRE COUNT AT `d ≥ 2` IS STILL UNKNOWN**, and this file does not narrow it: the two fibres
  computed are the ones where no collision is possible, and **every interior value is untouched**
  (`ERRATUM 246`). Knowing the ends of a count is not knowing the count.
* **NO SPECTRAL GAP.** The second-smallest and second-largest values are not identified, and
  nothing here says how far the next eigenvalue is from either end.
* **NOTHING NEW ABOUT THE KERNEL AS SUCH.** That a connected graph's Laplacian kernel is the
  constants is standard and in the estate; what is new is the count arriving from the frequency
  side, which is the side the `d ≥ 2` question lives on.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a dimension `d` and a side length written
`m + 1`, and nothing else. `d = 0` and `m = 0` are included and true — the one-point box has one
frequency vector and one eigenvalue.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BoxLapExtremes

open Real Finset BoxGraph BoxLapSpectrum

/-! ## 1. One coordinate -/

/-- The angle `kπ/(m+1)` stays inside `[0, π]` for `k ≤ m + 1`. -/
theorem angle_le_pi {m k : ℕ} (hk : k ≤ m) :
    (k : ℝ) * Real.pi / ((m : ℝ) + 1) ≤ Real.pi := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hm]
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
  nlinarith [Real.pi_pos]

theorem angle_nonneg (m k : ℕ) : (0 : ℝ) ≤ (k : ℝ) * Real.pi / ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  positivity

theorem term_nonneg (m k : ℕ) :
    0 ≤ 2 - 2 * Real.cos ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
  nlinarith [Real.cos_le_one ((k : ℝ) * Real.pi / ((m : ℝ) + 1))]

/-- **STRICTLY INCREASING IN THE FREQUENCY**, as long as the larger one is at most `m`. -/
theorem term_strictMono {m a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    2 - 2 * Real.cos ((a : ℝ) * Real.pi / ((m : ℝ) + 1))
      < 2 - 2 * Real.cos ((b : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hlt : (a : ℝ) * Real.pi / ((m : ℝ) + 1) < (b : ℝ) * Real.pi / ((m : ℝ) + 1) := by
    apply div_lt_div_of_pos_right _ hm
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg m a) (angle_le_pi hb) hlt
  linarith

theorem term_eq_zero_iff {m k : ℕ} (hk : k ≤ m) :
    2 - 2 * Real.cos ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) = 0 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < k := Nat.pos_of_ne_zero hne
    have := term_strictMono (m := m) (a := 0) (b := k) hpos hk
    simp at this
    linarith
  · rintro rfl
    simp

/-! ## 2. The bottom -/

/-- **THE SUM VANISHES EXACTLY AT THE ZERO FREQUENCY VECTOR.** -/
theorem boxLapEig_eq_zero_iff {d m : ℕ} {k : Fin d → ℕ} (hk : ∀ i, k i ≤ m) :
    boxLapEig d (m + 1) k = 0 ↔ ∀ i, k i = 0 := by
  rw [boxLapEig_eq]
  constructor
  · intro h i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => term_nonneg m (k j))).mp h i (Finset.mem_univ i)
    exact (term_eq_zero_iff (hk i)).mp this
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i]
    simp

/-- **THE GROUND STATE IS SIMPLE**, in every dimension and at every side length. -/
theorem finrank_ground_state_box (d m : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)) = 1 := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m 0]
  have : ∀ k : Site d (m + 1),
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = 0 ↔ k = fun _ => 0 := by
    intro k
    rw [boxLapEig_eq_zero_iff (fun i => Nat.lt_succ_iff.mp (k i).isLt)]
    constructor
    · intro h; funext i; exact Fin.ext (by simpa using h i)
    · intro h i; rw [h]; rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_one]
  exact ⟨fun _ => 0, by ext k; simp [this k]⟩

/-! ## 3. The top -/

/-- The largest value: every coordinate at `m`. -/
noncomputable def topVal (d m : ℕ) : ℝ :=
  (d : ℝ) * (2 - 2 * Real.cos ((m : ℝ) * Real.pi / ((m : ℝ) + 1)))

theorem sum_const_topVal (d m : ℕ) :
    ∑ _i : Fin d, (2 - 2 * Real.cos ((m : ℝ) * Real.pi / ((m : ℝ) + 1))) = topVal d m := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, topVal]

theorem boxLapEig_le_top {d m : ℕ} {k : Fin d → ℕ} (hk : ∀ i, k i ≤ m) :
    boxLapEig d (m + 1) k ≤ topVal d m := by
  rw [boxLapEig_eq, ← sum_const_topVal d m]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases eq_or_lt_of_le (hk i) with h | h
  · rw [h]
  · exact (term_strictMono h le_rfl).le

/-- **AND IT IS ATTAINED ONLY THERE.** -/
theorem boxLapEig_eq_top_iff {d m : ℕ} {k : Fin d → ℕ} (hk : ∀ i, k i ≤ m) :
    boxLapEig d (m + 1) k = topVal d m ↔ ∀ i, k i = m := by
  constructor
  · intro h i
    by_contra hne
    have hlt : k i < m := lt_of_le_of_ne (hk i) hne
    have hstrict : ∑ j, (2 - 2 * Real.cos ((k j : ℝ) * Real.pi / ((m : ℝ) + 1)))
        < ∑ _j : Fin d, (2 - 2 * Real.cos ((m : ℝ) * Real.pi / ((m : ℝ) + 1))) := by
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, term_strictMono hlt le_rfl⟩
      rcases eq_or_lt_of_le (hk j) with hj | hj
      · rw [hj]
      · exact (term_strictMono hj le_rfl).le
    rw [boxLapEig_eq, ← sum_const_topVal d m] at h
    exact absurd h (ne_of_lt hstrict)
  · intro h
    rw [boxLapEig_eq, ← sum_const_topVal d m]
    exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- **THE TOP STATE IS SIMPLE**, in every dimension and at every side length. -/
theorem finrank_top_state_box (d m : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ)
          - (topVal d m) • LinearMap.id)) = 1 := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m (topVal d m)]
  have : ∀ k : Site d (m + 1),
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = topVal d m
        ↔ k = fun _ => (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    intro k
    rw [boxLapEig_eq_top_iff (fun i => Nat.lt_succ_iff.mp (k i).isLt)]
    constructor
    · intro h; funext i; exact Fin.ext (by simpa using h i)
    · intro h i; rw [h]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_one]
  exact ⟨fun _ => ⟨m, Nat.lt_succ_self m⟩, by ext k; simp [this k]⟩

/-! ## 4. And both transfer to `Q`, the box being two-colourable -/

theorem finrank_ground_state_boxSignless (d m : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (LaplacianSignless.signlessLap (boxGraph d (m + 1)))
          - (0 : ℝ) • LinearMap.id)) = 1 := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_boxSignlessLap d m 0,
    ← BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m 0]
  exact finrank_ground_state_box d m

theorem finrank_top_state_boxSignless (d m : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (LaplacianSignless.signlessLap (boxGraph d (m + 1)))
          - (topVal d m) • LinearMap.id)) = 1 := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_boxSignlessLap d m (topVal d m),
    ← BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m (topVal d m)]
  exact finrank_top_state_box d m

end BoxLapExtremes
