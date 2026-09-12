import SecularPartValueAbove

/-!
# `K_{1,1,2,2}`, exactly: four eigenvalues, and the doubled lower bound is attained

`SignlessDoublingFails` exhibited `K_{1,1,2,2}` as the graph where a part value **coincides with a
pole**, so the trichotomy's cover of three `s`-element families overlaps and `#spec < 3s`. It gave
the count only as `< 6`, and four entries since have carried *the exact count at `K_{1,1,2,2}`* in
their `STILL OPEN` lists. **It is four**, and every ingredient was already in the chain.

**WHY IT NEEDED A UNIT AND NOT A LINE.** The trichotomy's cover here is
`{5, 4} ∪ {4, 2} ∪ {6 ± 2√2}` — **five** values, not four, and the cover is only an upper bound:
`5 = N − 1` is a part value of the singleton parts and **is not an eigenvalue**. Excluding a value
is the step the chain's usual criterion cannot take here, because
`isEigenvalue_signless_iff_secular` is stated **off** the part values and `5` is one. What does it
is `UnbalancedMultipartiteSecularEquation.finrank_signless_size_secular_zero`, which gives the
eigenspace at a part value of size `n` the dimension `k_n · (n − 1)` when the secular sum there
misses `−1` — and at `n = 1` that is **zero**. So the exclusion is available exactly because the
part is a singleton.

## What is proved

**`secularSum_P1122`** — the secular sum in closed form, `2/(4 − μ) + 4/(2 − μ)`, off the two
poles.

**`root_iff`** — off the poles the secular equation is `μ² − 12μ + 28 = 0`, whose roots are
`6 ± 2√2`. Proved by clearing denominators and factoring against `√2² = 2`; the roots are named
`lo` and `hi` and bracketed numerically, `3 < lo < 3.2` and `8.8 < hi < 9`, which is what keeps
them off the part values and the poles.

**`isEigen_four_P1122`, `isEigen_two_P1122`, `isEigen_root`** — the four eigenvalues, each from
the chain's own membership lemma: `4 = N − 2` from `isEigen_part_value` at a part of size two,
`2 = N − 2·2` from `isEigen_pole` at the same part, and the two irrational roots from
`isEigenvalue_signless_iff_secular`. The first two carry the graph's name because
`SignlessBracketAttained` has an `isEigen_four` and an `isEigen_two` of its own, about `K_{2,2}`
(`newnames_scan`, caught before the commit).

**`not_isEigen_five`** — **the exclusion, which is the new step**: `5 = N − 1` is a part value and
is not an eigenvalue, because the secular sum there is `−10/3` and the eigenspace dimension at a
part value of size `1` is `k₁ · 0 = 0`.

**`spectrum_P1122`, `card_spectrum_P1122_eq_four`** — so the spectrum is exactly
`{2, 4, 6 − 2√2, 6 + 2√2}` and has **four** elements.

**`card_spectrum_eq_two_mul_sizes_P1122`** — and four is `2s`. `SignlessDoubleBracket` proved
`2s ≤ #spec` under hypotheses this graph fails (its part values and poles are not `2s` distinct
values — that is the whole point of the graph), and `SignlessDoublingFails` proved `#spec < 3s`
here. **The count lands on the doubled lower bound anyway.** It is the chain's second exact count
at a graph that is not sharp — `SignlessPart133Complete` gave `K_{1,3,3}` the spectrum `{1, 4, 9}`
at entry 180 — and the two sit on opposite sides of that bound: `K_{1,3,3}` has three eigenvalues
against `2s = 4` and is **below** it, `K_{1,1,2,2}` has four and is **on** it. Both have `s = 2`.

## What is NOT here

* **NO MULTIPLICITIES, AND THE CHAIN'S COUNT DOES NOT REACH THEM HERE.** Four distinct values is
  not four eigenvalues: the graph has six vertices and nothing here says how the six split. The
  part-value dimension count is unavailable at `4` for a stated reason — it needs no part
  half-sized, `2 · 1 = 2` is the size of the other parts, so the hypothesis fails at exactly this
  graph. Not attempted (`ERRATUM 246`).
* **NO CHARACTERISTIC POLYNOMIAL**, which would need the multiplicities.
* **NO GENERAL STATEMENT.** *When does the trichotomy's cover fail to be attained?* is exactly the
  question this graph raises and it is not asked here: the exclusion runs through `n = 1`, and
  whether a part value of size `≥ 2` is ever missed is untouched.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): this file is about one graph and its
theorems take none, beyond the two poles' exclusion inside `secularSum_P1122` and `root_iff`.
**No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessP1122Exact

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessDoublingFails SignlessDoubleBracket
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

/-! ## 1. The graph, its total, and its two sizes -/

theorem total_P1122 : Fintype.card (Σ i, P1122 i) = 6 := by decide

theorem size_cases (i : Fin 4) :
    Fintype.card (P1122 i) = 1 ∨ Fintype.card (P1122 i) = 2 := by
  rw [card_P1122]; have := i.isLt; omega

/-! ## 2. The secular equation, solved -/

theorem secularSum_P1122 (μ : ℝ) (h4 : μ ≠ 4) (h2 : μ ≠ 2) :
    secularSum (V := P1122) μ = 2 / (4 - μ) + 4 / (2 - μ) := by
  have hd4 : (4 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h4)
  have hd2 : (2 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h2)
  simp only [secularSum, total_P1122, card_P1122, Fin.sum_univ_four]
  norm_num
  field_simp
  ring

/-- The smaller secular root, `6 - 2√2`. -/
noncomputable def lo : ℝ := 6 - 2 * Real.sqrt 2

/-- The larger secular root, `6 + 2√2`. -/
noncomputable def hi : ℝ := 6 + 2 * Real.sqrt 2

theorem sqrt2_bounds : 1.4 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.5 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h, h0]

theorem lo_bounds : 3 < lo ∧ lo < 3.2 := by
  obtain ⟨a, b⟩ := sqrt2_bounds; constructor <;> · rw [lo]; linarith

theorem hi_bounds : 8.8 < hi ∧ hi < 9 := by
  obtain ⟨a, b⟩ := sqrt2_bounds; constructor <;> · rw [hi]; linarith

/-- **THE SECULAR ROOTS ARE `6 ± 2√2`.** -/
theorem root_iff (μ : ℝ) (h4 : μ ≠ 4) (h2 : μ ≠ 2) :
    secularSum (V := P1122) μ = -1 ↔ μ = lo ∨ μ = hi := by
  have hd4 : (4 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h4)
  have hd2 : (2 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h2)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  rw [secularSum_P1122 μ h4 h2, div_add_div _ _ hd4 hd2,
    div_eq_iff (mul_ne_zero hd4 hd2), lo, hi]
  constructor
  · intro h
    have hq : (μ - (6 - 2 * Real.sqrt 2)) * (μ - (6 + 2 * Real.sqrt 2)) = 0 := by
      nlinarith [hs]
    rcases mul_eq_zero.mp hq with h' | h'
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith [hs]

/-! ## 3. The four eigenvalues -/

theorem isEigen_four_P1122 : IsEigen P1122 4 := by
  have h := isEigen_part_value (V := P1122) (fun _ => ⟨0⟩) 2 (by decide) (by decide)
  rwa [show ((Fintype.card (Σ i, P1122 i) : ℝ) - Fintype.card (P1122 2)) = 4 from by
    rw [total_P1122, card_P1122]; norm_num] at h

theorem isEigen_two_P1122 : IsEigen P1122 2 := by
  have h := isEigen_pole (V := P1122) (fun _ => ⟨0⟩) 2 (by decide) (by decide)
  rwa [show ((Fintype.card (Σ i, P1122 i) : ℝ) - 2 * Fintype.card (P1122 2)) = 2 from by
    rw [total_P1122, card_P1122]; norm_num] at h

theorem isEigen_root {μ : ℝ} (h4 : μ ≠ 4) (h2 : μ ≠ 2) (h5 : μ ≠ 5)
    (hroot : secularSum (V := P1122) μ = -1) : IsEigen P1122 μ := by
  refine (isEigenvalue_signless_iff_secular (V := P1122) (fun _ => ⟨0⟩) 0 ?_ ?_).mpr hroot
  · intro i
    rw [total_P1122]
    rcases size_cases i with h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h5 (by linarith)
    · exact h4 (by linarith)
  · intro i
    rw [total_P1122]
    rcases size_cases i with h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h4 (by linarith)
    · exact h2 (by linarith)

/-! ## 4. And the fifth candidate is not one -/

theorem secularSum_five : secularSum (V := P1122) 5 = -(10 / 3) := by
  rw [secularSum_P1122 5 (by norm_num) (by norm_num)]; norm_num

/-- **THE PART VALUE OF THE SINGLETONS IS NOT AN EIGENVALUE**, which is what makes the
trichotomy's five-element cover into a four-element spectrum. -/
theorem not_isEigen_five : ¬ IsEigen P1122 5 := by
  have hfive : ((Fintype.card (Σ i, P1122 i) : ℝ) - (1 : ℕ)) = 5 := by
    rw [total_P1122]; norm_num
  have hfr := finrank_signless_size_secular_zero (V := P1122) (n := 1)
    (by norm_num) (by rw [total_P1122]; norm_num) (fun _ => ⟨0⟩)
    (by intro i; rcases size_cases i with h | h <;> rw [h] <;> norm_num)
    (by rw [hfive, secularSum_five]; norm_num)
  rw [hfive] at hfr
  intro hx
  have hpos := (isEigenvector_iff_finrank_pos
    (signlessLap (completeMultipartiteGraph P1122)) (5 : ℝ)).mp hx
  rw [hfr] at hpos
  omega

/-! ## 5. So the spectrum is exactly those four -/

/-- **THE WHOLE SPECTRUM OF `Q` ON `K_{1,1,2,2}`.** -/
theorem spectrum_P1122 (μ : ℝ) :
    IsEigen P1122 μ ↔ μ = 2 ∨ μ = 4 ∨ μ = lo ∨ μ = hi := by
  constructor
  · intro hx
    rcases eigenvalue_trichotomy (V := P1122) (fun _ => ⟨0⟩) 0 hx with ⟨i, hi'⟩ | ⟨i, hi'⟩ | hs
    · rw [total_P1122] at hi'
      rcases size_cases i with h | h <;> rw [h] at hi' <;> push_cast at hi'
      · exact absurd (hi' ▸ hx) (by rw [show (6:ℝ) - 1 = 5 by norm_num] at hi' ⊢
                                    exact hi' ▸ not_isEigen_five)
      · right; left; linarith
    · rw [total_P1122] at hi'
      rcases size_cases i with h | h <;> rw [h] at hi' <;> push_cast at hi'
      · right; left; linarith
      · left; linarith
    · by_cases h4 : μ = 4
      · right; left; exact h4
      by_cases h2 : μ = 2
      · left; exact h2
      rcases (root_iff μ h4 h2).mp hs with h | h
      · right; right; left; exact h
      · right; right; right; exact h
  · obtain ⟨lo1, lo2⟩ := lo_bounds
    obtain ⟨hi1, hi2⟩ := hi_bounds
    rintro (rfl | rfl | rfl | rfl)
    · exact isEigen_two_P1122
    · exact isEigen_four_P1122
    · exact isEigen_root (by intro h; rw [h] at lo2; norm_num at lo2)
        (by intro h; rw [h] at lo1; norm_num at lo1)
        (by intro h; rw [h] at lo2; norm_num at lo2)
        ((root_iff lo (by intro h; rw [h] at lo2; norm_num at lo2)
          (by intro h; rw [h] at lo1; norm_num at lo1)).mpr (Or.inl rfl))
    · exact isEigen_root (by intro h; rw [h] at hi1; norm_num at hi1)
        (by intro h; rw [h] at hi1; norm_num at hi1)
        (by intro h; rw [h] at hi1; norm_num at hi1)
        ((root_iff hi (by intro h; rw [h] at hi1; norm_num at hi1)
          (by intro h; rw [h] at hi1; norm_num at hi1)).mpr (Or.inr rfl))

/-- **EXACTLY FOUR**, where `SignlessDoublingFails` had `< 6`. -/
theorem card_spectrum_P1122_eq_four :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ) ∧ S.card = 4 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds
  obtain ⟨hi1, hi2⟩ := hi_bounds
  refine ⟨{2, 4, lo, hi}, fun μ => ?_, ?_⟩
  · rw [spectrum_P1122 μ]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  · rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · norm_num at h
      · rw [← h] at lo1; norm_num at lo1
      · rw [← h] at hi1; norm_num at hi1),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · rw [← h] at lo2; norm_num at lo2
        · rw [← h] at hi1; norm_num at hi1),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        intro h; rw [h] at lo2; linarith),
      Finset.card_singleton]

/-- **AND FOUR IS `2s`** — the doubled lower bound, attained at a graph that is not sharp. -/
theorem card_spectrum_eq_two_mul_sizes_P1122 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ)
      ∧ S.card = 2 * (Finset.univ.image (fun i : Fin 4 => Fintype.card (P1122 i))).card := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_P1122_eq_four
  exact ⟨S, hS, by rw [sizes_P1122]; omega⟩

end SignlessP1122Exact
