import SignlessRootOverlap

/-!
# `K_{1,1,2,3}`, exactly: four eigenvalues, and the two-overlap bound is attained

`SignlessRootOverlap` found `K_{1,1,2,3}` by enumerating size multisets — the chain's first graph
carrying **both** overlaps — and bounded its spectrum by `4`, with the bracket giving `≥ 3` and the
exact count left open. **It is four**, so the two-overlap bound is attained, at the graph that was
built to exercise it.

**WHAT THE COUNT COSTS, AND WHY IT IS SHORT.** Every ingredient is now general.
`SignlessSpectrumComplete.isEigen_iff` sorts each candidate; `PartValueSingleton` kills the
singleton part value `6` without a computation; and the only arithmetic is the secular equation,
which on this graph is `2/(5−μ) + 2/(3−μ) + 3/(1−μ) = −1`, i.e. the cubic
`μ³ − 16μ² + 67μ − 76 = 0`. **Its rational root is the part value `4`** — which is not a
coincidence but the second overlap itself, seen from the polynomial side — and the quadratic factor
`μ² − 12μ + 19` gives `6 ± √17`.

## What is proved

**`secularSum_P1123`, `root_iff_P1123`** — the sum in closed form off the three poles, and the
roots of the resulting cubic: `4`, `6 − √17`, `6 + √17`. The factorisation is a
`linear_combination` against `√17² = 17` rather than a `nlinarith`, which does not reach a cubic.

**`isEigen_five_P1123`, `isEigen_four_P1123`, `not_isEigen_six`, `isEigen_of_root`** —
the four eigenvalues and the one candidate that is not. `5` and `4` are part values of parts with
two and three vertices; `6 = N − 1` is the singleton part value and dies to
`PartValueSingleton.not_isEigen_sub_one` with **no arithmetic at all**, where the same exclusion
at `K_{1,1,2,2}` needed the sum computed by hand five entries ago.

**`spectrum_P1123`, `card_spectrum_P1123_eq_four`** — the spectrum is exactly
`{5, 4, 6 − √17, 6 + √17}`. The poles `3` and `1` are excluded because their sizes are **not
shared**, which is `isEigen_iff`'s second clause doing the work `pole_isEigen_iff` was written for.

**`two_overlap_bound_attained_P1123`** — and `4` is what `SignlessRootOverlap.bound_P1123` gives,
so **the two-overlap bound is attained**. Three graphs now have a general upper bound meeting a
computed spectrum: `K_{1,1,2,2}` at one overlap, `K_{1,3,3}` at the other, and this one at both.

## What is NOT here

* **NO MULTIPLICITIES, as of 2026-09-12 (entry 65).** Four distinct values among seven vertices,
  and nothing here says how the seven split.
* **NO CHARACTERISTIC POLYNOMIAL**, which would need them.
* **NO GENERAL STATEMENT ABOUT WHEN THE BOUND IS ATTAINED, as of 2026-09-12 (entry 65).** Three
  graphs attain it and no theorem says why; the honest reading is that the chain can compute
  exactly three spectra and all three happen to be tight, which is evidence and not a pattern.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE NAMES CARRY THE GRAPH, AND TWO SCANNERS ASKED FOR THAT.** `SignlessP1122Exact` has a `lo`
and a `hi` — different numbers, same type — and this file imports it transitively; `dupname_scan`
called that a duplicate signature and `newnames_scan` counted seven collisions in all. Every one
now ends in `_P1123`, so a reader grepping `lo` gets one answer.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): this file is about one graph and its
theorems take none beyond the three poles' exclusion inside `secularSum_P1123` and
`root_iff_P1123`.
**No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessP1123Exact

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessSpectrumComplete SignlessRootOverlap PartValueSingleton
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

/-! ## 1. The secular equation, solved -/

theorem size_cases_P1123 (i : Fin 4) :
    Fintype.card (P1123 i) = 1 ∨ Fintype.card (P1123 i) = 2 ∨ Fintype.card (P1123 i) = 3 := by
  rw [card_P1123]; have := i.isLt; omega

theorem secularSum_P1123 (μ : ℝ) (h5 : μ ≠ 5) (h3 : μ ≠ 3) (h1 : μ ≠ 1) :
    secularSum (V := P1123) μ = 2 / (5 - μ) + 2 / (3 - μ) + 3 / (1 - μ) := by
  have d5 : (5 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h5)
  have d3 : (3 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h3)
  have d1 : (1 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h1)
  simp only [secularSum, total_P1123, card_P1123, Fin.sum_univ_four]
  norm_num
  field_simp
  ring

/-- The smaller irrational root, `6 - √17`. -/
noncomputable def lo_P1123 : ℝ := 6 - Real.sqrt 17

/-- The larger irrational root, `6 + √17`. -/
noncomputable def hi_P1123 : ℝ := 6 + Real.sqrt 17

theorem sqrt17_bounds : 4.12 < Real.sqrt 17 ∧ Real.sqrt 17 < 4.13 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 17 by norm_num)
  have h0 := Real.sqrt_nonneg 17
  constructor <;> nlinarith [h, h0]

theorem lo_bounds_P1123 : 1.87 < lo_P1123 ∧ lo_P1123 < 1.88 := by
  obtain ⟨a, b⟩ := sqrt17_bounds; constructor <;> · rw [lo_P1123]; linarith

theorem hi_bounds_P1123 : 10.12 < hi_P1123 ∧ hi_P1123 < 10.13 := by
  obtain ⟨a, b⟩ := sqrt17_bounds; constructor <;> · rw [hi_P1123]; linarith

/-- **THE CUBIC `μ³ − 16μ² + 67μ − 76`, FACTORED.** Its rational root is the part value `4`. -/
theorem root_iff_P1123 (μ : ℝ) (h5 : μ ≠ 5) (h3 : μ ≠ 3) (h1 : μ ≠ 1) :
    secularSum (V := P1123) μ = -1 ↔ μ = 4 ∨ μ = lo_P1123 ∨ μ = hi_P1123 := by
  have d5 : (5 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h5)
  have d3 : (3 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h3)
  have d1 : (1 : ℝ) - μ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h1)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 17 by norm_num)
  rw [secularSum_P1123 μ h5 h3 h1, div_add_div _ _ d5 d3,
    div_add_div _ _ (mul_ne_zero d5 d3) d1,
    div_eq_iff (mul_ne_zero (mul_ne_zero d5 d3) d1), lo_P1123, hi_P1123]
  constructor
  · intro h
    have hq : (μ - 4) * ((μ - (6 - Real.sqrt 17)) * (μ - (6 + Real.sqrt 17))) = 0 := by
      linear_combination -h - (μ - 4) * hs
    rcases mul_eq_zero.mp hq with h' | h'
    · left; linarith
    · rcases mul_eq_zero.mp h' with h'' | h''
      · right; left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl)
    · norm_num
    · linear_combination (-(2 - Real.sqrt 17)) * hs
    · linear_combination (-(2 + Real.sqrt 17)) * hs

/-! ## 2. The four eigenvalues, and the two candidates that are not -/

theorem isEigen_five_P1123 : IsEigen P1123 5 := by
  refine (isEigen_iff (V := P1123) nonempty_P1123 (by decide) 5).mpr (Or.inl ⟨2, ?_, by decide⟩)
  rw [total_P1123, card_P1123]; norm_num

theorem isEigen_four_P1123 : IsEigen P1123 4 := by
  refine (isEigen_iff (V := P1123) nonempty_P1123 (by decide) 4).mpr (Or.inl ⟨3, ?_, by decide⟩)
  rw [total_P1123, card_P1123]; norm_num

/-- **THE SINGLETON PART VALUE DIES WITH NO ARITHMETIC.** -/
theorem not_isEigen_six : ¬ IsEigen P1123 6 := by
  have h := not_isEigen_sub_one (V := P1123) nonempty_P1123 (by decide)
  rwa [show ((Fintype.card (Σ i, P1123 i) : ℝ) - 1) = 6 from by rw [total_P1123]; norm_num] at h

theorem isEigen_of_root {μ : ℝ} (h6 : μ ≠ 6) (h5 : μ ≠ 5) (h4 : μ ≠ 4) (h3 : μ ≠ 3)
    (h1 : μ ≠ 1) (hroot : secularSum (V := P1123) μ = -1) : IsEigen P1123 μ := by
  refine (isEigen_iff (V := P1123) nonempty_P1123 (by decide) μ).mpr
    (Or.inr (Or.inr ⟨?_, ?_, hroot⟩))
  · intro j
    rw [total_P1123]
    rcases size_cases_P1123 j with h | h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h6 (by linarith)
    · exact h5 (by linarith)
    · exact h4 (by linarith)
  · intro j
    rw [total_P1123]
    rcases size_cases_P1123 j with h | h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h5 (by linarith)
    · exact h3 (by linarith)
    · exact h1 (by linarith)

/-! ## 3. So the spectrum is exactly those four -/

/-- **THE WHOLE SPECTRUM OF `Q` ON `K_{1,1,2,3}`.** -/
theorem spectrum_P1123 (μ : ℝ) : IsEigen P1123 μ ↔ μ = 5 ∨ μ = 4 ∨ μ = lo_P1123 ∨ μ = hi_P1123 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds_P1123
  obtain ⟨hi1, hi2⟩ := hi_bounds_P1123
  constructor
  · intro hx
    rcases (isEigen_iff (V := P1123) nonempty_P1123 (by decide) μ).mp hx with
      ⟨j, hj, h2⟩ | ⟨i, hpole', h2⟩ | ⟨hval, hpole, hs⟩
    · rw [total_P1123] at hj
      rcases size_cases_P1123 j with h | h | h <;> rw [h] at hj h2 <;> push_cast at hj
      · omega
      · left; linarith
      · right; left; linarith
    · rw [total_P1123] at hpole'
      rcases size_cases_P1123 i with h | h | h <;> rw [h] at hpole' h2 <;> push_cast at hpole'
      · left; linarith
      · rw [show Fintype.card {k : Fin 4 //
          2 * Fintype.card (P1123 k) = 2 * 2} = 1 from by decide] at h2; omega
      · rw [show Fintype.card {k : Fin 4 //
          2 * Fintype.card (P1123 k) = 2 * 3} = 1 from by decide] at h2; omega
    · have hp : ∀ n : ℝ, ((Fintype.card (Σ i, P1123 i) : ℝ) - n) = 7 - n := by
        intro n; rw [total_P1123]; norm_num
      have h5 : μ ≠ 5 := by
        intro h; exact hpole 0 (by rw [total_P1123, card_P1123]; push_cast; rw [h]; norm_num)
      have h3 : μ ≠ 3 := by
        intro h; exact hpole 2 (by rw [total_P1123, card_P1123]; push_cast; rw [h]; norm_num)
      have h1 : μ ≠ 1 := by
        intro h; exact hpole 3 (by rw [total_P1123, card_P1123]; push_cast; rw [h]; norm_num)
      rcases (root_iff_P1123 μ h5 h3 h1).mp hs with h | h | h
      · exact absurd (by rw [total_P1123, card_P1123]; push_cast; rw [h]; norm_num) (hval 3)
      · right; right; left; exact h
      · right; right; right; exact h
  · rintro (rfl | rfl | rfl | rfl)
    · exact isEigen_five_P1123
    · exact isEigen_four_P1123
    · exact isEigen_of_root (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) ((root_iff_P1123 lo_P1123 (by linarith) (by linarith) (by linarith)).mpr
          (Or.inr (Or.inl rfl)))
    · exact isEigen_of_root (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) ((root_iff_P1123 hi_P1123 (by linarith) (by linarith) (by linarith)).mpr
          (Or.inr (Or.inr rfl)))

/-- **EXACTLY FOUR.** -/
theorem card_spectrum_P1123_eq_four :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1123 μ) ∧ S.card = 4 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds_P1123
  obtain ⟨hi1, hi2⟩ := hi_bounds_P1123
  refine ⟨{5, 4, lo_P1123, hi_P1123}, fun μ => ?_, ?_⟩
  · rw [spectrum_P1123 μ]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  · rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · norm_num at h
      · rw [← h] at lo2; norm_num at lo2
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

/-- **AND THE TWO-OVERLAP BOUND IS ATTAINED.** -/
theorem two_overlap_bound_attained_P1123 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1123 μ) ∧ S.card ≤ 4 ∧ 4 ≤ S.card := by
  obtain ⟨S, hS, hle⟩ := bound_P1123
  obtain ⟨T, hT, hT4⟩ := card_spectrum_P1123_eq_four
  have hST : S = T := Finset.ext fun μ => by rw [hS μ, hT μ]
  exact ⟨S, hS, hle, by rw [hST, hT4]⟩

end SignlessP1123Exact
