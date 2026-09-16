/-
  CycleEigenvalueDistinct: the cycle's eigenvalues are distinct on the half-range, they collide in
  pairs off it, and there are exactly `N/2 + 1` of them

  WHY THIS FILE EXISTS. Unit 89 named what blocks the wheel's multiplicity table: the values have
  to be **distinct** before a dimension count can be summed over them. The rim values are
  `2cos(2πk/N)`, and this is the statement that they are distinct — on the half-range, which is
  where they are, because `k` and `N − k` give the same cosine.

  **CHECKED ABSENT BEFORE BEING WRITTEN, and the check found two near-misses.** The estate holds
  `PathAdjBasis.eigenvalue_injective` — `k ↦ 2cos((k+1)π/(n+1))` is injective, for the PATH — and
  `BoxLapBasis.lapEigenvalue_injective` for the box. **Both are injective on their WHOLE index
  range, because the path's angle runs over half a turn.** The cycle's runs over a full turn and
  is injective on no such range: that is the difference between a path and a cycle, and it is why
  neither statement transfers. `awk` over the 14485-statement index for `Real.cos` beside
  `Injective` returns those two and nothing for the cycle. (`ERRATUM 621` is one unit old and its
  rule is why this paragraph exists.)

  **A LEAF FILE ON PURPOSE.** It imports Mathlib and nothing from `paper_f`. The statements are
  about `fun k : ℕ => Real.cos (2 * π * k / N)` and mention no graph, so the torus chain — whose
  `νR` is built from the same cosines — can consume them without reaching through the cone.

  WHAT IS PROVED.

  * **`cycle_angle_nonneg`** — the angle is non-negative, at every `N` including `N = 0`, where
    the quotient is `0`. **THE NAME `angle_nonneg` WAS TAKEN and the collision is not a
    duplicate**: `BoxLapExtremes.angle_nonneg` is `0 ≤ kπ/(m+1)`, the PATH/BOX angle, whose
    denominator is positive by construction. Specialising it here would need `N = m + 1` — so
    `N ≠ 0`, which this statement does not assume — and would need this file to import
    `BoxLapExtremes`, **which is the one thing the paragraph above says it does not do**. A
    three-line `positivity` is the cheaper side of that trade, and the prefix records that the
    trade was made knowingly (`newnames_scan` asked).
  * **`angle_mem_Icc`** — for `2k ≤ N` and `N ≠ 0` the angle `2πk/N` lies in `[0, π]`, which is
    where `Real.cos` is injective. Everything else is bookkeeping around this.
  * **`cos_injOn_half`, `eigenvalue_injOn_half`** — so `k ↦ cos(2πk/N)` and `k ↦ 2cos(2πk/N)`
    are injective on `{k | 2k ≤ N}`, off `Real.injOn_cos`.
  * **`cos_reflect`** — and off that range they collide in pairs: `cos(2π(N−k)/N) = cos(2πk/N)`.
    This is the statement that makes the half-range the right range rather than a convenience.
  * **`image_range_eq_image_half`** — the distinct values over all of `range N` are exactly those
    over `range (N/2 + 1)`.
  * **`card_image_range`** — **so there are exactly `N/2 + 1` of them**, by
    `Finset.card_image_of_injOn`.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT ANY GRAPH.** No cycle graph, no adjacency matrix, no eigenvector appears
    here. That these numbers ARE the cycle's eigenvalues is `SignlessCycleSpectrum`'s and unit
    87's business; this file only counts them.
  * **NOTHING ABOUT THE WHEEL'S TABLE.** The table also needs `hubRootMinus` shown distinct from
    all of these, and that is a coincidence question between a root of a quadratic and a cosine —
    `L102`'s library-blocked species, recorded by unit 89 and **not** touched here.
  * **NO IRRATIONALITY, NO TRANSCENDENCE, NO CYCLOTOMIC CLASSIFICATION.** The distinctness proved
    here is the cheap half: two angles in `[0, π]` with equal cosines are equal. The hard half —
    when a cosine coincides with something not of its own form — is exactly what is not here.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat

namespace CycleEigenvalueDistinct

open Real

/-! ## The angle lands in `[0, π]` -/

section Angle

variable {N : ℕ}

theorem cycle_angle_nonneg (k : ℕ) : 0 ≤ 2 * π * (k : ℝ) / N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have hN : (0 : ℝ) < N := Nat.cast_pos.2 h
    positivity

/-- **THE ONE FACT THE FILE RESTS ON**: on the half-range the angle is in `[0, π]`, where
`Real.cos` is injective. -/
theorem angle_mem_Icc (hN : N ≠ 0) {k : ℕ} (hk : 2 * k ≤ N) :
    2 * π * (k : ℝ) / N ∈ Set.Icc 0 π := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  refine ⟨cycle_angle_nonneg k, ?_⟩
  rw [div_le_iff₀ hN']
  have hk' : 2 * (k : ℝ) ≤ N := by
    have := Nat.cast_le (α := ℝ) |>.2 hk
    push_cast at this
    linarith
  nlinarith [pi_pos]

end Angle

/-! ## Injectivity on the half-range, and the collision off it -/

section Distinct

variable {N : ℕ}

theorem cos_injOn_half (hN : N ≠ 0) :
    Set.InjOn (fun k : ℕ => Real.cos (2 * π * (k : ℝ) / N)) {k | 2 * k ≤ N} := by
  intro a ha b hb hab
  have h := Real.injOn_cos (angle_mem_Icc hN ha) (angle_mem_Icc hN hb) hab
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hpos : (0 : ℝ) < 2 * π / N := by positivity
  have hrw : ∀ m : ℕ, 2 * π * (m : ℝ) / N = (2 * π / N) * m := by
    intro m; ring
  rw [hrw a, hrw b] at h
  exact Nat.cast_injective (mul_left_cancel₀ hpos.ne' h)

theorem eigenvalue_injOn_half (hN : N ≠ 0) :
    Set.InjOn (fun k : ℕ => 2 * Real.cos (2 * π * (k : ℝ) / N)) {k | 2 * k ≤ N} := by
  intro a ha b hb hab
  exact cos_injOn_half hN ha hb (by linarith [hab])

/-- **AND OFF THE HALF-RANGE THEY COLLIDE IN PAIRS.** This is what makes the half-range the
right range rather than a convenience. -/
theorem cos_reflect (hN : N ≠ 0) {k : ℕ} (hk : k ≤ N) :
    Real.cos (2 * π * ((N - k : ℕ) : ℝ) / N) = Real.cos (2 * π * (k : ℝ) / N) := by
  have hN' : (0 : ℝ) ≠ N := Ne.symm (Nat.cast_ne_zero.2 hN)
  have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := Nat.cast_sub hk
  rw [hcast]
  have hsplit : 2 * π * ((N : ℝ) - (k : ℝ)) / N = 2 * π - 2 * π * (k : ℝ) / N := by
    field_simp
  rw [hsplit, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring

end Distinct

/-! ## The count -/

section Count

variable {N : ℕ}

theorem image_range_eq_image_half (hN : N ≠ 0) :
    (Finset.range N).image (fun k : ℕ => 2 * Real.cos (2 * π * (k : ℝ) / N))
      = (Finset.range (N / 2 + 1)).image (fun k : ℕ => 2 * Real.cos (2 * π * (k : ℝ) / N)) := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_range] at hk
    by_cases hhalf : 2 * k ≤ N
    · exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), hkv⟩
    · refine Finset.mem_image.2 ⟨N - k, Finset.mem_range.2 (by omega), ?_⟩
      rw [cos_reflect hN (by omega)]
      exact hkv
  · intro v hv
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.1 hv
    rw [Finset.mem_range] at hk
    exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), hkv⟩

/-- **THERE ARE EXACTLY `N / 2 + 1` DISTINCT VALUES.** -/
theorem card_image_range (hN : N ≠ 0) :
    ((Finset.range N).image
        (fun k : ℕ => 2 * Real.cos (2 * π * (k : ℝ) / N))).card = N / 2 + 1 := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * Real.cos (2 * π * (k : ℝ) / N))
      ↑(Finset.range (N / 2 + 1)) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    exact eigenvalue_injOn_half hN (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hab
  rw [image_range_eq_image_half hN, Finset.card_image_of_injOn hinj, Finset.card_range]

end Count

end CycleEigenvalueDistinct
