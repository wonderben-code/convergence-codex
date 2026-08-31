import TorusGroundState

/-!
# The first interior multiplicity in this estate: the ring's spectrum is two-to-one

`TorusMultiplicity` turned every multiplicity on the periodic lattice into a counting question about
cosine sums and answered it at the two extremes; `TorusTopSimple` and `TorusGroundState` finished
those, and every unit in the chain has carried the same fence:

> **No multiplicity is computed at any interior eigenvalue.** Whether frequencies collide in
> between is combinatorics of `Σᵢ cos(2π kᵢ / n)` and nothing here touches it.

**In one dimension the sum has one term and the combinatorics is a classical fact**: two frequencies
give the same cosine exactly when they agree or are reflections of one another. That is proved here,
and it is the first statement in this estate about an eigenvalue that is neither the least nor the
greatest.

> **`cos_angle_eq_iff`** — for `a b < n`, `cos(2πa/n) = cos(2πb/n)` **iff** `a = b` or `a + b = n`.
> `Real.cos_eq_cos_iff` supplies an integer `k`; the range `0 ≤ a, b < n` pins it to `0` in the
> first branch and to `0` or `1` in the second, and the `a + b = 0` case collapses into `a = b`.
>
> **`nuR_eq_iff_one`** — hence on the ring: `νR k' = νR k` **iff** the two frequencies agree or
> reflect. No cosine appears in the statement.

## What is NOT here, and the fence is narrower than the one it replaces

**The count itself is not taken.** `nuR_eq_iff_one` says exactly which frequencies share an
eigenvalue; turning that into `Nat.card {k' // νR k' = νR k} = 2` needs the reflected frequency
exhibited as an object and shown distinct from `k`, and **that is not done below**. What replaces
the old fence is a smaller one: the combinatorics is settled and the bookkeeping is not.

**One dimension only.** At `d ≥ 2` the question is which multisets of `d` cosines have equal sums,
which is a genuinely different problem — reflections in each axis independently are *some* of the
collisions and nothing here says they are all of them. **No claim is made about `d ≥ 2` and no cost
is offered for it** (`ERRATUM 194`, `ERRATUM 246`).

**It is about `νR`, not about a graph.** The statement is about the eigenvalue function on
`Site 1 (N+3)`; transporting it to `cycleGraph` needs `TorusCycleGraph.torusGraph_one_iso`, which is
**not applied below**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleMultiplicity

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open MassiveTorusSpectrum

/-! ## 1. Where two cosines on the same ring agree -/

/-- **TWO FREQUENCIES GIVE THE SAME COSINE EXACTLY WHEN THEY AGREE OR REFLECT.**
`Real.cos_eq_cos_iff` gives an integer `k` with `θ_b = 2kπ ± θ_a`; clearing `π` and the denominator
turns that into `b = kn + a` or `b = kn - a`, and `0 ≤ a, b < n` pins `k`. -/
theorem cos_angle_eq_iff {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    Real.cos (2 * Real.pi * a / n) = Real.cos (2 * Real.pi * b / n)
      ↔ a = b ∨ a + b = n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hmul : ∀ j : ℤ, j ≤ -1 → j * n ≤ -n := fun j hj => by
    have := mul_le_mul_of_nonneg_right hj (le_of_lt hnZ)
    linarith [this]
  have hmul2 : ∀ j : ℤ, 2 ≤ j → 2 * n ≤ j * n := fun j hj =>
    mul_le_mul_of_nonneg_right hj (le_of_lt hnZ)
  have hmul1 : ∀ j : ℤ, 1 ≤ j → n ≤ j * n := fun j hj => by
    have := mul_le_mul_of_nonneg_right hj (le_of_lt hnZ)
    linarith [this]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Real.cos_eq_cos_iff.mp h
    rcases hk with hk | hk
    · -- `2πb/n = 2kπ + 2πa/n`
      have h1 : (b : ℝ) = (k : ℝ) * n + a := by
        field_simp at hk
        nlinarith [hk, Real.pi_pos]
      have h2 : (b : ℤ) = k * n + a := by exact_mod_cast h1
      have haZ : (a : ℤ) < n := by exact_mod_cast ha
      have hbZ : (b : ℤ) < n := by exact_mod_cast hb
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with hlt | heq | hgt
        · have := hmul k (by omega); omega
        · exact heq
        · have := hmul1 k (by omega); omega
      left
      have : (b : ℤ) = a := by rw [h2, hk0]; ring
      omega
    · -- `2πb/n = 2kπ − 2πa/n`
      have h1 : (b : ℝ) = (k : ℝ) * n - a := by
        field_simp at hk
        nlinarith [hk, Real.pi_pos]
      have h2 : (b : ℤ) = k * n - a := by exact_mod_cast h1
      have haZ : (a : ℤ) < n := by exact_mod_cast ha
      have hbZ : (b : ℤ) < n := by exact_mod_cast hb
      have hk01 : k = 0 ∨ k = 1 := by
        rcases lt_trichotomy k 0 with hlt | heq | hgt
        · have := hmul k (by omega); omega
        · exact Or.inl heq
        · rcases (by omega : k = 1 ∨ 2 ≤ k) with h' | h'
          · exact Or.inr h'
          · have := hmul2 k h'; omega
      rcases hk01 with hk0 | hk0
      · left
        have : (b : ℤ) = -a := by rw [h2, hk0]; ring
        omega
      · right
        have : (b : ℤ) = n - a := by rw [h2, hk0]; ring
        omega
  · intro h
    rcases h with h | h
    · rw [h]
    · have hb' : (b : ℝ) = n - a := by
        have : (b : ℕ) = n - a := by omega
        rw [this]
        push_cast [Nat.cast_sub (le_of_lt (by omega : a < n))]
        ring
      rw [hb']
      have hsplit : 2 * Real.pi * ((n : ℝ) - a) / n = 2 * Real.pi - 2 * Real.pi * a / n := by
        field_simp
      rw [hsplit, Real.cos_two_pi_sub]

/-! ## 2. Hence the ring's eigenvalue function -/

/-- **TWO FREQUENCIES SHARE AN EIGENVALUE ON THE RING EXACTLY WHEN THEY AGREE OR REFLECT.**
No cosine in the statement: this is `νR` against `νR`. -/
theorem nuR_eq_iff_one (N : ℕ) (m : ℝ) (k k' : Site 1 (N + 3)) :
    nuR N m k' = nuR N m k
      ↔ (k' 0).val = (k 0).val ∨ (k' 0).val + (k 0).val = N + 3 := by
  have hcast : ((N : ℝ) + 3) = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hpos : 0 < N + 3 := by omega
  have hexp : ∀ j : Site 1 (N + 3),
      nuR N m j = 2 * (1 : ℕ) + m ^ 2
        - 2 * Real.cos (2 * Real.pi * (j 0).val / ((N : ℝ) + 3)) := by
    intro j
    rw [nuR, Fin.sum_univ_one]
  rw [hexp k, hexp k']
  constructor
  · intro h
    have hc : Real.cos (2 * Real.pi * (k' 0).val / ((N + 3 : ℕ) : ℝ))
        = Real.cos (2 * Real.pi * (k 0).val / ((N + 3 : ℕ) : ℝ)) := by
      rw [← hcast]
      linarith
    exact (cos_angle_eq_iff hpos (k' 0).isLt (k 0).isLt).1 hc
  · intro h
    have hc : Real.cos (2 * Real.pi * (k' 0).val / ((N + 3 : ℕ) : ℝ))
        = Real.cos (2 * Real.pi * (k 0).val / ((N + 3 : ℕ) : ℝ)) :=
      (cos_angle_eq_iff hpos (k' 0).isLt (k 0).isLt).2 h
    rw [← hcast] at hc
    linarith

end CycleMultiplicity
