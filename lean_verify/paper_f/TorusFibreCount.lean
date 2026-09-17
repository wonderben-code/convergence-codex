/-
  TorusFibreCount: the `d = 1` massive torus's eigenspace dimension, as a NUMBER

  WHY THIS FILE EXISTS, AND IT IS ONE SENTENCE OF UNIT 94's HEADER. That unit proved the
  degeneracy bound TIGHT at `d = 1` and then said, under `WHAT IS NOT CLAIMED`:

  > **NO EIGENVALUE IS EVALUATED AND NO DIMENSION IS COMPUTED AS A NUMBER.** …
  > **`TorusPairClassFibre.card_pairClass_fibre` would give the number** — `2` at an interior
  > frequency and `1` at the two fixed ones — and composing it with this file is not done.

  **THAT IS A ONE-STEP FENCE, AND TODAY HAS PRODUCED TWO ERRATA ABOUT ONE-STEP FENCES**
  (`ERRATUM 622`, and the struck draft fence recorded in `WheelTable`'s header). So the step is
  taken here rather than left standing, and the composition is three rewrites long.

  WHAT IS PROVED.

  * **`card_nuRFibre_one`** — the `νR` fibre at `d = 1` has **exactly `2` members at an interior
    frequency and `1` at each of the two fixed ones**, through the identification of
    `Site 1 (N + 3)` with `Fin (N + 3)` by reading the one coordinate. The bijection is
    `Finset.card_nbij'` with `k' ↦ k' 0` one way and `v ↦ fun _ => v` the other, and its four
    obligations are unit 94's `cos_eq_iff` chain forwards and `mem_orbit_of_pairClass_eq` backwards.
  * **`finrank_one_explicit`** — **AND SO THE DIMENSION, AS A NUMBER**, off
    `TorusBoundTightIff.finrank_eq_card_nuRFibre`: at `d = 1` the eigenspace at `νR N m k` has
    dimension `if 0 < k₀ ∧ 2k₀ ≠ N + 3 then 2 else 1`, **at every side, every mass and every
    frequency, with no side condition.** This is the first explicit eigenspace DIMENSION the torus
    chain has: everything before it was a bound, or an equality between two unevaluated
    expressions.
  * **`finrank_one_interior`, `finrank_one_fixed`** — the two read-offs, `= 2` and `= 1`.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT `d ≥ 2`.** Unit 94's fence stands verbatim: `d = 1` is the one dimension in
    which the coincidence question does not arise, and `L102`'s general question is untouched and
    stays library-blocked (`ERRATUM 42`, `ERRATUM 194`, `ERRATUM 246`).
  * **THE EIGENVALUE ITSELF IS STILL NOT EVALUATED.** What is computed is the DIMENSION of the
    eigenspace at `νR N m k`; `νR N m k` is `2 + m² - 2cos(2πk₀/(N+3))` by unit 94's `nuR_one` and
    that is as evaluated as it gets — no cosine is turned into a rational number anywhere.
  * **NOTHING ABOUT THE FULL SPECTRUM.** This is one eigenvalue's multiplicity at a time. That the
    dimensions over all frequencies sum to `N + 3`, or that these are all the eigenvalues, is not
    stated here — **and unlike the wheel's case it is not one step away**, because the frequencies
    do not index distinct eigenvalues: the fibre is exactly what identifies which coincide.
  * **NOTHING ABOUT THE BOX, THE CASCADE, THE SPINE OR ANY WALL.**

  THE HYPOTHESES, READ OFF THE BINDERS. `card_nuRFibre_one` and `finrank_one_explicit` take
  **nothing** beyond the dimension being `1` in the type. The two read-offs take the branch
  condition, `finrank_one_fixed` in the disjunctive form `k₀ = 0 ∨ 2k₀ = N + 3` because that is how
  a reader meets it.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusFibreTight
import TorusPairClassFibre

namespace TorusFibreCount

open BoxGraph TorusHyperoctahedral MassiveTorusSpectrum TorusBoundTightIff
open TorusOrbitInvariant TorusOrbitCharacterisation TorusPairClassFibre
open TorusFibreOrbitPartition
open TorusFibreTight

section Count

variable (N : ℕ) (m : ℝ)

/-- **THE FIBRE'S SIZE AT `d = 1`**, through the identification of `Site 1 (N + 3)` with
`Fin (N + 3)` by reading the one coordinate. -/
theorem card_nuRFibre_one (k : Site 1 (N + 3)) :
    (nuRFibre N m k).card
      = if 0 < (k 0 : ℕ) ∧ 2 * (k 0 : ℕ) ≠ N + 3 then 2 else 1 := by
  rw [← card_pairClass_fibre (k 0)]
  refine Finset.card_nbij' (fun k' => k' 0) (fun v => fun _ => v) ?_ ?_ ?_ ?_
  · intro k' hk'
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hk' ⊢
    refine (pairClass_eq_iff (k' 0).isLt (k 0).isLt).2 ?_
    refine (cos_eq_iff (k' 0).isLt (k 0).isLt).1 ?_
    exact cos_eq_of_nuR_eq N m ((mem_nuRFibre_iff m k k').1 hk')
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hv ⊢
    exact orbit_eq_nuRFibre N m k ▸ mem_orbit_of_pairClass_eq N (by simpa using hv)
  · intro k' _
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  · intro v _
    rfl

/-- **AND SO THE DIMENSION, AS A NUMBER.** At `d = 1` the massive torus's eigenspace at `νR N m k`
has dimension exactly `2` at an interior frequency and exactly `1` at the two fixed ones, at every
side, every mass and every frequency, with no side condition. -/
theorem finrank_one_explicit (k : Site 1 (N + 3)) :
    Module.finrank ℝ
      (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph 1 (N + 3)) m)
        - nuR N m k • LinearMap.id).ker
      = if 0 < (k 0 : ℕ) ∧ 2 * (k 0 : ℕ) ≠ N + 3 then 2 else 1 := by
  rw [finrank_eq_card_nuRFibre, card_nuRFibre_one]

theorem finrank_one_interior (k : Site 1 (N + 3)) (h0 : 0 < (k 0 : ℕ))
    (hh : 2 * (k 0 : ℕ) ≠ N + 3) :
    Module.finrank ℝ
      (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph 1 (N + 3)) m)
        - nuR N m k • LinearMap.id).ker = 2 := by
  rw [finrank_one_explicit, if_pos ⟨h0, hh⟩]

theorem finrank_one_fixed (k : Site 1 (N + 3))
    (h : (k 0 : ℕ) = 0 ∨ 2 * (k 0 : ℕ) = N + 3) :
    Module.finrank ℝ
      (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph 1 (N + 3)) m)
        - nuR N m k • LinearMap.id).ker = 1 := by
  rw [finrank_one_explicit, if_neg]
  rintro ⟨h0, hh⟩
  rcases h with h | h <;> omega

end Count

end TorusFibreCount
