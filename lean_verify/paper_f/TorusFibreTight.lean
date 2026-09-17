/-
  TorusFibreTight: the torus degeneracy bound is TIGHT at `d = 1`, at every side and every
  frequency — the criterion's first positive instance

  WHY THIS FILE EXISTS. `RE-SWEEP #61` (2026-09-17) read the live watchlist against units 83–92 and
  its first finding was about `L102`, *which eigenvalue fibres of the massive torus Laplacian are a
  SINGLE hyperoctahedral orbit*. What the query found: the estate holds **four**
  equality-or-biconditional criteria for the bound being tight —
  `TorusBoundTightIff.bound_eq_finrank_iff`, `card_orbit_eq_finrank_iff`,
  `TorusFibreOrbitPartition.bound_eq_finrank_iff_card_orbitsOf` and `finrank_eq_sum_card_orbit` —
  and **one instance where the bound FAILS** (`TorusEightNotTight.nine_le_finrank_eight`), **and no
  instance anywhere where it holds.** Four criteria and a counterexample, attached to a class
  nobody had shown has a member: `ERRATUM 13`'s vacuity shape, one scope up.

  **AND THE INGREDIENT CAME FROM AN UNEXPECTED FILE.** Unit 90 wrote `CycleEigenvalueDistinct` as a
  LEAF — Mathlib only, no `paper_f` import — and said in its own header that this was so the torus
  chain could consume it. That was a guess about the future. **It is the missing step**: at `d = 1`
  the torus is the cycle, the hyperoctahedral group is `{±1}`, and the `νR` fibre is the orbit
  exactly when the cosine separates the half-range, which is unit 90's `cos_injOn_half`. This is
  the first consumer that stated reason has had.

  **WHAT WAS CHECKED BEFORE ANY OF IT WAS WRITTEN, and it changed the file twice.** A first draft
  defined its own `fold N a = if 2a ≤ N then a else N - a` and built the reflection by hand. Both
  were already here: `TorusOrbitInvariant.pairClass N v = min v ((N + 3 - v) % (N + 3))` **is that
  fold**, `TorusOrbitCharacterisation.pairClass_eq_iff` is the `a = b ∨ a + b = N + 3`
  characterisation of it, `mem_orbit_iff` decides orbit membership from mirror-name counts, and
  `TorusFibreOrbitPartition.mem_orbit_self` and `mem_nuRFibre_iff` are the two membership lemmas
  the draft re-proved. **Five of the draft's declarations were deleted** and the file now has ten,
  of which the only new mathematics is the cosine-to-`pairClass` bridge. `ERRATUM 621`'s rule is
  what caught it, applied by hand rather than by a mode.

  WHAT IS PROVED.

  * **`two_mul_pairClass_le`, `cos_pairClass`** — the mirror name is in the half-range and has the
    same cosine, the second being unit 90's `cos_reflect` at the member that needs it.
  * **`cos_eq_iff`** — **THE BRIDGE, AND THE FILE'S ONLY NEW MATHEMATICS.** For `a, b < N + 3`,
    `cos(2πa/(N+3)) = cos(2πb/(N+3))` **iff** `a = b ∨ a + b = N + 3`, i.e. iff `pairClass` agrees.
    Unit 90 had injectivity on the half-range and the reflection off it as two separate facts; this
    is the `iff` they combine into, and its right-hand side is `pairClass_eq_iff`'s, **which is
    why the trigonometric and the combinatorial vocabularies meet here and not earlier.**
  * **`nuR_one`, `cos_eq_of_nuR_eq`** — at `d = 1` the eigenvalue is `2 + m² - 2cos(2πk₀/(N+3))`,
    a one-term sum, so equal eigenvalues mean equal cosines.
  * **`mem_orbit_of_pairClass_eq`** — at `d = 1` `mem_orbit_iff`'s counting condition is decided by
    the single coordinate.
  * **`orbit_eq_nuRFibre`** — **THE FIBRE IS THE ORBIT.** The inclusion `orbit ⊆ nuRFibre` holds at
    every dimension (`TorusBoundTightIff.orbit_subset_nuRFibre`); **the reverse is what the estate
    held for no dimension at all until this file**, and here it is `cos_eq_iff` composed with
    `pairClass_eq_iff` and nothing else. The `iff`s above it have `orbit k = nuRFibre N m k` on one
    side; none of them proves it, which is the whole of what was missing.
  * **`bound_eq_finrank_one`** — **THE CRITERION'S FIRST POSITIVE INSTANCE**: at `d = 1` the bound
    `2 ^ |interiorAxes k| · multinomial` IS the eigenspace dimension, at every `N` and every `k`.
  * **`card_orbit_eq_finrank_one`, `card_orbitsOf_eq_one`** — the same tightness read on the orbit's
    size, and **in `L102`'s own words: the fibre is a SINGLE orbit.**

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT `d ≥ 2`, AND THAT IS `L102`'s ACTUAL QUESTION.** `d = 1` is the one dimension in
    which the whole difficulty disappears, because the hyperoctahedral group is `{±1}` and the sum
    defining `νR` has one term — so there is no coincidence between sums of cosines to have. `L102`
    asks which frequencies give a one-orbit fibre in general, `TorusNonReflectionCollision` shows
    the answer is not *always* at `d = 2`, and that question is **untouched here and stays
    library-blocked** on the classification of vanishing sums of roots of unity, which the pinned
    Mathlib does not have (`ERRATUM 42`, `ERRATUM 194`, `ERRATUM 246`).
  * **NO EIGENVALUE IS EVALUATED AND NO DIMENSION IS COMPUTED AS A NUMBER.** The tightness is an
    equality between two expressions, one of which is a `finrank`; nothing here says what either
    equals at a named `N` and `k`. **`TorusPairClassFibre.card_pairClass_fibre` would give the
    number** — `2` at an interior frequency and `1` at the two fixed ones — and composing it with
    this file is not done (`ERRATUM 246`).
  * **NOTHING ABOUT THE BOX.** The torus and the box are different graphs in this estate and the
    box's own bound has its own chain.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.** `W1`'s open part is `OS0`, `OS4` and
    `OS1` in its continuum sense, and an exact finite-volume multiplicity at one dimension is not
    among them.

  THE HYPOTHESES, READ OFF THE BINDERS. `cos_eq_iff`, `two_mul_pairClass_le` and `cos_pairClass`
  take only `a < N + 3`, which is what a `Fin (N + 3)` index supplies for free. The `d = 1`
  section takes no hypothesis at all beyond the dimension being `1` in the type, and neither does
  the tightness: **there is no side condition on `N`, on `m`, or on the frequency.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import CycleEigenvalueDistinct
import TorusFibreOrbitPartition

namespace TorusFibreTight

open BoxGraph TorusHyperoctahedral TorusReflectionCount MassiveTorusSpectrum TorusBoundTightIff
open TorusOrbitInvariant TorusOrbitCharacterisation TorusFibreOrbitPartition
open CycleEigenvalueDistinct

/-! ## The cosine fibre, characterised — and it is the estate's `pairClass` -/

section Fibre

variable {N : ℕ}

theorem two_mul_pairClass_le {a : ℕ} (ha : a < N + 3) : 2 * pairClass N a ≤ N + 3 := by
  unfold pairClass
  rcases Nat.eq_zero_or_pos a with rfl | h
  · simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The mirror name has the same cosine, which is `cos_reflect` at the member that needs it. -/
theorem cos_pairClass {a : ℕ} (ha : a < N + 3) :
    Real.cos (2 * Real.pi * ((pairClass N a : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ))
      = Real.cos (2 * Real.pi * (a : ℝ) / ((N + 3 : ℕ) : ℝ)) := by
  unfold pairClass
  rcases Nat.eq_zero_or_pos a with rfl | h
  · simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    rcases le_or_gt a (N + 3 - a) with hle | hgt
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right (by omega)]
      exact cos_reflect (N := N + 3) (by omega) (by omega)

/-- **THE COSINE FIBRE, CHARACTERISED, AND IT COINCIDES WITH THE ESTATE'S MIRROR CLASS.** Unit 90
gave injectivity on the half-range and the reflection off it as two separate facts; this is the
`iff` they combine into. The right-hand side is `TorusOrbitCharacterisation.pairClass_eq_iff`'s,
which is why the two vocabularies meet here and nowhere earlier. -/
theorem cos_eq_iff {a b : ℕ} (ha : a < N + 3) (hb : b < N + 3) :
    Real.cos (2 * Real.pi * (a : ℝ) / ((N + 3 : ℕ) : ℝ))
        = Real.cos (2 * Real.pi * (b : ℝ) / ((N + 3 : ℕ) : ℝ))
      ↔ (a = b ∨ a + b = N + 3) := by
  rw [← pairClass_eq_iff ha hb]
  constructor
  · intro h
    refine cos_injOn_half (N := N + 3) (by omega)
      (by simpa using two_mul_pairClass_le (N := N) ha)
      (by simpa using two_mul_pairClass_le (N := N) hb) ?_
    dsimp only
    rw [cos_pairClass ha, cos_pairClass hb]
    exact h
  · intro h
    rw [← cos_pairClass ha, ← cos_pairClass hb, h]

end Fibre

/-! ## At `d = 1` the torus is the cycle, and the fibre IS the orbit -/

section DimensionOne

variable (N : ℕ) (m : ℝ)

theorem nuR_one (k : Site 1 (N + 3)) :
    nuR N m k = 2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * ((k 0 : ℕ) : ℝ) / ((N : ℝ) + 3)) := by
  rw [nuR, Fin.sum_univ_one]
  norm_num

theorem cos_eq_of_nuR_eq {k k' : Site 1 (N + 3)} (h : nuR N m k' = nuR N m k) :
    Real.cos (2 * Real.pi * ((k' 0 : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ))
      = Real.cos (2 * Real.pi * ((k 0 : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ)) := by
  rw [nuR_one, nuR_one] at h
  rw [show ((N + 3 : ℕ) : ℝ) = (N : ℝ) + 3 by push_cast; ring]
  linarith

/-- At `d = 1` the orbit characterisation is decided by the single coordinate's mirror name. -/
theorem mem_orbit_of_pairClass_eq {k k' : Site 1 (N + 3)}
    (h : pairClass N (k' 0 : ℕ) = pairClass N (k 0 : ℕ)) : k' ∈ orbit k := by
  refine (mem_orbit_iff k k').2 ?_
  intro c
  have key : ∀ K : Site 1 (N + 3),
      (Finset.univ.filter fun i => pairClass N ((K i : ℕ)) = c)
        = if pairClass N ((K 0 : ℕ)) = c then {0} else ∅ := by
    intro K
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    by_cases hc : pairClass N ((K 0 : ℕ)) = c <;> simp [hc]
  rw [key k', key k, h]

/-- **THE FIBRE IS THE ORBIT, AT EVERY `N` AND EVERY FREQUENCY.** The inclusion
`orbit_subset_nuRFibre` holds at every dimension; the REVERSE is what the estate has for no
dimension at all, and at `d = 1` it is `cos_eq_iff` and nothing else. -/
theorem orbit_eq_nuRFibre (k : Site 1 (N + 3)) : orbit k = nuRFibre N m k := by
  refine Finset.Subset.antisymm (orbit_subset_nuRFibre N m k) ?_
  intro k' hk'
  refine mem_orbit_of_pairClass_eq N ?_
  refine (pairClass_eq_iff (k' 0).isLt (k 0).isLt).2 ?_
  refine (cos_eq_iff (k' 0).isLt (k 0).isLt).1 ?_
  exact cos_eq_of_nuR_eq N m ((mem_nuRFibre_iff m k k').1 hk')

end DimensionOne

/-! ## So the bound is tight, and the fibre is a single orbit -/

section Tight

variable (N : ℕ) (m : ℝ)

/-- **THE CRITERION'S FIRST POSITIVE INSTANCE.** `TorusEigenspaceLowerBound`'s bound
`2 ^ |interiorAxes k| · multinomial` EQUALS the eigenspace dimension at every frequency of the
one-dimensional torus. Before this the estate held four forms of the criterion and one instance
where it FAILS, and nothing at all showing the tight class non-empty. -/
theorem bound_eq_finrank_one (k : Site 1 (N + 3)) :
    (2 ^ (interiorAxes k).card
        * Nat.multinomial Finset.univ fun c =>
            Fintype.card { i // TorusOrbitMultinomial.cls k i = c })
      = Module.finrank ℝ
        (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph 1 (N + 3)) m)
          - nuR N m k • LinearMap.id).ker :=
  (bound_eq_finrank_iff N m k).2 (orbit_eq_nuRFibre N m k)

/-- The same tightness read on the orbit's size. -/
theorem card_orbit_eq_finrank_one (k : Site 1 (N + 3)) :
    (orbit k).card = Module.finrank ℝ
      (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph 1 (N + 3)) m)
        - nuR N m k • LinearMap.id).ker :=
  (card_orbit_eq_finrank_iff N m k).2 (orbit_eq_nuRFibre N m k)

/-- **AND IN THE WATCHLIST ITEM'S OWN WORDS**: the `νR` fibre is a SINGLE hyperoctahedral orbit. -/
theorem card_orbitsOf_eq_one (k : Site 1 (N + 3)) : (orbitsOf N m k).card = 1 :=
  (bound_eq_finrank_iff_card_orbitsOf N m k).1 (bound_eq_finrank_one N m k)

end Tight

end TorusFibreTight
