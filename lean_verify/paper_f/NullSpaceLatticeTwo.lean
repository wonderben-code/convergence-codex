import NullSpaceLattice

/-!
# The second-coordinate cut of the estate's lattice, which had positivity and nothing else

**THE ESTATE HAS NO STRICTNESS RESULT FOR THIS CUT AT ALL.** Grepped before this file was written
(`ERRATUM 270`'s rule, and `ERRATUM 265`'s): every occurrence of
`LatticeReflectionTwo.lowerHalfPair2` outside its own file is a **positivity** statement —
`OS2AnySide.reflectionPositive_two_any` and its `os2` companions, `BoxOddComplement`'s complement
forms — and `grep lowerHalfPair2 | grep -i strict` returns nothing. So `≥ 0` is known in the second
direction and *how far it is from `> 0`* is not known at all.

**WHY THAT IS NOT BOOKKEEPING**, and the record says so in its own words. The second-coordinate
item's own trigger line in `UNLOCK_WATCHLIST` reads:

> *"when the second direction is wanted — and note WHY it might be: OS2 reflects in the TIME
> coordinate, and which of the lattice coordinates carries time is a modelling choice this estate
> has not made. A result in one direction only is therefore weaker than it looks the moment a time
> axis is named."*

`OS2AnySide` §2b answered that for **positivity** (`reflectionPositive_two_any` and its `os2`
companions), and `RE-SWEEP #27` batch 2 re-read the block, superseded the clause in place, and
recorded that *the clause's REASON — that this estate has not chosen which coordinate carries time
— is still true and still unmade.* This answers the same question for **strictness**.

**The box already has strictness at every axis** —
`CrossBlockStructure.box_strict_iff_le_two_lowerHalf` takes `i : Fin d`, and `NullSpaceBoxAny`
describes the null space at any `i`. What was missing is on this side of the encoding: nothing
carried either into `Fin n × Fin n` at the second coordinate, and nothing described that null space
in **either** direction until `NullSpaceLattice` did the first one.

## What is proved

* `reflectedForm_lattice_two_eq` — the missing transport.
  `LatticeNotStrict.reflectedForm_lattice_eq` is first-coordinate only; this is its twin through
  `LatticeReflectionTwo.sitePair_revSite_two`, and it is three tokens because
  `LatticeReflectionPositive.sum_green_congr` never cared which reflection it was given.
* `innerLowerPair2`, `map_innerLower_two`, `nullSpace_lattice_two` — the null space at **every**
  side length, as the massive image of the sites two or more columns in.
* `mem_nullSub_iff_lattice_two`, `finrank_nullSub_lattice_two`, `codim_lattice_two` — the
  dimension, and the deficiency is exactly `n`.
* `exists_null_direction_lattice_two_any`, `not_strict_lattice_two_any` — **the first
  non-strictness statement in this direction**, at every parity from side three.
* `null_trivial_lattice_two_iff_side_le_two`, `strict_iff_innerLowerPair2_empty` and its `0 <`
  twin, and **`lattice_two_strict_iff_le_two`**.

## A FOURTH FAMILY FOR `all_three_thresholds`, AND THAT THEOREM IS NOT EDITED

`CrossBlockStructure.all_three_thresholds` states the box, the torus and the lattice's
**first-coordinate** cut in one theorem. `lattice_two_strict_iff_le_two` is the same threshold for
the second, so the estate now has four families with the same `n ≤ 2`/`n ≤ 4` picture.
`all_three_thresholds` keeps its statement: it is a pushed record, it is correct, and adding a
family to it would rewrite what three earlier units proved. This file adds beside it, which is what
`RE-SWEEP #27`'s `Even n` block records as the estate's practice.

## What is NOT here

The threshold's *value* is inherited, not discovered: the second-coordinate cut is the box's cut at
`i = 1`, and `CrossBlockStructure.box_strict_iff_le_two_lowerHalf` has held at every axis since
12 August 2026. What was missing is that nothing carried it into the lattice encoding on this side,
and nothing described the null space there in any direction.

Reflection positivity is untouched: `OS2AnySide.reflectionPositive_two_any` gives `≥ 0` at every
side, and everything here says by how much `≥` fails to be `>`.
-/

namespace NullSpaceLatticeTwo

open Finset BoxGraph GraphHalfSpace GraphReflection
open InnerLowerSupport LatticeReflectionPositive LatticeReflectionTwo NullSpaceDimension

open scoped Matrix

variable {n : ℕ} {m : ℝ}

/-! ## 1. The reflected form transports in the second direction too -/

/-- **THE MISSING TWIN OF `LatticeNotStrict.reflectedForm_lattice_eq`.** Same equivalence, same
adjacency lemma, the other reflection. -/
theorem reflectedForm_lattice_two_eq (c : IsingFiniteVolume.Site n → ℝ) :
    reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c
      = reflectedForm (boxGraph 2 n) m (revSite (n := n) (1 : Fin 2))
          (fun p => c (sitePair n p)) :=
  sum_green_congr (sitePair n) adj_sitePair sitePair_revSite_two m c

/-! ## 2. The set, carried across -/

/-- The sites two or more columns inside the second-coordinate half. -/
def innerLowerPair2 (n : ℕ) : Finset (IsingFiniteVolume.Site n) :=
  Finset.univ.filter fun p => 2 * p.2.val + 2 < n

theorem mem_innerLowerPair2 (p : IsingFiniteVolume.Site n) :
    p ∈ innerLowerPair2 n ↔ 2 * p.2.val + 2 < n := by
  simp [innerLowerPair2]

theorem map_innerLower_two (n : ℕ) :
    (innerLower (1 : Fin 2) n).map (sitePair n).toEmbedding = innerLowerPair2 n := by
  classical
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, mem_innerLowerPair2]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_innerLower] at hp
    simpa [sitePair] using hp
  · intro hq
    exact ⟨(sitePair n).symm q, mem_innerLower.mpr (by simpa [sitePair] using hq), by simp⟩

theorem innerLowerPair2_subset_lowerHalfPair2 (n : ℕ) :
    innerLowerPair2 n ⊆ lowerHalfPair2 n := fun p hp =>
  (mem_lowerHalfPair2 p).mpr (by rw [mem_innerLowerPair2] at hp; omega)

/-! ## 3. The null space -/

/-- **THE NULL SPACE AT THE SECOND-COORDINATE CUT, AT EVERY SIDE LENGTH.** -/
theorem nullSpace_lattice_two (n : ℕ) (hm : m ≠ 0)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ q, q ∉ lowerHalfPair2 n → c q = 0) :
    reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c = 0
      ↔ ∃ v : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ innerLowerPair2 n → v q = 0)
          ∧ GraphLaplacian.massive (IsingContourSeparation.latticeGraph n) m *ᵥ v = c := by
  classical
  have hbox : ∀ p, p ∉ lowerHalf (1 : Fin 2) n → c (sitePair n p) = 0 := by
    intro p hp
    refine hc _ fun hmem => hp ?_
    rw [← map_lowerHalf_two n] at hmem
    obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
    simpa [(sitePair n).injective (by simpa using hpe)] using hp'
  rw [reflectedForm_lattice_two_eq (m := m) c,
    NullSpaceBoxAny.nullSpace_box_any (m := m) (1 : Fin 2) n hm hbox]
  constructor
  · rintro ⟨v, hvsupp, hvc⟩
    refine ⟨fun q => v ((sitePair n).symm q), ?_, ?_⟩
    · intro q hq
      refine hvsupp _ fun hmem => hq ?_
      rw [← map_innerLower_two n]
      exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
    · funext q
      have := NullSpaceLattice.massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m v
        ((sitePair n).symm q)
      rw [Equiv.apply_symm_apply] at this
      rw [this, congrFun hvc ((sitePair n).symm q), Equiv.apply_symm_apply]
  · rintro ⟨w, hwsupp, hwc⟩
    refine ⟨fun p => w (sitePair n p), ?_, ?_⟩
    · intro p hp
      refine hwsupp _ fun hmem => hp ?_
      rw [← map_innerLower_two n] at hmem
      obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
      simpa [(sitePair n).injective (by simpa using hpe)] using hp'
    · funext p
      have := NullSpaceLattice.massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m
        (fun p' => w (sitePair n p')) p
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
      exact congrFun hwc (sitePair n p)

theorem mem_nullSub_iff_lattice_two (n : ℕ) (hm : m ≠ 0) (c : IsingFiniteVolume.Site n → ℝ) :
    c ∈ nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair2 n)
      ↔ (∀ q, q ∉ lowerHalfPair2 n → c q = 0)
        ∧ reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c = 0 := by
  classical
  constructor
  · intro hcm
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hcm
    have hboxsupp : ∀ p, p ∉ innerLower (1 : Fin 2) n → v (sitePair n p) = 0 := by
      intro p hp
      refine hvsupp _ fun hmem => hp ?_
      rw [← map_innerLower_two n] at hmem
      obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
      simpa [(sitePair n).injective (by simpa using hpe)] using hp'
    have hsupp : ∀ q, q ∉ lowerHalfPair2 n →
        (GraphLaplacian.massive (IsingContourSeparation.latticeGraph n) m *ᵥ v) q = 0 := by
      intro q hq
      have hb : ((sitePair n).symm q) ∉ lowerHalf (1 : Fin 2) n := by
        intro hmem
        refine hq ?_
        rw [← map_lowerHalf_two n]
        exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
      have hz := massive_mulVec_supported (1 : Fin 2) m hboxsupp _ hb
      have ht := NullSpaceLattice.massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m
        (fun p => v (sitePair n p)) ((sitePair n).symm q)
      simp only [Equiv.apply_symm_apply] at ht
      rw [← hz, ← ht]
    exact ⟨hsupp, (nullSpace_lattice_two n hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((nullSpace_lattice_two n hm hcsupp).mp hcnull)

/-! ## 4. The dimension and the deficiency -/

theorem finrank_nullSub_lattice_two (n : ℕ) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair2 n))
      = (innerLowerPair2 n).card :=
  NullSpaceDimensionEven.finrank_nullSub hm _

theorem card_lowerHalfPair2_sdiff_innerLowerPair2 (n : ℕ) (hn : 0 < n) :
    ((lowerHalfPair2 n) \ (innerLowerPair2 n)).card = n := by
  classical
  have h : (lowerHalfPair2 n) \ (innerLowerPair2 n)
      = ((lowerHalf (1 : Fin 2) n) \ (innerLower (1 : Fin 2) n)).map (sitePair n).toEmbedding := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_map, Equiv.coe_toEmbedding, mem_lowerHalfPair2,
      mem_innerLowerPair2, lowerHalf, mem_innerLower, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(sitePair n).symm q, ⟨by simpa [sitePair] using h1, by
        intro hc; exact h2 (by simpa [sitePair] using hc)⟩, by simp⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨by simpa [sitePair] using hp1, by
        intro hc; exact hp2 (by simpa [sitePair] using hc)⟩
  rw [h, Finset.card_map, NullSpaceBoxAny.card_lowerHalf_sdiff_innerLower (1 : Fin 2) hn]
  simp

theorem codim_lattice_two (n : ℕ) (hn : 0 < n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair2 n)) + n
      = Module.finrank ℝ (supportedOn (lowerHalfPair2 n)) := by
  have h := NullSpaceCodimension.finrank_nullSub_add_card_sdiff (m := m)
    (IsingContourSeparation.latticeGraph n) hm (innerLowerPair2_subset_lowerHalfPair2 n)
  rwa [card_lowerHalfPair2_sdiff_innerLowerPair2 n hn] at h

/-! ## 5. Emptiness, and the first non-strictness statement in this direction -/

theorem innerLowerPair2_eq_empty_of_le_two (n : ℕ) (hn : n ≤ 2) : innerLowerPair2 n = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [mem_innerLowerPair2] at hp
  omega

theorem innerLowerPair2_nonempty_iff (n : ℕ) : (innerLowerPair2 n).Nonempty ↔ 3 ≤ n := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_innerLowerPair2] at hp
    omega
  · intro h3
    exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), mem_innerLowerPair2 _ |>.mpr (by simpa using h3)⟩

/-- **A NONZERO NULL FAMILY AT THE SECOND-COORDINATE CUT, FROM SIDE THREE.** Nothing in the estate
said this in this direction; `LatticeNotStrict.exists_null_direction_lattice` is about the first
coordinate and carries `Even n` and `4 ≤ n` besides. -/
theorem exists_null_direction_lattice_two_any (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ∃ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 ∧ (∀ q, q ∉ lowerHalfPair2 n → c q = 0)
      ∧ reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c = 0 := by
  classical
  obtain ⟨p, hp⟩ := (innerLowerPair2_nonempty_iff n).mpr h3
  have hne : Nontrivial (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair2 n)) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_nullSub_lattice_two (m := m) n hm]; exact Finset.card_pos.mpr ⟨p, hp⟩)
  obtain ⟨c, hc0⟩ := exists_ne (0 : nullSub (IsingContourSeparation.latticeGraph n) m
    (innerLowerPair2 n))
  obtain ⟨hcsupp, hcnull⟩ := (mem_nullSub_iff_lattice_two n hm _).mp c.2
  exact ⟨c.1, fun h => hc0 (Subtype.ext h), hcsupp, hcnull⟩

/-- **SO THE SECOND-COORDINATE CUT IS NOT STRICT FROM SIDE THREE EITHER.** -/
theorem not_strict_lattice_two_any (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 → (∀ q, q ∉ lowerHalfPair2 n → c q = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_lattice_two_any (m := m) n h3 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

theorem null_trivial_lattice_two_iff_side_le_two (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ lowerHalfPair2 n → c q = 0) →
        reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c = 0 → c = 0)
      ↔ n ≤ 2 := by
  classical
  constructor
  · intro h
    by_contra h2
    obtain ⟨c, hc0, hcsupp, hcnull⟩ :=
      exists_null_direction_lattice_two_any (m := m) n (by omega) hm
    exact hc0 (h c hcsupp hcnull)
  · intro h2 c hcsupp hcnull
    obtain ⟨v, hvsupp, rfl⟩ := (nullSpace_lattice_two n hm hcsupp).mp hcnull
    have hv0 : v = 0 := funext fun q => hvsupp q (by
      rw [innerLowerPair2_eq_empty_of_le_two n h2]; exact Finset.notMem_empty q)
    rw [hv0, Matrix.mulVec_zero]

theorem strict_iff_innerLowerPair2_empty (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ lowerHalfPair2 n → c q = 0) →
        reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c = 0 → c = 0)
      ↔ innerLowerPair2 n = ∅ := by
  classical
  rw [null_trivial_lattice_two_iff_side_le_two n hm, ← Finset.not_nonempty_iff_eq_empty,
    innerLowerPair2_nonempty_iff n]
  omega

/-- **THE `0 <` FORM**, on `OS2AnySide.reflectionPositive_two_any`, which is the second
direction's positivity at every side. -/
theorem strict_iff_innerLowerPair2_empty' (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 → (∀ q, q ∉ lowerHalfPair2 n → c q = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c)
      ↔ innerLowerPair2 n = ∅ := by
  rw [← strict_iff_innerLowerPair2_empty n hm]
  constructor
  · intro hs c hcsupp hnull
    by_contra hc0
    exact absurd hnull (ne_of_gt (hs c hc0 hcsupp))
  · intro hs c hc0 hcsupp
    rcases lt_or_eq_of_le (OS2AnySide.reflectionPositive_two_any (m := m) n hm c hcsupp) with h | h
    · exact h
    · exact absurd (hs c hcsupp h.symm) hc0

/-- **THE THRESHOLD IN THE SECOND DIRECTION, WHICH THE ESTATE DID NOT HAVE.**
`CrossBlockStructure.all_three_thresholds` covers the box, the torus and this lattice's
FIRST-coordinate cut. This is the fourth family, and that theorem is left exactly as it stands. -/
theorem lattice_two_strict_iff_le_two (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 → (∀ q, q ∉ lowerHalfPair2 n → c q = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m (refl2 n) c)
      ↔ n ≤ 2 := by
  classical
  rw [strict_iff_innerLowerPair2_empty' n hm, ← Finset.not_nonempty_iff_eq_empty,
    innerLowerPair2_nonempty_iff n]
  omega

end NullSpaceLatticeTwo
