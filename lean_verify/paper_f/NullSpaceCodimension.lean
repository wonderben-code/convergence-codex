import NullSpaceTorusAny

/-!
# The codimension of the null space, which three files claimed and none stated

`NullSpaceDimension`, `NullSpaceDimensionEven` and `NullSpaceTorus` each say in prose that their
degeneracy statement is a **measured codimension** rather than a bare *"not strict"*.
`NullSpaceDimension.nullSub_lt_admissible_box_odd`'s docstring puts it exactly:

> *"the deficiency is exactly the midline layer … Degeneracy with a measured codimension rather
> than a bare `not strict`."*

**All four such theorems are strict inequalities.** `nullSub_lt_admissible_box_odd`,
`_box_even`, `_torus_even` and `_torus_any` say `finrank (nullSub …) < finrank (supportedOn …)`
and nothing more; the sets that make up the difference are named in *separate* identities
(`lowerHalf_sdiff_innerLower`, `lowerHalf_sdiff_torusInner`,
`TorusAdjAnySide.strictLower_sdiff_torusInner`) and nothing joins the two. So the word
*codimension* was doing work no statement supported. `ERRATUM 268`.

This file states it, and the general form costs three lines because both halves were already
general.

> `finrank_nullSub_add_card_sdiff` — on **every** finite graph, at every nonzero mass, for every
> `S ⊆ H`: `finrank (nullSub G m S) + (H \ S).card = finrank (supportedOn H)`.

## Why it is three lines

`NullSpaceDimensionEven.finrank_nullSub` gives `finrank (nullSub G m S) = S.card` for every graph,
mass and set — the theorem that has now been free four times — and `finrank_supportedOn` gives
`finrank (supportedOn H) = H.card`. What remains is `S.card + (H \ S).card = H.card`, which is
Mathlib's `Finset.card_sdiff_add_card_eq_card`. **The codimension was one `Finset` lemma away for
two weeks**, in the same sense the dimension was one instantiation away: nobody wrote the
statement down, and the prose that would have prompted it was busy asserting it was already there.

## The four instances, and what each deficiency is

* `codim_box_odd` — the deficiency is `midLayer i n`, the midline the reflection **fixes**.
* `codim_box_even` — `innerLower`'s complement in the half: the innermost layer, adjacent to its
  own mirror. The reflection fixes nothing at even side.
* `codim_torus_even` — **two** layers, the innermost and the seam.
* `codim_torus_any` — the same, against `strictLower`, at every side; at odd side the innermost
  layer is empty and the seam is the whole deficiency.

## What is NOT proved

**The deficiencies are still `Finset.card`s and not closed-form numbers.** Each is a union of
coordinate slices `{p : pᵢ = c}`, whose cardinality is `n ^ (d - 1)`, and that computation is not
here — it needs a fibre argument over the evaluation map `p ↦ pᵢ` and nothing in this estate has
needed it. **Stated as the honest remainder**: this file turns *"strictly smaller"* into *"smaller
by exactly this set"*, not into *"smaller by exactly this number"*.
-/

namespace NullSpaceCodimension

open Finset BoxGraph BoxOddReflection GraphHalfSpace GraphReflection
open TorusReflection TorusInnerSupport TorusAdjAnySide NullSpaceDimension

variable {V : Type*} [Fintype V] [DecidableEq V] {d n : ℕ} {m : ℝ}

/-! ## 1. The general statement -/

/-- **THE CODIMENSION OF THE NULL SPACE, ON EVERY FINITE GRAPH.** The families supported on `H`
that are null are exactly the massive image of those supported on `S`, and what the null space
misses is measured by `H \ S` — as a dimension count, not as an inequality. -/
theorem finrank_nullSub_add_card_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) {H S : Finset V} (hS : S ⊆ H) :
    Module.finrank ℝ (nullSub G m S) + (H \ S).card
      = Module.finrank ℝ (supportedOn H) := by
  rw [NullSpaceDimensionEven.finrank_nullSub hm, finrank_supportedOn, add_comm]
  exact Finset.card_sdiff_add_card_eq_card hS

/-- **AND SO THE STRICT INEQUALITY IS THE SPECIAL CASE `H \ S ≠ ∅`**, which is what the four
`nullSub_lt_admissible_*` theorems were each proving by hand from a witness. -/
theorem nullSub_lt_of_sdiff_nonempty (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) {H S : Finset V} (hS : S ⊆ H) (hne : (H \ S).Nonempty) :
    Module.finrank ℝ (nullSub G m S) < Module.finrank ℝ (supportedOn H) := by
  rw [← finrank_nullSub_add_card_sdiff G hm hS]
  exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hne)

/-! ## 2. The odd box: the deficiency is the layer the reflection fixes -/

theorem lowerHalf_sdiff_strictLower (i : Fin d) (n : ℕ) :
    (lowerHalf i n) \ (strictLower i n) = midLayer i n := by
  classical
  ext p
  simp only [Finset.mem_sdiff, lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_strictLower, mem_midLayer]
  omega

/-- **THE ODD BOX'S CODIMENSION**, which `nullSub_lt_admissible_box_odd`'s docstring asserted and
its statement did not carry. -/
theorem codim_box_odd (i : Fin d) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (strictLower i n)) + (midLayer i n).card
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← lowerHalf_sdiff_strictLower i n]
  refine finrank_nullSub_add_card_sdiff _ hm (fun p hp => ?_)
  rw [lowerHalf, Finset.mem_filter]
  rw [mem_strictLower] at hp
  exact ⟨Finset.mem_univ p, by omega⟩

/-! ## 3. The even box: the deficiency is the layer adjacent to its own mirror -/

theorem codim_box_even (i : Fin d) (hn : Even n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (InnerLowerSupport.innerLower i n))
        + ((lowerHalf i n).filter (fun p => 2 * (p i).val + 2 = n)).card
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← NullSpaceDimensionEven.lowerHalf_sdiff_innerLower i hn]
  exact finrank_nullSub_add_card_sdiff _ hm
    (NullSpaceDimensionEven.innerLower_subset_lowerHalf i n)

/-! ## 4. The torus: two layers at even side, the seam alone at odd -/

theorem codim_torus_even (i : Fin d) (hn : Even n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n))
        + ((lowerHalf i n).filter
            (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0)).card
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← lowerHalf_sdiff_torusInner i hn]
  exact finrank_nullSub_add_card_sdiff _ hm (torusInner_subset_lowerHalf i n)

/-- **AT EVERY SIDE**, against the half the machinery actually uses. At odd side the first
disjunct is unsatisfiable (`TorusAdjAnySide.inner_layer_empty_of_odd`), so the deficiency is the
seam alone. -/
theorem codim_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n))
        + ((strictLower i n).filter
            (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0)).card
      = Module.finrank ℝ (supportedOn (strictLower i n)) := by
  rw [← strictLower_sdiff_torusInner i n]
  exact finrank_nullSub_add_card_sdiff _ hm (torusInner_subset_strictLower i n)

/-- **THE ODD TORUS, WITH THE DISJUNCTION COLLAPSED.** -/
theorem codim_torus_odd (i : Fin d) (hn : Odd n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n))
        + ((strictLower i n).filter (fun p => (p i).val = 0)).card
      = Module.finrank ℝ (supportedOn (strictLower i n)) := by
  classical
  have hset : (strictLower i n).filter (fun p => (p i).val = 0)
      = (strictLower i n).filter
          (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, h⟩; exact ⟨hp, Or.inr h⟩
    · rintro ⟨hp, h | h⟩
      · exact absurd h (inner_layer_empty_of_odd i hn p)
      · exact ⟨hp, h⟩
  rw [hset]
  exact codim_torus_any i n hm

end NullSpaceCodimension
