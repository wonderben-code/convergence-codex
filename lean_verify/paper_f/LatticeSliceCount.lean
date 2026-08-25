import NullSpaceCodimension

/-!
# How many sites a coordinate slice has, and the codimensions as numbers

`NullSpaceCodimension` turned *"the null space is strictly smaller than the admissible families"*
into *"smaller by exactly this set"*, and said in its own closing section that the remaining step
was *"smaller by exactly this number"* — each deficiency being a union of coordinate slices
`{p : pᵢ = c}`, of cardinality `n ^ (d − 1)`, which nothing here computed.

This is that step.

> `card_slice` — `#{p : Fin d → Fin n | pᵢ = c} = n ^ (d − 1)`, for every axis and every value.

## Searched for first, and the scope is stated

`grep -rn "n ^ (d - 1)" paper_f` returns exactly three hits, and all three are the sentences in
`NullSpaceTorus`, `NullSpaceTorusAny` and `NullSpaceCodimension` recording this as **not** done —
so the estate has no slice count. Mathlib was searched by shape rather than by guessed name, and
the nearest thing is **`Equiv.subtypePreimage`**: functions whose restriction to a subtype is a
prescribed function, equivalent to functions off that subtype. Specialising it here means carrying
the constraint as a function equality `g ∘ (↑) = fun _ => c` and converting that to `g i = c`,
which is about as much work as `sliceEquiv` below and reads worse. `Equiv.subtypeEquivCodomain` is
the mirror statement — values prescribed OFF a point — and is not this. **The near-miss is named
so that a later reader does not assume it was missed.**

## Why it is a bijection and not an induction

A site of the slice is determined by its values off `i`, and those are unconstrained. So the slice
is in bijection with `{j : Fin d // j ≠ i} → Fin n` — `sliceEquiv`, whose inverse fills the `i`-th
coordinate back in with `c` — and `Fintype.card_fun` turns that into `n ^ #{j ≠ i}`, which is
`n ^ (d − 1)` by `Fintype.card_subtype_compl`. No arithmetic on `d` is done by hand, which matters
because `d − 1` is truncated subtraction and every hand-rolled step with it is a place to be wrong.

## What this buys, and where it stops

The single-layer deficiencies become numbers outright: the odd box's midline
(`codim_box_odd_eq`), the even box's innermost layer (`codim_box_even_eq`), and the odd torus's
seam (`codim_torus_odd_eq`). Each is exactly `n ^ (d − 1)`.

**The even torus is the case where two layers must not be double-counted.** They are the seam
`pᵢ = 0` and the innermost layer `2·pᵢ + 2 = n`, and they are the SAME layer at `n = 2` and
distinct from `n = 4` on. `codim_torus_even_eq` therefore carries `4 ≤ n` and gives
`2 * n ^ (d − 1)`; `codim_torus_two_eq` is the degenerate side, where the deficiency is the whole
half and the null space is trivial. **The hypothesis is not a convenience** — without it the
statement is false, and `NullSpaceTorus`'s header already recorded that `n = 2` is where "two
layers" stops being a count.
-/

namespace LatticeSliceCount

open Finset BoxGraph BoxOddReflection GraphHalfSpace GraphReflection
open TorusReflection TorusInnerSupport TorusAdjAnySide NullSpaceDimension NullSpaceCodimension

variable {d n : ℕ}

/-! ## 1. The slice -/

/-- A site with its `i`-th coordinate pinned is exactly a free choice off `i`. -/
def sliceEquiv (i : Fin d) (c : Fin n) :
    {p : Fin d → Fin n // p i = c} ≃ ({j : Fin d // j ≠ i} → Fin n) where
  toFun p j := p.1 j.1
  invFun g := ⟨fun j => if h : j = i then c else g ⟨j, h⟩, by simp⟩
  left_inv := by
    rintro ⟨p, hp⟩
    ext j
    by_cases h : j = i
    · subst h; simp [hp]
    · simp [h]
  right_inv := by
    intro g
    ext ⟨j, hj⟩
    simp [hj]

/-- **A COORDINATE SLICE HAS `n ^ (d − 1)` SITES**, at every axis and every value. -/
theorem card_slice (i : Fin d) (c : Fin n) :
    (Finset.univ.filter fun p : Fin d → Fin n => p i = c).card = n ^ (d - 1) := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (sliceEquiv i c), Fintype.card_fun,
    Fintype.card_fin]
  congr 1
  -- `Fintype.card {j // j ≠ i} = d - 1`, by `card_subtype_compl` and `card_subtype_eq`
  simp

/-- The same, for a slice cut out by a condition on the coordinate's VALUE rather than on the
coordinate — which is the shape every deficiency set in this chain has. -/
theorem card_slice_val (i : Fin d) (k : ℕ) (hk : k < n) :
    (Finset.univ.filter fun p : Fin d → Fin n => (p i).val = k).card = n ^ (d - 1) := by
  classical
  rw [← card_slice i ⟨k, hk⟩]
  congr 1
  ext p
  simp [Fin.ext_iff]

/-! ## 2. The single-layer codimensions, as numbers -/

/-- **THE ODD BOX**: the deficiency is the midline the reflection fixes, and it has exactly
`n ^ (d − 1)` sites. -/
theorem card_midLayer (i : Fin d) (hn : Odd n) : (midLayer i n).card = n ^ (d - 1) := by
  classical
  obtain ⟨k, hk⟩ := hn
  rw [← card_slice_val i k (by omega)]
  congr 1
  ext p
  simp only [midLayer, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem codim_box_odd_eq (i : Fin d) (hn : Odd n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (strictLower i n)) + n ^ (d - 1)
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← card_midLayer i hn]; exact codim_box_odd i hm

/-- **THE EVEN BOX**: the innermost layer, `2·pᵢ + 2 = n`, again `n ^ (d − 1)`. -/
theorem card_inner_layer_box (i : Fin d) (hn : Even n) (hpos : 0 < n) :
    ((lowerHalf i n).filter (fun p => 2 * (p i).val + 2 = n)).card = n ^ (d - 1) := by
  classical
  obtain ⟨t, ht⟩ := hn
  rw [← card_slice_val i (t - 1) (by omega)]
  congr 1
  ext p
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem codim_box_even_eq (i : Fin d) (hn : Even n) (hpos : 0 < n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (InnerLowerSupport.innerLower i n)) + n ^ (d - 1)
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← card_inner_layer_box i hn hpos]; exact codim_box_even i hn hm

/-- **THE ODD TORUS**: the seam alone, `pᵢ = 0`, and it is `n ^ (d − 1)`.

**`3 ≤ n` is needed and the statement is FALSE without it.** At `n = 1` the half `strictLower` is
empty, so the left side is `0`, while the right side is `1 ^ (d − 1) = 1`. The seam is a site of the
lattice at every side; it is a site of the HALF only from side two, and at odd side that means
three. `codim_torus_odd` itself holds at `n = 1` — both sides are zero — so the hypothesis belongs
to the numeric form and not to the codimension. -/
theorem card_seam (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n) :
    ((strictLower i n).filter (fun p => (p i).val = 0)).card = n ^ (d - 1) := by
  classical
  obtain ⟨k, hk⟩ := hn
  rw [← card_slice_val i 0 (by omega)]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_strictLower]
  omega

theorem codim_torus_odd_eq (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n)) + n ^ (d - 1)
      = Module.finrank ℝ (supportedOn (strictLower i n)) := by
  rw [← card_seam i hn h3]; exact codim_torus_odd i hn hm

/-! ## 3. The even torus, where the two layers must be kept apart -/

/-- **AT `4 ≤ n` THE TWO LAYERS ARE DISJOINT AND THE DEFICIENCY IS `2 · n ^ (d − 1)`.**
The hypothesis is load-bearing: at `n = 2` the seam and the innermost layer coincide. -/
theorem card_two_layers (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) :
    ((lowerHalf i n).filter
        (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0)).card = 2 * n ^ (d - 1) := by
  classical
  obtain ⟨t, ht⟩ := hn
  have hsplit : (lowerHalf i n).filter
        (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0)
      = ((Finset.univ.filter fun p : Fin d → Fin n => (p i).val = t - 1)
          ∪ (Finset.univ.filter fun p : Fin d → Fin n => (p i).val = 0)) := by
    ext p
    simp only [lowerHalf, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    omega
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin d → Fin n => (p i).val = t - 1)
      (Finset.univ.filter fun p : Fin d → Fin n => (p i).val = 0) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    card_slice_val i (t - 1) (by omega), card_slice_val i 0 (by omega)]
  ring

theorem codim_torus_even_eq (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n)) + 2 * n ^ (d - 1)
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← card_two_layers i hn h4]; exact codim_torus_even i hn hm

/-- **AND AT SIDE TWO THE TWO LAYERS ARE ONE**, so the deficiency is `n ^ (d − 1)` and not twice
it — the null space being trivial there, since `torusInner i 2 = ∅`. Stated so that the
`4 ≤ n` above reads as a fact rather than as caution. -/
theorem card_two_layers_side_two (i : Fin d) :
    ((lowerHalf i 2).filter
        (fun p => 2 * (p i).val + 2 = 2 ∨ (p i).val = 0)).card = 2 ^ (d - 1) := by
  classical
  rw [← card_slice_val i 0 (by omega)]
  congr 1
  ext p
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

end LatticeSliceCount
