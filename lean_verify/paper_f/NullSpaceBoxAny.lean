import LatticeSliceCount
import CrossBlockStructure

/-!
# The box's null space at every side length, and the threshold as a consequence of the count

`NullSpace.nullSpace_box_odd` describes the null space of the reflected form on the **odd** box and
`NullSpaceEven.nullSpace_box_even` on the **even** box, with two different sets: `strictLower`
there and `innerLower` here. `InnerLowerSupport` already showed that the second set is the right
one at both parities — `innerLower_eq_strictLower_of_odd` — and proved the support lemma with no
parity at all. **This file is the fusion those three make available**: one biconditional over every
`n`, then the dimension, the deficiency as a number, and the strictness threshold read off the
count.

## THE THRESHOLD IS NOT NEW AND THIS FILE DOES NOT CLAIM IT IS

`CrossBlockStructure.box_strict_iff_le_two_lowerHalf` has had `n ≤ 2`, at every side, in every
dimension, with no parity hypothesis, since **12 August 2026** (`44a346d`), and
`all_three_thresholds` states it beside the torus and the lattice. Nothing below discovers that
number.

What is new is the **route**, and `ERRATUM 267` is the entry about announcing one as the other. The
estate's threshold is read off the cut: the criterion asks whether the coupling matrix is a block
of ones, and below side three it is. The threshold below is read off the *null space*: the form is
nondegenerate exactly when there is nothing for a null family to be built from, and there is
nothing below side three because `innerLower` is empty. `strict_iff_innerLower_empty` is the
statement that carries the content, and composing it with the estate's biconditional gives
`innerLower i n = ∅ ↔ n ≤ 2`, which is `innerLower_nonempty_iff` read backwards. Two agreeing
arguments become one argument and its explanation, which is exactly what the torus got in
`NullSpaceTorusAny` §6.

## What is proved

* `nullSpace_box_any` — at **every** `n`: an admissible family is null for the reflected form
  **iff** it is the massive image of something supported on `innerLower`.
* `mem_nullSub_iff_box_any` — the same as a description of the submodule.
* `lowerHalf_sdiff_innerLower_any` and `card_lowerHalf_sdiff_innerLower` — **the deficiency is
  exactly one layer at every parity**, and that layer is the slice at height `(n − 1) / 2`, of
  size `n ^ (d − 1)`. This unifies `LatticeSliceCount.card_midLayer` (odd, the midline the
  reflection fixes) and `card_inner_layer_box` (even, the layer adjacent to its own mirror): two
  geometrically different layers, the same count, and now one statement.
* `codim_box_any` and `nullSub_lt_admissible_box_any` — the codimension, at every parity, from
  `0 < n` rather than from `Even n ∧ 2 ≤ n` or from `Odd n`.
* `innerLower_eq_empty_of_le_two`, `innerLower_nonempty_iff`, `null_trivial_iff_side_le_two`,
  `strict_iff_innerLower_empty` and its `0 <` twin.

## What is NOT here

**The dimension is not restated, because it is already parity-free.**
`NullSpaceDimensionEven.finrank_nullSub_box_even` reads
`finrank (nullSub (boxGraph d n) m (innerLower i n)) = (innerLower i n).card` and carries **no**
`Even n` — it is `finrank_nullSub` applied to a set, and the set does not care. Its NAME says
`even` and its statement does not, which is a naming residue and not a gap; it is used directly
below rather than aliased, so that nothing here duplicates a declaration that already holds.

Reflection positivity is untouched: `BoxOddReflection.reflectionPositive_box_any` says the form is
`≥ 0` at every side. Everything below says by how much `≥` fails to be `>`.

The torus is not touched either. Its threshold is five, not three, and the reason is visible in the
two `innerLower`-shaped sets: `torusInner` carries the extra clause `1 ≤ pᵢ`, excluding the seam,
because on the torus layer `0` wraps round to layer `n − 1` — which is its own mirror image under
`revSite` — and `TorusInnerSupport` records that this is the case where the support lemma fails.
The box has no wrap and so nothing to exclude.
-/

namespace NullSpaceBoxAny

open Finset BoxGraph BoxOddReflection GraphHalfSpace GraphReflection
open InnerLowerSupport NullSpaceDimension NullSpaceDimensionEven

open scoped Matrix

variable {d n : ℕ} {m : ℝ}

private theorem mem_lowerHalf (i : Fin d) (p : Site d n) :
    p ∈ lowerHalf i n ↔ 2 * (p i).val < n := by
  simp [lowerHalf]

/-! ## 1. The null space, with the parity gone

The two halves are already proved; what makes them fuse is that `innerLower` **is** `strictLower`
at odd side, so the odd statement is the same statement in a different spelling.
-/

/-- **THE NULL SPACE OF THE REFLECTED FORM ON THE BOX, AT EVERY SIDE LENGTH.** An admissible
family is annihilated by the reflected form **iff** it is the massive operator applied to something
supported two or more layers below the cut.

At even side this is `NullSpaceEven.nullSpace_box_even` verbatim. At odd side it is
`NullSpace.nullSpace_box_odd` with `strictLower` rewritten to `innerLower`, which
`InnerLowerSupport.innerLower_eq_strictLower_of_odd` licenses — and that rewrite is the whole
content of the fusion, because at even side the two sets differ by a layer. -/
theorem nullSpace_box_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ, (∀ p, p ∉ innerLower i n → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c := by
  rcases Nat.even_or_odd n with hn | hn
  · exact NullSpaceEven.nullSpace_box_even i hn hm hc
  · rw [NullSpace.nullSpace_box_odd i hn hm hc, innerLower_eq_strictLower_of_odd i hn]

/-- **THE SAME, AS A DESCRIPTION OF THE SUBMODULE.** The massive image of the functions on
`innerLower` is exactly the admissible null families, at every `n`. The even case is
`NullSpaceDimensionEven.mem_nullSub_iff_box_even` and the odd case is
`NullSpaceDimension.mem_nullSub_iff_box_odd` over `strictLower`; this is one statement over both. -/
theorem mem_nullSub_iff_box_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) (c : Site d n → ℝ) :
    c ∈ nullSub (boxGraph d n) m (innerLower i n)
      ↔ (∀ p, p ∉ lowerHalf i n → c p = 0)
        ∧ reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 := by
  constructor
  · intro hcm
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hcm
    have hsupp := massive_mulVec_supported i m hvsupp
    exact ⟨hsupp, (nullSpace_box_any i n hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((nullSpace_box_any i n hm hcsupp).mp hcnull)

/-! ## 2. The deficiency is one layer, at every parity

At odd side the missing layer is the midline, which the reflection fixes. At even side it is the
layer whose sites are adjacent to their own mirrors. They are different layers — one is fixed by
the reflection and the other is not — but they sit at the same height and they have the same size.
-/

/-- **THE DEFICIENCY SET, IN ONE FORMULA.** `lowerHalf \ innerLower` is the single slice at height
`(n − 1) / 2`. At odd `n = 2k + 1` that is `pᵢ = k`, the midline; at even `n = 2t` it is
`pᵢ = t − 1`, the innermost layer.

**BOTH HALVES ALREADY EXIST AND THIS DOES NOT CLAIM OTHERWISE.**
`NullSpaceCodimension.lowerHalf_sdiff_strictLower` is `lowerHalf \ strictLower = midLayer`, with no
parity at all, and `NullSpaceDimensionEven.lowerHalf_sdiff_innerLower` is the even statement with
`Even n`. What is new is the single formula: writing the height as `(n − 1) / 2` makes one slice
serve both, so no parity and no set-name appears on the right. -/
theorem lowerHalf_sdiff_innerLower_any (i : Fin d) {n : ℕ} (hn : 0 < n) :
    (lowerHalf i n) \ (innerLower i n)
      = Finset.univ.filter (fun p : Site d n => (p i).val = (n - 1) / 2) := by
  classical
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_innerLower, mem_lowerHalf i p]
  omega

/-- **AND IT HAS `n ^ (d − 1)` SITES.** One layer of the lattice, at every parity — which is what
`LatticeSliceCount.card_midLayer` says at odd side and `card_inner_layer_box` at even side, each
under its own hypothesis. -/
theorem card_lowerHalf_sdiff_innerLower (i : Fin d) {n : ℕ} (hn : 0 < n) :
    ((lowerHalf i n) \ (innerLower i n)).card = n ^ (d - 1) := by
  rw [lowerHalf_sdiff_innerLower_any i hn]
  exact LatticeSliceCount.card_slice_val i ((n - 1) / 2) (by omega)

/-- **THE CODIMENSION AS A NUMBER, AT EVERY PARITY, FROM `0 < n`.**

Stated against the two existing numeric forms rather than against the abstract ones, because that
is where the parity actually sits: `NullSpaceCodimension.codim_box_odd` carries **no** parity
already (its deficiency is `(midLayer i n).card`, unevaluated) and `codim_box_even` carries
`Even n`. It is `LatticeSliceCount.codim_box_odd_eq` that needs `Odd n` and `codim_box_even_eq`
that needs `Even n` and `0 < n`, each to turn its layer into `n ^ (d − 1)`. This subsumes those
two — it does not replace them, and both stay. -/
theorem codim_box_any (i : Fin d) {n : ℕ} (hn : 0 < n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (innerLower i n)) + n ^ (d - 1)
      = Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  rw [← card_lowerHalf_sdiff_innerLower i hn]
  exact NullSpaceCodimension.finrank_nullSub_add_card_sdiff _ hm
    (innerLower_subset_lowerHalf i n)

/-- **SO THE FORM IS DEGENERATE FROM SIDE ONE UP**, with the deficiency measured rather than merely
positive. `NullSpaceDimension.nullSub_lt_admissible_box_odd` needs `Odd n` and
`NullSpaceDimensionEven.nullSub_lt_admissible_box_even` needs `Even n` and `2 ≤ n`; this needs
`0 < n`, which is sharp — at `n = 0` the site type is empty and both ranks are zero.

**Degenerate is not the same as non-strict.** This says the null space is smaller than the
admissible families; it does not say the null space is nonzero. At `n = 1` and `n = 2` it is zero,
and §4 is where that is settled. -/
theorem nullSub_lt_admissible_box_any (i : Fin d) {n : ℕ} (hn : 0 < n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (innerLower i n))
      < Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  have h := codim_box_any (m := m) i hn hm
  have hpos : 0 < n ^ (d - 1) := pow_pos hn (d - 1)
  omega

/-! ## 3. When the set is empty -/

/-- Below side three there is nothing two layers under the cut. -/
theorem innerLower_eq_empty_of_le_two (i : Fin d) {n : ℕ} (hn : n ≤ 2) :
    innerLower i n = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [mem_innerLower] at hp
  omega

/-- **AND FROM SIDE THREE THERE IS.** `InnerLowerSupport.innerLower_nonempty` supplies one
direction and it is the direction that needs a site; this pairs it with the other. -/
theorem innerLower_nonempty_iff (i : Fin d) (n : ℕ) :
    (innerLower i n).Nonempty ↔ 3 ≤ n := by
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_innerLower] at hp
    omega
  · exact fun h3 => innerLower_nonempty i h3

/-! ## 4. The threshold, as a consequence of the count -/

/-- **A NONZERO NULL FAMILY FROM SIDE THREE, AT EVERY PARITY, AND NOTHING IS CONSTRUCTED.**
`BoxNotStrict.exists_null_direction` builds one at even sides from four and
`BoxOddNotStrict.exists_null_direction_box_odd` at odd sides from three; each exhibits a family.
This produces one from the dimension alone: `finrank_nullSub_box_even` makes the rank
`(innerLower i n).card` and `innerLower_nonempty_iff` makes that positive from three. -/
theorem exists_null_massive_box_any (i : Fin d) (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0)
      ∧ reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0
      ∧ ∃ v : Site d n → ℝ, (∀ p, p ∉ innerLower i n → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c := by
  classical
  obtain ⟨p, hp⟩ := (innerLower_nonempty_iff (n := n) i).mpr h3
  have hne : Nontrivial (nullSub (boxGraph d n) m (innerLower i n)) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_nullSub_box_even (m := m) i hm]; exact Finset.card_pos.mpr ⟨p, hp⟩)
  obtain ⟨c, hc0⟩ := exists_ne (0 : nullSub (boxGraph d n) m (innerLower i n))
  obtain ⟨hcsupp, hcnull⟩ := (mem_nullSub_iff_box_any i n hm _).mp c.2
  exact ⟨c.1, fun h => hc0 (Subtype.ext h), hcsupp, hcnull,
    (nullSpace_box_any i n hm hcsupp).mp hcnull⟩

/-- **NONDEGENERATE EXACTLY BELOW SIDE THREE, AT EVERY PARITY.**

**The number is `CrossBlockStructure.box_strict_iff_le_two_lowerHalf`'s and has been since 12
August 2026.** What this adds is that it follows from the size of the null space rather than from
the shape of the cut; see `strict_iff_innerLower_empty` below, which is the statement that carries
the reason. -/
theorem null_trivial_iff_side_le_two (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : Site d n → ℝ, (∀ p, p ∉ lowerHalf i n → c p = 0) →
        reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 → c = 0) ↔ n ≤ 2 := by
  constructor
  · intro h
    by_contra h2
    obtain ⟨c, hc0, hcsupp, hcnull, -⟩ := exists_null_massive_box_any (m := m) i n (by omega) hm
    exact hc0 (h c hcsupp hcnull)
  · intro h2 c hcsupp hcnull
    obtain ⟨v, hvsupp, rfl⟩ := (nullSpace_box_any i n hm hcsupp).mp hcnull
    have hv0 : v = 0 := funext fun p => hvsupp p (by
      rw [innerLower_eq_empty_of_le_two i h2]; exact Finset.notMem_empty p)
    rw [hv0, Matrix.mulVec_zero]

/-- **STRICT ON THE HALF EXACTLY WHEN THERE IS NOTHING TWO LAYERS DOWN.** No side length appears.
The null space is the massive image of the families on `innerLower` (§1) and has dimension
`(innerLower i n).card`, so it is trivial exactly when that set is empty. -/
theorem strict_iff_innerLower_empty (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : Site d n → ℝ, (∀ p, p ∉ lowerHalf i n → c p = 0) →
        reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 → c = 0)
      ↔ innerLower i n = ∅ := by
  classical
  rw [null_trivial_iff_side_le_two i n hm]
  constructor
  · exact fun h2 => innerLower_eq_empty_of_le_two i h2
  · intro he
    by_contra h2
    obtain ⟨p, hp⟩ := (innerLower_nonempty_iff (n := n) i).mpr (by omega)
    rw [he] at hp
    exact absurd hp (by simp)

/-- **THE SAME, IN THE ESTATE'S STRICTNESS VOCABULARY** — the left side is *literally*
`CrossBlockStructure.box_strict_iff_le_two_lowerHalf`'s left side, so the two compose to

  `innerLower i n = ∅ ↔ n ≤ 2`,

which is `innerLower_nonempty_iff` read backwards. **That composition is the point of the file.**
The estate already knew the threshold; what it did not have is the sentence *the box's reflected
form is strict on the half because there is nothing for a null family to be built from*, with both
halves proved.

Passing from `= 0 → c = 0` to `0 < …` is where reflection positivity enters, and it holds at every
side (`BoxOddReflection.reflectionPositive_box_any`). -/
theorem strict_iff_innerLower_empty' (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < reflectedForm (boxGraph d n) m (revSite (n := n) i) c)
      ↔ innerLower i n = ∅ := by
  rw [← strict_iff_innerLower_empty i n hm]
  constructor
  · intro hs c hcsupp hnull
    by_contra hc0
    exact absurd hnull (ne_of_gt (hs c hc0 hcsupp))
  · intro hs c hc0 hcsupp
    rcases lt_or_eq_of_le
      (BoxOddReflection.reflectionPositive_box_any i n hm c hcsupp) with h | h
    · exact h
    · exact absurd (hs c hcsupp h.symm) hc0

/-- **AND THE COMPOSITION, WRITTEN DOWN.** The estate's criterion and this file's count are the
same biconditional through different middles, so the emptiness of `innerLower` and the side length
determine one another. Stated because `ERRATUM 267`'s lesson is that two agreeing routes are worth
one theorem saying they agree, not two files each claiming the number. -/
theorem innerLower_empty_iff_side_le_two (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    innerLower i n = ∅ ↔ n ≤ 2 := by
  rw [← strict_iff_innerLower_empty i n hm, null_trivial_iff_side_le_two i n hm]

end NullSpaceBoxAny
