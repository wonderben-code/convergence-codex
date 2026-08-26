import MirrorStrictness

/-!
# The odd-side gap `MirrorStrictness` named, closed from side five

`MirrorStrictness` carried a gap and said so. Strictness transfers between a half and its mirror
image as a biconditional; at **odd** side the COMPLEMENT of the lower half is a proper subset of
that image — the midline is the difference — so only one direction transferred, and the file said
of the converse:

> *"would need a null family supported strictly above the midline. **This file does not claim
> it**, and the reason is stated rather than hidden: the mirror of a lower-half null family is
> supported on the image, and nothing here shows it vanishes on the midline."*

**It is supplied here, from side five, and the route is not the one that sentence expected.**

## The identity that does the work

At **odd** side the complement of the lower half is not merely inside the mirror image of the lower
half: it is **exactly the mirror image of `innerLower`**.

  `p ∉ lowerHalf` ⟺ `2·pᵢ ≥ n` ⟺ `2·pᵢ > n` (parity: equality is impossible at odd `n`)

and reflecting sends `pᵢ` to `n − 1 − pᵢ`, which turns `2·pᵢ > n` into `2·pᵢ + 2 < n`. So
`compl_lowerHalf_eq_image_innerLower`, and with `MirrorStrictness.strict_iff_mirror` the question
*"is the form strict above the midline?"* becomes *"is it strict on `innerLower`?"* — a question
about a set BELOW the cut, where this estate's null families live.

**The parity is the whole of it.** At even side `2·pᵢ = n` is attainable and the identity fails;
that is the same fact `BoxOddComplement.compl_subset_image` records as an inclusion rather than an
equality.

## What is proved

* **`massive_mulVec_supported_of_gap`** — on **any** finite graph: if nothing outside `T` is equal
  or adjacent to anything in `S`, then the massive image of a vector supported on `S` vanishes off
  `T`. `InnerLowerSupport.massive_mulVec_supported` is this at one particular pair of sets: its
  proof spends its first half establishing the gap for `innerLower` and `lowerHalf`, and
  everything after that is the four lines below. **The third time this week the missing piece has
  been the massive operator's action on a vector, stated only for the case that needed it** —
  after `NullSpaceLattice.massive_mulVec_congr` for a relabelling and
  `NullSpaceMirror.massive_mulVec_mir` for a reflection.
* **`compl_lowerHalf_eq_image_innerLower`** — the identity above.
* **`exists_null_innerLower`** — from side five, a nonzero family supported on `innerLower` that
  the reflected form annihilates. The witness is the massive image of one site of the bottom layer;
  its support reaches two layers, and two layers sit inside `innerLower` exactly when `5 ≤ n`.
* **`not_strict_compl_box_odd`** — so at odd side from five the form is **not** strict on the
  complement either, and `MirrorStrictness`'s gap is closed there.

## WHAT IS STILL OPEN, AND IT IS ONE SIDE LENGTH

**`n = 3` is not settled and nothing below claims it.** There the complement is a single layer, the
mirror image of `innerLower i 3 = {pᵢ = 0}`, and the witness used here does not fit: its support
reaches `pᵢ = 1`, which is outside `innerLower` at that side. Whether the form is strict on one
layer at odd side three is a question this file leaves exactly where it found it — a genuinely
smaller question than the one it started with, which is the point of writing it down.
-/

namespace MirrorComplement

open Finset BoxGraph GraphHalfSpace GraphReflection InnerLowerSupport

open scoped Matrix

/-! ## 1. The support lemma, for any two sets with a gap between them -/

/-- **THE MASSIVE IMAGE STAYS INSIDE ANYTHING THAT SURROUNDS ITS SUPPORT.** No graph structure is
used beyond the hypothesis, which is the closed-neighbourhood condition written out. -/
theorem massive_mulVec_supported_of_gap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {S T : Finset V}
    (h : ∀ p, p ∉ T → ∀ q ∈ S, p ≠ q ∧ ¬ G.Adj p q)
    {v : V → ℝ} (hv : ∀ p, p ∉ S → v p = 0) :
    ∀ p, p ∉ T → (GraphLaplacian.massive G m *ᵥ v) p = 0 := by
  classical
  intro p hp
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ S
  · obtain ⟨hne, hadj⟩ := h p hp q hq
    rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hadj]
    ring
  · rw [hv q hq, mul_zero]

/-! ## 2. The two layers at the bottom, and the gap above them -/

variable {d n : ℕ} {m : ℝ}

/-- The bottom layer in direction `i`. -/
def bottom (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => (p i).val = 0

/-- The bottom two layers. -/
def twoLayers (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => (p i).val ≤ 1

theorem mem_bottom {i : Fin d} {p : Site d n} : p ∈ bottom i n ↔ (p i).val = 0 := by
  simp [bottom]

theorem mem_twoLayers {i : Fin d} {p : Site d n} : p ∈ twoLayers i n ↔ (p i).val ≤ 1 := by
  simp [twoLayers]

/-- Nothing two or more layers up is equal or adjacent to the bottom layer. -/
theorem gap_twoLayers (i : Fin d) (n : ℕ) :
    ∀ p, p ∉ twoLayers i n → ∀ q ∈ bottom i n, p ≠ q ∧ ¬ (boxGraph d n).Adj p q := by
  classical
  intro p hp q hq
  rw [mem_twoLayers] at hp
  rw [mem_bottom] at hq
  have hne : p ≠ q := fun hc => by rw [hc] at hp; omega
  refine ⟨hne, ?_⟩
  rintro ⟨j, hsame, hstep⟩
  by_cases hj : j = i
  · subst hj; omega
  · exact hne (funext fun l => by
      by_cases hl : l = j
      · subst hl
        exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm))) (by omega)
      · exact hsame l hl)

theorem bottom_subset_innerLower (i : Fin d) {n : ℕ} (h3 : 3 ≤ n) :
    bottom i n ⊆ innerLower i n := fun p hp => by
  rw [mem_bottom] at hp
  exact mem_innerLower.mpr (by omega)

theorem twoLayers_subset_innerLower (i : Fin d) {n : ℕ} (h5 : 5 ≤ n) :
    twoLayers i n ⊆ innerLower i n := fun p hp => by
  rw [mem_twoLayers] at hp
  exact mem_innerLower.mpr (by omega)

/-! ## 3. The identity, and the parity is the whole of it -/

/-- **AT ODD SIDE THE COMPLEMENT OF THE LOWER HALF IS THE MIRROR IMAGE OF `innerLower`.**
At even side `2·pᵢ = n` is attainable and this is only an inclusion, which is what
`BoxOddComplement.compl_subset_image` records. -/
theorem compl_lowerHalf_eq_image_innerLower (i : Fin d) {n : ℕ} (hn : Odd n) :
    (lowerHalf i n)ᶜ = (innerLower i n).image (revSite (n := n) i) := by
  classical
  obtain ⟨k, hk⟩ := hn
  ext p
  simp only [Finset.mem_compl, Finset.mem_image, lowerHalf, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt, mem_innerLower]
  constructor
  · intro hp
    refine ⟨revSite (n := n) i p, ?_, revSite_involutive i p⟩
    have := (p i).isLt
    rw [revSite_apply_self, Fin.val_rev]
    omega
  · rintro ⟨q, hq, rfl⟩
    have := (q i).isLt
    rw [revSite_apply_self, Fin.val_rev]
    omega

/-! ## 4. A null family on `innerLower`, from side five -/

/-- **THE WITNESS.** The massive image of one site of the bottom layer: nonzero because the massive
operator is injective, supported on two layers by §1, and annihilated by the reflected form because
it is a massive image of something on `innerLower` (`NullSpaceBoxAny.nullSpace_box_any`). Two layers
sit inside `innerLower` exactly from side five. -/
theorem exists_null_innerLower (i : Fin d) {n : ℕ} (h5 : 5 ≤ n) (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ innerLower i n → c p = 0)
      ∧ reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 := by
  classical
  have hpos : 0 < n := by omega
  set p₀ : Site d n := fun _ => ⟨0, hpos⟩ with hp₀
  set v : Site d n → ℝ := fun p => if p = p₀ then 1 else 0 with hv
  have hv0 : v ≠ 0 := fun hc => by
    have := congrFun hc p₀
    simp [hv] at this
  have hvsupp : ∀ p, p ∉ bottom i n → v p = 0 := by
    intro p hp
    refine if_neg fun hc => hp ?_
    rw [hc, mem_bottom, hp₀]
  have hvinner : ∀ p, p ∉ innerLower i n → v p = 0 := fun p hp =>
    hvsupp p fun hc => hp (bottom_subset_innerLower i (by omega) hc)
  refine ⟨GraphLaplacian.massive (boxGraph d n) m *ᵥ v, ?_, ?_, ?_⟩
  · intro hc
    exact hv0 (NullSpaceDimension.massive_mulVecLin_injective
      (G := boxGraph d n) (m := m) hm (by simpa using hc))
  · intro p hp
    exact massive_mulVec_supported_of_gap _ m (gap_twoLayers i n) hvsupp p
      (fun hmem => hp (twoLayers_subset_innerLower i h5 hmem))
  · refine (NullSpaceBoxAny.nullSpace_box_any (m := m) i n hm ?_).mpr ⟨v, hvinner, rfl⟩
    intro p hp
    exact massive_mulVec_supported_of_gap _ m (gap_twoLayers i n) hvsupp p
      (fun hmem => hp (NullSpaceDimensionEven.innerLower_subset_lowerHalf i n
        (twoLayers_subset_innerLower i h5 hmem)))

/-! ## 5. So the complement is not strict either, at odd side from five -/

/-- **`MirrorStrictness`'S GAP, CLOSED FROM SIDE FIVE.** -/
theorem not_strict_compl_box_odd (i : Fin d) {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ (lowerHalf i n)ᶜ → c p = 0) →
        0 < reflectedForm (boxGraph d n) m (revSite (n := n) i) c) := by
  classical
  rw [compl_lowerHalf_eq_image_innerLower i hn,
    ← MirrorStrictness.strict_iff_mirror (BoxNotStrict.isRefl_box i) m (innerLower i n)]
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_innerLower (m := m) i h5 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

end MirrorComplement
