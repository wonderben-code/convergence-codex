import TorusAdjAnySide
import NullSpaceTorus

/-!
# The null space of the torus at every side length, and its dimension

`NullSpaceTorus` did this at even side an hour ago and left the odd side as the last
lattice-and-parity combination in this group without an exact description. `TorusAdjAnySide`
removed the two places `Even n` was load-bearing. This is the assembly, and it **subsumes** the
even-side statements rather than sitting beside them: at even side `strictLower = lowerHalf`, so
`nullSpace_torus_even'` recovers the earlier theorem in one line.

> `nullSpace_torus_any` — on a periodic box of **any** side, a family supported on `lowerHalf i n`
> is null **exactly when** it is the massive image of something supported on `torusInner i n`.
>
> `finrank_nullSub_torus_any` — that space has dimension `(torusInner i n).card`, and
> `null_trivial_iff_side_le_four_any` — it is trivial **exactly** when `n ≤ 4`.

## What changed and what did not

The half is `strictLower` and not `lowerHalf`, which is the whole adaptation. At even side the two
sets are equal (`strictLower_eq_lowerHalf_of_even`); at odd side `lowerHalf` is not a half at all,
and the machinery wants the three-way splitting `V = strictLower ⊔ midLayer ⊔ θ·strictLower` that
`BoxOddReflection.isMirrorHalf_strictLower` supplies at every side. The coefficient family `c`
still lives on `lowerHalf` — the mirror layer carries values and contributes nothing, which is
`GraphMirrorReflection`'s entire point.

**The interior set does not change**, and this is the part worth noticing. `torusInner` was
defined for the even side and `mem_torusInner_iff_sdiff` shows it is already `strictLower` minus
both layers at every `n`. So the odd torus's null space is described by the same set as the even
one, and the dimension is the same instance of the same general theorem.

## The threshold, and the third independent route to it

`null_trivial_iff_side_le_four_any` says the torus reflected form is nondegenerate on the half
**exactly** at sides `n ≤ 4`, at every parity. Three routes now reach that number and they share
no argument:

* `SmallSideStrict` transports strictness from the box and the estate's own `def` (sides 1–4).
* `NullSpaceTorus.null_trivial_iff_side_le_four` counts the even-side null space.
* This file counts it at every side. The estate's own degeneracy results are split by parity —
  `TorusNotStrict.exists_null_direction_torus` at `Even n` with `6 ≤ n`, and
  `OddNotStrictInstances.exists_null_direction_torus_odd` at `Odd n` with `5 ≤ n`, each with its
  own hand-built witness — and §4 makes **both** of them instances of one statement,
  `exists_null_direction_torus_any`, which asks only `5 ≤ n` and builds no witness at all: the
  null space is nontrivial because its dimension is positive.

**That agreement had a way of failing, which is the point.** `not_strict_torus_odd` was proved
from an explicit family; `null_trivial_iff_side_le_four_any` is proved from
`torusInner_nonempty_iff`. The two share no argument, and the count could have come out at six —
in which case it would have contradicted a theorem the estate already had, at `n = 5`. It does
not. Contrast ERRATUM 264, where the two numbers being compared could not have disagreed.

## What is NOT proved

The deficiency is still bounded below rather than counted, for the same reason as at even side:
`strictLower_sdiff_torusInner` names the missing sites and nothing turns them into a cardinality.
At odd side that set is ONE layer (the seam) rather than two, so the odd count is the easier of
the two and is still not done — it needs the size of `{p : pᵢ = 0}`, which is `n ^ (d - 1)` and
which nothing in this estate has had a reason to compute.

Reflection positivity is untouched at every side: `TorusAnySide.reflectionPositive_torus_any` says
the form is `≥ 0`. This says by how much `≥` fails to be `>`.
-/

namespace NullSpaceTorusAny

open Finset BoxGraph BoxOddReflection GraphHalfSpace GraphMirrorReflection GraphReflection
open TorusReflection TorusInnerSupport TorusAdjAnySide NullSpaceDimension

open scoped Matrix

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The coupling, at every side -/

/-- **THE CROSS FORM ON THE TORUS AT EVERY SIDE.** `NullSpaceTorus.crossForm_torus_eq` with
`Even n` deleted and the half taken to be `strictLower`. -/
theorem crossForm_torus_any_eq (i : Fin d) (n : ℕ) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (torusGraph d n) m (revSite (n := n) i) (strictLower i n) w
      = - ∑ p ∈ (strictLower i n).filter
            (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0), (w p) ^ 2 := by
  classical
  rw [crossForm_eq_neg_adj (isMirrorHalf_strictLower i n) m w]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · by_cases hin : 2 * (p i).val + 2 = n ∨ (p i).val = 0
    · rw [if_pos hin, if_pos ((adj_torus_revSite_iff_any i n hp hp).mpr ⟨rfl, hin⟩)]
      ring
    · rw [if_neg hin, if_neg fun hc =>
        hin ((adj_torus_revSite_iff_any i n hp hp).mp hc).2]
      ring
  · intro q hq hqp
    rw [if_neg fun hc => hqp ((adj_torus_revSite_iff_any i n hp hq).mp hc).1.symm]
    ring
  · intro hpn
    exact absurd hp hpn

/-- **AND IT VANISHES EXACTLY ON THE LAYERS.** Two of them at even side, one at odd. -/
theorem crossForm_eq_zero_iff_torus_any (i : Fin d) (n : ℕ) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (torusGraph d n) m (revSite (n := n) i) (strictLower i n) w = 0
      ↔ ∀ p ∈ strictLower i n, (2 * (p i).val + 2 = n ∨ (p i).val = 0) → w p = 0 := by
  classical
  rw [crossForm_torus_any_eq i n m w, neg_eq_zero]
  constructor
  · intro h p hp hin
    have hmem : p ∈ (strictLower i n).filter
        (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0) := Finset.mem_filter.mpr ⟨hp, hin⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg (w q))).mp h p hmem
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    rw [h q hq1 hq2]
    ring

/-! ## 2. The null space, at every side -/

/-- **THE NULL SPACE OF THE TORUS, EXACTLY, AT EVERY SIDE LENGTH.** -/
theorem nullSpace_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ, (∀ p, p ∉ torusInner i n → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c := by
  classical
  have hc' : ∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0 := by
    intro p hp hmid
    refine hc p ?_
    rw [lowerHalf_eq_union]
    simp only [Finset.mem_union]
    tauto
  have hM := isMirrorHalf_strictLower i n
  have hcross : ∀ w : Site d n → ℝ,
      crossForm (torusGraph d n) m (revSite (n := n) i) (strictLower i n) w ≤ 0 := fun w =>
    crossForm_nonpos_of_cross_diag hM (TorusAnySide.torus_cross_diag_any i n) w
  rw [NullSpace.reflectedForm_eq_zero_iff_massive hM (isRefl_torus i) hm hcross hc']
  constructor
  · rintro ⟨v, hvsupp, hvc, hcr⟩
    refine ⟨v, ?_, hvc⟩
    intro p hp
    by_cases hph : p ∈ strictLower i n
    · have hlayer : 2 * (p i).val + 2 = n ∨ (p i).val = 0 := by
        rw [mem_torusInner_iff_sdiff] at hp
        tauto
      have := (crossForm_eq_zero_iff_torus_any i n m _).mp hcr p hph hlayer
      rwa [anti_eq_self_of_mem_any i n hvsupp hph] at this
    · exact hvsupp p hph
  · rintro ⟨v, hvsupp, hvc⟩
    have hlow : ∀ p, p ∉ strictLower i n → v p = 0 := fun p hp =>
      hvsupp p fun hcon => hp (torusInner_subset_strictLower i n hcon)
    refine ⟨v, hlow, hvc, ?_⟩
    refine (crossForm_eq_zero_iff_torus_any i n m _).mpr fun p hp hlayer => ?_
    rw [anti_eq_self_of_mem_any i n hlow hp]
    refine hvsupp p fun hcon => ?_
    rw [mem_torusInner_iff_sdiff] at hcon
    tauto

/-- **THE EVEN CASE, RECOVERED.** `NullSpaceTorus.nullSpace_torus_even` from the general
statement, which is the check that this file subsumes the earlier one rather than duplicating it. -/
theorem nullSpace_torus_even' (i : Fin d) (_hn : Even n) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ, (∀ p, p ∉ torusInner i n → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c :=
  nullSpace_torus_any i n hm hc

/-- **THE MASSIVE IMAGE OF `torusInner` IS THE NULL SPACE, AT EVERY SIDE.** -/
theorem mem_nullSub_iff_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) (c : Site d n → ℝ) :
    c ∈ nullSub (torusGraph d n) m (torusInner i n)
      ↔ (∀ p, p ∉ lowerHalf i n → c p = 0)
        ∧ reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 := by
  constructor
  · intro hc
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hc
    have hsupp := massive_mulVec_supported_torus i m hvsupp
    exact ⟨hsupp, (nullSpace_torus_any i n hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((nullSpace_torus_any i n hm hcsupp).mp hcnull)

/-! ## 3. The dimension and the threshold, at every side -/

/-- **THE DIMENSION.** Unchanged from the even case, because
`NullSpaceDimensionEven.finrank_nullSub` never mentioned a lattice, a parity or a half. -/
theorem finrank_nullSub_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n)) = (torusInner i n).card :=
  NullSpaceDimensionEven.finrank_nullSub hm _

/-- **AND THE FORM IS DEGENERATE ON THE HALF AT EVERY SIDE FROM TWO, AT EVERY PARITY.** The seam
alone witnesses it: `pᵢ = 0` is in the half and never in `torusInner`.

**The hypothesis is `2 ≤ n` and not `0 < n`**, which is a genuine difference from
`NullSpaceTorus.nullSub_lt_admissible_torus_even` and not a weaker proof. That statement is about
`lowerHalf`, which contains the seam as soon as `n ≥ 1`; this one is about `strictLower`, which
asks `2·pᵢ + 1 < n` and so is EMPTY at `n = 1`. At side one there is no half and nothing to be
degenerate, and the statement would be false rather than unproved. The compiler found this. -/
theorem nullSub_lt_admissible_torus_any (i : Fin d) (h2 : 2 ≤ n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n))
      < Module.finrank ℝ (supportedOn (strictLower i n)) := by
  classical
  rw [finrank_nullSub_torus_any i n hm, finrank_supportedOn]
  refine Finset.card_lt_card ⟨torusInner_subset_strictLower i n, fun hsub => ?_⟩
  have hseam : (fun _ => ⟨0, by omega⟩ : Site d n) ∈ strictLower i n := by
    rw [mem_strictLower]; simp; omega
  have := hsub hseam
  rw [mem_torusInner] at this
  simp at this

/-! ## 4. The estate's two parity-split degeneracy theorems, as one -/

/-- **A NONZERO NULL FAMILY AT EVERY SIDE FROM FIVE, AT EVERY PARITY.**
`TorusNotStrict.exists_null_direction_torus` is this at `Even n` with `6 ≤ n` and
`OddNotStrictInstances.exists_null_direction_torus_odd` at `Odd n` with `5 ≤ n`; each builds an
explicit family and each covers one parity. This covers both with `5 ≤ n` and **builds nothing**:
the null space is nontrivial because `finrank_nullSub_torus_any` makes its dimension
`(torusInner i n).card` and `torusInner_nonempty_iff` makes that positive from five. The massive
shape comes out as well, which in the two parity-split versions is a separate step. -/
theorem exists_null_direction_torus_any (i : Fin d) (n : ℕ) (h5 : 5 ≤ n) (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0)
      ∧ reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0
      ∧ ∃ v : Site d n → ℝ, (∀ p, p ∉ torusInner i n → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c := by
  obtain ⟨p, hp⟩ := NullSpaceTorus.torusInner_nonempty_of_five_le (n := n) i h5
  have hne : Nontrivial (nullSub (torusGraph d n) m (torusInner i n)) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_nullSub_torus_any i n hm]; exact Finset.card_pos.mpr ⟨p, hp⟩)
  obtain ⟨c, hc0⟩ := exists_ne (0 : nullSub (torusGraph d n) m (torusInner i n))
  obtain ⟨hcsupp, hcnull⟩ := (mem_nullSub_iff_torus_any i n hm _).mp c.2
  exact ⟨c.1, fun h => hc0 (Subtype.ext h), hcsupp, hcnull,
    (nullSpace_torus_any i n hm hcsupp).mp hcnull⟩

/-- **SO THE TORUS IS NOT STRICT FROM SIDE FIVE, AT EVERY PARITY**, which subsumes
`OddNotStrictInstances.not_strict_torus_odd` and the even-side statement together. -/
theorem not_strict_torus_any (i : Fin d) (n : ℕ) (h5 : 5 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < reflectedForm (torusGraph d n) m (revSite (n := n) i) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform, -⟩ := exists_null_direction_torus_any i n h5 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-- **NONDEGENERATE EXACTLY BELOW SIDE FIVE, AT EVERY PARITY.**
`NullSpaceTorus.null_trivial_iff_side_le_four` is this at even side. What is added is every odd
side — and `n = 5` in particular, which the even-side count could not reach and which
`SmallSideStrict`'s transported range (sides one to four) does not cover either. The estate does
know `n = 5`, from `OddNotStrictInstances.not_strict_torus_odd` and a hand-built family; this
reaches it from the dimension instead. -/
theorem null_trivial_iff_side_le_four_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : Site d n → ℝ, (∀ p, p ∉ lowerHalf i n → c p = 0) →
        reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 → c = 0) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra h4
    obtain ⟨c, hc0, hcsupp, hcnull, -⟩ :=
      exists_null_direction_torus_any (m := m) i n (by omega) hm
    exact hc0 (h c hcsupp hcnull)
  · intro h4 c hcsupp hcnull
    obtain ⟨v, hvsupp, rfl⟩ := (nullSpace_torus_any i n hm hcsupp).mp hcnull
    have hv0 : v = 0 := funext fun p => hvsupp p (by
      rw [NullSpaceTorus.torusInner_eq_empty_of_le_four i h4]; exact Finset.notMem_empty p)
    rw [hv0, Matrix.mulVec_zero]

/-- **THE ODD SIDE, WHICH IS WHAT THIS FILE WAS FOR.** At odd side the deficiency is the seam
alone — the innermost layer is empty — so the null space is the massive image of everything in
`strictLower` except the seam. Stated separately because the odd torus is the case the estate
recorded as having no description. -/
theorem nullSpace_torus_odd (i : Fin d) (hn : Odd n) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ,
          (∀ p, ¬ (1 ≤ (p i).val ∧ 2 * (p i).val + 1 < n) → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c := by
  rw [nullSpace_torus_any i n hm hc]
  obtain ⟨t, ht⟩ := hn
  constructor
  · rintro ⟨v, hvsupp, hvc⟩
    exact ⟨v, fun p hp => hvsupp p (by rw [mem_torusInner]; omega), hvc⟩
  · rintro ⟨v, hvsupp, hvc⟩
    exact ⟨v, fun p hp => hvsupp p (by rw [mem_torusInner] at hp; omega), hvc⟩

end NullSpaceTorusAny
