import TorusInnerSupport
import NullSpaceDimensionEven
import TorusAnySide
import TorusNotStrict

/-!
# The null space of the even torus, exactly, and its dimension

`NullSpaceEven` and `NullSpaceDimensionEven` did this for the box this afternoon;
`TorusInnerSupport` supplied the torus's support lemma and the set with **two** boundary layers
removed. This is the rest: description, dimension, and the deficiency.

> `nullSpace_torus_even` — on a periodic box of even side, a family supported on `lowerHalf i n`
> is null **exactly when** it is the massive image of something supported on `torusInner i n`.
>
> `finrank_nullSub_torus_even` — and that space has dimension `(torusInner i n).card`.

## What the wrap costs, stated exactly

Nothing new in the argument, and one thing in the geometry. Both lattices reach
`NullSpace.reflectedForm_eq_zero_iff_massive`, whose third clause asks a coupling form to vanish.
On the box that form is minus an indicator of **one** layer; on the torus,
`TorusReflection.adj_torus_revSite_iff` makes it minus an indicator of **two** — the innermost
and the seam. So `crossForm_torus_eq` collapses to a sum of squares over both, and the clause
reads *"`v` vanishes on both layers"*, which for a half-supported vector is *"supported on
`torusInner`"*.

**Everything else is reused rather than re-proved.** `NullSpaceEven.anti_eq_self_of_mem` is about
`anti` and `IsHalf` and mentions no graph, so it applies to the torus verbatim.
`NullSpaceDimensionEven.finrank_nullSub` was already stated for every finite graph and every
half, so the dimension is an instance and not a port — which is the same discovery that made the
box's dimension free, arriving a second time.

## The threshold, read off the dimension rather than transported

`SmallSideStrict`'s summary settles the torus by transport — *"strict at one, two, three and
four; not strict at five and up"* — and its own honest bullet says of the large sides that
**"only a subspace of [the null space] is exhibited"**. §4 removes that caveat at even side and
reaches the same threshold from the other direction: the null space has dimension
`(torusInner i n).card`, that set is empty exactly below side five, and so
`null_trivial_iff_side_le_four` says the even torus is nondegenerate on the half **exactly** at
sides `≤ 4`. Two independent routes to one number is the only real check available here, and
they agree.

`exists_null_massive_torus` is the torus twin of `NullSpaceEven.exists_null_massive`: it runs
`TorusNotStrict`'s witness forwards through the biconditional and so shows that witness has the
massive shape, which `TorusNotStrict` asserted of the box's construction and never computed here.

## What is NOT proved

The deficiency is bounded below rather than computed: `nullSub_lt_admissible_torus_even` says the
null space is strictly smaller than the admissible families, and
`TorusInnerSupport.lowerHalf_sdiff_torusInner` says by exactly which sites, but the two are not
combined into a codimension count the way the odd box's `nullSub_lt_admissible_box_odd` is —
because that would need the cardinality of a two-layer set, and counting it is arithmetic nobody
has needed yet.

**"Two layers" is prose, not a count.** At `n = 2` the seam `pᵢ = 0` and the innermost layer
`2·pᵢ + 2 = n` are the same layer, and the disjunction in `crossForm_torus_eq` is one condition
wearing two. The theorems say `∨` and are correct there; only the word *two* is loose.

Reflection positivity for the torus — `TorusReflection.reflectionPositive_torus` at even side,
`TorusAnySide.reflectionPositive_torus_any` at every side — is untouched: the form is still
`≥ 0`. This says by how much `≥` fails to be `>`. (`GraphReflectionPositive` is the general
graph file and never mentions the torus; an earlier draft of this header named it, ERRATUM 263.)
-/

namespace NullSpaceTorus

open Finset BoxGraph GraphHalfSpace GraphMirrorReflection GraphReflection
open TorusReflection TorusInnerSupport NullSpaceDimension

open scoped Matrix

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The cut is diagonal, on the half -/

/-- `TorusAnySide.torus_cross_diag_any` is stated for `strictLower`; at even side that is
`lowerHalf`, but reading it off `adj_torus_revSite_iff` directly is shorter and needs no
rewriting of the set. -/
theorem torus_cross_diag_lowerHalf (i : Fin d) (hn : Even n) :
    ∀ p ∈ lowerHalf i n, ∀ q ∈ lowerHalf i n,
      (torusGraph d n).Adj p (revSite (n := n) i q) → p = q :=
  fun _ hp _ hq hadj => ((adj_torus_revSite_iff i hn hp hq).mp hadj).1

/-! ## 2. The coupling on the torus is minus a sum of squares over TWO layers -/

/-- **THE CROSS FORM ON THE TORUS.** The box's `crossForm_box_eq` with the two-layer disjunction
in place of the one-layer condition. -/
theorem crossForm_torus_eq (i : Fin d) (hn : Even n) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (torusGraph d n) m (revSite (n := n) i) (lowerHalf i n) w
      = - ∑ p ∈ (lowerHalf i n).filter
            (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0), (w p) ^ 2 := by
  classical
  rw [crossForm_eq_neg_adj (isMirrorHalf_of_isHalf (isHalf_lowerHalf i hn)) m w]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · by_cases hin : 2 * (p i).val + 2 = n ∨ (p i).val = 0
    · rw [if_pos hin, if_pos ((adj_torus_revSite_iff i hn hp hp).mpr ⟨rfl, hin⟩)]
      ring
    · rw [if_neg hin, if_neg fun hc =>
        hin ((adj_torus_revSite_iff i hn hp hp).mp hc).2]
      ring
  · intro q hq hqp
    rw [if_neg fun hc => hqp ((adj_torus_revSite_iff i hn hp hq).mp hc).1.symm]
    ring
  · intro hpn
    exact absurd hp hpn

/-- **AND SO IT VANISHES EXACTLY ON THOSE TWO LAYERS.** -/
theorem crossForm_eq_zero_iff_torus (i : Fin d) (hn : Even n) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (torusGraph d n) m (revSite (n := n) i) (lowerHalf i n) w = 0
      ↔ ∀ p ∈ lowerHalf i n, (2 * (p i).val + 2 = n ∨ (p i).val = 0) → w p = 0 := by
  classical
  rw [crossForm_torus_eq i hn m w, neg_eq_zero]
  constructor
  · intro h p hp hin
    have hmem : p ∈ (lowerHalf i n).filter
        (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0) := Finset.mem_filter.mpr ⟨hp, hin⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg (w q))).mp h p hmem
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    rw [h q hq1 hq2]
    ring

/-! ## 3. The null space, and its dimension -/

/-- **THE NULL SPACE OF THE EVEN TORUS, EXACTLY.** -/
theorem nullSpace_torus_even (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ, (∀ p, p ∉ torusInner i n → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c := by
  classical
  have hM := isMirrorHalf_of_isHalf (isHalf_lowerHalf (n := n) i hn)
  have hcross : ∀ w : Site d n → ℝ,
      crossForm (torusGraph d n) m (revSite (n := n) i) (lowerHalf i n) w ≤ 0 := fun w =>
    crossForm_nonpos_of_cross_diag hM (torus_cross_diag_lowerHalf i hn) w
  rw [NullSpace.reflectedForm_eq_zero_iff_massive hM (isRefl_torus i) hm hcross
    (fun p hp _ => hc p hp)]
  constructor
  · rintro ⟨v, hvsupp, hvc, hcr⟩
    refine ⟨v, ?_, hvc⟩
    intro p hp
    by_cases hph : p ∈ lowerHalf i n
    · have hlayer : 2 * (p i).val + 2 = n ∨ (p i).val = 0 := by
        rw [mem_torusInner] at hp
        have hlow : 2 * (p i).val < n := by
          simpa [lowerHalf, Finset.mem_filter] using hph
        obtain ⟨t, ht⟩ := hn
        omega
      have := (crossForm_eq_zero_iff_torus i hn m _).mp hcr p hph hlayer
      rwa [NullSpaceEven.anti_eq_self_of_mem i hn hvsupp hph] at this
    · exact hvsupp p hph
  · rintro ⟨v, hvsupp, hvc⟩
    have hlow : ∀ p, p ∉ lowerHalf i n → v p = 0 := fun p hp =>
      hvsupp p fun hcon => hp (torusInner_subset_lowerHalf i n hcon)
    refine ⟨v, hlow, hvc, ?_⟩
    refine (crossForm_eq_zero_iff_torus i hn m _).mpr fun p hp hlayer => ?_
    rw [NullSpaceEven.anti_eq_self_of_mem i hn hlow hp]
    refine hvsupp p fun hcon => ?_
    rw [mem_torusInner] at hcon
    omega

/-- **THE MASSIVE IMAGE OF `torusInner` IS THE NULL SPACE.** -/
theorem mem_nullSub_iff_torus_even (i : Fin d) (hn : Even n) (hm : m ≠ 0) (c : Site d n → ℝ) :
    c ∈ nullSub (torusGraph d n) m (torusInner i n)
      ↔ (∀ p, p ∉ lowerHalf i n → c p = 0)
        ∧ reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 := by
  constructor
  · intro hc
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hc
    have hsupp := massive_mulVec_supported_torus i m hvsupp
    exact ⟨hsupp, (nullSpace_torus_even i hn hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((nullSpace_torus_even i hn hm hcsupp).mp hcnull)

/-- **THE DIMENSION**, an instance of `NullSpaceDimensionEven.finrank_nullSub` rather than a port:
that theorem was already stated for every finite graph, every nonzero mass and every half.

`Even n` does not appear and is not needed — the count is of a set, and the parity is only what
makes that set the null space (`mem_nullSub_iff_torus_even`). The name keeps `_even` for the file's
symmetry, not because the hypothesis is used. -/
theorem finrank_nullSub_torus_even (i : Fin d) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n)) = (torusInner i n).card :=
  NullSpaceDimensionEven.finrank_nullSub hm _

/-- **AND THE FORM IS DEGENERATE**, the torus twin of
`NullSpaceDimensionEven.nullSub_lt_admissible_box_even`. The seam alone witnesses it: `pᵢ = 0` is
in the half and never in `torusInner`. -/
theorem nullSub_lt_admissible_torus_even (i : Fin d) (hpos : 0 < n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n))
      < Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  classical
  rw [finrank_nullSub_torus_even i hm, finrank_supportedOn]
  refine Finset.card_lt_card ?_
  constructor
  · exact torusInner_subset_lowerHalf i n
  · intro hsub
    have hseam : (fun _ => ⟨0, hpos⟩ : Site d n) ∈ lowerHalf i n := by
      simp [lowerHalf]
      omega
    have := hsub hseam
    rw [mem_torusInner] at this
    simp at this

/-! ## 4. The threshold: nondegenerate exactly below side five -/

/-- **BELOW SIDE FIVE THERE IS NO INTERIOR AT ALL.** A site of `torusInner` needs `1 ≤ pᵢ` and
`2·pᵢ + 2 < n`, and those two force `n ≥ 5`. No parity. -/
theorem torusInner_eq_empty_of_le_four (i : Fin d) (h4 : n ≤ 4) : torusInner i n = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [mem_torusInner] at hp
  omega

/-- **AND FROM SIDE FIVE IT IS INHABITED**, which sharpens `TorusInnerSupport.torusInner_nonempty`
by one: that lemma asks `6 ≤ n` because `TorusNotStrict` asks it, but the witness `pᵢ = 1` only
needs `4 < n`. The two agree at every even side, so nothing downstream changes; the gain is that
the odd side is now covered too. -/
theorem torusInner_nonempty_of_five_le (i : Fin d) (h5 : 5 ≤ n) : (torusInner i n).Nonempty :=
  ⟨fun _ => ⟨1, by omega⟩, mem_torusInner.mpr (by simp; omega)⟩

/-- **SO THE INTERIOR IS INHABITED EXACTLY FROM FIVE.** -/
theorem torusInner_nonempty_iff (i : Fin d) : (torusInner i n).Nonempty ↔ 5 ≤ n := by
  constructor
  · intro h
    by_contra h4
    rw [torusInner_eq_empty_of_le_four i (by omega)] at h
    exact absurd h (by simp)
  · exact torusInner_nonempty_of_five_le i

/-- **THE NULL SPACE IS TRIVIAL EXACTLY BELOW SIDE FIVE**, as a dimension. Stated for every `n`
because it is a statement about `nullSub`; it becomes a statement about the null space only when
`n` is even, via `mem_nullSub_iff_torus_even`. -/
theorem finrank_nullSub_torus_eq_zero_iff (i : Fin d) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (torusGraph d n) m (torusInner i n)) = 0 ↔ n ≤ 4 := by
  rw [finrank_nullSub_torus_even i hm, Finset.card_eq_zero]
  constructor
  · intro h
    by_contra h4
    obtain ⟨p, hp⟩ := torusInner_nonempty_of_five_le (n := n) i (by omega)
    rw [h] at hp
    exact absurd hp (by simp)
  · exact fun h4 => torusInner_eq_empty_of_le_four i h4

/-! ## 5. What that means for the form -/

/-- **AT EVEN SIDES BELOW FIVE THE FORM IS NONDEGENERATE ON THE HALF**, recovered from the
description rather than transported from the box the way `SmallSideStrict` recovers it. There is
no interior for the massive image to come from, so the only null family is zero. -/
theorem null_of_le_four (i : Fin d) (hn : Even n) (h4 : n ≤ 4) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 ↔ c = 0 := by
  rw [nullSpace_torus_even i hn hm hc]
  constructor
  · rintro ⟨v, hvsupp, rfl⟩
    have hv0 : v = 0 := funext fun p => hvsupp p (by
      rw [torusInner_eq_empty_of_le_four i h4]; exact Finset.notMem_empty p)
    rw [hv0, Matrix.mulVec_zero]
  · rintro rfl
    exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩

/-- **AND FROM SIX THERE IS A NONZERO NULL FAMILY OF MASSIVE SHAPE**, the torus twin of
`NullSpaceEven.exists_null_massive`. `TorusNotStrict.exists_null_direction_torus` produces the
family; running it forwards through `nullSpace_torus_even` is what shows it is the massive image
of something supported on `torusInner`, which that file asserted of the box's construction and
did not compute here. This also shows the biconditional is not vacuous on either side. -/
theorem exists_null_massive_torus (i : Fin d) (hn : Even n) (h6 : 6 ≤ n) (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0)
      ∧ ∃ v : Site d n → ℝ, (∀ p, p ∉ torusInner i n → v p = 0)
          ∧ GraphLaplacian.massive (torusGraph d n) m *ᵥ v = c := by
  obtain ⟨c, hc0, hcsupp, hcnull⟩ := TorusNotStrict.exists_null_direction_torus i hn h6 hm
  exact ⟨c, hc0, hcsupp, (nullSpace_torus_even i hn hm hcsupp).mp hcnull⟩

/-- **THE THRESHOLD, SHARP.** At even side the reflected form is nondegenerate on the lower half
**exactly** when `n ≤ 4`. `SmallSideStrict` reaches the same number by transporting strictness from
the box and the estate's own `def`; this reaches it from the dimension of the null space. The two
routes share no argument, and they agree. -/
theorem null_trivial_iff_side_le_four (i : Fin d) (hn : Even n) (hm : m ≠ 0) :
    (∀ c : Site d n → ℝ, (∀ p, p ∉ lowerHalf i n → c p = 0) →
        reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 → c = 0) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra h4
    obtain ⟨t, ht⟩ := hn
    obtain ⟨c, hc0, hcsupp, v, hvsupp, hvc⟩ :=
      exists_null_massive_torus i ⟨t, ht⟩ (by omega) hm
    exact hc0 (h c hcsupp ((nullSpace_torus_even i ⟨t, ht⟩ hm hcsupp).mpr ⟨v, hvsupp, hvc⟩))
  · exact fun h4 c hcsupp hcnull => (null_of_le_four i hn h4 hm hcsupp).mp hcnull

end NullSpaceTorus
