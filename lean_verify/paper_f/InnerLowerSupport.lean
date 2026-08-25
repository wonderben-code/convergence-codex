import BoxOddNotStrict

/-!
# The support lemma without the parity, and the set that unifies the two boxes

`BoxOddNotStrict.massive_mulVec_supported` says that on an **odd** box the massive image of a
vector supported strictly below the midline stays inside the lower half, and its docstring names
the parity as the thing being spent:

> On an ODD side, a step from strictly below the midline lands no higher than the midline. **This
> is where the parity is spent**, and it is the reason the null direction charges the mirror
> rather than escaping past it.

**The parity is spent on the SET, not on the argument.** What the proof needs is a gap of two
layers between the support and the complement of `lowerHalf`, and `strictLower` supplies that gap
only when `n` is odd — because at **even** `n`,

  `strictLower i n = {p : 2·pᵢ + 1 < n} = {p : 2·pᵢ < n} = lowerHalf i n`,

the two sets coincide and there is no gap at all. So the hypothesis is load-bearing exactly as
written, and removing it needs a different set rather than a better proof. That is worth saying
because the obvious first attempt — keep `strictLower`, drop `Odd n` — proves something false.

## The set

`innerLower i n = {p : 2·pᵢ + 2 < n}`. It is `strictLower` when `n` is odd
(`innerLower_eq_strictLower_of_odd`) and it is `lowerHalf` minus its innermost layer when `n` is
even — the layer `2·pᵢ + 2 = n` that `BoxNotStrict.sub_apply` computes the block difference to be
supported on, and that `sub_mulVec_eq_zero` already asks vectors to avoid.

## What is proved

* `massive_mulVec_supported` — **at every `n`, no parity**: a vector supported on `innerLower`
  has massive image vanishing off `lowerHalf`.
* `massive_mulVec_supported_odd` — and it recovers `BoxOddNotStrict`'s statement verbatim, so
  this is a strict generalisation and not a variant.
* `innerLower_nonempty` — and the set is inhabited from `n = 3` up, so the even case is content
  and not a vacuous quantifier.

## Why it was wanted

`RE-SWEEP #27` batch 4 sharpened a watch-list clause into an asymmetry: the odd box has a
dimension count for its null space (`NullSpaceDimension.finrank_nullSub_box_odd`) because it has
the support lemma above; the even box has no analogue and therefore no count. **This is that
analogue.** It is the first rung and not the count: what still has no even-side statement is the
biconditional `NullSpace.nullSpace_box_odd` — that the reflected form vanishing on a supported
family is *equivalent* to being a massive image — and nothing here attempts it.
-/

namespace InnerLowerSupport

open Finset BoxGraph GraphHalfSpace BoxOddReflection
open scoped Matrix

variable {d n : ℕ}

/-- Sites at least two layers below the top of the lower half. Equal to `strictLower` at odd `n`,
and to `lowerHalf` minus its innermost layer at even `n`. -/
def innerLower (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => 2 * (p i).val + 2 < n

theorem mem_innerLower {i : Fin d} {p : Site d n} :
    p ∈ innerLower i n ↔ 2 * (p i).val + 2 < n := by
  simp [innerLower]

/-- **AT ODD `n` IT IS `strictLower`**, so nothing is lost where the old statement applied. -/
theorem innerLower_eq_strictLower_of_odd (i : Fin d) (hn : Odd n) :
    innerLower i n = strictLower i n := by
  obtain ⟨k, hk⟩ := hn
  ext p
  rw [mem_innerLower, mem_strictLower]
  omega

/-- And in general it is contained in `strictLower`: the two differ only at even `n`, by the
innermost layer. -/
theorem innerLower_subset_strictLower (i : Fin d) (n : ℕ) :
    innerLower i n ⊆ strictLower i n := by
  intro p hp
  rw [mem_innerLower] at hp
  exact mem_strictLower.mpr (by omega)

/-- **AND IT IS NOT EMPTY** from `n = 3` up, so the lemma below is not vacuous at even `n` —
`ERRATUM 48`'s rule, that a hypothesis nothing satisfies makes an empty class. The corner works,
and `3 ≤ n` is weaker than the `4 ≤ n` that `BoxNotStrict` carries. -/
theorem innerLower_nonempty (i : Fin d) (h3 : 3 ≤ n) : (innerLower i n).Nonempty :=
  ⟨fun _ => ⟨0, by omega⟩, mem_innerLower.mpr (by simp; omega)⟩

/-- **THE SUPPORT LEMMA, AT EVERY `n`.** A vector supported on `innerLower` has massive image
vanishing off `lowerHalf`.

The mechanism, stated so it is not mistaken for parity: `p ∉ lowerHalf` gives `2·pᵢ ≥ n` and
`q ∈ innerLower` gives `2·qᵢ + 2 < n`, so `pᵢ − qᵢ ≥ 2`. Two layers apart is neither equal nor
adjacent, and every term of the row vanishes. -/
theorem massive_mulVec_supported (i : Fin d) (m : ℝ)
    {v : Site d n → ℝ} (hv : ∀ p, p ∉ innerLower i n → v p = 0) :
    ∀ p, p ∉ lowerHalf i n → (GraphLaplacian.massive (boxGraph d n) m *ᵥ v) p = 0 := by
  classical
  intro p hp
  have hpn : ¬ (2 * (p i).val < n) := by
    simpa [lowerHalf, Finset.mem_filter] using hp
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ innerLower i n
  · rw [mem_innerLower] at hq
    have hqlt := (q i).isLt
    have hne : p ≠ q := fun hc => by rw [hc] at hpn; omega
    have hadj : ¬ (boxGraph d n).Adj p q := by
      rintro ⟨j, hsame, hstep⟩
      by_cases hj : j = i
      · subst hj; omega
      · exact hne (funext fun l => by
          by_cases hl : l = j
          · subst hl
            exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm)))
              (by omega)
          · exact hsame l hl)
    rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hadj]
    ring
  · rw [hv q hq, mul_zero]

/-- **AND IT RECOVERS THE ODD STATEMENT VERBATIM**, which is what makes this a generalisation
rather than a second theorem of the same shape. -/
theorem massive_mulVec_supported_odd (i : Fin d) (hn : Odd n) (m : ℝ)
    {v : Site d n → ℝ} (hv : ∀ p, p ∉ strictLower i n → v p = 0) :
    ∀ p, p ∉ lowerHalf i n → (GraphLaplacian.massive (boxGraph d n) m *ᵥ v) p = 0 :=
  massive_mulVec_supported i m
    (fun p hp => hv p (by rwa [← innerLower_eq_strictLower_of_odd i hn]))

end InnerLowerSupport
