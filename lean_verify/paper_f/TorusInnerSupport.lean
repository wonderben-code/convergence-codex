import TorusNotStrict
import InnerLowerSupport

/-!
# The torus's support lemma, and the set with two layers removed

`BoxNotStrict`'s header says of the periodic box:

> **It says nothing about the torus**, whose null direction for the coupling `CrossDegenerate`
> supplies but whose block difference has TWO layers in it; the same construction should work and
> is not written.

The box chain is now finished — description (`NullSpaceEven`), dimension
(`NullSpaceDimensionEven`), deficiency exactly one layer. **This is the torus's first rung**, the
analogue of `InnerLowerSupport`, and the two layers are exactly where it differs.

## Why two

On the box the lower half has one boundary, the innermost layer against the cut. On the torus it
has **two**: the innermost layer and the **seam**, layer `0`, which wraps round to layer `n − 1`
and so reaches outside the half in the other direction. `TorusNotStrict.sub_apply_torus` computes
the block difference to be supported on both, and `TorusReflection.adj_torus_revSite_iff` gives
the same disjunction for the cross-cut geometry.

So the set that works is `torusInner i n = {p : 1 ≤ pᵢ and 2·pᵢ + 2 < n}` — the half with **both**
boundary layers removed. Its being inhabited needs `n ≥ 6`, and
`TorusNotStrict.exists_null_direction_torus` carries exactly `6 ≤ n`: the same bound, arrived at
from the other side, which is the check that the set is the right one.

## What is proved

* `massive_mulVec_supported_torus` — a vector supported on `torusInner` has massive image
  vanishing off `lowerHalf`. The wrap is the whole difference from the box: four adjacency cases
  rather than two, and the seam case is the one that fails without `1 ≤ pᵢ`.
* `lowerHalf_sdiff_torusInner` — the deficiency is **exactly the two layers**, as a set identity,
  mirroring `NullSpaceDimensionEven.lowerHalf_sdiff_innerLower` where it is one.
* `torusInner_nonempty` — inhabited from `n = 6`, so the lemma is not vacuous.

## What is NOT proved

This is the support half only. The torus analogues of `NullSpaceEven.nullSpace_box_even` and of
the dimension count do not exist yet. The cross-form computation they need should follow the box's
`crossForm_box_eq` with the two-layer disjunction in place of the one-layer condition, since
`adj_torus_revSite_iff` is already in the shape `crossForm_box_eq` consumed — **but it is not
written, and after three occasions today of underestimating how close a named statement was, that
sentence is a description of what exists rather than a forecast.**
-/

namespace TorusInnerSupport

open Finset BoxGraph GraphHalfSpace TorusReflection

open scoped Matrix

variable {d n : ℕ}

/-- `BoxCrossCoupling`'s version is `private`, so it is restated. -/
private theorem mem_lowerHalf (i : Fin d) (p : Site d n) :
    p ∈ lowerHalf i n ↔ 2 * (p i).val < n := by
  simp [lowerHalf]

/-- The lower half with **both** boundary layers removed: the innermost layer against the cut,
and the seam at `pᵢ = 0` which wraps to the far side. -/
def torusInner (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => 1 ≤ (p i).val ∧ 2 * (p i).val + 2 < n

theorem mem_torusInner {i : Fin d} {p : Site d n} :
    p ∈ torusInner i n ↔ 1 ≤ (p i).val ∧ 2 * (p i).val + 2 < n := by
  simp [torusInner]

theorem torusInner_subset_lowerHalf (i : Fin d) (n : ℕ) :
    torusInner i n ⊆ lowerHalf i n := fun p hp =>
  (mem_lowerHalf i p).mpr (by rw [mem_torusInner] at hp; omega)

/-- **INHABITED FROM `n = 6`** — the same bound `TorusNotStrict.exists_null_direction_torus`
carries, reached from the other side. -/
theorem torusInner_nonempty (i : Fin d) (h6 : 6 ≤ n) : (torusInner i n).Nonempty :=
  ⟨fun _ => ⟨1, by omega⟩, mem_torusInner.mpr (by simp; omega)⟩

/-- **THE DEFICIENCY IS EXACTLY THE TWO LAYERS**, as a set identity. On the box the corresponding
statement names one layer (`NullSpaceDimensionEven.lowerHalf_sdiff_innerLower`); the extra one
here is the seam, and it is the whole geometric difference between the two lattices. -/
theorem lowerHalf_sdiff_torusInner (i : Fin d) (hn : Even n) :
    (lowerHalf i n) \ (torusInner i n)
      = (lowerHalf i n).filter
          (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, mem_torusInner, not_and_or, not_le, not_lt]
  obtain ⟨t, ht⟩ := hn
  constructor
  · rintro ⟨hlow, hnot⟩
    rw [mem_lowerHalf] at hlow
    refine ⟨(mem_lowerHalf i p).mpr hlow, ?_⟩
    rcases hnot with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · rintro ⟨hlow, hin⟩
    have hlow' := (mem_lowerHalf i p).mp hlow
    refine ⟨hlow, ?_⟩
    rcases hin with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- **THE SUPPORT LEMMA ON THE TORUS.** A vector supported on `torusInner` has massive image
vanishing off `lowerHalf`.

The wrap is the whole difference from the box. `adjT` has four cases rather than two, and the
fourth — `qᵢ = 0` with `pᵢ + 1 = n`, the seam reaching round — is exactly the one that fails
without `1 ≤ qᵢ`. That is why the set removes two layers and not one. -/
theorem massive_mulVec_supported_torus (i : Fin d) (m : ℝ)
    {v : Site d n → ℝ} (hv : ∀ p, p ∉ torusInner i n → v p = 0) :
    ∀ p, p ∉ lowerHalf i n → (GraphLaplacian.massive (torusGraph d n) m *ᵥ v) p = 0 := by
  classical
  intro p hp
  have hpn : ¬ (2 * (p i).val < n) := by
    simpa [lowerHalf, Finset.mem_filter] using hp
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ torusInner i n
  · rw [mem_torusInner] at hq
    have hplt := (p i).isLt
    have hqlt := (q i).isLt
    have hne : p ≠ q := fun hc => by rw [hc] at hpn; omega
    have hadj : ¬ (torusGraph d n).Adj p q := by
      rintro ⟨j, hsame, hstep⟩
      by_cases hj : j = i
      · subst hj
        obtain ⟨-, hcases⟩ := hstep
        rcases hcases with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      · exact hne (funext fun l => by
          by_cases hl : l = j
          · subst hl
            exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm)))
              (by omega)
          · exact hsame l hl)
    rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hadj]
    ring
  · rw [hv q hq, mul_zero]

end TorusInnerSupport
