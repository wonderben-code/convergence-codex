import NullSpaceEven
import NullSpaceDimension

/-!
# The null space of the even box has a dimension, and the deficiency is the innermost layer

`NullSpaceDimension` computes the dimension of the degenerate directions on the **odd** box and
measures the deficiency against the admissible families: it is exactly the midline layer.
`RE-SWEEP #27` batch 4 found the even box had no such count and named the one missing piece;
`InnerLowerSupport` and `NullSpaceEven` supplied it. **This finishes the chain.**

## What is proved

* `finrank_nullSub` — **the general fact, which was never stated.** On every finite graph, at
  every nonzero mass, for every `H`, the massive image of the functions supported on `H` has
  dimension `H.card`. `NullSpaceDimension.finrank_nullSub_box_odd` is this at
  `boxGraph`/`strictLower`, and its three-line proof uses neither the box nor the parity nor the
  particular half — only injectivity of the massive operator and the dimension of a supported
  family. Stating the general form costs nothing and is the honest shape, and
  `finrank_nullSub_box_odd'` recovers the odd count from it in one line, so the claim that it was
  always general is checkable rather than asserted.
* `mem_nullSub_iff_box_even` — at even side the massive image of `innerLower` **is** the null
  space: `NullSpaceEven.nullSpace_box_even` gives one containment and
  `InnerLowerSupport.massive_mulVec_supported` the other. Without the second the image could
  contain families the reflected form is not even defined on as admissible, which is the same
  gap `NullSpaceDimension` §3 records for the odd box.
* `finrank_nullSub_box_even` — hence the dimension is `(innerLower i n).card`.
* `lowerHalf_sdiff_innerLower` — and the deficiency is **exactly the innermost layer**, as a set
  identity rather than as a remark.
* `nullSub_lt_admissible_box_even` — so the form is degenerate at even side with a measured
  codimension, the even twin of `nullSub_lt_admissible_box_odd`.

## The symmetry worth naming

At **odd** side the deficiency is the **midline** layer — the sites the reflection fixes. At
**even** side the reflection fixes nothing, and the deficiency is the **innermost** layer — the
sites adjacent to their own mirrors. Both are one layer, both are nonempty from side two upwards,
and neither file could see the other's until the two were stated in the same vocabulary.

## What this does not do

It does not weaken `GraphReflectionPositive.reflectionPositive_box`: the form is still `≥ 0` and
that is still sharp. It says by how much `≥` fails to be `>`.
-/

namespace NullSpaceDimensionEven

open Finset BoxGraph GraphHalfSpace GraphReflection NullSpaceDimension InnerLowerSupport

open scoped Matrix

/-! ## 1. The count, in the generality its proof always had -/

/-- **THE DIMENSION OF THE MASSIVE IMAGE IS THE SIZE OF THE SUPPORT** — every finite graph, every
nonzero mass, every `H`. -/
theorem finrank_nullSub {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {m : ℝ} (hm : m ≠ 0) (H : Finset V) :
    Module.finrank ℝ (nullSub G m H) = H.card := by
  have hinj := massive_mulVecLin_injective (G := G) (m := m) hm
  have hequiv := Submodule.equivMapOfInjective _ hinj (supportedOn H)
  rw [nullSub, ← hequiv.finrank_eq, finrank_supportedOn]

variable {d n : ℕ} {m : ℝ}

/-- **AND IT RECOVERS THE ODD COUNT VERBATIM**, which is what makes §1 a generalisation rather
than a second theorem: `NullSpaceDimension.finrank_nullSub_box_odd` is `finrank_nullSub` at
`boxGraph`/`strictLower` and nothing else. -/
theorem finrank_nullSub_box_odd' (i : Fin d) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (BoxOddReflection.strictLower i n))
      = (BoxOddReflection.strictLower i n).card :=
  finrank_nullSub hm _

/-- `BoxCrossCoupling`'s version is `private`, so it is restated. -/
private theorem mem_lowerHalf (i : Fin d) (p : Site d n) :
    p ∈ lowerHalf i n ↔ 2 * (p i).val < n := by
  simp [lowerHalf]

theorem innerLower_subset_lowerHalf (i : Fin d) (n : ℕ) :
    innerLower i n ⊆ lowerHalf i n := fun p hp =>
  (mem_lowerHalf i p).mpr (by rw [mem_innerLower] at hp; omega)

/-! ## 2. At even side the image is the null space -/

/-- **THE MASSIVE IMAGE OF `innerLower` IS THE NULL SPACE AT EVEN SIDE.** Both containments:
everything in the image is admissible and null, and everything admissible and null is in the
image. -/
theorem mem_nullSub_iff_box_even (i : Fin d) (hn : Even n) (hm : m ≠ 0) (c : Site d n → ℝ) :
    c ∈ nullSub (boxGraph d n) m (innerLower i n)
      ↔ (∀ p, p ∉ lowerHalf i n → c p = 0)
        ∧ reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 := by
  constructor
  · intro hc
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hc
    have hsupp := InnerLowerSupport.massive_mulVec_supported i m hvsupp
    exact ⟨hsupp, (NullSpaceEven.nullSpace_box_even i hn hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((NullSpaceEven.nullSpace_box_even i hn hm hcsupp).mp hcnull)

/-! ## 3. The dimension, and the deficiency -/

/-- **THE DIMENSION.** At even side the null space of the reflected form has dimension exactly the
number of sites two or more layers below the cut. -/
theorem finrank_nullSub_box_even (i : Fin d) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (innerLower i n)) = (innerLower i n).card :=
  finrank_nullSub hm _

/-- **THE DEFICIENCY IS EXACTLY THE INNERMOST LAYER**, as a set identity. At odd side the
corresponding statement is about the midline layer — the sites the reflection fixes. Here the
reflection fixes nothing, and the layer is instead the one whose sites are adjacent to their own
mirrors. -/
theorem lowerHalf_sdiff_innerLower (i : Fin d) (hn : Even n) :
    (lowerHalf i n) \ (innerLower i n)
      = (lowerHalf i n).filter (fun p => 2 * (p i).val + 2 = n) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, mem_innerLower]
  obtain ⟨t, ht⟩ := hn
  constructor
  · rintro ⟨hlow, hnot⟩
    rw [mem_lowerHalf] at hlow
    exact ⟨(mem_lowerHalf i p).mpr hlow, by omega⟩
  · rintro ⟨hlow, hin⟩
    exact ⟨hlow, by omega⟩

/-- **AND SO THE FORM IS DEGENERATE WITH A MEASURED CODIMENSION** at even side, the twin of
`NullSpaceDimension.nullSub_lt_admissible_box_odd`. -/
theorem nullSub_lt_admissible_box_even (i : Fin d) (hn : Even n) (h2 : 2 ≤ n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (innerLower i n))
      < Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  classical
  rw [finrank_nullSub_box_even i hm, finrank_supportedOn]
  refine Finset.card_lt_card ?_
  constructor
  · exact innerLower_subset_lowerHalf i n
  · intro hsub
    obtain ⟨p₀, hp₀low, hp₀in⟩ := BoxCrossCoupling.exists_innermost i hn h2
    have := hsub hp₀low
    rw [mem_innerLower] at this
    omega

end NullSpaceDimensionEven
