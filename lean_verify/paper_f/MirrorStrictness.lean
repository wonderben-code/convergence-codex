import NullSpaceLatticeTwo
import BoxOddComplement

/-!
# The reflected form does not notice the mirror, and so strictness crosses the cut

**THE ESTATE HAS NO STRICTNESS STATEMENT ON THE FAR SIDE OF ANY CUT.** Grepped before this file was
written (`ERRATA 265`/`270`): every theorem about `(lowerHalf i n)ᶜ`, `(lowerHalfPair n)ᶜ` and
`(lowerHalfPair2 n)ᶜ` is a **positivity** statement — `BoxOddComplement`'s six, `GraphOS2`'s and
`GraphOS2Exponential`'s `_either` forms — and `BoxOddComplement`'s own header says so in its
`WHAT THIS DOES NOT DO` section, first bullet: *"**No strictness.** Unchanged."*

That bullet has stood since 2026-08-10. It is discharged here, and not by redoing any of the work
it refers to.

## The lemma the estate had every piece of and never stated

`LatticeReflectionPositive.ReflectionPositive.mirror` carries positivity from `H` to `H.image θ`,
and the arithmetic inside it is not about positivity at all. Stripped of its hypothesis it says:

> **`reflectedForm G m θ (mir θ c) = reflectedForm G m θ c`** — the reflected form is invariant
> under precomposing the coefficient family with the reflection, for every `c`, on every finite
> graph, whenever `θ` is a reflection.

**It is four tokens from `GraphReflection`'s own bilinear form.** `reflectedForm_eq_bil` says
`reflectedForm G m θ c = bil G m (mir θ c) c`, `mir θ` is an involution, and `bil_comm` is
symmetry; that is the whole proof. A first draft reindexed the double sum by hand in fourteen
lines, and the adversarial pass replaced it — the estate had been able to state this since
`bil_comm` existed, which is the fact worth recording. Everything else in the file is a
consequence.

## What follows, and why the far side was never a separate problem

`mir θ` is an involution on coefficient families that fixes the form, sends families supported on
`H` to families supported on `H.image θ`, and sends nonzero to nonzero. So **any statement about
the form quantified over families supported on `H` transfers verbatim to `H.image θ`** — strictness,
non-strictness, nondegeneracy, and the null space's triviality alike. That is `strict_iff_mirror`,
`nondegenerate_iff_mirror` and the biconditionals below.

The far side of the cut is therefore not a second theorem. It is the same theorem read through an
involution, and the reason nothing had it is that the estate's transfer lemma was stated with
positivity baked in.

## The instances, and the honest gap at odd side

For the box, the torus and both cuts of the estate's lattice, `H.image θ` is the **upper** half.
At **even** side that is exactly the complement of the lower half, so the thresholds transfer as
biconditionals: strict on the upper half **iff** `n ≤ 2` (box, lattice) and **iff** `n ≤ 4`
(torus).

At **odd** side the complement is a proper subset of the image — the inclusion is
`BoxOddComplement.compl_subset_image` and the midline is the difference — so only one direction
transfers, by
`strict_of_subset`: strictness on the image gives strictness on the complement, and the converse
would need a null family supported strictly above the midline. **This file does not claim it**, and
the reason is stated rather than hidden: the mirror of a lower-half null family is supported on the
image, and nothing here shows it vanishes on the midline.

## What is NOT here

No new threshold. Every number below is the corresponding lower-half number read through the
involution — `CrossBlockStructure`'s `n ≤ 2` for the box since 12 August 2026 and `n ≤ 4` for the
torus, and `NullSpaceBoxAny` / `NullSpaceLattice` / `NullSpaceLatticeTwo` for the counts. What is
new is that the far side has any strictness statement at all.
-/

namespace MirrorStrictness

open Finset BoxGraph GraphHalfSpace GraphReflection

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {m : ℝ} {θ : V ≃ V}

/-! ## 1. The reflected form is invariant under the mirror -/

/-- **THE REFLECTED FORM DOES NOT NOTICE THE MIRROR.** For every coefficient family, on every
finite graph, whenever `θ` is a reflection.

This is the arithmetic inside `LatticeReflectionPositive.ReflectionPositive.mirror` with the
positivity removed. That proof needs it twice — once to move the outer index and once the inner —
and states neither. -/
theorem reflectedForm_mir (h : IsRefl G θ) (m : ℝ) (c : V → ℝ) :
    reflectedForm G m θ (mir θ c) = reflectedForm G m θ c := by
  rw [reflectedForm_eq_bil h, reflectedForm_eq_bil h,
    (funext fun p => congrArg c (h.invol p) : mir θ (mir θ c) = c),
    bil_comm (G := G) (m := m) c (mir θ c)]

/-! ## 2. `mir θ` moves supports across the cut and fixes nothing else

**No graph appears in this section and none is needed.** These four are about an involution of a
finite type and the reindexing it induces on functions; stating them over `G` would have carried a
hypothesis none of them uses, which the unused-variable linter says out loud.
-/

section Mir

variable {W : Type*} {ϑ : W ≃ W}

theorem mir_ne_zero {c : W → ℝ} (hc : c ≠ 0) : mir ϑ c ≠ 0 := by
  intro h
  refine hc (funext fun p => ?_)
  have := congrFun h (ϑ.symm p)
  simpa [mir] using this

theorem mir_mir (h : Function.Involutive ϑ) (c : W → ℝ) : mir ϑ (mir ϑ c) = c :=
  funext fun p => by simp [mir, h p]

variable [DecidableEq W]

theorem mir_supported {H : Finset W} {c : W → ℝ}
    (hc : ∀ p, p ∉ H.image ϑ → c p = 0) : ∀ p, p ∉ H → mir ϑ c p = 0 := by
  intro p hp
  refine hc _ fun hmem => hp ?_
  obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hmem
  rwa [ϑ.injective hke] at hk

theorem image_image (h : Function.Involutive ϑ) (H : Finset W) : (H.image ϑ).image ϑ = H := by
  ext p
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨q, ⟨k, hk, rfl⟩, rfl⟩
    rwa [h k]
  · intro hp
    exact ⟨ϑ p, ⟨p, hp, rfl⟩, h p⟩

end Mir

/-! ## 3. Every statement about the form transfers across the cut -/

/-- **STRICTNESS CROSSES THE CUT.** Not an implication with a side condition: an equivalence, on
every finite graph and every half. -/
theorem strict_iff_mirror (h : IsRefl G θ) (m : ℝ) (H : Finset V) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → c p = 0) → 0 < reflectedForm G m θ c)
      ↔ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H.image θ → c p = 0) → 0 < reflectedForm G m θ c) := by
  classical
  constructor
  · intro hs c hc0 hcsupp
    have := hs (mir θ c) (mir_ne_zero hc0) (mir_supported hcsupp)
    rwa [reflectedForm_mir h] at this
  · intro hs c hc0 hcsupp
    have hsupp : ∀ p, p ∉ (H.image θ).image θ → c p = 0 := by
      rw [image_image h.invol]; exact hcsupp
    have := hs (mir θ c) (mir_ne_zero hc0) (mir_supported hsupp)
    rwa [reflectedForm_mir h] at this

/-- **AND SO DOES NONDEGENERACY**, in the `= 0 → c = 0` form the null-space files use. -/
theorem nondegenerate_iff_mirror (h : IsRefl G θ) (m : ℝ) (H : Finset V) :
    (∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) → reflectedForm G m θ c = 0 → c = 0)
      ↔ (∀ c : V → ℝ, (∀ p, p ∉ H.image θ → c p = 0) → reflectedForm G m θ c = 0 → c = 0) := by
  classical
  have hzero : mir θ (0 : V → ℝ) = 0 := funext fun p => rfl
  constructor
  · intro hs c hcsupp hnull
    have h1 : mir θ c = 0 :=
      hs (mir θ c) (mir_supported hcsupp) (by rwa [reflectedForm_mir h])
    calc c = mir θ (mir θ c) := (mir_mir h.invol c).symm
      _ = 0 := by rw [h1, hzero]
  · intro hs c hcsupp hnull
    have hsupp : ∀ p, p ∉ (H.image θ).image θ → c p = 0 := by
      rw [image_image h.invol]; exact hcsupp
    have h1 : mir θ c = 0 :=
      hs (mir θ c) (mir_supported hsupp) (by rwa [reflectedForm_mir h])
    calc c = mir θ (mir θ c) := (mir_mir h.invol c).symm
      _ = 0 := by rw [h1, hzero]

/-- **STRICTNESS IS INHERITED BY SUBSETS**, because a family supported on a subset is supported on
the whole. Stated because the odd-side complement is a proper subset of the image. -/
theorem strict_of_subset {H H' : Finset V} (hsub : H' ⊆ H)
    (hs : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → c p = 0) → 0 < reflectedForm G m θ c) :
    ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H' → c p = 0) → 0 < reflectedForm G m θ c :=
  fun c hc0 hcsupp => hs c hc0 fun p hp => hcsupp p fun hmem => hp (hsub hmem)

/-! ## 4. The far side of every cut this estate has

Each of these is `strict_iff_mirror` applied to the estate's own reflection, composed with the
lower-half threshold that was already proved. **No number below is new**; what is new is that the
upper half has a statement.
-/

section Instances

/-- **THE BOX'S UPPER HALF, AT EVERY AXIS AND EVERY SIDE LENGTH.**
`CrossBlockStructure.box_strict_iff_le_two_lowerHalf` read through the mirror. -/
theorem strict_upper_box_iff {d n : ℕ} (i : Fin d) {m : ℝ} (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ (lowerHalf i n).image (revSite (n := n) i) → c p = 0) →
        0 < reflectedForm (boxGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 2 := by
  rw [← strict_iff_mirror (BoxNotStrict.isRefl_box i) m (lowerHalf i n)]
  exact CrossBlockStructure.box_strict_iff_le_two_lowerHalf i n hm

/-- **AND SO THE STRICT COMPLEMENT AT SIDES TWO AND BELOW**, which is the far side of the cut in
the estate's own vocabulary. At odd side the complement is a PROPER subset of the image
(`BoxOddComplement.compl_subset_image`), so only this direction is available and the file says so
rather than stating a biconditional it cannot prove. -/
theorem strict_compl_box_of_le_two {d n : ℕ} (i : Fin d) {m : ℝ} (hm : m ≠ 0) (hn : n ≤ 2) :
    ∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ (lowerHalf i n)ᶜ → c p = 0) →
      0 < reflectedForm (boxGraph d n) m (revSite (n := n) i) c :=
  strict_of_subset (BoxOddComplement.compl_subset_image i n)
    ((strict_upper_box_iff i hm).mpr hn)

/-- **THE TORUS'S UPPER HALF**, where the threshold is four rather than two — the wrap-around bond
is the whole difference, as `CrossBlockStructure.all_three_thresholds` records. -/
theorem strict_upper_torus_iff {d n : ℕ} (i : Fin d) {m : ℝ} (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ (lowerHalf i n).image (revSite (n := n) i) → c p = 0) →
        0 < reflectedForm (TorusReflection.torusGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 4 := by
  rw [← strict_iff_mirror (TorusReflection.isRefl_torus i) m (lowerHalf i n)]
  exact CrossBlockStructure.torus_strict_iff_le_four_lowerHalf i n hm

/-- **THE UPPER SIDE OF THE ESTATE'S OWN FIRST-COORDINATE CUT.** -/
theorem strict_upper_lattice_iff {n : ℕ} {m : ℝ} (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ (LatticeReflectionPositive.lowerHalfPair n).image (LatticeReflection.refl n) →
          c p = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c)
      ↔ n ≤ 2 := by
  rw [← strict_iff_mirror (GraphReflection.isRefl_latticeGraph n) m
    (LatticeReflectionPositive.lowerHalfPair n)]
  exact CrossBlockStructure.lattice_strict_iff_le_two n hm

/-- **AND OF THE SECOND-COORDINATE CUT**, on `NullSpaceLatticeTwo.lattice_two_strict_iff_le_two`,
which is itself from earlier today. -/
theorem strict_upper_lattice_two_iff {n : ℕ} {m : ℝ} (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ (LatticeReflectionTwo.lowerHalfPair2 n).image (LatticeReflectionTwo.refl2 n) →
          c p = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflectionTwo.refl2 n) c)
      ↔ n ≤ 2 := by
  rw [← strict_iff_mirror (LatticeReflectionTwo.isRefl_refl2 n) m
    (LatticeReflectionTwo.lowerHalfPair2 n)]
  exact NullSpaceLatticeTwo.lattice_two_strict_iff_le_two n hm

/-- **THE NONDEGENERACY FORM ON THE BOX'S UPPER HALF**, so the null-space chain reads across the
cut as well as the strictness chain does. -/
theorem nondegenerate_upper_box_iff {d n : ℕ} (i : Fin d) {m : ℝ} (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ,
        (∀ p, p ∉ (lowerHalf i n).image (revSite (n := n) i) → c p = 0) →
        reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0 → c = 0)
      ↔ n ≤ 2 := by
  rw [← nondegenerate_iff_mirror (BoxNotStrict.isRefl_box i) m (lowerHalf i n)]
  exact NullSpaceBoxAny.null_trivial_iff_side_le_two i n hm

end Instances

end MirrorStrictness
