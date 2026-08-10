/-
  BoxOddComplement.lean — the upper side at odd length, and a refusal
  withdrawn.

  WHY, AND THE ERROR THAT MADE THIS A SEPARATE FILE. `OS2AnySide` removed the
  parity hypothesis from eight downstream statements and stopped at the
  complement versions, saying: *"a `mirror` + `mono` route probably works —
  but `ReflectionPositive.mirror` is stated through `IsHalf`, so it would
  need the same generalisation first."*

  **That sentence is false, and I wrote it without opening the lemma.**
  `LatticeReflectionPositive.ReflectionPositive.mirror` takes `IsRefl` and a
  reflection-positivity hypothesis. There is no `IsHalf` in its statement or
  its proof. Nothing needed generalising; the route was open the whole time
  and was refused on an unchecked belief about the estate's own machinery.
  ERRATUM 71 records it. This file is the withdrawal, and the correction is
  made by proving the thing, not by editing the sentence.

  **WHAT THE EVEN CASE USED AND THE ODD CASE DOES NOT NEED.** The even-side
  proof rewrites the complement as the image of the half — `IsHalf.image_eq`,
  which needs a fixed-point-free reflection. At odd length that equality is
  genuinely false: the image of `lowerHalf` is the sites weakly above the
  midline, the complement is the sites strictly above, and the fixed middle
  layer is in one and not the other. **But an equality was never needed — an
  inclusion suffices**, because reflection positivity is monotone in the
  region. `compl_subset_image` is that inclusion, it holds at every `n`, and
  it is four lines of arithmetic.

  WHAT THIS FILE PROVES, all with no parity hypothesis:
  1. **`compl_subset_image`** — the complement of `lowerHalf` sits inside its
     mirror image, at every side length. The even case has equality and does
     not care; the odd case has strict inclusion and this is what it needs.
  2. **`reflectionPositive_box_upper_any`** and
     **`reflectionPositive_box_compl_any`** — reflection positivity on the
     upper side of the cut, and on the complement, at every side length.
  3. **`reflectionPositive_box_either_any`** — either side, which is the form
     the OS2 statements consume.
  4. **`os2_box_either_any`**, **`os2_exponential_box_either_any`** — the
     measure-level and exponential statements on either side, any side
     length.
  5. **`reflectionPositive_lattice_compl_any`**, **`os2_lattice_any`**,
     **`os2_exponential_lattice_any`** — the estate's own field, both sides,
     any side length. `GraphOS2.os2_lattice` with `Even n` deleted and
     nothing else changed.
  6. **`os2_two_any`**, **`os2_exponential_two_any`** — the same across the
     second-coordinate cut.

  **SO THE PARITY HYPOTHESIS IS NOW GONE FROM THE WHOLE OS2 CHAIN**, both
  cuts, both sides, measure level and exponential algebra. What remains
  carrying `Even n` is listed in §4 and none of it is this chain.

  WHAT THIS DOES NOT DO.
  * **No strictness.** Unchanged. **AMENDED 2026-08-10: the sentence that
    stood here predicted "more directions should be null, not fewer", and
    measurement says that is only half right (ERRATUM 72).** At odd side
    THREE the reflected form is nondegenerate on the strict half alone, so
    every null direction must charge the mirror layer; from odd side FIVE
    upward it is already degenerate on the strict half. Two regimes, not one,
    and the prediction saw neither.
  * **Nothing for the torus**, still untraced.
  * **The originals are untouched.** Pushed records, still correct, still
    compiling.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import OS2AnySide

namespace BoxOddComplement

open Finset BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open IsingFiniteVolume LatticeReflectionPositive
open scoped ComplexOrder

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The inclusion that replaces the equality

`IsHalf.image_eq` says the image of a half is its complement, and needs the
reflection to be fixed-point-free. Monotonicity of reflection positivity
means only one direction of that is ever used, and that direction survives a
fixed layer.
-/

/-- **THE COMPLEMENT SITS INSIDE THE MIRROR IMAGE**, at every side length.
    Witness: a site above the midline is the mirror of its own mirror, and
    that mirror is below. -/
theorem compl_subset_image (i : Fin d) (n : ℕ) :
    (lowerHalf i n)ᶜ ⊆ (lowerHalf i n).image (GraphReflection.revSite (n := n) i) := by
  classical
  intro p hp
  rw [Finset.mem_compl, lowerHalf, Finset.mem_filter] at hp
  have hge : ¬ (2 * (p i).val < n) := fun h => hp ⟨Finset.mem_univ p, h⟩
  refine Finset.mem_image.mpr ⟨GraphReflection.revSite (n := n) i p, ?_, ?_⟩
  · rw [lowerHalf, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hrev : ((GraphReflection.revSite (n := n) i p) i).val = n - 1 - (p i).val := by
      rw [GraphReflection.revSite_apply_self, Fin.val_rev]; omega
    have hlt := (p i).isLt
    omega
  · exact GraphReflection.revSite_involutive i p

/-! ## 2. Reflection positivity on the other side, at every side length -/

/-- **THE UPPER SIDE.** `ReflectionPositive.mirror` applied to
    `BoxOddReflection.reflectionPositive_box_any` — and `mirror` needs only
    `IsRefl`, which is the fact the previous unit failed to check. -/
theorem reflectionPositive_box_upper_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i)
      ((lowerHalf i n).image (GraphReflection.revSite (n := n) i)) :=
  ReflectionPositive.mirror (GraphReflection.boxGraph_revSite_aut i)
    (BoxOddReflection.reflectionPositive_box_any i n hm)

/-- **THE COMPLEMENT.** -/
theorem reflectionPositive_box_compl_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n)ᶜ :=
  ReflectionPositive.mono (compl_subset_image i n)
    (reflectionPositive_box_upper_any i n hm)

/-- **EITHER SIDE, ANY SIDE LENGTH.** The form the OS2 statements consume. -/
theorem reflectionPositive_box_either_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) half := by
  rcases hs with h | h
  · exact ReflectionPositive.mono h (BoxOddReflection.reflectionPositive_box_any i n hm)
  · exact ReflectionPositive.mono h (reflectionPositive_box_compl_any i n hm)

/-! ## 3. The measure, both sides, any side length -/

/-- **MEASURE-LEVEL OS2 ON THE BOX, EITHER SIDE, ANY SIDE LENGTH.** -/
theorem os2_box_either_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(GraphLaplacian.gaussianField (boxGraph d n) m) :=
  GraphOS2.os2_measure_level _ hm (reflectionPositive_box_either_any i n hm hs) hc

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_box_either_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ)
    {M : ℕ} (t : Fin M → BoxGraph.Site d n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(GraphLaplacian.gaussianField (boxGraph d n) m) :=
  GraphOS2Exponential.os2_exponential m hm
    { invol := GraphReflection.revSite_involutive i
      adj := fun p q => by
        simpa using GraphReflection.adj_revSite (n := n) i p q }
    (reflectionPositive_box_either_any i n hm hs) t ht c

/-! ## 4. The estate's own field, both sides, any side length

The same three steps transported to `Fin n × Fin n`. `mirror` is applied on
the lattice side rather than transported, because the transport
(`reflectionPositive_congr`) has already delivered the lower half there and
`mirror` is graph-agnostic.
-/

/-- **THE UPPER SIDE OF THE FIRST-COORDINATE CUT, ANY SIDE LENGTH.** -/
theorem reflectionPositive_lattice_compl_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hsub : half ⊆ (lowerHalfPair n)ᶜ) :
    LatticeReflection.ReflectionPositive n m half := by
  classical
  refine (GraphReflection.reflectionPositive_box n m half).mp
    (ReflectionPositive.mono (hsub.trans ?_)
      (ReflectionPositive.mirror (GraphReflection.isRefl_latticeGraph n)
        (OS2AnySide.rp_lowerHalfPair_any n hm)))
  -- the complement sits inside the image, transported from §1 along `sitePair`
  rw [← map_lowerHalf n]
  intro p hp
  rw [Finset.mem_compl] at hp
  -- pull `p` back to the box, apply §1 there, push the witness forward
  have hpre : (sitePair n).symm p ∉ lowerHalf (0 : Fin 2) n := by
    intro hc
    exact hp (Finset.mem_map.mpr ⟨(sitePair n).symm p, hc, by simp⟩)
  obtain ⟨r, hr, hre⟩ :=
    Finset.mem_image.mp (compl_subset_image (0 : Fin 2) n (Finset.mem_compl.mpr hpre))
  refine Finset.mem_image.mpr ⟨sitePair n r, Finset.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
  rw [← sitePair_revSite r, hre, Equiv.apply_symm_apply]

/-- **THE ESTATE'S OWN FIELD, PAIRED, EITHER SIDE, ANY SIDE LENGTH.**
    `GraphOS2.os2_lattice` with `Even n` deleted and nothing else changed. -/
theorem os2_lattice_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hlow : half ⊆ lowerHalfPair n ∨ half ⊆ (lowerHalfPair n)ᶜ)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (LatticeReflection.refl n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine GraphOS2.os2_measure_level _ hm ?_ hc
  rw [GraphReflection.reflectionPositive_box n m half]
  rcases hlow with h | h
  · exact OS2AnySide.reflectionPositive_lattice_any n hm h
  · exact reflectionPositive_lattice_compl_any n hm h

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_lattice_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hlow : half ⊆ lowerHalfPair n ∨ half ⊆ (lowerHalfPair n)ᶜ)
    {M : ℕ} (t : Fin M → IsingFiniteVolume.Site n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (LatticeReflection.refl n p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine GraphOS2Exponential.os2_exponential m hm
    (GraphReflection.isRefl_latticeGraph n) ?_ t ht c
  rw [GraphReflection.reflectionPositive_box n m half]
  rcases hlow with h | h
  · exact OS2AnySide.reflectionPositive_lattice_any n hm h
  · exact reflectionPositive_lattice_compl_any n hm h

/-! ## 4b. The second-coordinate cut, both sides, any side length

Identical to §4 with `revSite 1` and `refl2` in place of `revSite 0` and
`refl n`. Written out rather than gestured at, because the header advertises
it and a header that advertises a theorem it does not have is this project's
most-repeated error.
-/

/-- **THE UPPER SIDE OF THE SECOND-COORDINATE CUT, ANY SIDE LENGTH.** -/
theorem reflectionPositive_two_compl_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hsub : half ⊆ (LatticeReflectionTwo.lowerHalfPair2 n)ᶜ) :
    GraphReflection.ReflectionPositive (IsingContourSeparation.latticeGraph n) m
      (LatticeReflectionTwo.refl2 n) half := by
  classical
  refine ReflectionPositive.mono (hsub.trans ?_)
    (ReflectionPositive.mirror (LatticeReflectionTwo.isRefl_refl2 n)
      (OS2AnySide.reflectionPositive_two_any n hm))
  rw [← LatticeReflectionTwo.map_lowerHalf_two n]
  intro p hp
  rw [Finset.mem_compl] at hp
  have hpre : (sitePair n).symm p ∉ lowerHalf (1 : Fin 2) n := by
    intro hc
    exact hp (Finset.mem_map.mpr ⟨(sitePair n).symm p, hc, by simp⟩)
  obtain ⟨r, hr, hre⟩ :=
    Finset.mem_image.mp (compl_subset_image (1 : Fin 2) n (Finset.mem_compl.mpr hpre))
  refine Finset.mem_image.mpr ⟨sitePair n r, Finset.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
  rw [← LatticeReflectionTwo.sitePair_revSite_two r, hre, Equiv.apply_symm_apply]

/-- **MEASURE-LEVEL OS2 ACROSS THE SECOND-COORDINATE CUT, EITHER SIDE, ANY
    SIDE LENGTH.** `LatticeReflectionTwo.os2_two` with `Even n` deleted. -/
theorem os2_two_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hs : half ⊆ LatticeReflectionTwo.lowerHalfPair2 n ∨
          half ⊆ (LatticeReflectionTwo.lowerHalfPair2 n)ᶜ)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (LatticeReflectionTwo.refl2 n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine GraphOS2.os2_measure_level _ hm ?_ hc
  rcases hs with h | h
  · exact OS2AnySide.reflectionPositive_two_mono_any n hm h
  · exact reflectionPositive_two_compl_any n hm h

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_two_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hs : half ⊆ LatticeReflectionTwo.lowerHalfPair2 n ∨
          half ⊆ (LatticeReflectionTwo.lowerHalfPair2 n)ᶜ)
    {M : ℕ} (t : Fin M → IsingFiniteVolume.Site n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (LatticeReflectionTwo.refl2 n p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine GraphOS2Exponential.os2_exponential m hm
    (LatticeReflectionTwo.isRefl_refl2 n) ?_ t ht c
  rcases hs with h | h
  · exact OS2AnySide.reflectionPositive_two_mono_any n hm h
  · exact reflectionPositive_two_compl_any n hm h

/-! ## 5. Review — the ways this could be hollow

**"Is this a real theorem or the withdrawal of a bad excuse?"** Both, and the
second is the reason it is a separate file. The mathematics is short — one
inclusion, one application of an existing lemma, one monotonicity step — and
it was available when the previous unit refused it. **What made the refusal
wrong was not caution, it was an unchecked claim about the estate's own
`mirror` lemma**, asserted in a header and a log entry without opening the
file. ERRATUM 71 has it. The rule ERRATUM 41 already stated — checking that a
name resolves is not checking what it requires — applies to this project's
own lemmas and not only to Mathlib's, and that is what was new.

**"Does the inclusion really hold at even length too, or is this odd-only?"**
Every side length, and the even case is where it is an equality
(`IsHalf.image_eq`). `compl_subset_image` proves only the inclusion because
that is all monotonicity consumes; proving the equality would need the parity
back, and would buy nothing.

**"Is `mirror` doing something that secretly needs a half?"** Its statement
takes `IsRefl G θ` and a reflection-positivity hypothesis, and its proof is a
reindexing of the double sum along `θ` plus `green_aut` and involutivity.
**The claim that it is `IsHalf`-free is checked by this file compiling**, not
by reading it: §2 applies it to a box of arbitrary side length, where no half
exists whenever the side is odd.

**"What still carries `Even n` after this?"** Not the OS2 chain, on either
cut or either side, at measure level or on the exponential algebra. Still
carrying it: `isHalf_lowerHalf` and `BoxCrossCoupling`, permanently and
correctly, because they are ABOUT fixed-point-free reflections; the torus,
untraced; and the three strictness files, which are expected to change shape
rather than generalise.
-/

end BoxOddComplement
