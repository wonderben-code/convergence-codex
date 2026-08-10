/-
  OS2AnySide.lean — the parity hypothesis carried downstream, as far as it
  actually goes.

  WHY. `BoxOddReflection.reflectionPositive_box_any` proves reflection
  positivity on `boxGraph d n` at every side length. Every statement built on
  top of it still said `Even n`, for no reason except that it was written
  before the odd case existed. **A hypothesis that is removable and not
  removed is a false advertisement of difficulty**, so this file removes it —
  and stops, loudly, at the one place where it is not removable.

  **WHERE IT STOPS, AND WHY THAT IS THE INTERESTING PART.** The lattice
  statements come in two halves: regions inside `lowerHalfPair`, and regions
  inside its COMPLEMENT. The first needs only reflection positivity and
  generalises. The second is proved by reflecting the first, and that step
  goes through `IsHalf.image_eq` — the image of a half under the reflection
  is its complement. **That is exactly the statement that fails on an odd
  side**, and not incidentally: with a middle layer, the complement of
  `lowerHalf` is the sites strictly above the midline, which is the image of
  the sites strictly BELOW it, not of `lowerHalf` itself. The mirror layer
  belongs to neither. So the upper-half statement is not merely unproved here
  — its usual proof is unavailable, and a different one would have to say
  something about the sites strictly above rather than about a complement.

  WHAT THIS FILE PROVES, all with no parity hypothesis:
  1. **`os2_box_any`**, **`os2_box_four_any`** — measure-level OS2 on the
     `d`-dimensional box at every side length, four dimensions included.
  2. **`os2_exponential_box_any`**, **`os2_exponential_box_four_any`** — the
     same on the exponential algebra, which is the form OS2 is actually
     stated in.
  3. **`rp_lowerHalfPair_any`** and **`reflectionPositive_lattice_any`** —
     the estate's own `LatticeReflection.ReflectionPositive`, for regions in
     the lower half, at every side length.
  4. **`os2_lattice_lower_any`** and **`os2_exponential_lattice_lower_any`** —
     the estate's own field, paired, at every side length, on the lower side
     of the cut.
  5. **`reflectionPositive_two_any`**, **`reflectionPositive_two_mono_any`**,
     **`os2_two_lower_any`**, **`os2_exponential_two_lower_any`** — the same
     across the SECOND-coordinate cut, which matters because OS2 reflects in
     the time coordinate and which lattice direction carries time is a
     modelling choice this estate has not made.

  WHAT THIS DOES NOT DO.
  * **No upper-half or complement statement at odd side.** Explained above;
    this is a gap with a named cause, not an oversight.
  * **No `_compl` or `_either` form on either cut.** Same cause as above:
    both route through the fact about halves that fails at odd side.
  * **Nothing for the torus.** `TorusReflection` builds its own reflection
    and its own cross-coupling, and `torus_two_eq_box` may genuinely need the
    parity. Untraced, and deliberately not guessed at.
  * **Nothing for strictness.** `BoxNotStrict`, `TorusNotStrict` and
    `LatticeNotStrict` carry `Even n` AND `4 ≤ n` to build a null direction.
    On an odd side the cross-coupling vanishes identically, so those results
    should get EASIER and change shape rather than transfer. Separate unit.
  * **The original theorems are untouched.** They are pushed records and they
    are correct; this file adds, it does not edit. Callers that already pass
    `Even n` keep working.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxOddReflection
import GraphOS2Exponential
import LatticeReflectionTwo

namespace OS2AnySide

open Finset BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open IsingFiniteVolume LatticeReflectionPositive
open scoped ComplexOrder

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The box, at every side length -/

/-- **MEASURE-LEVEL OS2 ON THE BOX, ANY SIDE.** `GraphOS2.os2_box` with the
    parity hypothesis deleted. -/
theorem os2_box_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(GraphLaplacian.gaussianField (boxGraph d n) m) :=
  GraphOS2.os2_measure_level _ hm
    (BoxOddReflection.reflectionPositive_box_any i n hm) hc

/-- **AND IN FOUR DIMENSIONS, ANY SIDE.** -/
theorem os2_box_four_any (i : Fin 4) (n : ℕ) (hm : m ≠ 0)
    {c : BoxGraph.Site 4 n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(GraphLaplacian.gaussianField (boxGraph 4 n) m) :=
  os2_box_any i n hm hc

/-- **THE EXPONENTIAL ALGEBRA, ANY SIDE.** This is the form OS2 is stated in
    when it is stated properly, so it is the one that matters. -/
theorem os2_exponential_box_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {M : ℕ} (t : Fin M → BoxGraph.Site d n → ℝ)
    (ht : ∀ k p, p ∉ lowerHalf i n → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(GraphLaplacian.gaussianField (boxGraph d n) m) :=
  GraphOS2Exponential.os2_exponential m hm
    { invol := GraphReflection.revSite_involutive i
      adj := fun p q => by
        simpa using GraphReflection.adj_revSite (n := n) i p q }
    (BoxOddReflection.reflectionPositive_box_any i n hm) t ht c

/-- **AND IN FOUR DIMENSIONS, ANY SIDE.** -/
theorem os2_exponential_box_four_any (i : Fin 4) (n : ℕ) (hm : m ≠ 0)
    {M : ℕ} (t : Fin M → BoxGraph.Site 4 n → ℝ)
    (ht : ∀ k p, p ∉ lowerHalf i n → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(GraphLaplacian.gaussianField (boxGraph 4 n) m) :=
  os2_exponential_box_any i n hm t ht c

/-! ## 2. The estate's own definition, at every side length

`rp_lowerHalfPair` consumes reflection positivity on the two-dimensional box
and nothing else, so it generalises verbatim. `reflectionPositive_lattice`
adds only monotonicity in the region. The COMPLEMENT version does not follow
and §3 says why.
-/

/-- **THE LOWER HALF, ANY SIDE.** `LatticeReflectionPositive.rp_lowerHalfPair`
    with the parity hypothesis deleted — the proof is the original, with
    `reflectionPositive_box_any` in place of `reflectionPositive_box`. -/
theorem rp_lowerHalfPair_any (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (IsingContourSeparation.latticeGraph n) m
      (LatticeReflection.refl n) (lowerHalfPair n) := by
  rw [← map_lowerHalf n]
  exact (reflectionPositive_congr (sitePair n) adj_sitePair sitePair_revSite m _).mp
    (BoxOddReflection.reflectionPositive_box_any (0 : Fin 2) n hm)

/-- **`LatticeReflection.ReflectionPositive` AT EVERY SIDE LENGTH**, for
    regions inside the lower half. The `def` the estate wrote, with the last
    hypothesis its proof needed now gone on this side of the cut. -/
theorem reflectionPositive_lattice_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hsub : half ⊆ lowerHalfPair n) :
    LatticeReflection.ReflectionPositive n m half :=
  (GraphReflection.reflectionPositive_box n m half).mp
    (ReflectionPositive.mono hsub (rp_lowerHalfPair_any n hm))

/-- **THE ESTATE'S OWN FIELD, PAIRED, AT EVERY SIDE LENGTH** — lower side of
    the cut. -/
theorem os2_lattice_lower_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hlow : half ⊆ lowerHalfPair n)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (LatticeReflection.refl n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine GraphOS2.os2_measure_level _ hm ?_ hc
  rw [GraphReflection.reflectionPositive_box n m half]
  exact reflectionPositive_lattice_any n hm hlow

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_lattice_lower_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hlow : half ⊆ lowerHalfPair n)
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
  exact reflectionPositive_lattice_any n hm hlow

/-! ## 2b. The second-coordinate cut, at every side length

`LatticeReflectionTwo.reflectionPositive_two` consumes reflection positivity
on the box at `i = 1` and nothing else, so it generalises the same way §2's
first-coordinate version does. The `_compl` and `_either` forms do not, for
the reason §3 gives — they route through the same fact about halves.
-/

/-- **THE SECOND-COORDINATE CUT, ANY SIDE.** -/
theorem reflectionPositive_two_any (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (IsingContourSeparation.latticeGraph n) m
      (LatticeReflectionTwo.refl2 n) (LatticeReflectionTwo.lowerHalfPair2 n) := by
  rw [← LatticeReflectionTwo.map_lowerHalf_two n]
  exact (reflectionPositive_congr (sitePair n) adj_sitePair
    LatticeReflectionTwo.sitePair_revSite_two m _).mp
    (BoxOddReflection.reflectionPositive_box_any (1 : Fin 2) n hm)

theorem reflectionPositive_two_mono_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hsub : half ⊆ LatticeReflectionTwo.lowerHalfPair2 n) :
    GraphReflection.ReflectionPositive (IsingContourSeparation.latticeGraph n) m
      (LatticeReflectionTwo.refl2 n) half :=
  ReflectionPositive.mono hsub (reflectionPositive_two_any n hm)

/-- **MEASURE-LEVEL OS2 ACROSS THE SECOND-COORDINATE CUT, ANY SIDE** — lower
    side only, for the reason §3 gives. -/
theorem os2_two_lower_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hs : half ⊆ LatticeReflectionTwo.lowerHalfPair2 n)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (LatticeReflectionTwo.refl2 n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  exact GraphOS2.os2_measure_level _ hm (reflectionPositive_two_mono_any n hm hs) hc

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_two_lower_any (n : ℕ) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hs : half ⊆ LatticeReflectionTwo.lowerHalfPair2 n)
    {M : ℕ} (t : Fin M → IsingFiniteVolume.Site n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (LatticeReflectionTwo.refl2 n p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  exact GraphOS2Exponential.os2_exponential m hm (LatticeReflectionTwo.isRefl_refl2 n)
    (reflectionPositive_two_mono_any n hm hs) t ht c

/-! ## 3. Review — the ways this could be hollow

**"Is this just copying eight theorems with one word deleted?"** Mostly yes,
and that is the honest description of §1 and §2. The reason it is a unit
rather than a chore is §3's boundary: **six of the downstream statements
generalise and one does not**, and finding out which is which required
tracing each hypothesis to what it feeds instead of deleting the word
wherever it appeared. The one that does not is the one this section exists to
name.

**"Why exactly does the complement version fail?"** Because its proof uses
`IsHalf.image_eq`: the image of a half under the reflection is its
complement. On an odd side that is false — the complement of `lowerHalf` is
the sites strictly ABOVE the midline, and the image of `lowerHalf` is the
sites strictly above TOGETHER WITH the midline itself, since the middle layer
is fixed. **The mirror layer is in the image and not in the complement.** A
correct odd-side upper statement would be about the strictly-upper region,
which is a different set, so it is a different theorem and not a missing
instance of this one.

**"Could the complement version be recovered by monotonicity?"** Yes, and it
now is — `BoxOddComplement` (c22723c), on both cuts and at every side length.

**AMENDED 2026-08-10, SAME DAY: the paragraph that stood here was FALSE and
is corrected rather than deleted (ERRATUM 71).** It said the route "would
need the same generalisation this file's §2 performed, because
`ReflectionPositive.mirror` is stated through `IsHalf` in
`LatticeReflectionPositive`". **It is not.** `mirror` takes `IsRefl G θ` and
a reflection-positivity hypothesis; there is no `IsHalf` in its statement or
in its proof. The claim was written without opening the lemma, and it
converted an available five-line argument into a recorded refusal. What the
even case actually uses is `IsHalf.image_eq` — the complement EQUALS the
image — which does need fixed-point-freeness and is false at odd length; but
monotonicity only ever consumes the INCLUSION, and that survives a fixed
layer. The original sentence is kept above in the commit history and the
superseding file names it.

**"Does anything here weaken a statement to make it provable?"** No. Every
theorem in §1 and §2 has the conclusion of the theorem it generalises,
character for character, with `hn : Even n` replaced by an explicit `(n : ℕ)`.
The originals are untouched and still compile, which is the check that
nothing was quietly reshaped.

**"What is the state of the parity hypothesis across the estate now?"**
Removed on: the box (positivity, measure-level, exponential, four
dimensions), and the estate's own lattice definition on the lower side.
Still present and NOT yet traced on: the torus, the second-coordinate cut,
the prism instances. Still present and expected to STAY, because the
statement genuinely needs a fixed-point-free reflection: `isHalf_lowerHalf`,
`BoxCrossCoupling`, and the lattice complement statements. Still present and
expected to CHANGE SHAPE rather than generalise: all three strictness files.
-/

end OS2AnySide
