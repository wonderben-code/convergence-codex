/-
  LatticeReflectionTwo.lean — the other coordinate.

  WHY. Three files landed today whose every theorem carries the same
  restriction: the box is cut in its FIRST coordinate. `WALLS.md` W1 records
  that as a non-closure and `LatticeReflectionPositive`'s header says plainly
  that the estate has no second-direction statement at all, "neither proved
  nor written down", with the question of whether the transport reaches one
  left open and seeded on the watchlist.

  **It reaches it, and the point of the file is that nothing new was
  needed.** `LatticeReflectionPositive.reflectionPositive_congr` is stated for
  an arbitrary bijection of vertex sets intertwining two reflections;
  `GraphReflectionPositive.reflectionPositive_box` is stated for an arbitrary
  coordinate `i : Fin d`. **The first-coordinate restriction was never in the
  mathematics — it was in the two small lemmas that connected them**, and this
  file writes the other two.

  That is also the honest test of yesterday's generalisation. A transport
  lemma used once may have been shaped around its single application. Used a
  second time, with a different reflection and a different half, it either
  works unchanged or it does not. **It works unchanged: §1 is imported, not
  adapted.**

  WHAT THIS FILE PROVES:
  1. **`refl2`** — reflection of the estate's box in its SECOND coordinate,
     with `isRefl_refl2` obtained by transport from `BoxGraph`'s `revSite 1`
     rather than by redoing the `Fin` arithmetic.
  2. **`sitePair_revSite_two`, `map_lowerHalf_two`** — the two lemmas that
     were missing: the pair encoding intertwines `revSite 1` with `refl2`, and
     carries `GraphHalfSpace.lowerHalf 1 n` onto the second-coordinate half.
  3. **`reflectionPositive_two`, `reflectionPositive_two_compl`** —
     **reflection positivity of the massive lattice Green function across the
     SECOND-coordinate cut**, on either side, for even `n` and nonzero `m`.
  4. **`os2_two`, `os2_exponential_two`** — and hence measure-level OS2 and
     exponential-algebra OS2 in that direction, immediately, because
     `GraphOS2` and `GraphOS2Exponential` are stated for an arbitrary
     reflection and consume reflection positivity as a hypothesis.
  5. **`isHalf_lowerHalfPair_two`, `card_lowerHalfPair_two`** — the half is a
     genuine half, `2·|H| = n²`, so none of this is the degenerate corner.

  WHAT THIS DOES NOT DO.
  * **It does not touch `LatticeReflection.ReflectionPositive`.** That `def`
    hardcodes `refl n`, the first-coordinate reflection. A second-direction
    statement in the estate's own vocabulary would need either a second `def`
    or a widening of the existing one, and **that is a schema decision about
    the author's record**, recorded under DECISIONS NEEDED and not taken here.
    Everything below is stated in the general graph vocabulary, where the
    reflection is already a parameter.
  * **Even side only, still.** For odd `n` the middle column is fixed and
    `GraphHalfSpace.not_isHalf_of_odd` says no half exists — the same fact as
    for the first coordinate, for the same reason.
  * **Two coordinates is not Euclidean invariance.** The box has cuts in
    other directions (diagonals, in particular) about which nothing is
    claimed, and OS1 proper is a statement about a symmetry GROUP that is not
    formalised for this field at all.
  * **No infinite-volume limit, no continuum limit, and the field is free.**
    Unchanged from the three files this one extends.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphOS2Exponential

namespace LatticeReflectionTwo

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open IsingFiniteVolume IsingContourSeparation LatticeReflectionPositive
open scoped ComplexOrder RealInnerProductSpace

variable {n : ℕ} {m : ℝ}

/-! ## 1. The second-coordinate reflection -/

/-- **Reflection of the box in its SECOND coordinate.** `LatticeReflection.refl`
    is the first-coordinate twin; the only difference is which component
    `Fin.rev` acts on. -/
def refl2 (n : ℕ) : Site n ≃ Site n where
  toFun p := (p.1, p.2.rev)
  invFun p := (p.1, p.2.rev)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem refl2_apply (p : Site n) : refl2 n p = (p.1, p.2.rev) := rfl

theorem refl2_involutive (n : ℕ) : Function.Involutive (refl2 n) := by
  intro p; simp

/-- **The pair encoding intertwines `revSite 1` with `refl2`.** This and
    `map_lowerHalf_two` are the entire content of the extension; everything
    after them is `LatticeReflectionPositive.reflectionPositive_congr` applied
    unchanged. -/
theorem sitePair_revSite_two (p : BoxGraph.Site 2 n) :
    sitePair n (GraphReflection.revSite (n := n) (1 : Fin 2) p)
      = refl2 n (sitePair n p) := by
  have h0 : GraphReflection.revSite (n := n) (1 : Fin 2) p 0 = p 0 :=
    GraphReflection.revSite_apply_ne (by decide) p
  have h1 : GraphReflection.revSite (n := n) (1 : Fin 2) p 1 = Fin.rev (p 1) :=
    GraphReflection.revSite_apply_self 1 p
  simp [sitePair, h0, h1]

/-- **`refl2` IS A GRAPH AUTOMORPHISM**, obtained by transport rather than by
    redoing `LatticeReflection.adj_refl`'s `Fin` arithmetic in the other
    slot. -/
theorem isRefl_refl2 (n : ℕ) : IsRefl (latticeGraph n) (refl2 n) where
  invol := refl2_involutive n
  adj := by
    intro p q
    obtain ⟨p', rfl⟩ := (sitePair n).surjective p
    obtain ⟨q', rfl⟩ := (sitePair n).surjective q
    rw [← sitePair_revSite_two, ← sitePair_revSite_two,
      adj_sitePair, adj_sitePair, boxGraph_adj, boxGraph_adj]
    exact GraphReflection.adj_revSite (n := n) 1 p' q'

/-! ## 2. The second-coordinate half -/

/-- The half below the second-coordinate midline. -/
def lowerHalfPair2 (n : ℕ) : Finset (Site n) :=
  Finset.univ.filter fun p => 2 * p.2.val < n

theorem mem_lowerHalfPair2 (p : Site n) :
    p ∈ lowerHalfPair2 n ↔ 2 * p.2.val < n := by simp [lowerHalfPair2]

theorem map_lowerHalf_two (n : ℕ) :
    (GraphHalfSpace.lowerHalf (1 : Fin 2) n).map (sitePair n).toEmbedding
      = lowerHalfPair2 n := by
  classical
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, GraphHalfSpace.lowerHalf,
    lowerHalfPair2, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [sitePair] using hp
  · intro hq
    exact ⟨(sitePair n).symm q, by simpa [sitePair] using hq, by simp⟩

theorem isHalf_lowerHalfPair2 (hn : Even n) :
    GraphHalfSpace.IsHalf (refl2 n) (lowerHalfPair2 n) := by
  intro p
  simp only [mem_lowerHalfPair2, refl2_apply]
  have hrev := Fin.val_rev p.2
  have hlt := p.2.isLt
  obtain ⟨k, hk⟩ := hn
  omega

/-- **AND IT IS EXACTLY HALF**, so nothing below is the degenerate corner. -/
theorem card_lowerHalfPair2 (hn : Even n) :
    2 * (lowerHalfPair2 n).card = n * n := by
  classical
  have himg := (isHalf_lowerHalfPair2 hn).image_eq (refl2_involutive n)
  have hc : ((lowerHalfPair2 n).image (refl2 n)).card = (lowerHalfPair2 n).card :=
    Finset.card_image_of_injective _ (refl2 n).injective
  rw [himg, Finset.card_compl] at hc
  have hle : (lowerHalfPair2 n).card ≤ Fintype.card (Site n) := Finset.card_le_univ _
  have htot : Fintype.card (Site n) = n * n := by simp
  rw [← htot]
  omega

/-! ## 3. Reflection positivity across the other cut -/

/-- **REFLECTION POSITIVITY IN THE SECOND COORDINATE.** The transport lemma is
    used exactly as it was for the first, with `revSite 1` in place of
    `revSite 0`. -/
theorem reflectionPositive_two (hn : Even n) (hm : m ≠ 0) :
    ReflectionPositive (latticeGraph n) m (refl2 n) (lowerHalfPair2 n) := by
  rw [← map_lowerHalf_two n]
  exact (reflectionPositive_congr (sitePair n) adj_sitePair sitePair_revSite_two m _).mp
    (GraphReflectionPositive.reflectionPositive_box (1 : Fin 2) hn hm)

theorem reflectionPositive_two_mono (hn : Even n) (hm : m ≠ 0)
    {half : Finset (Site n)} (hsub : half ⊆ lowerHalfPair2 n) :
    ReflectionPositive (latticeGraph n) m (refl2 n) half :=
  ReflectionPositive.mono hsub (reflectionPositive_two hn hm)

theorem reflectionPositive_two_compl (hn : Even n) (hm : m ≠ 0)
    {half : Finset (Site n)} (hsub : half ⊆ (lowerHalfPair2 n)ᶜ) :
    ReflectionPositive (latticeGraph n) m (refl2 n) half := by
  refine ReflectionPositive.mono ?_ (ReflectionPositive.mirror (isRefl_refl2 n)
    (reflectionPositive_two hn hm))
  rw [(isHalf_lowerHalfPair2 hn).image_eq (refl2_involutive n)]
  exact hsub

theorem reflectionPositive_two_either (hn : Even n) (hm : m ≠ 0)
    {half : Finset (Site n)}
    (hs : half ⊆ lowerHalfPair2 n ∨ half ⊆ (lowerHalfPair2 n)ᶜ) :
    ReflectionPositive (latticeGraph n) m (refl2 n) half := by
  rcases hs with h | h
  · exact reflectionPositive_two_mono hn hm h
  · exact reflectionPositive_two_compl hn hm h

/-! ## 4. And therefore both measure-level statements

Neither of the two theorems below is proved here in any real sense: `GraphOS2`
and `GraphOS2Exponential` quantify over the reflection and take reflection
positivity as a hypothesis, so §3 is the only input. **That is the payoff of
having stated them generally**, and it is worth one sentence rather than a
section: a direction-specific OS2 layer would have needed both files written
twice.
-/

/-- Measure-level OS2 across the second-coordinate cut. -/
theorem os2_two (hn : Even n) (hm : m ≠ 0) {half : Finset (Site n)}
    (hs : half ⊆ lowerHalfPair2 n ∨ half ⊆ (lowerHalfPair2 n)ᶜ)
    {c : Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (refl2 n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  exact GraphOS2.os2_measure_level _ hm (reflectionPositive_two_either hn hm hs) hc

/-- **Exponential-algebra OS2 across the second-coordinate cut.** -/
theorem os2_exponential_two (hn : Even n) (hm : m ≠ 0) {half : Finset (Site n)}
    (hs : half ⊆ lowerHalfPair2 n ∨ half ⊆ (lowerHalfPair2 n)ᶜ)
    {M : ℕ} (t : Fin M → Site n → ℝ) (ht : ∀ k p, p ∉ half → t k p = 0)
    (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp ((∑ p, t k p * ω (refl2 n p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  exact GraphOS2Exponential.os2_exponential m hm (isRefl_refl2 n)
    (reflectionPositive_two_either hn hm hs) t ht c

/-! ## 5. Review round 87 — the ways this could be hollow

**"Is this just the first coordinate with a `1` where the `0` was?"** In the
Lean, very nearly, and that is the result rather than a confession. The claim
being tested is that yesterday's transport lemma was general and not shaped
around its one application; the way to test that is to apply it to a second
case and see whether anything has to change. **Nothing did.** §1 of
`LatticeReflectionPositive` is imported and used as-is, and the two new lemmas
are the two the file itself identified as the connective tissue. Had the
transport needed adjusting, that would have been the finding; it did not, and
that is this one.

**"Then why is `isRefl_refl2` proved by transport rather than directly?"**
Because doing it directly would duplicate `LatticeReflection.adj_refl`'s
`Fin` arithmetic in the other slot, and duplicated arithmetic is where sign
errors live. Transporting it costs three rewrites and consumes
`BoxGraph.adj_revSite`, which was already proved for every coordinate.
**`BoxGraph`'s generality in `i : Fin d` is being cashed here for the second
time today**, and it was written speculatively.

**"Does this close the fifth non-closure?"** It closes it for the general
graph statement and **not** for the estate's own `def`, and the header says
which. `LatticeReflection.ReflectionPositive` hardcodes `refl n`; giving it a
second direction means a second `def` or a widened one, and that is the
author's call, already on record under DECISIONS NEEDED. **Two directions of
two is also not all directions** — a diagonal cut is not covered and is not
claimed, and OS1 proper is about a symmetry group this field does not have
formalised.

**"§4 looks like it is claiming two theorems for free."** It is claiming
exactly that, and the sentence in §4 says so. The content is in `GraphOS2` and
`GraphOS2Exponential` having been stated over an arbitrary reflection with
reflection positivity as a hypothesis; §3 supplies the hypothesis. **The
observation worth keeping is the counterfactual**: had those two files been
written for `LatticeReflection.refl` specifically — which was the obvious way
to write them, since that was the only reflection the estate had — this unit
would have had to duplicate both.
-/

end LatticeReflectionTwo
