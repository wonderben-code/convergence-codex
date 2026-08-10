/-
  BoxOddReflection.lean — the odd-side box, and `Even n` gone.

  WHY. `GraphMirrorReflection` removed the machinery obstacle to reflections
  that fix a layer, and said in its own review section that it supplied no
  instance: `IsMirrorHalf` had exactly one witness in the estate, the empty
  mirror, which is the old case. **A generalisation with no new witness is a
  definition wearing a theorem's clothes**, and this file is the witness.

  **WHAT THE MIRROR LAYER DOES TO THE BOX, and it is the whole file.** Cut a
  box of ODD side down the middle. The middle layer is fixed by the
  reflection, and it sits BETWEEN the two open halves — so a site strictly
  below the middle and a site strictly above it are never nearest
  neighbours. **The cross-coupling is not merely negative semidefinite: it is
  identically zero.** On an even side there is no middle layer, the two
  innermost layers touch, and the cross-coupling is the nonzero diagonal
  thing `BoxCrossCoupling` computes. The odd case is easier, and it was
  unreachable only because no half existed to state it with.

  WHAT THIS FILE PROVES:
  1. **`strictLower` and `midLayer`**, and **`lowerHalf_eq_union`** — the
     estate's existing `lowerHalf` is their union, for EVERY `n`. No new
     region is introduced; the old one is resolved into two pieces.
  2. **`isMirrorHalf_strictLower`** — the splitting holds **with no parity
     hypothesis at all**. On an even side `midLayer` is empty and this is
     `isHalf_lowerHalf` again; on an odd side it is new. One statement,
     both parities, and the parity is not mentioned.
  3. **`not_adj_cross_odd`** — on an odd side, no site strictly below the
     middle is adjacent to the mirror image of any site strictly below the
     middle. The geometric heart, and two lines of arithmetic once stated.
  4. **`crossForm_odd_eq_zero`** — hence the cross-coupling form vanishes
     identically. Not an inequality: an equality with zero.
  5. **`reflectionPositive_box_odd`** — reflection positivity on the box of
     ODD side, for the half cut by any one coordinate, over the estate's own
     `lowerHalf`. **The conclusion is
     `GraphReflectionPositive.reflectionPositive_box`'s, verbatim; the only
     difference anywhere is `Even n → Odd n`.** Not asserted — item 6
     typechecks while calling both, which it could not do if the conclusions
     differed.
  6. **`reflectionPositive_box_any`** — the two parities combined. **The
     hypothesis is gone.** Every finite box, every side, every coordinate.

  WHAT THIS DOES NOT DO.
  * **It does not touch the downstream `Even n`s.** `GraphOS2`'s measure-level
    and exponential statements, `LatticeReflectionPositive`, `LatticeReflectionTwo`
    and the torus all still carry the hypothesis in their own signatures.
    Removing it there is mechanical and is a separate unit; doing it here
    would mean editing eight files behind one theorem.
  * **No strictness, and the odd case is expected to be worse.** With the
    cross-coupling identically zero the symmetric and antisymmetric operators
    coincide, so the reflected form is degenerate wherever `BoxNotStrict`'s
    is and probably further. Nothing here proves that; the numerical evidence
    that odd boxes are degenerate in `d = 1, 2, 3` is what prompted the
    remark and is not a proof.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphMirrorReflection

namespace BoxOddReflection

open Finset BoxGraph GraphReflection GraphHalfSpace GraphMirrorReflection

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The half and the mirror

`lowerHalf` is `2·vᵢ < n`. Splitting that into `2·vᵢ + 1 < n` and
`2·vᵢ + 1 = n` costs nothing and separates the sites strictly below the
midline from the sites ON it. For even `n` the second set is empty.
-/

/-- Sites strictly below the midline in coordinate `i`. -/
def strictLower (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => 2 * (p i).val + 1 < n

/-- Sites exactly on the midline in coordinate `i`. Empty when `n` is even. -/
def midLayer (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => 2 * (p i).val + 1 = n

theorem mem_strictLower {i : Fin d} {p : Site d n} :
    p ∈ strictLower i n ↔ 2 * (p i).val + 1 < n := by
  simp [strictLower]

theorem mem_midLayer {i : Fin d} {p : Site d n} :
    p ∈ midLayer i n ↔ 2 * (p i).val + 1 = n := by
  simp [midLayer]

/-- **THE ESTATE'S OWN HALF IS THE UNION**, for every `n`. So the theorem
    proved below is about `lowerHalf` and not about a region invented to
    make the proof work. -/
theorem lowerHalf_eq_union (i : Fin d) (n : ℕ) :
    lowerHalf i n = strictLower i n ∪ midLayer i n := by
  ext p
  simp only [lowerHalf, strictLower, midLayer, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

/-- On an even side the mirror layer is empty, which is why the old
    machinery could get away with never mentioning one. -/
theorem midLayer_eq_empty_of_even (i : Fin d) (hn : Even n) :
    midLayer i n = (∅ : Finset (Site d n)) := by
  ext p
  simp only [midLayer, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  obtain ⟨k, hk⟩ := hn
  omega

/-! ## 2. The splitting, with no parity hypothesis -/

private theorem revSite_eq_self_iff (i : Fin d) (p : Site d n) :
    GraphReflection.revSite (n := n) i p = p ↔ 2 * (p i).val + 1 = n := by
  have hlt := (p i).isLt
  constructor
  · intro h
    have := congrFun h i
    rw [GraphReflection.revSite_apply_self] at this
    have hv : (Fin.rev (p i)).val = (p i).val := congrArg Fin.val this
    rw [Fin.val_rev] at hv
    omega
  · intro h
    funext j
    by_cases hj : j = i
    · subst hj
      rw [GraphReflection.revSite_apply_self]
      refine Fin.ext ?_
      rw [Fin.val_rev]
      omega
    · exact GraphReflection.revSite_apply_ne hj p

/-- **THE THREE-WAY SPLITTING OF THE BOX.** Stated for every `n`: on an even
    side the mirror is empty and this is `isHalf_lowerHalf` wearing a
    different name, on an odd side it is the new content. -/
theorem isMirrorHalf_strictLower (i : Fin d) (n : ℕ) :
    IsMirrorHalf (GraphReflection.revSite (n := n) i) (strictLower i n) (midLayer i n) where
  fixed p := by rw [mem_midLayer, revSite_eq_self_iff]
  disj p hp := by
    rw [mem_strictLower] at hp
    rw [mem_midLayer]
    omega
  split p hp := by
    rw [mem_midLayer] at hp
    have hlt := (p i).isLt
    have hrev : ((GraphReflection.revSite (n := n) i p) i).val = n - 1 - (p i).val := by
      rw [GraphReflection.revSite_apply_self, Fin.val_rev]; omega
    rw [mem_strictLower, mem_strictLower, hrev]
    omega

/-! ## 3. On an odd side the two halves do not touch

The geometric content. A site strictly below the midline and the mirror
image of a site strictly below the midline differ by at least two in the
reflected coordinate, so they cannot be nearest neighbours — and they agree
in no other coordinate either, because the reflected coordinates already
differ.
-/

/-- **THE MIRROR LAYER SEPARATES.** -/
theorem not_adj_cross_odd (i : Fin d) (hn : Odd n) {p q : Site d n}
    (hp : p ∈ strictLower i n) (hq : q ∈ strictLower i n) :
    ¬ (boxGraph d n).Adj p (GraphReflection.revSite (n := n) i q) := by
  rw [mem_strictLower] at hp hq
  obtain ⟨k, hk⟩ := hn
  have hqlt := (q i).isLt
  have hrev : ((GraphReflection.revSite (n := n) i q) i).val = n - 1 - (q i).val := by
    rw [GraphReflection.revSite_apply_self, Fin.val_rev]; omega
  rintro ⟨j, hsame, hstep⟩
  by_cases hj : j = i
  · subst hj
    omega
  · -- a step in another direction leaves the reflected coordinate alone, and
    -- there it already differs
    have hi : (p i).val = ((GraphReflection.revSite (n := n) i q) i).val :=
      congrArg Fin.val (hsame i fun h => hj h.symm)
    omega

/-- **SO THE CROSS-COUPLING VANISHES IDENTICALLY.** An equality with zero,
    not an estimate: on an odd side there is no cut-crossing edge to
    estimate. -/
theorem crossForm_odd_eq_zero (i : Fin d) (hn : Odd n) (m : ℝ) (w : Site d n → ℝ) :
    GraphMirrorReflection.crossForm (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) (strictLower i n) w = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
  have hne : p ≠ GraphReflection.revSite (n := n) i q := by
    rw [mem_strictLower] at hp hq
    have hrev : ((GraphReflection.revSite (n := n) i q) i).val = n - 1 - (q i).val := by
      rw [GraphReflection.revSite_apply_self, Fin.val_rev]; omega
    have hqlt := (q i).isLt
    intro hc
    have : (p i).val = ((GraphReflection.revSite (n := n) i q) i).val := by rw [hc]
    omega
  rw [GraphLaplacian.massive_apply, if_neg hne,
    if_neg (not_adj_cross_odd i hn hp hq)]
  ring

/-! ## 4. Reflection positivity on the odd box, and then on any box -/

/-- **REFLECTION POSITIVITY ON THE BOX OF ODD SIDE.** The statement is
    `GraphReflectionPositive.reflectionPositive_box`'s, with `Even n`
    replaced by `Odd n` and nothing else changed. -/
theorem reflectionPositive_box_odd (i : Fin d) (hn : Odd n) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) := by
  intro c hc
  refine GraphMirrorReflection.reflectionPositive_mirror
    (isMirrorHalf_strictLower i n) (GraphReflection.boxGraph_revSite_aut i) hm
    (fun w => le_of_eq (crossForm_odd_eq_zero i hn m w)) (c := c) ?_
  intro p hpH hpM
  refine hc p ?_
  rw [lowerHalf_eq_union]
  simp only [Finset.mem_union]
  tauto

/-- **THE PARITY HYPOTHESIS IS GONE.** Reflection positivity of the massive
    Green function on `boxGraph d n`, for the half cut by any one
    coordinate, at every side length. -/
theorem reflectionPositive_box_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) := by
  rcases Nat.even_or_odd n with hn | hn
  · exact GraphReflectionPositive.reflectionPositive_box i hn hm
  · exact reflectionPositive_box_odd i hn hm

/-! ## 5. Review — the ways this could be hollow

**"Is `strictLower` a region invented to make the proof go through?"** No,
and `lowerHalf_eq_union` is the check: the estate's existing `lowerHalf` IS
`strictLower ∪ midLayer`, at every `n`, and the theorems in §4 are stated
about `lowerHalf`. Nothing was reshaped. Had the conclusion been about
`strictLower` alone it would have been a weaker theorem about a smaller
region, which is exactly the kind of quiet narrowing this project exists to
catch.

**"Is the odd case really easier, or is something being skipped?"** Really
easier, and the reason is geometric rather than technical: the fixed layer
sits between the halves, so there is no cut-crossing edge at all. The
even case has one per innermost site. **`crossForm_odd_eq_zero` is an
equality with zero**, where the even case needs `BoxCrossCoupling`'s
computation and a nonpositivity argument. A reader who expects the harder
parity to be the odd one has the picture upside down.

**"Does `reflectionPositive_box_any` actually subsume the old theorem, or
does it restate it?"** It calls it. The even branch is
`GraphReflectionPositive.reflectionPositive_box` verbatim; the odd branch is
§4. Nothing was reproved and nothing was weakened to make the two branches
agree — the statements were already identical apart from the hypothesis,
which is why the combination is three lines.

**"What still carries `Even n`?"** Everything downstream:
`GraphOS2.os2_box`, `os2_box_four`, `os2_lattice`, the exponential versions,
`LatticeReflectionPositive`, `LatticeReflectionTwo`, `TorusReflection`, and
the strictness files. **The hypothesis is now removable in all of them and
removed in none**, which is the honest state and is a unit of mechanical
work, not of mathematics. Recorded rather than quietly left.

**"Is the `d = 0` or `n = 0` case doing something silly?"** With `d = 0`
there is no coordinate `i`, so every statement is vacuous. With `n = 0` the
site type is empty when `d > 0` and the sums are empty; `Odd 0` is false, so
the odd theorem does not apply, and `reflectionPositive_box_any` routes
`n = 0` through the even branch. Nothing depends on a degenerate case
behaving well.
-/

end BoxOddReflection
