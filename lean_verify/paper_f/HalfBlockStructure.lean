import CrossBlockStructure
import ReflectedFormCongr

/-!
# Why the half decides: the block structure of the cut

`ReflectedFormCongr` §7 proved that one graph, one reflection and one mass give **strict** on one
half and **degenerate** on another. It proved *that* it happens; it did not say *why*. The reason is
already in the estate, in `CrossBlockStructure`, and this file joins the two.

## The general statement, which is the repair of a refuted sentence

`ERRATUM 73` refuted the estate's long-standing prose criterion *"strictness holds exactly when
every vertex touches the mirror"* — the torus at side three has a midline site touching nothing and
is strict anyway. **The refutation is right and the sentence was one word away from a theorem.** The
midline site is in the *mirror*, not in the *half*, and the cut there is diagonal:

> **`strict_iff_touching_of_cross_diag` — on a DIAGONAL cut, the reflected form is strict exactly
> when every site OF THE HALF is joined to its own mirror image.**

`MirrorStrict.reflectionPositive_mirror_strict` is the sufficient direction and calls itself *"the
corrected criterion"*; the **converse** was never stated generally. `CrossBlockStructure`'s §§9–11
instantiate the underlying `strict_iff_cut_perfect` at the torus, the box and the estate's own
`def`, one family at a time. This is the one statement those three are cases of.

## And the same criterion explains §7 exactly

Both halves of `ReflectedFormCongr` §7 satisfy `IsCrossBlock`. They differ in the block structure:

* **`rotHalf = {1,2}`**, a contiguous side — the cut is **diagonal**, every site joined to its own
  mirror and to no other's. **Perfect. Strict.**
* **`torusHalf = {0,2}`**, an antipodal pair — the cut is the **all-ones** matrix on two sites, one
  block of size two. Both sites touch their own mirror, **and they also touch each other's**, so
  the cut is not perfect and the block contributes a kernel direction. **Degenerate.**

All four facts are `decide`d. **So the mechanism is not "which half you chose" but "how many blocks
the cut has", and `crossForm_eq_zero_iff` already said the coupling's degeneracy is exactly that
count.** `CrossBlockStructure` recorded that reading and said it *"is not followed up here"*.

## An independent second proof of §7's negative half

`torusFour_not_strict_via_blocks` re-derives `ReflectedFormCongr.torusFour_not_strict` from
`strict_iff_cut_perfect` and a `decide` — **a completely different route** from §4's, which
transported the result along a graph isomorphism from `IndefiniteCoupling.bipGraph`. Two routes,
one answer, and neither proof uses the other.

**Said precisely, because the objects are shared:** `torusRho` and `torusHalf` are *defined* through
the relabelling, so the equivalence is in their definitions. What §3 avoids is the transport
*theorems* — `bipGraph` does not appear in these proofs, and neither does `strict_congr`.

## What this is NOT

**It does not remove the diagonality hypothesis** from the biconditional. On a general block cut
the criterion is `strict_iff_cut_perfect`, which is already stated and already general; diagonality
is what turns *"perfect"* into the one-clause *"everybody touches"*, and `torusHalf` is the witness
that the two are different conditions.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HalfBlockStructure

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The general criterion on a diagonal cut -/

/-- **ON A DIAGONAL CUT, STRICTNESS IS EXACTLY THAT EVERY SITE OF THE HALF TOUCHES ITS OWN
MIRROR.**

This is the sentence `ERRATUM 73` refuted, with the one word it was missing. The refuted version
said *every vertex*; the torus at side three has a **mirror** site touching nothing and is strict,
which refutes that and leaves this untouched — the quantifier here is over `H`, and `Mir` is not
`H`.

**`MirrorStrict.reflectionPositive_mirror_strict` is the `←` direction, hypothesis for
hypothesis** — the `example` below checks that by kernel rather than asserting it. **The new
content is the `→` direction**, which was never stated in general; the `←` half is re-obtained here
by a different route, uniformly from `strict_iff_cut_perfect`, rather than re-proved. -/
theorem strict_iff_touching_of_cross_diag (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ∀ s ∈ H, G.Adj s (θ s) := by
  rw [strict_iff_cut_perfect hM h hm (isCrossBlock_of_cross_diag hdiag)]
  constructor
  · intro hperf s hs
    exact (hperf s hs s hs).mpr rfl
  · intro htouch s hs q hq
    refine ⟨fun ha => hdiag s hs q hq ha, ?_⟩
    rintro rfl
    exact htouch s hs

/-- **THE `←` HALF IS `MirrorStrict`'S THEOREM, CHECKED BY THE KERNEL.** Same five hypotheses,
same conclusion, so the biconditional above is that theorem plus a converse and not a rival to
it. -/
example (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) (hfull : ∀ p ∈ H, G.Adj p (θ p))
    {c : V → ℝ} (hc0 : c ≠ 0) (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    0 < GraphReflection.reflectedForm G m θ c :=
  (strict_iff_touching_of_cross_diag hM h hm hdiag).mpr hfull c hc0 hc

/-- **AND SO ONE UNTOUCHED SITE OF THE HALF IS ENOUGH TO BREAK IT**, which is the form the estate's
`§§9–11` use family by family: at the torus, the box and the estate's own `def`, strictness fails
as soon as the half is thick enough to contain a site not adjacent to the cut. -/
theorem not_strict_of_untouched (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) {s : V} (hs : s ∈ H)
    (hns : ¬ G.Adj s (θ s)) :
    ¬ ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c :=
  fun hstrict => hns ((strict_iff_touching_of_cross_diag hM h hm hdiag).mp hstrict s hs)

/-! ## 2. The two halves of `ReflectedFormCongr` §7, decided -/

open ReflectedFormCongr

/-- **THE CONTIGUOUS HALF GIVES A DIAGONAL CUT.** No two distinct sites of `{1,2}` are joined
across the mirror. -/
theorem crossDiag_rotHalf :
    ∀ p ∈ rotHalf, ∀ q ∈ rotHalf,
      (TorusReflection.torusGraph 1 4).Adj p (torusRho q) → p = q := by decide

/-- **AND EVERY SITE OF IT TOUCHES ITS OWN MIRROR.** With the line above, the cut is perfect. -/
theorem touching_rotHalf :
    ∀ s ∈ rotHalf, (TorusReflection.torusGraph 1 4).Adj s (torusRho s) := by decide

/-- `rotHalf` is a half for `torusRho`, with empty mirror — the companion of
`ReflectedFormCongr.isMirrorHalf_torusHalf`, which §7 needed for the other half only. -/
theorem isMirrorHalf_rotHalf :
    IsMirrorHalf torusRho rotHalf (∅ : Finset (BoxGraph.Site 1 4)) where
  fixed := by intro p; revert p; decide
  disj := by intro p; revert p; decide
  split := by intro p; revert p; decide

/-- **THE ANTIPODAL HALF DOES NOT GIVE A DIAGONAL CUT.** `0` and `2` are joined across the mirror
to *each other*, not only to themselves — one block of size two. -/
theorem not_crossDiag_torusHalf :
    ¬ ∀ p ∈ torusHalf, ∀ q ∈ torusHalf,
      (TorusReflection.torusGraph 1 4).Adj p (torusRho q) → p = q := by decide

/-- **AND EVERY SITE OF IT TOUCHES ITS OWN MIRROR TOO.** So *touching* is not what separates the
two halves — the previous theorem is, and this one is here to rule out the easy explanation. -/
theorem touching_torusHalf :
    ∀ s ∈ torusHalf, (TorusReflection.torusGraph 1 4).Adj s (torusRho s) := by decide

/-- It is still a **block** cut, so `strict_iff_cut_perfect` applies to it. -/
theorem isCrossBlock_torusHalf :
    IsCrossBlock (TorusReflection.torusGraph 1 4) torusRho torusHalf := by decide

/-- **BUT THE CUT IS NOT PERFECT**, and that single fact is the whole difference. -/
theorem not_cutPerfect_torusHalf :
    ¬ ∀ s ∈ torusHalf, ∀ q ∈ torusHalf,
      ((TorusReflection.torusGraph 1 4).Adj s (torusRho q) ↔ s = q) := by decide

/-! ## 3. Hence §7 again, by a route with no isomorphism in it -/

/-- **`ReflectedFormCongr.torusFour_not_strict`, RE-DERIVED FROM THE CUT.**

§4 got this by transporting `CrossBlockStructure.bipGraph_not_strict` along a graph isomorphism.
This gets it from `strict_iff_cut_perfect` and one `decide` about which sites are joined to which.
**Two routes, one answer, and neither uses the other.** -/
theorem torusFour_not_strict_via_blocks (hm : m ≠ 0) :
    ¬ ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
        (∀ p, p ∉ torusHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c :=
  fun hstrict => not_cutPerfect_torusHalf
    ((strict_iff_cut_perfect isMirrorHalf_torusHalf isRefl_torusRho hm
      isCrossBlock_torusHalf).mp hstrict)

/-- **AND §7's POSITIVE HALF FROM §1**, so both sides of that finding now come from the cut rather
than from a transport. -/
theorem torusFour_strict_rotHalf_via_blocks (hm : m ≠ 0) :
    ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
      (∀ p, p ∉ rotHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
      0 < GraphReflection.reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c :=
  (strict_iff_touching_of_cross_diag isMirrorHalf_rotHalf isRefl_torusRho hm
    crossDiag_rotHalf).mpr touching_rotHalf

end HalfBlockStructure
