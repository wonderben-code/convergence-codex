import ExtendedDual

/-!
# The even-degree hypothesis, exactly — what `ExtendedDual` proved, read back on the ordinary dual

The entropy half of this estate's Peierls chain rests on `DualGraph.evenDegrees_dualGraph`,
*every plaquette has an even number of dual neighbours*, which is what
`CircuitCount.three_mul_card_le_card_contour` needs to decompose a contour into circuits.
**And it carries `PlusBoundary σ`.**

`ExtendedDual` already asked what that hypothesis is for and answered it: it enlarges the graph
by four rim vertices and proves `evenDegrees_plaq` — *every plaquette has even degree in the
**extended** graph, with no hypothesis on `σ` at all* — with the header sentence *"the hypothesis
was there to rule the outward sides out; here they are counted instead."* This file does not
repeat any of that. It imports it.

What that file never said is what its own theorem implies about the graph the chain actually
uses. The extended degree of `P` is its **ordinary** dual degree plus its count of broken outward
sides (`ncard_neighborSet_inl`, the step `evenDegrees_plaq` performs inline and does not name).
The extended degree is even. So:

> **`evenDegrees_dualGraph_iff`** — `EvenDegrees (dualGraph σ)` holds **if and only if** every
> plaquette has an **even number of broken OUTWARD sides**. No boundary condition anywhere.

`PlusBoundary` forces that count to be **zero** — even, and far more than even
(`no_broken_outer_of_plusBoundary`). So it is sufficient, and it is strictly stronger than
necessary. Two witnesses say how strictly, and they fail to be conclusive in opposite directions,
which is why both are here:

> **`cornerDown_evenDegrees`** — `MinimumContour.cornerDown` is not `PlusBoundary` and satisfies
> the criterion **by parity rather than by absence**: its broken-outward count at the corner
> plaquette is *two*. But its dual graph has no edges at all
> (`cornerDown_neighborSet_eq_empty`), so as evidence that the conclusion has content off the old
> hypothesis it is worth nothing.

> **`flip_strict_extension`** — the global flip carries **every** `PlusBoundary` configuration to
> one that is not `PlusBoundary` and has the **same dual graph**. That witness has content
> exactly when the original did, and none of it is new content.

## What this does and does not do to the Peierls wall

**It moves `WALLS` §W3.0's obstruction off the even-degree step.** The corner-down configuration,
which that account uses as its witness, passes the even-degree criterion for the ordinary dual
graph — a reader of §W3.0 could easily have concluded otherwise. The real reason is the one
`contour_cornerDown_eq`'s docstring already gives: that contour has two sides and a dual circuit
needs four. And note the sharp contrast with `ExtendedDual`: the very repair that makes the degree
count unconditional is what makes `cornerDown` fail `EvenDegrees` — on the rim vertices, not the
plaquettes (`cornerDown_even_ordinary_odd_extended`).

**It does not weaken any existing theorem and does not unlock the chain.** Every consumer of
`evenDegrees_dualGraph` still has `PlusBoundary` in hand and is untouched; the gate theorem is
re-derived here from the criterion (`evenDegrees_dualGraph_of_plusBoundary`) to check that nothing
was lost. The criterion is not easier to verify for a general boundary-reaching cluster than the
original hypothesis was — **it is exactly the same difficulty, relocated and named**. Nothing here
counts clusters, which is what a uniform field bound would need.

**A witness with content on both sides is missing and is not proved here.** What would show the
criterion genuinely reaches configurations the old hypothesis could not serve is one that is *both*
not `PlusBoundary` **and** has a nonempty dual graph **and** has a nonzero broken-outward count.
`cornerDown` supplies the third, the flip supplies the second, and no configuration in this estate
is known to supply all three. `PlusCondition.contour_xor` makes such a configuration constructible
in principle — the symmetric difference of a `+` contour with `cornerDown`'s two outward sides —
and `UNLOCK_WATCHLIST`'s S3b-ii block records that leg, with its own trigger, rather than leaving
it implied here.
-/

namespace DualDegreeExact

open IsingFiniteVolume DualObstruction PlaquetteLattice DualGraph SimpleGraph
open IsingContourPlaquette IsingContourEnergy ExtendedDual

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The extended degree, split — and the exact criterion

`ExtendedDual.evenDegrees_plaq` proves its result by computing this splitting inside a `rw` chain
and then discarding it. Named, it is the whole content of this file. -/

/-- **THE EXTENDED DEGREE IS THE ORDINARY DEGREE PLUS THE BROKEN OUTWARD SIDES.** Every step is
`ExtendedDual`'s: `neighborSet_inl` splits the neighbour set, `card_inl_neighbours` counts the
plaquette half and `card_inr_neighbours` the rim half. -/
theorem ncard_neighborSet_inl (σ : Config n) (P : Plaq n) :
    ((extDual σ).neighborSet (Sum.inl P)).ncard
      = ((dualGraph σ).neighborSet P).ncard
        + (Finset.univ.filter fun d : Fin 4 =>
            sideOf P d ∈ contour σ ∧ Outward P d).card := by
  classical
  have hdisj : Disjoint (Sum.inl '' {Q : Plaq n | dualAdj σ P Q})
      (Sum.inr '' {d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d}) := by
    rw [Set.disjoint_left]
    rintro v ⟨Q, -, rfl⟩ ⟨d, -, hEq⟩
    exact absurd hEq (by simp)
  have hns : (dualGraph σ).neighborSet P = {Q : Plaq n | dualAdj σ P Q} := rfl
  rw [neighborSet_inl σ P, hns,
    Set.ncard_union_eq hdisj ((Set.toFinite _).image _) ((Set.toFinite _).image _),
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective,
    card_inl_neighbours σ P, card_inr_neighbours σ P]

/-- **THE EXACT CRITERION, ONE PLAQUETTE AT A TIME.** A sum is even exactly when its two summands
agree in parity, and `evenDegrees_plaq` says the sum is even. -/
theorem even_degree_iff (σ : Config n) (P : Plaq n) :
    Even ((dualGraph σ).neighborSet P).ncard
      ↔ Even (Finset.univ.filter fun d : Fin 4 =>
          sideOf P d ∈ contour σ ∧ Outward P d).card := by
  have h := evenDegrees_plaq σ P
  rw [ncard_neighborSet_inl σ P] at h
  exact Nat.even_add.mp h

/-- **THE EXACT HYPOTHESIS.** `EvenDegrees (dualGraph σ)` needs no boundary condition — only that
every plaquette meets the outer face in an even number of broken sides. -/
theorem evenDegrees_dualGraph_iff (σ : Config n) :
    EvenDegrees (dualGraph σ)
      ↔ ∀ P : Plaq n, Even (Finset.univ.filter fun d : Fin 4 =>
          sideOf P d ∈ contour σ ∧ Outward P d).card :=
  ⟨fun h P => (even_degree_iff σ P).mp (h P), fun h P => (even_degree_iff σ P).mpr (h P)⟩

/-! ## 2. `PlusBoundary` is the extreme case, and nothing was lost -/

/-- **UNDER `PlusBoundary` THE COUNT IS NOT MERELY EVEN, IT IS ZERO.** So the old hypothesis
implies the new criterion by the widest possible margin, which is why it was never noticed to be
stronger than needed. `ExtendedDual.no_rim_edge_of_plusBoundary` is this in graph form; this is the
form the criterion consumes. -/
theorem no_broken_outer_of_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n) :
    (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d) = ∅ := by
  classical
  refine Finset.filter_eq_empty_iff.mpr fun d _ => ?_
  rintro ⟨hmem, hout⟩
  exact partnerOf_ne_of_mem hσ P d hmem hout

/-- **THE GATE THEOREM, RE-DERIVED FROM THE CRITERION.** This proves nothing new —
`DualGraph.evenDegrees_dualGraph` is the same statement and came first. It is here because the
claim *"the criterion is weaker and loses nothing"* is checkable, and this is the check. -/
theorem evenDegrees_dualGraph_of_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) :
    EvenDegrees (dualGraph σ) :=
  (evenDegrees_dualGraph_iff σ).mpr fun P => by
    rw [no_broken_outer_of_plusBoundary hσ P]
    simp

/-! ## 3. First witness: `cornerDown`, where the *even* is doing the work

This is the only configuration in the estate for which the criterion holds by parity rather than
by absence: its broken-outward count at the corner plaquette is two. -/

/-- `MinimumContour.cornerDown` fails `PlusBoundary`, at every `n > 1`.
`DualObstruction.not_plusBoundary_cornerDown` says this of `DualObstruction.cornerDown`, a separate
`Config 3` with the same description; the contour development uses the `MinimumContour` one. -/
theorem cornerDown_not_plusBoundary (hn : 1 < n) :
    ¬ PlusBoundary (MinimumContour.cornerDown n) := by
  intro hplus
  have hn0 : 0 < n := by omega
  have h := hplus (⟨⟨0, hn0⟩, ⟨0, hn0⟩⟩ : Site n)
    (IsingBoundaryField.isBoundary_corner n hn0)
  exact (MinimumContour.cornerDown_eq_true_iff _).mp h ⟨rfl, rfl⟩

/-- **EVERY BROKEN SIDE OF `cornerDown` FACES OUTWARDS.** The contour is exactly
`{sideL (cornerPlaq), sideD (cornerPlaq)}` (`OuterFaceObstruction.contour_cornerDown_eq`), and
neither bond is a side of any other plaquette: a left side sits in column `P.i` and a bottom side
in row `P.j`, so matching either against the corner's forces `P.i + 1 = 0` or `P.j + 1 = 0` in
every case but the corner's own.

This generalises `ExtendedDual.cornerDown_left_rim_unique` from direction `0` to all four, and
drops its `Outward P 0` hypothesis, which is here a conclusion rather than an assumption. -/
theorem outward_of_mem_cornerDown (hn : 1 < n) {P : Plaq n} {d : Fin 4}
    (hmem : sideOf P d ∈ contour (MinimumContour.cornerDown n)) : Outward P d := by
  classical
  rw [OuterFaceObstruction.contour_cornerDown_eq hn, Finset.mem_insert,
    Finset.mem_singleton] at hmem
  have hi := P.hi
  have hj := P.hj
  fin_cases d <;>
    simp only [sideOf, sideL, sideU, sideR, sideD, OuterFaceObstruction.cornerPlaq,
      bl, tl, br, tr, Sym2.eq_iff, Prod.mk.injEq, Fin.mk.injEq] at hmem <;>
    first
      | exact (leftP_eq_self_iff P).mpr (by omega)
      | exact (downP_eq_self_iff P).mpr (by omega)
      | (exfalso; omega)

/-- **AND SO THE CONTAINMENT IS STRICT.** The broken-outward count equals the broken count, which
`IsingContourPlaquette.even_plaquette` says is even for every configuration. -/
theorem cornerDown_evenDegrees (hn : 1 < n) :
    EvenDegrees (dualGraph (MinimumContour.cornerDown n)) := by
  classical
  refine (evenDegrees_dualGraph_iff _).mpr fun P => ?_
  have hfilter :
      (Finset.univ.filter fun d : Fin 4 =>
          sideOf P d ∈ contour (MinimumContour.cornerDown n) ∧ Outward P d)
        = Finset.univ.filter fun d : Fin 4 =>
            sideOf P d ∈ contour (MinimumContour.cornerDown n) :=
    Finset.filter_congr fun d _ =>
      ⟨fun h => h.1, fun h => ⟨h, outward_of_mem_cornerDown hn h⟩⟩
  rw [hfilter, Finset.card_filter, Fin.sum_univ_four]
  exact even_plaquette _ P.i P.j P.hi P.hj

/-- **BUT THE WITNESS IS EMPTY AS A GRAPH**, and saying so is the honest half. Every broken side of
`cornerDown` faces outwards, so no dual edge exists at all and `cornerDown_evenDegrees` holds with
every degree `0`. It shows the hypothesis is not necessary; it does not show the *conclusion* has
content beyond `PlusBoundary`'s reach. §4 supplies a witness that is nonempty as a graph, and the
header records that no witness supplying both is known. -/
theorem cornerDown_neighborSet_eq_empty (hn : 1 < n) (P : Plaq n) :
    (dualGraph (MinimumContour.cornerDown n)).neighborSet P = ∅ := by
  ext Q
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨d, hmem, rfl, hne⟩
  exact hne (outward_of_mem_cornerDown hn hmem)

/-- **THE ORDINARY DUAL GRAPH KEEPS EVEN DEGREES HERE AND THE EXTENDED ONE DOES NOT.** Both halves
are proved elsewhere; the conjunction is stated because either half alone invites the wrong
reading. `ExtendedDual`'s repair is what makes the degree count unconditional, and it is also what
introduces the odd vertices — they are rim vertices, never plaquettes
(`RimWalk.odd_degree_isRim`). -/
theorem cornerDown_even_ordinary_odd_extended (hn : 1 < n) :
    EvenDegrees (dualGraph (MinimumContour.cornerDown n))
      ∧ ¬ EvenDegrees (extDual (MinimumContour.cornerDown n)) :=
  ⟨cornerDown_evenDegrees hn, not_evenDegrees_extDual hn⟩

/-! ## 4. Second witness: the global flip, which doubles the class without changing a graph

`cornerDown` is empty as a graph. The global flip gives the opposite kind of witness: it moves
**every** `PlusBoundary` configuration off the hypothesis while leaving its dual graph exactly
where it was. -/

/-- The dual graph sees the configuration only through its contour. -/
theorem dualGraph_congr {σ τ : Config n} (h : contour σ = contour τ) :
    dualGraph σ = dualGraph τ := by
  ext P Q
  constructor
  · rintro ⟨d, hmem, rfl, hne⟩
    exact ⟨d, by rw [← h]; exact hmem, rfl, hne⟩
  · rintro ⟨d, hmem, rfl, hne⟩
    exact ⟨d, by rw [h]; exact hmem, rfl, hne⟩

theorem dualGraph_flip (σ : Config n) :
    dualGraph (IsingFiniteVolume.flip σ) = dualGraph σ :=
  dualGraph_congr (IsingContourInvariant.contour_flip σ)

/-- The flip of a `+` configuration is never a `+` configuration: the corner spin was `true` and
is now `false`. `IsingFiniteVolume.flip_ne` says the flip moves every configuration; this says it
moves every configuration *out of the class*. -/
theorem not_plusBoundary_flip (hn : 0 < n) {σ : Config n} (hσ : PlusBoundary σ) :
    ¬ PlusBoundary (IsingFiniteVolume.flip σ) := by
  intro hf
  have hc := IsingBoundaryField.isBoundary_corner n hn
  have h1 := hσ (⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n) hc
  have h2 := hf (⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n) hc
  rw [IsingFiniteVolume.flip, h1] at h2
  exact Bool.noConfusion h2

/-- **THE CRITERION'S CLASS IS STRICTLY LARGER, AND NOT ONLY ON EMPTY GRAPHS.** For every `σ` the
old hypothesis covered, its flip is outside the hypothesis, inside the criterion, and carries the
**same** dual graph.

*And that is also the limit of this witness.* Same graph means same content: it exhibits no dual
graph that `evenDegrees_dualGraph` could not already reach. The two witnesses of this file bound
the question from opposite sides and neither settles it. -/
theorem flip_strict_extension (hn : 0 < n) {σ : Config n} (hσ : PlusBoundary σ) :
    ¬ PlusBoundary (IsingFiniteVolume.flip σ)
      ∧ dualGraph (IsingFiniteVolume.flip σ) = dualGraph σ
      ∧ EvenDegrees (dualGraph (IsingFiniteVolume.flip σ)) :=
  ⟨not_plusBoundary_flip hn hσ, dualGraph_flip σ,
    (dualGraph_flip σ) ▸ evenDegrees_dualGraph hσ⟩

end DualDegreeExact
