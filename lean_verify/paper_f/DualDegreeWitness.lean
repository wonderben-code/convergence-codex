import DualDegreeExact
import PlusCondition

/-!
# A configuration the even-degree criterion serves and `PlusBoundary` does not

`DualDegreeExact` proved that `EvenDegrees (dualGraph σ)` holds exactly when every plaquette has an
even number of broken outward sides, and that `PlusBoundary` is strictly stronger — but its two
witnesses for the strictness failed in opposite directions and it said so:

* `cornerDown` is off `PlusBoundary` with a broken-outward count of **two**, so the *even* in the
  criterion does real work there — but its dual graph has **no edges at all**, so it exhibits no
  conclusion the old hypothesis could not already deliver.
* the global flip is off `PlusBoundary` with a dual graph that has edges — but it is the **same**
  graph as its `+` partner's, and its broken-outward count is **zero**.

That file recorded the missing witness as an open `UNLOCK_WATCHLIST` item and said the one
ingredient it lacked was *a concrete `+` configuration with an exhibited dual edge*.
**`DualGraph.sigmaPlus` is exactly that and has been since the dual graph was built**
(`adj_sigmaPlus`, `dualGraph_sigmaPlus_ne_bot`, written to show `exists_dual_cycle_decomposition`
is not vacuous). The item was one `xorC` away from closed and its "not in hand" paragraph was
wrong — `ERRATUM 133`, and the same error as `ERRATUM 132` one turn later.

> **`witness_has_content_on_both_sides`** — `witness := xorC sigmaPlus (cornerDown 4)` is **not**
> `PlusBoundary`, its dual graph is **not** `⊥`, it satisfies `EvenDegrees`, and its
> broken-outward count at the corner plaquette is **exactly two**.

So the criterion is not merely weaker than `PlusBoundary` on paper: there is a configuration it
serves, with a graph that has edges to say it about, on which `DualGraph.evenDegrees_dualGraph`
has nothing to say.

## How it is built, and the one general lemma that makes it cheap

`PlusCondition.contour_xor` makes the contour of an exclusive-or the symmetric difference of the
two contours. `cornerDown`'s whole contour is the corner plaquette's two **outward** sides, and a
`+` configuration breaks no bond with both ends on the boundary
(`DualObstruction.notMem_contour_of_plusBoundary`), so the two contours are **disjoint** and the
xor's contour is their union. The added bonds are outward, so they contribute no dual edge —
**`dualGraph_eq_of_outward_diff`**, which is the general statement: *enlarging a contour by bonds
that are only ever outward sides leaves the dual graph alone.* Hence
`dualGraph witness = dualGraph sigmaPlus`, and `sigmaPlus`'s edge and even degrees transfer.

## What this does not do, which is most of it

**The dual graph is `sigmaPlus`'s, on the nose, by construction.** No *new* dual graph is
exhibited and none is claimed: what the witness shows is that the criterion **applies** where the
hypothesis does not, not that it reaches a conclusion of a new shape. Whether some configuration
has an even-degree dual graph arising from no `+` configuration at all is **not investigated
here** — no attempt was made, and it is not implied by anything below.

**And it does not move the Peierls wall by a line.** `WALLS` §W3.0 §7b already records why: the
criterion is exactly as hard to verify for a general boundary-reaching cluster as the hypothesis
it replaces, and nothing counts clusters. This closes a watchlist item about the criterion's
sharpness. It closes nothing about `IsingBoundaryField.MagnetisationBound`.
-/

namespace DualDegreeWitness

open IsingFiniteVolume DualObstruction PlaquetteLattice DualGraph SimpleGraph
open IsingContourPlaquette IsingContourEnergy ExtendedDual PlusCondition DualDegreeExact

set_option linter.style.openClassical false
open scoped Classical

/-! ## 1. Outward-only bonds are invisible to the dual graph -/

/-- **ENLARGING A CONTOUR BY OUTWARD SIDES LEAVES THE DUAL GRAPH ALONE.** The `Q ≠ P` clause of
`dualAdj` drops exactly the outward directions, so a bond that is only ever an outward side can be
added freely. `DualDegreeExact.dualGraph_congr` is the special case where nothing is added. -/
theorem dualGraph_eq_of_outward_diff {n : ℕ} {σ τ : Config n}
    (hsub : contour σ ⊆ contour τ)
    (hout : ∀ (P : Plaq n) (d : Fin 4),
      sideOf P d ∈ contour τ → sideOf P d ∉ contour σ → Outward P d) :
    dualGraph τ = dualGraph σ := by
  ext P Q
  constructor
  · rintro ⟨d, hmem, rfl, hne⟩
    by_cases hs : sideOf P d ∈ contour σ
    · exact ⟨d, hs, rfl, hne⟩
    · exact absurd (hout P d hmem hs) hne
  · rintro ⟨d, hmem, rfl, hne⟩
    exact ⟨d, hsub hmem, rfl, hne⟩

/-! ## 2. The two contours are disjoint

`sigmaPlus` lives on the `4 × 4` box, so the corner plaquette is taken there. -/

theorem one_lt_four : (1 : ℕ) < 4 := by omega

/-- The corner plaquette of the `4 × 4` box. -/
abbrev cornerP : Plaq 4 := OuterFaceObstruction.cornerPlaq one_lt_four

theorem cornerL_notMem_sigmaPlus : sideL cornerP ∉ contour sigmaPlus := by
  rw [sideL, mem_contour]
  rintro ⟨-, hne⟩
  exact hne (by decide)

theorem cornerD_notMem_sigmaPlus : sideD cornerP ∉ contour sigmaPlus := by
  rw [sideD, mem_contour]
  rintro ⟨-, hne⟩
  exact hne (by decide)

theorem inter_eq_empty :
    contour sigmaPlus ∩ contour (MinimumContour.cornerDown 4) = ∅ := by
  classical
  rw [OuterFaceObstruction.contour_cornerDown_eq one_lt_four]
  ext e
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    iff_false, not_and]
  rintro he (rfl | rfl)
  · exact cornerL_notMem_sigmaPlus he
  · exact cornerD_notMem_sigmaPlus he

/-! ## 3. The witness -/

/-- **THE WITNESS.** `sigmaPlus` with the corner-flip configuration xored in: the boundary is now
down everywhere except at the corner, and the interior droplet of `sigmaPlus` is untouched as a
contour. -/
def witness : Config 4 := xorC sigmaPlus (MinimumContour.cornerDown 4)

theorem contour_witness :
    contour witness = contour sigmaPlus ∪ contour (MinimumContour.cornerDown 4) := by
  rw [witness, contour_xor, inter_eq_empty, Finset.sdiff_empty]

theorem sub_contour_witness : contour sigmaPlus ⊆ contour witness := by
  rw [contour_witness]
  exact Finset.subset_union_left

theorem outward_of_diff (P : Plaq 4) (d : Fin 4)
    (hmem : sideOf P d ∈ contour witness) (hns : sideOf P d ∉ contour sigmaPlus) :
    Outward P d := by
  rw [contour_witness, Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact absurd h hns
  · exact outward_of_mem_cornerDown one_lt_four h

/-- **THE ADDED BONDS CHANGE NOTHING.** -/
theorem dualGraph_witness : dualGraph witness = dualGraph sigmaPlus :=
  dualGraph_eq_of_outward_diff sub_contour_witness outward_of_diff

/-! ## 4. The three properties, one at a time -/

/-- (a) The boundary is down at `(0,1)`, which is a boundary site and is not the corner. -/
theorem not_plusBoundary_witness : ¬ PlusBoundary witness := by
  intro h
  have hb := h (((0 : Fin 4), (1 : Fin 4)) : Site 4) (by decide)
  exact absurd hb (by decide)

/-- (b) The dual graph has an edge — `sigmaPlus`'s, transported. -/
theorem adj_witness : (dualGraph witness).Adj plaq01 plaq11 := by
  rw [dualGraph_witness]
  exact adj_sigmaPlus

theorem dualGraph_witness_ne_bot : dualGraph witness ≠ ⊥ := by
  rw [dualGraph_witness]
  exact dualGraph_sigmaPlus_ne_bot

/-- And the criterion holds, which is the point: `DualDegreeExact.evenDegrees_dualGraph_iff`
delivers this for a configuration `DualGraph.evenDegrees_dualGraph` cannot be applied to. -/
theorem evenDegrees_witness : EvenDegrees (dualGraph witness) := by
  rw [dualGraph_witness]
  exact evenDegrees_dualGraph plusBoundary_sigmaPlus

theorem cornerL_mem_witness : sideL cornerP ∈ contour witness := by
  rw [contour_witness]
  exact Finset.mem_union_right _ (OuterFaceObstruction.cornerDown_sideL_mem one_lt_four)

theorem cornerD_mem_witness : sideD cornerP ∈ contour witness := by
  rw [contour_witness]
  exact Finset.mem_union_right _ (OuterFaceObstruction.cornerDown_sideD_mem one_lt_four)

/-- (c) **THE BROKEN-OUTWARD COUNT AT THE CORNER IS `{0, 3}`.** Directions `1` and `2` are not
outward at all in a `4 × 4` box — `upP cornerP = cornerP` would need `0 + 2 = 4` — so the two that
survive are the two the corner flip broke. -/
theorem brokenOutward_corner :
    (Finset.univ.filter fun d : Fin 4 =>
      sideOf cornerP d ∈ contour witness ∧ Outward cornerP d) = {0, 3} := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨-, hout⟩
    fin_cases d
    · exact Or.inl rfl
    · exact absurd ((upP_eq_self_iff cornerP).mp hout) (by decide)
    · exact absurd ((rightP_eq_self_iff cornerP).mp hout) (by decide)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨cornerL_mem_witness, (leftP_eq_self_iff cornerP).mpr rfl⟩
    · exact ⟨cornerD_mem_witness, (downP_eq_self_iff cornerP).mpr rfl⟩

theorem brokenOutward_corner_card :
    (Finset.univ.filter fun d : Fin 4 =>
      sideOf cornerP d ∈ contour witness ∧ Outward cornerP d).card = 2 := by
  rw [brokenOutward_corner]
  decide

/-! ## 5. The item, closed -/

/-- **THE WITNESS THE STRICTNESS QUESTION ASKED FOR.** Off `PlusBoundary`, a dual graph with
edges, `EvenDegrees` by the criterion, and a broken-outward count that is nonzero — so the *even*
in *even number of broken outward sides* is the clause carrying the proof, not a stand-in for
*none*.

**And the honest limit, which is in the header and repeated here because a reader may arrive at
this theorem first:** the dual graph is `sigmaPlus`'s by construction, so no dual graph is
exhibited here that `evenDegrees_dualGraph` could not already produce from some other
configuration. What is exhibited is a **configuration** it cannot be applied to. -/
theorem witness_has_content_on_both_sides :
    ¬ PlusBoundary witness
      ∧ dualGraph witness ≠ ⊥
      ∧ EvenDegrees (dualGraph witness)
      ∧ (Finset.univ.filter fun d : Fin 4 =>
          sideOf cornerP d ∈ contour witness ∧ Outward cornerP d).card = 2 :=
  ⟨not_plusBoundary_witness, dualGraph_witness_ne_bot, evenDegrees_witness,
    brokenOutward_corner_card⟩

end DualDegreeWitness
