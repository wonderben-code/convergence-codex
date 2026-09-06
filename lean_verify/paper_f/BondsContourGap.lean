import PieceBranchesRealised

/-!
# The bond set is not the contour, on a named configuration

`OuterFaceObstruction` states, in prose, why the outer face cannot be one vertex: a side facing out
of the box has no plaquette on its far side. `OddPieceSelect` then named the consequence as the
reason its theorem cannot reach a site's spin — *off a `+` boundary, `bonds σ (dualGraph σ)` is not
the contour* — and `DualBonds.bonds_dualGraph` proves the equality **under** `PlusBoundary`.

**Nothing exhibited the failure.** As of 2026-09-06 no theorem in this estate says the two differ
for any configuration; the gap was a description. `PieceBranchesRealised.sigmaEdge` is the
configuration that makes it a theorem, and it is the same one that fires the path branch, for the
same reason: it breaks the single outward side of an edge plaquette that is not a corner.

## What is proved

**`sideOf_notMem_bonds_of_outward`** — **no outward side is a bond of the dual graph, on any
configuration.** `DualUnique.sideOf_eq_cases` says only two pairs can name a given side and both
fail: the first is `(P, d)` itself, whose partner is `P` because the side faces out, so the dual
graph would have to be reflexive; the second would make `P` its own neighbour's partner, which
`DualGraph.partnerOf_partnerOf` forbids. **`sideD_plaqEdge_notMem_bonds`** is that at
`plaqEdge`.

**`bonds_ne_contour_sigmaEdge`** — **so the bond set is not the contour.** It is in the contour
(`PieceBranchesRealised.sideD_plaqEdge_mem`) and not in the bonds. The obstruction
`OuterFaceObstruction` describes is now a statement about a named object.

## What is NOT here

**THE GENERAL STATEMENT IS PROVED AND THE CONCRETE ONE FOLLOWS FROM IT.** A first draft fenced
the general form as out of reach, saying it needs `partnerOf (partnerOf P d) (opp d) = P` and
that *this estate does not have* it. **It has had it since `DualGraph.partnerOf_partnerOf`**,
used in four files. The claim was false when written — the fourth such in four units — and the
fold-back was to prove the general theorem rather than to date the excuse.

**NOTHING IS REPAIRED.** This is the obstruction stated, not removed. `OuterFaceObstruction`'s own
account of what a repair would need is unchanged, and `ExtendedDual`'s four-rim construction — which
is the repair — is untouched here.

**NO CONVERSE.** `DualBonds.bonds_dualGraph` gives equality under `PlusBoundary`; **nothing here
says the two are equal *only* under it**, and `sigmaEdge` is one configuration, not a
characterisation.

**W3 DOES NOT MOVE**, and this is the plainest case of that in the run: what is proved is that a
step **cannot** be taken the way `OddPieceSelect` would need it. **Residue (b) is not closed and no
part of it is claimed.**

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **none** — both theorems are about one
named configuration on the `4 × 4` box and take no hypothesis at all. In particular they take **no
`PlusBoundary`**, which is the point: `sigmaEdge` does not satisfy it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace BondsContourGap

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique ExtendedDual
open PieceBranchesRealised SimpleGraph

/-! ## 1. The broken outward side is in no dual edge -/

/-- `opp` sends only `1` to `3`. -/
theorem eq_one_of_opp_eq_three {d : Fin 4} (h : (3 : Fin 4) = opp d) : d = 1 := by
  revert h
  revert d
  decide

/-- **NO OUTWARD SIDE IS A BOND OF THE DUAL GRAPH, ON ANY CONFIGURATION.** Only two pairs can name
a given side (`DualUnique.sideOf_eq_cases`), and both fail: the first is `(P, d)` itself, whose
partner is `P` because the side faces out, so the dual graph would have to be reflexive; the second
would make `P` its own neighbour's partner, which `DualGraph.partnerOf_partnerOf` forbids. -/
theorem sideOf_notMem_bonds_of_outward {n : ℕ} (σ : Config n) {P : Plaq n} {d : Fin 4}
    (hout : Outward P d) : sideOf P d ∉ bonds σ (dualGraph σ) := by
  intro hmem
  rw [mem_bonds] at hmem
  obtain ⟨-, P', d', hadj, hside⟩ := hmem
  have hne : partnerOf P' d' ≠ P' := ((dualGraph σ).ne_of_adj hadj).symm
  rcases sideOf_eq_cases hside with ⟨hP, hd⟩ | ⟨hP, hd⟩
  · subst hP
    subst hd
    rw [show partnerOf P d = P from hout] at hadj
    exact (dualGraph σ).irrefl hadj
  · have hback : partnerOf P d = P' := by
      rw [hP, hd]
      exact partnerOf_partnerOf P' d' hne
    have hPP : P' = P := by rw [← hback]; exact hout
    exact hne (by rw [← hP]; exact hPP.symm)

/-- **THE BROKEN OUTWARD SIDE OF `plaqEdge` IS NOT A BOND**, the general theorem at the named
configuration. -/
theorem sideD_plaqEdge_notMem_bonds :
    sideD plaqEdge ∉ bonds sigmaEdge (dualGraph sigmaEdge) :=
  sideOf_notMem_bonds_of_outward sigmaEdge outward_three

/-! ## 2. So the bond set is not the contour -/

/-- **THE BOND SET IS NOT THE CONTOUR.** `DualBonds.bonds_dualGraph` gives equality under
`PlusBoundary`; `sigmaEdge` does not satisfy it, and here the two genuinely differ. -/
theorem bonds_ne_contour_sigmaEdge :
    bonds sigmaEdge (dualGraph sigmaEdge) ≠ contour sigmaEdge := by
  intro hEq
  exact sideD_plaqEdge_notMem_bonds (hEq ▸ sideD_plaqEdge_mem)

end BondsContourGap
