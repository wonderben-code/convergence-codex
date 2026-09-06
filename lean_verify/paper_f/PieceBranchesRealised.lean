import OddPieceSelect

/-!
# Both branches of the disjunction are real, and the fence that called one of them a gap was wrong

`OddPieceSelect.exists_odd_path_or_cycle_piece` returns a piece that is **a path graph or a cycle
graph**, and its header fenced the disjunction like this:

> **NOTHING SAYS THE ODD PIECE IS A PATH RATHER THAN A CYCLE.** … **ruling out the cycle case would
> need the ray's crossings of a cycle piece to be even** … **This is a real gap and not a
> formality.**

**Both halves of that are wrong** (`ERRATUM 473`). The premise is false —
`DualUnique.exists_circuit_surrounding` exhibits a **cycle** piece crossed an **odd** number of
times, which is the enclosure step working exactly as intended — and so the "gap" is not a gap: the
cycle branch is the **normal** case, and under a `+` boundary it is the **only** case, every piece
of the decomposition being a circuit.

**This file proves both branches are inhabited**, which is what the fence should have asked for.

## What is proved

**`cycle_branch_realised`** — **the cycle branch fires, on a named configuration.**
`DualGraph.sigmaPlus` is down at one interior site of the `4 × 4` box and up everywhere else, and
`plusBoundary_sigmaPlus` says its boundary is untouched; `exists_circuit_surrounding` then hands
back a **cycle** piece crossed oddly. So `exists_odd_path_or_cycle_piece`'s right disjunct is not
decorative.

**`exists_path_piece_of_not_evenDegrees`** — **and the path branch is forced whenever the graph has
an odd degree**: if every piece of an edge-disjoint decomposition were a cycle graph then the whole
would have even degrees (`CycleDecomposition.evenDegrees_of_cycle_decomposition`), so a graph that
does not must have a path piece in **every** such decomposition. Not an example — a criterion, and
the one `DualDegreeExact.evenDegrees_dualGraph_iff` decides for a dual graph.

## What is NOT here

**NO CONFIGURATION IS EXHIBITED WITH AN ODD DUAL DEGREE.** `exists_path_piece_of_not_evenDegrees` is
a criterion and **is not instantiated**; the estate's two candidates go the other way —
`DualGraph.evenDegrees_dualGraph` makes every `+` configuration even, and `ExtendedDual`'s own
witness `cornerDown` **passes** the even-degree test (`cornerDown_evenDegrees`), the corner
plaquette having **two** broken outward sides rather than one. So **the path branch is shown
FORCED-IF, not shown to FIRE**, and finding a configuration that fires it is left open. **Not
attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING IS SAID ABOUT WHICH PIECE THE RAY CROSSES ODDLY.** `cycle_branch_realised` produces a
cycle crossed oddly; it does **not** say every odd piece there is a cycle, though under `+` that is
true for the trivial reason that every piece is.

**W3 DOES NOT MOVE.** A disjunction is shown non-vacuous on one side and conditional on the other.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `exists_path_piece_of_not_evenDegrees`
takes **`Finite` and nothing else** — no lattice, no configuration, no boundary condition; it is a
statement about arbitrary finite graphs. `cycle_branch_realised` takes **nothing at all**, being
about one named configuration.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace PieceBranchesRealised

open IsingFiniteVolume IsingContourClosed IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique SimpleGraph

/-! ## 1. The cycle branch fires, on a named configuration -/

/-- **THE CYCLE BRANCH IS NOT DECORATIVE.** On `sigmaPlus` — down at one interior site of the
`4 × 4` box — a **cycle** piece of the dual decomposition is crossed an **odd** number of times. -/
theorem cycle_branch_realised :
    ∃ (L : List (SimpleGraph (Plaq 4))) (w : (IsingContourSeparation.latticeGraph 4).Walk
        ((1 : Fin 4), (1 : Fin 4)) (SurroundsParity.origin (by omega)))
      (H : SimpleGraph (Plaq 4)),
      (∀ K ∈ L, IsCycleGraph K) ∧ L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = dualGraph sigmaPlus ∧ H ∈ L ∧
        ¬ Even (crossings (bonds sigmaPlus H) w) :=
  exists_circuit_surrounding plusBoundary_sigmaPlus (by omega) (by decide)

/-! ## 2. And the path branch is forced whenever a degree is odd -/

/-- **A GRAPH WITH AN ODD DEGREE HAS A PATH PIECE IN EVERY DECOMPOSITION.** If every piece were a
cycle the whole would have even degrees. A criterion, not an example. -/
theorem exists_path_piece_of_not_evenDegrees {V : Type*} [Finite V] {G : SimpleGraph V}
    (hodd : ¬ EvenDegrees G) {L : List (SimpleGraph V)}
    (hkind : ∀ K ∈ L, IsPathGraph K ∨ IsCycleGraph K) (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ⊔ ·) ⊥ = G) :
    ∃ K ∈ L, IsPathGraph K := by
  by_contra hcon
  have hall : ∀ K ∈ L, IsCycleGraph K := by
    intro K hK
    rcases hkind K hK with h | h
    · exact absurd (show ∃ K ∈ L, IsPathGraph K from ⟨K, hK, h⟩) hcon
    · exact h
  exact hodd (evenDegrees_of_cycle_decomposition hall hp hsup)

end PieceBranchesRealised
