import MinimumContour
import DualPathCount

/-!
# Why the outer face cannot be one vertex, stated as a theorem rather than as a difficulty

`DualPathCount` leaves S3b-ii as a **covering** statement: a down cluster reaching the edge of
the box should contain a dual walk running to that edge. The natural proof is the one the
interior case uses — every plaquette carries an even number of broken sides
(`IsingContourPlaquette.even_plaquette`, which needs no hypothesis at all), so the dual graph
of broken bonds has even degrees and decomposes into circuits
(`DualGraph.exists_dual_cycle_decomposition`). To get **open** walks instead of circuits, add a
vertex for the outer face and read a circuit through it as a path between two edge plaquettes.

**That repair does not typecheck, and this file says why in the estate's own terms.**

## The obstruction

A side of a plaquette faces the outer face exactly when the plaquette on its far side does not
exist — `leftPlaq` requires `P.i ≠ 0`, `downPlaq` requires `P.j ≠ 0`, and so on. The corner
plaquette has `i = 0` **and** `j = 0`, so **two** of its sides face the outer face, and they
are distinct (`PlaquetteLattice.sideL_ne_sideD`). That is `exists_two_outer_sides`.

And both can be broken at once: `MinimumContour.cornerDown` — the configuration that is down at
the corner and up everywhere else, whose contour has exactly two bonds — breaks precisely those
two (`cornerDown_sideL_mem`, `cornerDown_sideD_mem`). So a single outer-face vertex would have
to carry **two distinct edges to one plaquette**, which `SimpleGraph` cannot express, and the
degree it would report is `1` where the parity argument needs `2`.

## What this locates

`PlaquetteLattice.sideL_notMem_contour` and its three siblings say that under `PlusBoundary` an
outer side is **never** broken. That is not a convenience: it is exactly what makes the outer
face invisible, and it is why the interior chain never needed a vertex for it. The `+`
hypothesis and this obstruction are the same fact seen from two sides.

## What is not attempted

The natural repair is **four** outer vertices, one per edge of the box, which is enough for
simplicity — a plaquette meets each edge of the box in at most one side. Whether the parity
bookkeeping then closes is **not settled here and not attempted**: the degree of each of the
four is the number of sign changes along one edge of the box, which is not even in general,
and what an Eulerian decomposition with odd vertices delivers is cycles plus paths between
them — a coarser object than one path per cluster. **Recorded as not attempted, not as
blocked** (`ERRATUM 71` addendum 3): no failed construction was observed, only a sketch that
does not obviously close.

⚠ **IT WAS ATTEMPTED THE SAME DAY, BY THE FILE THAT IMPORTS THIS ONE, AND THIS PARAGRAPH IS
KEPT AS WRITTEN** (`ERRATUM 94`, `ERRATUM 471`, annotated 2026-09-06). `ExtendedDual` builds
exactly the four-vertex repair described above — the outer face indexed by **direction**,
`Plaq n ⊕ Fin 4` — and proves `evenDegrees_plaq`, every plaquette of even degree with **no
hypothesis on the configuration**. **And this paragraph's prediction became a theorem there**:
the rim degrees are not even, `ExtendedDual.not_evenDegrees_extDual`, with `cornerDown` giving
two rim vertices of degree one. What is still missing is what this paragraph names last — a
decomposition into circuits **plus paths between the odd vertices** — which is absent from
this estate and is an open to-do item in Mathlib's own `Trails.lean`. `OddVertexAugment`
(2026-09-06) supplies the step before it: adjoining one vertex joined to the odd-degree
vertices makes every degree even, for any finite graph. **`WALLS.md` recorded this
supersession on 2026-08-12 and this file was never annotated**, which is what `ERRATUM 471` is
about.

Nothing here touches the Ising measure. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace OuterFaceObstruction

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open DualObstruction MinimumContour

variable {n : ℕ}

/-! ## 1. Facing the outer face -/

/-- The left side of `P` faces the outer face: there is no plaquette to its left, which is
precisely the condition under which `PlaquetteLattice.leftPlaq` is not defined. -/
def OuterL (P : Plaq n) : Prop := P.i = 0

/-- The bottom side of `P` faces the outer face — no plaquette below it. -/
def OuterD (P : Plaq n) : Prop := P.j = 0

/-- The corner plaquette, which exists as soon as the box has a plaquette at all. -/
def cornerPlaq (hn : 1 < n) : Plaq n := ⟨0, 0, by omega, by omega⟩

theorem cornerPlaq_outerL (hn : 1 < n) : OuterL (cornerPlaq hn) := rfl

theorem cornerPlaq_outerD (hn : 1 < n) : OuterD (cornerPlaq hn) := rfl

/-- **A PLAQUETTE CAN FACE THE OUTER FACE TWICE.** The corner has no plaquette to its left and
none below, and those two sides are distinct — so any single vertex standing for the outer
face would need two edges to this one plaquette. -/
theorem exists_two_outer_sides (hn : 1 < n) :
    ∃ P : Plaq n, OuterL P ∧ OuterD P ∧ sideL P ≠ sideD P :=
  ⟨cornerPlaq hn, cornerPlaq_outerL hn, cornerPlaq_outerD hn,
    sideL_ne_sideD (cornerPlaq hn)⟩

/-! ## 2. And both can be broken at once -/

theorem cornerDown_sideL_mem (hn : 1 < n) :
    sideL (cornerPlaq hn) ∈ contour (cornerDown n) := by
  refine (mem_contour _ _ _).mpr ⟨adj_sideL (cornerPlaq hn), ?_⟩
  simp [cornerPlaq, bl, tl, MinimumContour.cornerDown]

theorem cornerDown_sideD_mem (hn : 1 < n) :
    sideD (cornerPlaq hn) ∈ contour (cornerDown n) := by
  refine (mem_contour _ _ _).mpr ⟨adj_sideD (cornerPlaq hn), ?_⟩
  simp [cornerPlaq, br, bl, MinimumContour.cornerDown]

/-- **THE OBSTRUCTION, EXHIBITED.** For the corner-flip configuration, the corner plaquette's
two outer sides are **both** broken and are **distinct** — and by
`MinimumContour.card_contour_cornerDown` they are the whole contour.

So a dual graph with one vertex for the outer face would record a single edge where the
even-degree bookkeeping needs two, and the circuit decomposition that the interior Peierls
chain rests on has nothing to say here. Compare `PlaquetteLattice.sideL_notMem_contour`: under
`PlusBoundary` an outer side is never broken, which is why the interior chain never met this. -/
theorem cornerDown_two_outer_broken (hn : 1 < n) :
    ∃ P : Plaq n, OuterL P ∧ OuterD P ∧ sideL P ≠ sideD P ∧
      sideL P ∈ contour (cornerDown n) ∧ sideD P ∈ contour (cornerDown n) ∧
      (contour (cornerDown n)).card = 2 :=
  ⟨cornerPlaq hn, cornerPlaq_outerL hn, cornerPlaq_outerD hn, sideL_ne_sideD (cornerPlaq hn),
    cornerDown_sideL_mem hn, cornerDown_sideD_mem hn, card_contour_cornerDown hn⟩

/-- And the contour is **exactly** those two sides, so the whole of this configuration's
contour lives on the outer face. There is no circuit in it at all
(`MinimumContour.two_le_card_contour` gives the minimum, and a dual circuit needs four sides),
which is the sharpest form of the statement that the interior chain cannot reach here. -/
theorem contour_cornerDown_eq (hn : 1 < n) :
    contour (cornerDown n) = {sideL (cornerPlaq hn), sideD (cornerPlaq hn)} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact cornerDown_sideL_mem hn
    · rw [Finset.mem_singleton.mp he']
      exact cornerDown_sideD_mem hn
  · rw [card_contour_cornerDown hn, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact sideL_ne_sideD (cornerPlaq hn)), Finset.card_singleton]

end OuterFaceObstruction
