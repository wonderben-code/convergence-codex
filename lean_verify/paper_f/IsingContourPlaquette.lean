/-
  IsingContourPlaquette.lean — the local form of closedness, and the first
  place the box being two-dimensional is used for anything.

  WHY. `IsingContourClosed` proved closedness globally: every cycle of the
  box crosses the contour evenly. The dual-lattice argument uses the LOCAL
  form — every dual vertex has even degree — which on the square lattice
  means **every unit square has an even number of broken bonds on its four
  sides**. That is one application of the global theorem to one particular
  4-cycle, and it needs no dual lattice.

  **AND IT IS THE FIRST TIME IN THIS STAIRCASE THAT THE BOX BEING A SQUARE
  LATTICE IS USED FOR ANYTHING.** Every theorem in the six preceding units
  is about a connected graph: the energy identity, separation, the ground
  states, the Gibbs mode, the reindexing, closedness and the cocycle
  characterisation would all read the same on any connected graph, with
  bipartiteness needed only for the chessboard witnesses. §3 records the
  file-by-file check of that claim rather than asserting it.

  WHAT THIS FILE PROVES:
  1. **`even_four_cycle`** — any 4-cycle in the box crosses the contour
     evenly, and `four_cycle_ne_three`: never exactly three.
  2. **`even_plaquette`** — the unit square at `(i, j)` is such a 4-cycle,
     so it has an even number of broken bonds; `plaquette_ne_three` is the
     form the dual-lattice argument consumes (no T-junction, no loose end
     inside a square).

  WHAT THIS DOES NOT DO. It is one corollary, and it does not decompose
  anything. **The step it is aiming at — an even-degree edge set breaks into
  circuits — is Euler's theorem, and Mathlib does not have the direction
  that would give it.** `SimpleGraph.Walk.IsEulerian` proves only that an
  Eulerian trail forces even degrees; the module's own TODO reads "Prove
  that there exists an Eulerian trail when the conclusion to
  `IsEulerian.card_odd_degree` holds". Checked 9 August 2026. So the circuit
  decomposition needs a general graph theorem written first, and that is
  recorded in `UNLOCK_WATCHLIST.md` as an upstreaming candidate rather than
  attempted here. No `3^{|γ|}`, no "surrounds", no dual lattice.
  **`IsingBoundaryField.MagnetisationBound` untouched.**

  AMENDED 2026-08-10 (`11eda2a`, `2ae6338`). **THE GENERAL GRAPH THEOREM IS
  NOW WRITTEN**, so the paragraph above is out of date in its reason though
  not in its conclusion. `EvenDegreeCycle` proves that an even-degree graph
  with an edge contains a cycle, and `CycleDecomposition` runs that as an
  induction to
  `SimpleGraph.evenDegrees_iff_exists_cycle_decomposition` — all degrees
  even EXACTLY WHEN the edges are an edge-disjoint union of cycles, for any
  finite simple graph. Neither goes near `IsEulerian`; the route is
  `IsAcyclic.isTree_connectedComponent`.

  **AND IT DOES NOT APPLY HERE, WHICH IS THE PART WORTH READING.**
  `ContourCircuits.not_evenDegrees_brokenGraph_sigmaOdd` exhibits a
  configuration on the 3×3 box — down at the centre, up elsewhere — whose
  broken-bond graph has a site of degree ONE. The primal contour is a CUT,
  and cuts do not have even degrees; the evenness the textbook uses is a
  DUAL-lattice statement, and this estate has no dual lattice. So the
  blocker moved from "the general theorem does not exist" to "there is no
  dual lattice", which is a different and more specific piece of work.
  `ContourCircuits` carries the conditional corollary
  (`contour_decomposes_of_evenDegrees`) so that the moment a dual exists the
  decomposition is one line. **`MagnetisationBound` still untouched, and
  "surrounds" and `3^{|γ|}` are exactly where they were.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourCocycle

namespace IsingContourPlaquette

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourClosed

variable {n : ℕ}

/-! ## 1. Any 4-cycle crosses the contour evenly

Stated for an arbitrary 4-cycle first. The unit square is then one instance,
and keeping them apart is what makes the `Fin` bookkeeping of §2 a separate,
checkable thing rather than something tangled into the parity argument.
-/

/-- **Any 4-cycle in the box crosses the contour an even number of times.**
    One application of `IsingContourClosed.even_crossings_closed`. -/
theorem even_four_cycle (σ : Config n) {a b c d : Site n}
    (h1 : adj a b) (h2 : adj b c) (h3 : adj c d) (h4 : adj d a) :
    Even ((if s(a, b) ∈ contour σ then 1 else 0)
        + (if s(b, c) ∈ contour σ then 1 else 0)
        + (if s(c, d) ∈ contour σ then 1 else 0)
        + (if s(d, a) ∈ contour σ then 1 else 0)) := by
  set w : (latticeGraph n).Walk a a :=
    SimpleGraph.Walk.cons (show (latticeGraph n).Adj a b from h1)
      (SimpleGraph.Walk.cons (show (latticeGraph n).Adj b c from h2)
        (SimpleGraph.Walk.cons (show (latticeGraph n).Adj c d from h3)
          (SimpleGraph.Walk.cons (show (latticeGraph n).Adj d a from h4)
            SimpleGraph.Walk.nil))) with hwdef
  have hc : crossings (contour σ) w
      = (if s(a, b) ∈ contour σ then 1 else 0)
        + (if s(b, c) ∈ contour σ then 1 else 0)
        + (if s(c, d) ∈ contour σ then 1 else 0)
        + (if s(d, a) ∈ contour σ then 1 else 0) := by
    rw [hwdef, crossings_cons, crossings_cons, crossings_cons, crossings_cons,
      crossings_nil]
    omega
  rw [← hc]
  exact even_crossings_closed σ w

/-- **So a 4-cycle never carries exactly three broken bonds.** This is the
    form the dual-lattice argument consumes: no T-junction and no loose end
    inside a square. Stated separately because "even" is the proof and "not
    three" is the use. -/
theorem four_cycle_ne_three (σ : Config n) {a b c d : Site n}
    (h1 : adj a b) (h2 : adj b c) (h3 : adj c d) (h4 : adj d a) :
    (if s(a, b) ∈ contour σ then 1 else 0)
      + (if s(b, c) ∈ contour σ then 1 else 0)
      + (if s(c, d) ∈ contour σ then 1 else 0)
      + (if s(d, a) ∈ contour σ then 1 else 0) ≠ 3 := by
  intro h
  have hev := even_four_cycle σ h1 h2 h3 h4
  rw [h] at hev
  exact (by decide : ¬ Even 3) hev

/-! ## 2. The unit square is a 4-cycle

The only place in this staircase where the box being a SQUARE LATTICE is
used for anything. §3 says what that means.
-/

/-- Bottom-left corner of the unit square at `(i, j)`. -/
def bl (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) : Site n := (⟨i, by omega⟩, ⟨j, by omega⟩)
/-- Top-left corner. -/
def tl (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) : Site n := (⟨i, by omega⟩, ⟨j + 1, hj⟩)
/-- Top-right corner. -/
def tr (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) : Site n := (⟨i + 1, hi⟩, ⟨j + 1, hj⟩)
/-- Bottom-right corner. -/
def br (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) : Site n := (⟨i + 1, hi⟩, ⟨j, by omega⟩)

theorem adj_bl_tl (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    adj (bl i j hi hj) (tl i j hi hj) := Or.inl ⟨rfl, Or.inl rfl⟩

theorem adj_tl_tr (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    adj (tl i j hi hj) (tr i j hi hj) := Or.inr ⟨rfl, Or.inl rfl⟩

theorem adj_tr_br (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    adj (tr i j hi hj) (br i j hi hj) := Or.inl ⟨rfl, Or.inr rfl⟩

theorem adj_br_bl (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    adj (br i j hi hj) (bl i j hi hj) := Or.inr ⟨rfl, Or.inr rfl⟩

/-- **EVERY UNIT SQUARE HAS AN EVEN NUMBER OF BROKEN BONDS.** The local form
    of closedness — the dual-lattice statement "every dual vertex has even
    degree", said on the original lattice with no dual lattice in sight. -/
theorem even_plaquette (σ : Config n) (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    Even ((if s(bl i j hi hj, tl i j hi hj) ∈ contour σ then 1 else 0)
        + (if s(tl i j hi hj, tr i j hi hj) ∈ contour σ then 1 else 0)
        + (if s(tr i j hi hj, br i j hi hj) ∈ contour σ then 1 else 0)
        + (if s(br i j hi hj, bl i j hi hj) ∈ contour σ then 1 else 0)) :=
  even_four_cycle σ (adj_bl_tl i j hi hj) (adj_tl_tr i j hi hj)
    (adj_tr_br i j hi hj) (adj_br_bl i j hi hj)

theorem plaquette_ne_three (σ : Config n) (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) :
    (if s(bl i j hi hj, tl i j hi hj) ∈ contour σ then 1 else 0)
      + (if s(tl i j hi hj, tr i j hi hj) ∈ contour σ then 1 else 0)
      + (if s(tr i j hi hj, br i j hi hj) ∈ contour σ then 1 else 0)
      + (if s(br i j hi hj, bl i j hi hj) ∈ contour σ then 1 else 0) ≠ 3 :=
  four_cycle_ne_three σ (adj_bl_tl i j hi hj) (adj_tl_tr i j hi hj)
    (adj_tr_br i j hi hj) (adj_br_bl i j hi hj)

/-! ## 3. Where the two-dimensionality actually enters

This section is a claim about the six preceding files, so it was checked
against them rather than remembered — ERRATUM 58 fired six times on the day
they were written, and every instance was a sentence of exactly this kind.

**`IsingContourEnergy`** — `brokenCount`, `brokenGraph`, `contour`, the
energy identity, the ground-state bound, `bondCount`, the forcing theorems.
These go through `adj_symm`, `adj_irrefl` and `spin` only. The `pq.1`/`pq.2`
that appear are projections of an ORDERED PAIR OF SITES in a filter, not
coordinates of a site. **One exception, stated precisely because the loose
version would be wrong**: `chess_ne_of_adj` does read the coordinates, as
`(p.1.val + p.2.val) % 2`. What it uses them FOR is a 2-colouring — the
square lattice is bipartite and the coordinate sum exhibits the bipartition.
Any bipartite graph with a named 2-colouring would do; the coordinates are
how this one is named, not what the argument needs.

**`IsingContourSeparation`** — `agreeGraph`, walk induction, separation, the
ground-state characterisation. Connectivity only. The one place the square
lattice appears is `reachable_snd_zero`/`reachable_fst_zero`, which walk the
two coordinates down to zero — and that is a proof that the box IS
connected, not a use of its shape.

**`IsingContourGibbs`**, **`IsingContourInvariant`**, **`IsingContourClosed`**,
**`IsingContourCocycle`** — monotonicity of `exp`, a fibre count, a walk
induction, a path-parity construction. All four are statements about a
connected graph.

**So the honest description of this staircase is: seven units of GRAPH
THEORY, and the planar geometry has not started.** `even_plaquette` above is
the first theorem whose statement mentions a square, and it is a corollary
rather than a step. What remains — circuits, "surrounds", `3^{|γ|}` — is
exactly the part that needs the plane, and none of the work so far has made
it smaller. That is not a discouraging reading; it is a precise one, and it
says where a next attempt should be aimed.

**A caveat on this section, because it is an inspection and not a theorem.**
Nothing here is machine-checked. The claim "these proofs would work on any
connected graph" is not formalised — doing that would mean restating the
files over an abstract `SimpleGraph` and rechecking, which is a refactor and
not a proof. What IS checked is narrower and is what the paragraphs above
say: no proof in those files invokes planarity, and the square structure is
used only to establish connectivity and bipartiteness.

## Review round 70 — the ways this could be hollow

**"`even_plaquette` could be a restatement with no content."** It is a
corollary and the header says so. Its content is entirely in WHICH cycle it
picks: the 4-cycle around a unit square is the one the dual-lattice argument
uses, and `plaquette_ne_three` is the consequence in the form that argument
consumes. A corollary that names the right instance is worth stating; this
one is not claimed to be more.

**"The `Fin` bookkeeping could hide an off-by-one."** The four adjacency
witnesses are each a single constructor application against
`IsingFiniteVolume.adj`'s definition, with no arithmetic: `Or.inl ⟨rfl, Or.inl rfl⟩`
and its three variants. If a corner were wrong the term would not typecheck.

**"§3 could be the seventh ERRATUM-58 instance."** It is the most likely
candidate in this file, which is why it carries its own caveat naming what
is and is not checked. It is an inspection, it is labelled as one, and the
thing it asserts — that no proof in those files invokes planarity — is
decidable by reading them, which is what was done.
-/

end IsingContourPlaquette
