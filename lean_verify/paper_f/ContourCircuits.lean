import IsingContourEnergy
import CycleDecomposition

/-!
# Pointing the circuit decomposition at this estate's contour

`CycleDecomposition` proves, for any finite simple graph, that all degrees even is
exactly the same as being an edge-disjoint union of cycles. Two files already in
this estate say, in their own headers, that this is the step the Peierls argument
needs next and that it is not available: `IsingContourPlaquette` says it is Euler's
theorem and that **"Mathlib does not have the direction that would give it"**, so it
"needs a general graph theorem written first"; `IsingContourClosed` says the weaker
thing, that "a `Finset` of bonds with the cocycle property has not been cut into an
explicit list of circuits, and Peierls counts circuits". The general theorem is now
written. This file is the check that writing it was enough, and the answer is *no,
and for a reason worth recording*.

## What is now immediate

`IsingContourEnergy.brokenGraph` is a genuine `SimpleGraph (Site n)` — the estate
built it that way on purpose — so `CycleDecomposition` applies to it with no
adaptation at all. `contour_decomposes_of_evenDegrees` is that corollary and its
proof is one line.

## What is not

**Its hypothesis is not free, and `not_evenDegrees_brokenGraph_sigmaOdd` proves
that rather than asserting it**: on the 3×3 box, the configuration that is down at
the centre and up everywhere else has a site with exactly one broken bond. Odd. So
"the contour decomposes into circuits" is *not* a theorem about every configuration
of this model, and no amount of graph theory will make it one.

That is exactly the step the textbook takes in the **dual** lattice — as
`IsingContourClosed`'s own header records, the textbook sentence is "every dual
vertex has even degree, so the contour decomposes into circuits". This estate has no
dual lattice and has deliberately not built one; what it has instead is closedness
in the primal (`IsingContourClosed.even_crossings_closed`), which is a statement
about *crossings of cycles* and not about *degrees*. The two are not the same
statement, and the witness below shows the primal one does not imply even degrees.

**So the blocker changed rather than went away.** Before today it was "the general
graph theorem does not exist". It is now "the estate has no dual lattice", which is
a different and much more specific piece of work.

## And the hypothesis is not empty either

`evenDegrees_brokenGraph_chess` exhibits a configuration where it does hold and the
conclusion is not vacuous: the chessboard on the 2×2 box breaks every one of its
four bonds, every site has degree two, and the decomposition returns a **nonempty**
list of circuits. How many, and which, is not claimed — only that the list is not
empty. Both witnesses are decided by the kernel.

## Main results

* `SimpleGraph.edgeSet_foldr_sup` — the edge set of a decomposition is the union of
  the pieces' edge sets, so a decomposition of the graph *is* a decomposition of the
  contour, which is what `contour` literally is.
* `ContourCircuits.contour_decomposes_of_evenDegrees` — the corollary, conditional.
* `ContourCircuits.not_evenDegrees_brokenGraph_sigmaOdd` — the hypothesis can fail.
* `ContourCircuits.evenDegrees_brokenGraph_chess` — and it can hold, non-vacuously.


## ⚠ "HAS DELIBERATELY NOT BUILT ONE" WAS FALSE THIRTY-SEVEN MINUTES LATER. Annotated 1 Sep 2026

Kept as written (`ERRATUM 94`), and the interval is the point. This header says *"This estate has no
dual lattice and has deliberately not built one"* at **2026-08-10 15:25**.
`paper_f/DualGraph.lean` was committed at **16:02 the same day** — thirty-seven minutes — and its
commit message is *"the Peierls circuit decomposition, on the dual"*. `evenDegrees_dualGraph` plus
`exists_cycle_decomposition` are exactly the two steps this header describes as belonging to the
textbook's dual route; `ExtendedDual.evenDegrees_plaq` (2026-08-11) then drops the hypothesis.

**The witness below is unaffected and so is the conditional corollary**: the primal statement still
does not imply even degrees, which is why the dual was built. What fell is the sentence about what
the estate contains, written in the present tense about a gap that was closed the same afternoon.
`ERRATUM 389` is about that pattern.
-/

namespace SimpleGraph

variable {V : Type*}

/-- The edge set of an edge-disjoint (or not) union of graphs is the union of their
edge sets. Stated here rather than in `CycleDecomposition` because it is what turns
a decomposition of the broken-bond *graph* into a decomposition of the *contour*,
which is that graph's edge set. -/
theorem edgeSet_foldr_sup (L : List (SimpleGraph V)) :
    (L.foldr (· ⊔ ·) ⊥).edgeSet = ⋃ H ∈ L, H.edgeSet := by
  induction L with
  | nil => simp
  | cons K L ih => simp [ih]

end SimpleGraph

namespace ContourCircuits

open IsingFiniteVolume IsingContourEnergy SimpleGraph

variable {n : ℕ}

/-! ## 1. The corollary, in full

Nothing here is new mathematics. It is here because the point of
`IsingContourEnergy` building the contour as a `SimpleGraph` rather than as a
bespoke `Finset` was that Mathlib's graph API would apply to it "without further
work", and this is the first time that promise is cashed against a theorem the
estate did not already have. -/

/-- **If the broken-bond graph has all degrees even, the contour is an
edge-disjoint union of circuits.** Immediate from
`SimpleGraph.exists_cycle_decomposition`; the content is entirely in the
hypothesis, which §2 shows is a real restriction. -/
theorem contour_decomposes_of_evenDegrees (σ : Config n)
    (h : EvenDegrees (brokenGraph σ)) :
    ∃ L : List (SimpleGraph (Site n)), (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = brokenGraph σ :=
  (brokenGraph σ).exists_cycle_decomposition h

/-- The same conclusion read on the contour itself — the set of broken bonds is the
union of the circuits' edge sets. `contour σ` is `(brokenGraph σ).edgeFinset`, so
this is the previous theorem plus `edgeSet_foldr_sup`. -/
theorem contour_edgeSet_decomposes_of_evenDegrees (σ : Config n)
    (h : EvenDegrees (brokenGraph σ)) :
    ∃ L : List (SimpleGraph (Site n)), (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ (brokenGraph σ).edgeSet = ⋃ H ∈ L, H.edgeSet := by
  obtain ⟨L, h1, h2, h3⟩ := contour_decomposes_of_evenDegrees σ h
  exact ⟨L, h1, h2, by rw [← h3, edgeSet_foldr_sup]⟩

/-- And it is a biconditional, inherited: the contour decomposes into circuits
exactly when the broken-bond graph has all degrees even. -/
theorem evenDegrees_iff_contour_decomposes (σ : Config n) :
    EvenDegrees (brokenGraph σ) ↔
      ∃ L : List (SimpleGraph (Site n)), (∀ H ∈ L, IsCycleGraph H) ∧
        L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = brokenGraph σ :=
  (brokenGraph σ).evenDegrees_iff_exists_cycle_decomposition

/-! ## 2. The hypothesis is a real restriction

The witness is the smallest interesting one: a single flipped site. Its four
neighbours each disagree with it and with nobody else, so each of them has exactly
one broken bond. One is odd, and that is the whole obstruction — in the primal. -/

/-- Down at the centre of the 3×3 box, up everywhere else. -/
def sigmaOdd : Config 3 := fun p => !(decide (p = ((1 : Fin 3), (1 : Fin 3))))

/-- A neighbour of the flipped site has exactly one broken bond. Decided. -/
theorem degree_brokenGraph_sigmaOdd :
    (brokenGraph sigmaOdd).degree ((0 : Fin 3), (1 : Fin 3)) = 1 := by decide

/-- **So the broken-bond graph of a perfectly ordinary configuration does NOT have
all degrees even**, and `contour_decomposes_of_evenDegrees` does not apply to it.
This is the primal/dual gap, exhibited rather than described. -/
theorem not_evenDegrees_brokenGraph_sigmaOdd : ¬ EvenDegrees (brokenGraph sigmaOdd) := by
  intro h
  have h1 : Even ((brokenGraph sigmaOdd).degree ((0 : Fin 3), (1 : Fin 3))) :=
    ((evenDegrees_iff_forall_even_degree (brokenGraph sigmaOdd)).mp h) _
  rw [degree_brokenGraph_sigmaOdd] at h1
  simp at h1

/-! ## 3. …and it is not empty

A configuration where the hypothesis holds, and where the conclusion says something:
the chessboard on the 2×2 box breaks all four of its bonds and every site has degree
two, so the decomposition returns a genuine circuit rather than the empty list. -/

/-- The chessboard configuration on the 2×2 box. -/
def chess : Config 2 := fun p => decide ((p.1.val + p.2.val) % 2 = 0)

theorem degree_brokenGraph_chess (p : Site 2) : (brokenGraph chess).degree p = 2 := by
  revert p; decide

/-- **The chessboard's broken-bond graph does have all degrees even.** -/
theorem evenDegrees_brokenGraph_chess : EvenDegrees (brokenGraph chess) := by
  rw [evenDegrees_iff_forall_even_degree]
  intro p
  rw [degree_brokenGraph_chess]
  exact even_two

/-- The chessboard's contour is not empty — all four bonds are broken. -/
theorem card_contour_chess : (contour chess).card = 4 := by decide

theorem brokenGraph_chess_ne_bot : brokenGraph chess ≠ ⊥ := by
  intro hEq
  have hadj : (brokenGraph chess).Adj ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) := by
    decide
  rw [hEq] at hadj
  exact hadj

/-- **So the decomposition is non-vacuous on this model**: there is a configuration
whose contour is a nonempty edge-disjoint union of circuits, produced by the general
theorem and not by hand. -/
theorem chess_decomposes_nonempty :
    ∃ L : List (SimpleGraph (Site 2)), L ≠ [] ∧ (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = brokenGraph chess :=
  (brokenGraph chess).exists_cycle_decomposition_ne_nil evenDegrees_brokenGraph_chess
    brokenGraph_chess_ne_bot

/-! ## 4. What is left, stated so it cannot be mistaken for progress

The decomposition is proved and it is pointed at this estate's own object. What it
needs — even degrees — is false for the primal contour of a general configuration,
and the textbook's route to evenness runs through the dual lattice, which this
estate does not have. Building it is a construction (plaquette centres, the
correspondence between a primal bond and the dual bond crossing it, and a proof that
the dual degree at a plaquette is the number of broken bonds on its four sides,
which `IsingContourPlaquette.even_plaquette` already shows is even).

**Even with the dual in hand, the wall does not fall.** `WALLS.md` W3 costs the
remaining work as contours of a given LENGTH SURROUNDING a fixed site, and the
`3 ^ |γ|` bound. "Surrounds" is not defined anywhere in this estate and nothing
here defines it. `IsingBoundaryField.MagnetisationBound` is untouched. -/

end ContourCircuits
