import DualGraph
import SurroundsParity

/-!
# From dual edges back to primal bonds, and the covering half

`SurroundsParity` proves Peierls' enclosure step for an arbitrary disjoint decomposition
of the contour into **bond sets**. `DualGraph` produces the decomposition, but as
**circuits in the dual** — lists of `SimpleGraph (Plaq n)`. This file is the map between
them, and it delivers one of the two facts that join the two theorems.

## What is proved

* `PlaquetteLattice.exists_side_eq` — **every bond of the box is a side of some
  plaquette.** Unconditionally: a bond at the far edge is not the *left* side of a
  plaquette but it is the *right* side of the one before it, and one of the two always
  exists because a bond existing at all forces `2 ≤ n`. No interiority hypothesis and no
  boundary condition.
* `DualBonds.bonds` — the primal bonds crossed by the dual edges of a subgraph, as a
  subset of the contour.
* `DualBonds.bonds_dualGraph` — **the whole dual graph's bonds are exactly the contour**,
  under `+` boundary conditions. That is the covering half.

## What is not proved, and it is the other half

**Disjointness.** Two edge-disjoint dual subgraphs should cross disjoint sets of primal
bonds, and that needs a fact this estate does not have: *a bond is the side of at most two
plaquettes, and those two are partners across it*. `PlaquetteLattice` proves the four
sides of **one** plaquette are distinct and that partners share a side; it does not
exclude a third plaquette having the same bond as a side. The missing statement is

> `sideOf P d = sideOf P' d' → (P' = P ∧ d' = d) ∨ (P' = partnerOf P d ∧ d' = opp d)`

which is a case analysis on `Sym2` equalities over `Fin`-coordinates. Until it exists,
`SurroundsParity.odd_countP_iff_down` cannot be fed the circuits from
`DualGraph.exists_dual_cycle_decomposition`, because its hypothesis is that the pieces are
pairwise disjoint. **That single lemma is the whole remaining distance**, and it is named
here so the next attempt starts at it.

`IsingBoundaryField.MagnetisationBound` is untouched, and the `3 ^ |γ|` count is not
begun.
-/

namespace PlaquetteLattice

open IsingFiniteVolume IsingContourPlaquette

variable {n : ℕ}

/-! ## 1. Every bond of the box is a side of a plaquette

Four cases, and the arithmetic of each is the same shape: the plaquette on one side of
the bond exists, or the one on the other side does, and both cannot fail at once because
that would force the box to have a single row. -/

/-- **Every bond of the box is a side of some plaquette.** No hypothesis beyond the bond
existing — which already forces the box to be at least `2 × 2`. -/
theorem exists_side_eq {p q : Site n} (h : adj p q) :
    (∃ P : Plaq n, sideL P = s(p, q)) ∨ (∃ P : Plaq n, sideU P = s(p, q)) ∨
      (∃ P : Plaq n, sideR P = s(p, q)) ∨ (∃ P : Plaq n, sideD P = s(p, q)) := by
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  simp only [adj, Fin.ext_iff] at h
  rcases h with ⟨hfst, hsnd⟩ | ⟨hsnd, hfst⟩
  · -- same first coordinate: a vertical bond, so a left side or a right side
    rcases hsnd with h1 | h1
    · by_cases hi : p.1.val + 1 < n
      · refine Or.inl ⟨⟨p.1.val, p.2.val, hi, by omega⟩, ?_⟩
        simp only [sideL, bl, tl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [true_and]
        all_goals omega
      · refine Or.inr (Or.inr (Or.inl ⟨⟨p.1.val - 1, p.2.val, by omega, by omega⟩, ?_⟩))
        simp only [sideR, tr, br, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [and_true]
        all_goals omega
    · by_cases hi : p.1.val + 1 < n
      · refine Or.inl ⟨⟨p.1.val, q.2.val, hi, by omega⟩, ?_⟩
        simp only [sideL, bl, tl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [true_and, and_true]
        all_goals omega
      · refine Or.inr (Or.inr (Or.inl ⟨⟨p.1.val - 1, q.2.val, by omega, by omega⟩, ?_⟩))
        simp only [sideR, tr, br, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [and_true]
        all_goals omega
  · -- same second coordinate: a horizontal bond, so a bottom side or a top side
    rcases hfst with h1 | h1
    · by_cases hj : p.2.val + 1 < n
      · refine Or.inr (Or.inr (Or.inr ⟨⟨p.1.val, p.2.val, by omega, hj⟩, ?_⟩))
        simp only [sideD, br, bl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [and_true]
        all_goals omega
      · refine Or.inr (Or.inl ⟨⟨p.1.val, p.2.val - 1, by omega, by omega⟩, ?_⟩)
        simp only [sideU, tl, tr, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [true_and]
        all_goals omega
    · by_cases hj : p.2.val + 1 < n
      · refine Or.inr (Or.inr (Or.inr ⟨⟨q.1.val, p.2.val, by omega, hj⟩, ?_⟩))
        simp only [sideD, br, bl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [true_and, and_true]
        all_goals omega
      · refine Or.inr (Or.inl ⟨⟨q.1.val, p.2.val - 1, by omega, by omega⟩, ?_⟩)
        simp only [sideU, tl, tr, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff]
        simp only [true_and]
        all_goals omega

end PlaquetteLattice

namespace DualBonds

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph SimpleGraph


variable {n : ℕ}

/- The predicate defining `bonds` quantifies over `Plaq n`, whose `Fintype` instance is
itself noncomputable, and over the adjacency of an arbitrary subgraph. There is no
decidable instance to state instead, so the classical one is the honest choice rather
than a shortcut and the linter's advice does not apply here. -/
set_option linter.style.openClassical false
open scoped Classical

/-! ## 2. The bonds a dual subgraph crosses -/

/-- The primal bonds crossed by the dual edges of `H`. Defined as a subset of the contour,
so that the containment in one direction is free and only the covering has content. -/
noncomputable def bonds (σ : Config n) (H : SimpleGraph (Plaq n)) : Finset (Sym2 (Site n)) :=
  (contour σ).filter fun e => ∃ (P : Plaq n) (d : Fin 4), H.Adj P (partnerOf P d) ∧
    sideOf P d = e

theorem bonds_subset (σ : Config n) (H : SimpleGraph (Plaq n)) : bonds σ H ⊆ contour σ :=
  Finset.filter_subset _ _

theorem mem_bonds {σ : Config n} {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)} :
    e ∈ bonds σ H ↔ e ∈ contour σ ∧
      ∃ (P : Plaq n) (d : Fin 4), H.Adj P (partnerOf P d) ∧ sideOf P d = e := by
  simp [bonds]

theorem bonds_mono {σ : Config n} {H K : SimpleGraph (Plaq n)} (h : H ≤ K) :
    bonds σ H ⊆ bonds σ K := by
  intro e he
  rw [mem_bonds] at he ⊢
  obtain ⟨hc, P, d, hadj, hside⟩ := he
  exact ⟨hc, P, d, h hadj, hside⟩

/-! ## 3. The covering half

Every broken bond is a side of some plaquette (§1), and under `+` boundary conditions a
broken side is never outward-facing, so its partner is a genuine second plaquette and the
dual edge exists. -/

/-- **Under `+` boundary conditions, the dual graph crosses exactly the contour.** -/
theorem bonds_dualGraph {σ : Config n} (hσ : PlusBoundary σ) :
    bonds σ (dualGraph σ) = contour σ := by
  refine Finset.Subset.antisymm (bonds_subset _ _) fun e he => ?_
  rw [mem_bonds]
  refine ⟨he, ?_⟩
  induction e using Sym2.ind with
  | _ p q =>
    have hadj : adj p q := ((mem_contour σ p q).mp he).1
    have key : ∀ (P : Plaq n) (d : Fin 4), sideOf P d = s(p, q) →
        ∃ (P' : Plaq n) (d' : Fin 4), (dualGraph σ).Adj P' (partnerOf P' d') ∧
          sideOf P' d' = s(p, q) := by
      intro P d hside
      have hmem : sideOf P d ∈ contour σ := hside ▸ he
      exact ⟨P, d, ⟨d, hmem, rfl, partnerOf_ne_of_mem hσ P d hmem⟩, hside⟩
    rcases exists_side_eq hadj with ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩
    · exact key P 0 hP
    · exact key P 1 hP
    · exact key P 2 hP
    · exact key P 3 hP

/-- Consequently the crossing count of the whole dual graph is the crossing count of the
contour — the statement `SurroundsParity` will consume once the pieces are known
disjoint. -/
theorem crossings_bonds_dualGraph {σ : Config n} (hσ : PlusBoundary σ) {x b : Site n}
    (w : (latticeGraph n).Walk x b) :
    IsingContourClosed.crossings (bonds σ (dualGraph σ)) w =
      IsingContourClosed.crossings (contour σ) w := by
  rw [bonds_dualGraph hσ]

/-- And the enclosure step, phrased against the dual graph as a whole: under `+` boundary
conditions, a walk from a down site to the corner crosses the dual graph's bonds an odd
number of times. The step from here to *circuits* is the disjointness lemma named in the
header. -/
theorem odd_crossings_bonds_of_down {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = false)
    (w : (latticeGraph n).Walk x (SurroundsParity.origin hn)) :
    ¬ Even (IsingContourClosed.crossings (bonds σ (dualGraph σ)) w) := by
  rw [crossings_bonds_dualGraph hσ]
  exact (SurroundsParity.odd_crossings_iff_down hσ
    (SurroundsParity.isBoundary_origin hn) w).mpr hx

end DualBonds
