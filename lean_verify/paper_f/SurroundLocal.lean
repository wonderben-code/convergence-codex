import WalkCount

/-!
# A circuit that surrounds a site meets the walk to the boundary

`WalkCount` bounds how many circuits of a given length pass through a **fixed** plaquette.
To turn that into a bound on how many circuits surround a **fixed site**, one needs to
know that the circuits in question are not free to sit anywhere: they must be anchored
somewhere near the site. This file proves the first, and easiest, anchoring statement.

> If a circuit surrounds `x` — that is, if the walk from `x` to the corner crosses its
> bonds an odd number of times — then **one of its bonds is an edge of that walk**, and so
> one of its plaquettes has a side on the walk.

The proof is arithmetic: an odd count is a nonzero count, and a nonzero count means the
walk uses one of the bonds.

## What this gives, and what it does not

**Gives:** every surrounding circuit is anchored to the walk. Together with
`WalkCount.card_closed_walks_le` that bounds the surrounding circuits of length `L` by
(number of anchor plaquettes) × `4 ^ L`.

**Does not give the Peierls estimate**, and the gap is specific and worth stating rather
than glossing. The anchor set here is the whole walk from `x` to the corner, whose length
grows with the box; the textbook argument anchors instead within distance `L` of `x`,
because a circuit of length `L` surrounding `x` cannot reach further than that. **The
prefactor here therefore grows with `n` and the textbook's does not**, and a magnetisation
bound needs one that does not — so this is a rung and not the estimate.

**Also missing**, as before: the Gibbs weight of a circuit of length `L`, and the
summation over `L`. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SurroundLocal

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A nonzero crossing count means a shared bond -/

/-- A list with a nonzero `countP` has a member satisfying the predicate. Proved here
because `exact?` finds nothing for it in this Mathlib. -/
theorem exists_of_countP_ne_zero {α : Type*} (p : α → Bool) (l : List α)
    (h : l.countP p ≠ 0) : ∃ a ∈ l, p a := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.countP_cons] at h
    by_cases hp : p a
    · exact ⟨a, List.mem_cons_self .., hp⟩
    · simp only [hp, Bool.false_eq_true, if_false, Nat.add_zero] at h
      obtain ⟨b, hb, hpb⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem _ hb, hpb⟩

theorem exists_mem_edges_of_crossings_ne_zero {γ : Finset (Sym2 (Site n))} {x b : Site n}
    {w : (latticeGraph n).Walk x b} (h : crossings γ w ≠ 0) : ∃ e ∈ w.edges, e ∈ γ := by
  obtain ⟨e, he, hmem⟩ := exists_of_countP_ne_zero _ _ h
  exact ⟨e, he, by simpa using hmem⟩

theorem exists_mem_edges_of_odd {γ : Finset (Sym2 (Site n))} {x b : Site n}
    {w : (latticeGraph n).Walk x b} (h : ¬ Even (crossings γ w)) :
    ∃ e ∈ w.edges, e ∈ γ := by
  refine exists_mem_edges_of_crossings_ne_zero fun h0 => h ?_
  rw [h0]
  exact ⟨0, rfl⟩

/-! ## 2. So a surrounding circuit has a plaquette on the walk -/

/-- **A circuit that surrounds `x` shares a bond with the walk from `x` to the corner.** -/
theorem exists_bond_on_walk {σ : Config n} {H : SimpleGraph (Plaq n)} {x b : Site n}
    {w : (latticeGraph n).Walk x b} (h : ¬ Even (crossings (bonds σ H) w)) :
    ∃ e ∈ w.edges, e ∈ bonds σ H :=
  exists_mem_edges_of_odd h

/-- **And hence one of its plaquettes has a side on the walk.** This is the anchoring
statement: a surrounding circuit is not free to sit anywhere in the box. -/
theorem exists_plaq_on_walk {σ : Config n} {H : SimpleGraph (Plaq n)} {x b : Site n}
    {w : (latticeGraph n).Walk x b} (h : ¬ Even (crossings (bonds σ H) w)) :
    ∃ (P : Plaq n) (d : Fin 4), H.Adj P (partnerOf P d) ∧ sideOf P d ∈ w.edges := by
  obtain ⟨e, hew, heb⟩ := exists_bond_on_walk h
  obtain ⟨-, P, d, hadj, hside⟩ := mem_bonds.mp heb
  exact ⟨P, d, hadj, hside ▸ hew⟩

/-- The same fact stated as membership in the circuit's vertex support: the anchor
plaquette is one the circuit actually passes through. -/
theorem exists_mem_support_on_walk {σ : Config n} {H : SimpleGraph (Plaq n)} {x b : Site n}
    {w : (latticeGraph n).Walk x b} (h : ¬ Even (crossings (bonds σ H) w)) :
    ∃ P : Plaq n, (∃ Q, H.Adj P Q) ∧ ∃ d, sideOf P d ∈ w.edges := by
  obtain ⟨P, d, hadj, hside⟩ := exists_plaq_on_walk h
  exact ⟨P, ⟨partnerOf P d, hadj⟩, d, hside⟩

/-! ## 3. What is still missing, as a statement rather than a remark

The anchor above is the whole walk, and a walk from `x` to the corner is as long as the
box. The Peierls estimate needs the anchor to be within `L` of `x` for a circuit of length
`L`, so that the number of anchors is bounded by a function of `L` alone. That is the next
statement on this wall, and it is genuine planar geometry: it says a closed curve of
length `L` around a point stays within `L` of it.

Nothing here proves it and nothing here needs it; it is written down so the next attempt
starts at a statement rather than at a topic. -/

end SurroundLocal
