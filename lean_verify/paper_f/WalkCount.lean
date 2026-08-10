import CircuitLength
import Mathlib.Combinatorics.SimpleGraph.Walks.Counting

/-!
# How many walks of a given length, and hence how many circuits

`WALLS.md` W3 has one item left, the entropy side of Peierls' comparison: **how many
circuits of a given length can surround a fixed site**. This file proves the counting
bound that item rests on, in its general form and then for the dual lattice.

## The general bound

> In a graph whose degrees are all at most `d`, there are at most `d ^ L` walks of length
> `L` from one vertex to another.

That is an induction directly on Mathlib's own recursive description of the walks of a
given length (`SimpleGraph.finsetWalkLength`): a walk of length `L + 1` is a neighbour
followed by a walk of length `L`, so the count multiplies by at most the degree. Nothing
about planarity, nothing about the Ising model, and it is stated for an arbitrary graph.

## For the dual lattice

Every plaquette has at most four neighbours in the dual graph, because every dual
neighbour is one of the four partners — and that needs no boundary condition, since it is
read straight off the definition of `dualAdj`. So there are at most `4 ^ L` closed walks
of length `L` at a plaquette, and hence at most `4 ^ L` circuits through it of that
length.

## What this is and is not

**Is:** the entropy input, in the shape the wall names.

**Is not:** the classic constant. Peierls' textbook bound is `3 ^ L`-shaped, because a
self-avoiding walk cannot immediately turn back and so has only three continuations after
the first step. A degree bound alone gives `4 ^ L`, and the sharper constant is **not
proved here**. *Remark, not a theorem of this estate:* in the textbook argument any
constant base works once the temperature is low enough, so `4` in place of `3` costs only
a worse threshold — but that is a statement about the summation step, which is not
formalised anywhere here, and nothing in this file depends on it.

**Also is not:** the comparison. Turning "at most `4 ^ L` circuits of length `L` through
a plaquette" into a magnetisation bound needs, beyond this: that a circuit surrounding a
site must pass within `L` of it, so that the plaquettes to sum over are themselves
bounded in number; the Gibbs weight of a circuit of length `L`; and the summation over
`L`. None of those is begun. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## 1. Walks of a given length, counted by the degree bound -/

/-- **A graph with all degrees at most `d` has at most `d ^ L` walks of length `L`
between any two vertices.** The induction is Mathlib's own recursion for
`finsetWalkLength`: a walk of length `L + 1` out of `u` is a neighbour of `u` followed by
a walk of length `L`, so the count multiplies by the degree of `u` at worst. -/
theorem card_finsetWalkLength_le [DecidableEq V] [LocallyFinite G] {d : ℕ}
    (hd : ∀ w, G.degree w ≤ d) (L : ℕ) (u v : V) :
    (G.finsetWalkLength L u v).card ≤ d ^ L := by
  induction L generalizing u with
  | zero =>
    rw [pow_zero]
    rcases eq_or_ne u v with rfl | huv
    · simp [finsetWalkLength]
    · simp [finsetWalkLength, huv]
  | succ L ih =>
    rw [finsetWalkLength]
    calc (Finset.univ.biUnion fun w : G.neighborSet u =>
            (G.finsetWalkLength L w v).map ⟨fun p => Walk.cons w.property p, by
              intro _ _ h; simpa using h⟩).card
        ≤ ∑ w : G.neighborSet u, ((G.finsetWalkLength L w v).map
            ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ _w : G.neighborSet u, (G.finsetWalkLength L _w v).card := by
          simp only [Finset.card_map]
      _ ≤ ∑ _w : G.neighborSet u, d ^ L := Finset.sum_le_sum fun w _ => ih w
      _ = G.degree u * d ^ L := by
          rw [Finset.sum_const, Finset.card_univ, card_neighborSet_eq_degree, smul_eq_mul]
      _ ≤ d * d ^ L := Nat.mul_le_mul_right _ (hd u)
      _ = d ^ (L + 1) := by ring

end SimpleGraph

namespace WalkCount

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette
open PlaquetteLattice DualGraph SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 2. The dual lattice has degree at most four

Read straight off `dualAdj`: a dual neighbour of `P` is `partnerOf P d` for one of the
four directions. No boundary condition is used. -/

theorem neighborFinset_subset (σ : Config n) (P : Plaq n) :
    (dualGraph σ).neighborFinset P ⊆ Finset.univ.image (partnerOf P) := by
  intro Q hQ
  rw [mem_neighborFinset] at hQ
  obtain ⟨d, -, hQd, -⟩ := hQ
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hQd.symm⟩

/-- **Every plaquette has at most four dual neighbours.** -/
theorem degree_le_four (σ : Config n) (P : Plaq n) : (dualGraph σ).degree P ≤ 4 := by
  calc (dualGraph σ).degree P = ((dualGraph σ).neighborFinset P).card := rfl
    _ ≤ (Finset.univ.image (partnerOf P)).card :=
        Finset.card_le_card (neighborFinset_subset σ P)
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

/-! ## 3. The entropy bound -/

/-- **At most `4 ^ L` walks of length `L` between two plaquettes.** -/
theorem card_finsetWalkLength_le_four_pow (σ : Config n) (L : ℕ) (P Q : Plaq n) :
    ((dualGraph σ).finsetWalkLength L P Q).card ≤ 4 ^ L :=
  card_finsetWalkLength_le (degree_le_four σ) L P Q

/-- **At most `4 ^ L` closed walks of length `L` at a plaquette** — and every circuit
through `P` of length `L` is one of them, so the circuits are bounded by the same
number. This is the entropy input Peierls' comparison needs; the constant is `4` and not
the textbook `3`, which is what a bare degree bound gives. -/
theorem card_closed_walks_le (σ : Config n) (L : ℕ) (P : Plaq n) :
    ((dualGraph σ).finsetWalkLength L P P).card ≤ 4 ^ L :=
  card_finsetWalkLength_le_four_pow σ L P P

/-- Spelled out for cycles: the closed walks at `P` of length `L` that happen to be
cycles are a subset of the closed walks of that length, so there are at most `4 ^ L` of
them.

**This counts walks, not circuits.** One circuit through `P` of length `L` is traversed by
two walks based at `P`, one in each direction, so the number of *circuits* is smaller
still — which is the safe direction for a bound, and the file does not use the sharper
count. -/
theorem card_cycles_le (σ : Config n) (L : ℕ) (P : Plaq n) :
    ((dualGraph σ).finsetWalkLength L P P |>.filter fun p => p.IsCycle).card ≤ 4 ^ L :=
  le_trans (Finset.card_filter_le _ _) (card_closed_walks_le σ L P)

end WalkCount
