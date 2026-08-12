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


/-! ## 1b. Non-backtracking walks, and why the constant is `d - 1`

**A walk that has just crossed an edge cannot cross it back**, so after the first step it
has at most `d - 1` continuations rather than `d`. Nothing in Mathlib says this: there is
no non-backtracking walk predicate, no count for one, and `Walk.IsTrail` is the closest
object — which is what makes it usable here, since **a trail never immediately reverses**
(reversing traverses one edge twice) and so a cycle is non-backtracking for free.

The induction carries the vertex just left as a parameter, which is what makes the bound
`(d - 1) ^ L` rather than `d ^ L`: the hypothesis `G.Adj u x` says the forbidden vertex is
genuinely one of `u`'s neighbours, so forbidding it really does remove a choice. Drop that
hypothesis and the lemma is false — with `x` a non-neighbour every one of the `d` edges is
available and the count is `d · (d-1) ^ L`.
-/

section NonBacktracking

-- The predicate below is decidable by structural recursion, but stating that costs more
-- than it buys here and the rest of this file already runs classically.
set_option linter.style.openClassical false
open scoped Classical

/-- `NB x p` : the walk `p` never immediately reverses, and its first step does not go
back to `x`. -/
def NB : ∀ {u v : V}, V → G.Walk u v → Prop
  | _, _, _, Walk.nil => True
  | u, _, x, @Walk.cons _ _ _ w _ _ p => w ≠ x ∧ NB u p

@[simp] theorem NB_nil {u : V} (x : V) : NB x (Walk.nil : G.Walk u u) := trivial

@[simp] theorem NB_cons {u w v : V} (x : V) (h : G.Adj u w) (p : G.Walk w v) :
    NB x (Walk.cons h p) ↔ (w ≠ x ∧ NB u p) := Iff.rfl

/-- **NON-BACKTRACKING WALKS OUT OF A VERTEX YOU JUST CAME FROM: at most `(d-1) ^ L`.** -/
theorem card_nb_le [DecidableEq V] [LocallyFinite G] {d : ℕ}
    (hd : ∀ w, G.degree w ≤ d) :
    ∀ (L : ℕ) (u v x : V), G.Adj u x →
      ((G.finsetWalkLength L u v).filter (NB x)).card ≤ (d - 1) ^ L := by
  intro L
  induction L with
  | zero =>
    intro u v x _
    calc ((G.finsetWalkLength 0 u v).filter (NB x)).card
        ≤ (G.finsetWalkLength 0 u v).card := Finset.card_filter_le _ _
      _ ≤ 1 := by
          rcases eq_or_ne u v with rfl | huv
          · simp [finsetWalkLength]
          · simp [finsetWalkLength, huv]
      _ = (d - 1) ^ 0 := (pow_zero _).symm
  | succ L ih =>
    intro u v x hux
    set x' : G.neighborSet u := ⟨x, hux⟩ with hx'
    have hdeg : 1 ≤ G.degree u := by
      rw [← card_neighborSet_eq_degree]
      exact Fintype.card_pos_iff.2 ⟨x'⟩
    have hstep : ∀ w : G.neighborSet u,
        (((G.finsetWalkLength L (w : V) v).map
            ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
          (NB x)).card ≤ if w = x' then 0 else (d - 1) ^ L := by
      intro w
      rw [Finset.filter_map]
      rw [Finset.card_map]
      by_cases hw : w = x'
      · subst hw
        rw [if_pos rfl]
        refine le_of_eq (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_))
        intro p _ hcon
        exact hcon.1 rfl
      · rw [if_neg hw]
        have hne : (w : V) ≠ x := fun h => hw (Subtype.ext h)
        refine le_trans (le_of_eq ?_) (ih (w : V) v u w.property.symm)
        congr 1
        apply Finset.filter_congr
        intro p _
        simp [hne]
    calc (((G.finsetWalkLength (L + 1) u v)).filter (NB x)).card
        = ((Finset.univ.biUnion fun w : G.neighborSet u =>
              (G.finsetWalkLength L (w : V) v).map
                ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
            (NB x)).card := by rw [finsetWalkLength]
      _ = (Finset.univ.biUnion fun w : G.neighborSet u =>
              ((G.finsetWalkLength L (w : V) v).map
                ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
                  (NB x)).card := by rw [Finset.filter_biUnion]
      _ ≤ ∑ w : G.neighborSet u, (((G.finsetWalkLength L (w : V) v).map
              ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
                (NB x)).card := Finset.card_biUnion_le
      _ ≤ ∑ w : G.neighborSet u, (if w = x' then 0 else (d - 1) ^ L) :=
            Finset.sum_le_sum fun w _ => hstep w
      _ = (Finset.univ.erase x').card * (d - 1) ^ L := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x'), if_pos rfl, add_zero,
              Finset.sum_congr rfl (fun w hw => if_neg (Finset.mem_erase.1 hw).1),
              Finset.sum_const, smul_eq_mul]
      _ ≤ (d - 1) * (d - 1) ^ L := by
            refine Nat.mul_le_mul_right _ ?_
            have hcard : (Finset.univ.erase x').card = G.degree u - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                card_neighborSet_eq_degree]
            rw [hcard]
            exact Nat.sub_le_sub_right (hd u) 1
      _ = (d - 1) ^ (L + 1) := (pow_succ' _ _).symm

/-- A trail never immediately reverses: the step after arriving from `x` cannot return
to `x`, because that would traverse the same edge twice. -/
theorem NB_of_isTrail_cons : ∀ {x u v : V} (h : G.Adj x u) (p : G.Walk u v),
    (Walk.cons h p).IsTrail → NB x p
  | _, _, _, _, Walk.nil, _ => trivial
  | x, u, v, h, Walk.cons h' q, ht => by
      refine ⟨?_, NB_of_isTrail_cons h' q ht.of_cons⟩
      rintro rfl
      have := ht.edges_nodup
      simp only [Walk.edges_cons, List.nodup_cons] at this
      exact this.1 (by simp [Sym2.eq_swap])

/-- **NON-BACKTRACKING WALKS OUT OF A VERTEX: at most `d * (d-1) ^ L`** of length `L+1`.
The first step has the full degree available; every later step has one fewer, because it
cannot return along the edge it just used. -/
theorem card_nb_top_le [DecidableEq V] [LocallyFinite G] {d : ℕ}
    (hd : ∀ w, G.degree w ≤ d) (L : ℕ) (u v : V) :
    ((G.finsetWalkLength (L + 1) u v).filter
      (fun p => ∀ (w : V) (h : G.Adj u w) (q : G.Walk w v), p = Walk.cons h q → NB u q)).card
      ≤ d * (d - 1) ^ L := by
  classical
  calc ((G.finsetWalkLength (L + 1) u v).filter
        (fun p => ∀ (w : V) (h : G.Adj u w) (q : G.Walk w v), p = Walk.cons h q → NB u q)).card
      = ((Finset.univ.biUnion fun w : G.neighborSet u =>
            (G.finsetWalkLength L (w : V) v).map
              ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
          (fun p => ∀ (w : V) (h : G.Adj u w) (q : G.Walk w v),
            p = Walk.cons h q → NB u q)).card := by rw [finsetWalkLength]
    _ = (Finset.univ.biUnion fun w : G.neighborSet u =>
            ((G.finsetWalkLength L (w : V) v).map
              ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
                (fun p => ∀ (w : V) (h : G.Adj u w) (q : G.Walk w v),
                  p = Walk.cons h q → NB u q)).card := by rw [Finset.filter_biUnion]
    _ ≤ ∑ w : G.neighborSet u, (((G.finsetWalkLength L (w : V) v).map
            ⟨fun p => Walk.cons w.property p, by intro _ _ h; simpa using h⟩).filter
              (fun p => ∀ (w : V) (h : G.Adj u w) (q : G.Walk w v),
                p = Walk.cons h q → NB u q)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w : G.neighborSet u, (d - 1) ^ L := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [Finset.filter_map, Finset.card_map]
          refine le_trans (le_of_eq ?_) (card_nb_le hd L (w : V) v u w.property.symm)
          congr 1
          apply Finset.filter_congr
          intro p _
          constructor
          · intro hp; exact hp (w : V) w.property p rfl
          · intro hp w' h' q' heq
            cases heq
            exact hp
    _ = G.degree u * (d - 1) ^ L := by
          rw [Finset.sum_const, Finset.card_univ, card_neighborSet_eq_degree, smul_eq_mul]
    _ ≤ d * (d - 1) ^ L := Nat.mul_le_mul_right _ (hd u)

/-- A cycle satisfies the non-backtracking condition, because it is a trail. -/
theorem nb_of_isCycle {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    ∀ (w : V) (h : G.Adj u w) (q : G.Walk w u), p = Walk.cons h q → NB u q := by
  intro w h q heq
  subst heq
  exact NB_of_isTrail_cons h q hp.isTrail

/-- **CYCLES OF LENGTH `L+1` THROUGH A VERTEX: at most `d * (d-1) ^ L`**, which is the
non-backtracking bound rather than the bare `d ^ (L+1)`. -/
theorem card_cycles_nb_le [DecidableEq V] [LocallyFinite G] {d : ℕ}
    (hd : ∀ w, G.degree w ≤ d) (L : ℕ) (u : V) :
    ((G.finsetWalkLength (L + 1) u u).filter (fun p => p.IsCycle)).card ≤ d * (d - 1) ^ L := by
  refine le_trans (Finset.card_le_card ?_) (card_nb_top_le hd L u u)
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, nb_of_isCycle p hp.2⟩

end NonBacktracking

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

/-! ## 4. The same count, non-backtracking: `4 · 3 ^ L` instead of `4 ^ (L+1)`

**The textbook Peierls constant is `3`, this file's was `4`, and the gap was one unused
fact:** a circuit cannot cross a bond and immediately cross it back, so after the first
step three of the four directions remain, not four. §1b proves that for an arbitrary
graph; here it is read off at `d = 4`.
-/

/-- **AT MOST `4 · 3 ^ L` CYCLES OF LENGTH `L + 1` THROUGH A PLAQUETTE.** -/
theorem card_cycles_le_three_pow (σ : Config n) (L : ℕ) (P : Plaq n) :
    (((dualGraph σ).finsetWalkLength (L + 1) P P).filter fun p => p.IsCycle).card
      ≤ 4 * 3 ^ L :=
  card_cycles_nb_le (degree_le_four σ) L P

/-- And it really is sharper, stated as a theorem rather than asserted: `4 · 3 ^ L` is at
most `4 ^ (L+1)`, strictly so once `L ≥ 1`. -/
theorem three_pow_le_four_pow (L : ℕ) : 4 * 3 ^ L ≤ 4 ^ (L + 1) := by
  rw [pow_succ']
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by norm_num) L)

/-! ### What this does NOT move, and it is the number a reader will look for

**The threshold is unchanged.** `DualPathCount` and `ExplicitThreshold` do not consume the
cycle count. They consume `card_walksTo_bdry_le`, which bounds **every walk** of length `L`
from a plaquette to the boundary — not the cycles, and not the trails — and that is where
the `4 ^ L` producing `8 · exp(-4β)` comes from. Nothing above touches it.

**What rethreading would need**, named so it is a piece of work rather than a hope: the
walks that chain actually quantifies over would have to be known to be **trails** at the
point where they are counted, which means the files that produce them —
`RayWalk.exists_circuit_near_of_down` and the chain into `SideLength`/`SeriesBound` —
carrying `IsTrail` through. `NB_of_isTrail_cons` is then the only bridge needed, and
`card_nb_top_le` replaces `card_finsetWalkLength_le`. **That is four files and is not
begun.** The arithmetic it would buy is recorded in `UNLOCK_WATCHLIST`: the geometric
ratio `8 · exp(-4β)` becomes `6 · exp(-4β)` and the closed-form threshold moves from about
`0.69` to about `0.62`.
-/

end WalkCount
