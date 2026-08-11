import RimWalk
import EdgeAddParity

/-!
# How many odd vertices the extended dual graph has, and therefore how many open paths

`ExtendedDual.evenDegrees_plaq` says every plaquette of `extDual σ` has even degree with no
hypothesis on `σ`, and `RimWalk.odd_degree_isRim` reads that back as: **every odd-degree
vertex is one of the four rim vertices.** That is a containment. This file adds the counting
fact that goes with it, which is Mathlib's handshake lemma
(`SimpleGraph.even_card_odd_degree_vertices`) and nothing more:

> **`card_oddExt_eq_zero_or_two_or_four`** — the odd-degree vertices of `extDual σ` number
> exactly `0`, `2` or `4`, for every `n` and every configuration.

Even, because handshake; at most four, because they are rims.

## Two, and the two things this does not settle

**It is two, not one.** Four odd vertices are permitted by both facts at once and nothing here
excludes that case, so the bound is `2` and not `1`. **Nor is four exhibited.** No
configuration in this estate is shown to have four odd rims; `4` is a case left open, which is
not the same as a case shown to occur (`ERRATA 71` addendum 3 and `ERRATUM 101`).

**And the reading "at most two open paths" is conditional, everywhere it appears below.** §6
does produce a decomposition, but of the *repaired* graph `extDual σ ⊔ edge u v`, into circuits
— **there is no path object anywhere in this file.** A decomposition into circuits plus open
paths, *if one is ever proved*, would have `2k` odd vertices for `k` paths, and §4 bounds that
count; it does not bound paths, because there are none here to bound. Every sentence below
saying "at most two open paths" is shorthand for that conditional and for nothing stronger.

## What the parity buys that geometry did not

`ExtendedDual.cornerDown_left_rim_degree_one` cost about forty lines of contour analysis to
establish that ONE rim vertex of `cornerDown` has odd degree. `exists_second_odd_rim` then
gives a second one for free, by parity alone:

> **`cornerDown_exists_second_odd_rim`** — for `cornerDown n` with `1 < n` there is a rim
> direction `e ≠ 0` whose rim vertex also has odd degree.

No second geometric argument, no repeat of `cornerDown_left_rim_unique` in direction `3`. That
is the shape of the whole point: a path has two ends, and the parity of the graph knows it even
when we have only looked at one end.

## And then the repair, which the count makes available

Knowing the odd vertices are exactly two is not just a bound — it is the hypothesis of the
classical fix. `EdgeAddParity.evenDegrees_sup_edge` (general, any finite graph) says a graph
even everywhere but at two non-adjacent vertices becomes even everywhere when those two are
joined. Here the non-adjacency is **free**: the odd vertices are rims, and `extAdj` puts no edge
between two rims. So §6 gets

> **`exists_cycle_decomposition_sup_edge_of_card_two`** — when `extDual σ` has exactly two odd
> vertices, adding one edge between them yields a graph that is an edge-disjoint union of
> cycles, by the estate's own `CycleDecomposition.exists_cycle_decomposition`.

## What this does not do

**It does not produce a walk, and that is now the whole of the remaining step.** From a cycle
through the added edge one wants to delete that edge and read off an `extDual σ`-path from one
rim to the other. The decomposition returns cycle **graphs** (`SimpleGraph.IsCycleGraph`), not
walks, so there is nothing to rotate: **recovering a walk from an `IsCycleGraph` is the missing
theorem**, and it is general graph theory with no Ising content in it.

**The `4` case is untreated.** Two edges must be added and the pairing is a choice; nothing here
makes it.

`S3bResidue.ClusterReachesRim` is untouched and unproved, and
`IsingBoundaryField.MagnetisationBound` is untouched. What has changed is that "a
circuits-plus-paths decomposition" — an unbounded family, and a theorem nobody had written down
— is now one bounded case plus one named general lemma about `IsCycleGraph`.
-/

namespace RimParity

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open DualObstruction DualGraph ExtendedDual RimWalk

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The odd-degree vertices as a finite set -/

/-- The odd-degree vertices of the extended dual graph. Stated through `Set.ncard` to match
`CycleDecomposition.EvenDegrees`, which is the property the decomposition theorem asks for. -/
noncomputable def oddExt (σ : Config n) : Finset (ExtV n) :=
  Finset.univ.filter fun v => ¬ Even ((extDual σ).neighborSet v).ncard

@[simp] theorem mem_oddExt {σ : Config n} {v : ExtV n} :
    v ∈ oddExt σ ↔ ¬ Even ((extDual σ).neighborSet v).ncard := by
  simp [oddExt]

/-! ## 2. Containment: they are rims

This is `RimWalk.odd_degree_isRim` packaged as a `Finset` inequality, which is what a
cardinality bound consumes. -/

/-- Every odd-degree vertex is a rim vertex, as a subset statement. -/
theorem oddExt_subset_rims (σ : Config n) :
    oddExt σ ⊆ Finset.univ.image (Sum.inr : Fin 4 → ExtV n) := by
  intro v hv
  obtain ⟨d, rfl⟩ := odd_degree_isRim (mem_oddExt.mp hv)
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

/-- **At most four odd vertices**, because there are only four rims. -/
theorem card_oddExt_le_four (σ : Config n) : (oddExt σ).card ≤ 4 := by
  classical
  refine (Finset.card_le_card (oddExt_subset_rims σ)).trans ?_
  calc (Finset.univ.image (Sum.inr : Fin 4 → ExtV n)).card
      ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

/-! ## 3. Parity: there is an even number of them

Mathlib's handshake lemma, transported across `degree_eq_ncard_neighborSet`. The transport is
the only real work: `oddExt` is phrased with `Set.ncard` and `¬ Even`, Mathlib's is phrased with
`degree` and `Odd`. -/

/-- `oddExt` is Mathlib's odd-degree filter. -/
theorem oddExt_eq_filter_odd_degree (σ : Config n) :
    oddExt σ = Finset.univ.filter fun v => Odd ((extDual σ).degree v) := by
  classical
  ext v
  simp only [mem_oddExt, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.degree_eq_ncard_neighborSet, Nat.not_even_iff_odd]

/-- **THE HANDSHAKE LEMMA FOR THE EXTENDED DUAL GRAPH.** The number of odd-degree vertices is
even — true for any finite graph, and recorded here in the estate's own vocabulary. -/
theorem even_card_oddExt (σ : Config n) : Even (oddExt σ).card := by
  classical
  rw [oddExt_eq_filter_odd_degree σ]
  exact (extDual σ).even_card_odd_degree_vertices

/-! ## 4. The count -/

/-- **THE COUNT: `0`, `2` OR `4`.** Even by handshake, at most four because every odd vertex is
a rim. That is the whole of what is proved.

Its intended use is conditional and is not proved here: a decomposition into circuits plus open
paths would have two odd endpoints per path, so `k` paths would need `2k ≤ 4` — at most two
paths, each running rim to rim by `RimWalk.odd_degree_isRim`. **No circuits-plus-paths
decomposition exists in this estate or in Mathlib**, so this theorem bounds a count and not a
number of paths. §6 uses the `= 2` case to build a circuits-only decomposition of a repaired
graph, which is a different statement. -/
theorem card_oddExt_eq_zero_or_two_or_four (σ : Config n) :
    (oddExt σ).card = 0 ∨ (oddExt σ).card = 2 ∨ (oddExt σ).card = 4 := by
  obtain ⟨k, hk⟩ := even_card_oddExt σ
  have h4 := card_oddExt_le_four σ
  omega

/-- Half the count is at most two. This is arithmetic on `card_oddExt_le_four` and nothing else;
it becomes a statement about paths only if something proves that the odd vertices pair up as the
endpoints of paths, which nothing does. -/
theorem card_oddExt_div_two_le_two (σ : Config n) : (oddExt σ).card / 2 ≤ 2 :=
  Nat.div_le_div_right (card_oddExt_le_four σ) |>.trans (by norm_num)

/-! ## 5. A path has a second end

The corollary that pays for the section. Mathlib's `exists_ne_odd_degree_of_exists_odd_degree`
plus `odd_degree_isRim` says: if one rim vertex has odd degree then **another rim vertex does
too**. -/

/-- **A SECOND ODD RIM, FOR FREE.** If the rim vertex in direction `d` has odd degree, some
other direction's rim vertex does as well. Geometry is not consulted: this is parity. -/
theorem exists_second_odd_rim {σ : Config n} {d : Fin 4}
    (h : ¬ Even ((extDual σ).neighborSet (Sum.inr d)).ncard) :
    ∃ e : Fin 4, e ≠ d ∧ ¬ Even ((extDual σ).neighborSet (Sum.inr e)).ncard := by
  classical
  have hodd : Odd ((extDual σ).degree (Sum.inr d)) := by
    rw [SimpleGraph.degree_eq_ncard_neighborSet]
    exact Nat.not_even_iff_odd.mp h
  obtain ⟨w, hne, hw⟩ :=
    (extDual σ).exists_ne_odd_degree_of_exists_odd_degree (Sum.inr d) hodd
  have hw' : ¬ Even ((extDual σ).neighborSet w).ncard := by
    rw [← SimpleGraph.degree_eq_ncard_neighborSet]
    exact Nat.not_even_iff_odd.mpr hw
  obtain ⟨e, rfl⟩ := odd_degree_isRim hw'
  exact ⟨e, fun hEq => hne (by rw [hEq]), hw'⟩

/-- **THE WITNESS.** `ExtendedDual.cornerDown_left_rim_degree_one` establishes by contour
analysis that the left rim of `cornerDown n` has degree one. Parity then hands over a second
odd rim with no further geometry — the other end of the two-bond path through the corner. -/
theorem cornerDown_exists_second_odd_rim (hn : 1 < n) :
    ∃ e : Fin 4, e ≠ 0 ∧
      ¬ Even ((extDual (MinimumContour.cornerDown n)).neighborSet (Sum.inr e)).ncard := by
  refine exists_second_odd_rim ?_
  rw [cornerDown_left_rim_degree_one hn]
  exact Nat.not_even_iff_odd.mpr odd_one

/-- And so for `cornerDown` the count is not zero: it is `2` or `4`. -/
theorem cornerDown_card_oddExt (hn : 1 < n) :
    (oddExt (MinimumContour.cornerDown n)).card = 2
      ∨ (oddExt (MinimumContour.cornerDown n)).card = 4 := by
  classical
  have hmem : (Sum.inr 0 : ExtV n) ∈ oddExt (MinimumContour.cornerDown n) := by
    refine mem_oddExt.mpr ?_
    rw [cornerDown_left_rim_degree_one hn]
    exact Nat.not_even_iff_odd.mpr odd_one
  have hpos : 0 < (oddExt (MinimumContour.cornerDown n)).card := Finset.card_pos.mpr ⟨_, hmem⟩
  rcases card_oddExt_eq_zero_or_two_or_four (MinimumContour.cornerDown n) with h | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h

/-! ## 6. The repair, applied to this graph

`EdgeAddParity.evenDegrees_sup_edge` is the classical move: if a finite graph is even
everywhere except at two non-adjacent vertices, joining those two makes it even everywhere. For
the extended dual graph the non-adjacency hypothesis is **free** — the odd vertices are rims by
`RimWalk.odd_degree_isRim`, and `ExtendedDual.extAdj` puts no edge between two rims. -/

/-- Two rim vertices are never adjacent: `extAdj` sends `inr, inr` to `False` outright. -/
theorem rim_not_adj (σ : Config n) (d e : Fin 4) :
    ¬ (extDual σ).Adj (Sum.inr d) (Sum.inr e) := id

/-- Odd vertices of the extended dual graph are never adjacent, since both are rims. -/
theorem odd_not_adj {σ : Config n} {u v : ExtV n} (hu : u ∈ oddExt σ) (hv : v ∈ oddExt σ) :
    ¬ (extDual σ).Adj u v := by
  obtain ⟨d, rfl⟩ := odd_degree_isRim (mem_oddExt.mp hu)
  obtain ⟨e, rfl⟩ := odd_degree_isRim (mem_oddExt.mp hv)
  exact rim_not_adj σ d e

/-- **THE REPAIR.** With exactly two odd vertices, adding the single edge between them makes
every degree of the extended dual graph even. Nothing has to be checked about where the two
vertices are: they are rims, so they are not already joined. -/
theorem evenDegrees_extDual_sup_edge {σ : Config n} {u v : ExtV n} (hne : u ≠ v)
    (hall : oddExt σ = {u, v}) :
    SimpleGraph.EvenDegrees (extDual σ ⊔ SimpleGraph.edge u v) := by
  classical
  have hu : u ∈ oddExt σ := by rw [hall]; exact Finset.mem_insert_self u {v}
  have hv : v ∈ oddExt σ := by
    rw [hall]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  refine SimpleGraph.evenDegrees_sup_edge hne (odd_not_adj hu hv)
    (mem_oddExt.mp hu) (mem_oddExt.mp hv) ?_
  intro w hwu hwv
  by_contra hodd
  rcases Finset.mem_insert.mp (hall ▸ mem_oddExt.mpr hodd) with h | h
  · exact hwu h
  · exact hwv (Finset.mem_singleton.mp h)

/-- **AND SO THE REPAIRED GRAPH DECOMPOSES INTO CIRCUITS.** When the extended dual graph has
exactly two odd vertices, one added edge turns it into an edge-disjoint union of cycles, via
`CycleDecomposition.exists_cycle_decomposition`.

This is as far as the circuit route goes today, and the remaining step is small and named.
What one wants next is the `extDual σ`-**walk** from `u` to `v` obtained by deleting the added
edge from whichever cycle carries it. The decomposition returns cycle *graphs*
(`SimpleGraph.IsCycleGraph`), not walks, so there is nothing to rotate; **recovering a walk
from an `IsCycleGraph` is the missing theorem**, and it is a general graph statement with no
Ising content. `S3bResidue.ClusterReachesRim` remains unproved.

The `4` case is untreated: two edges must be added and the pairing is a choice. -/
theorem exists_cycle_decomposition_sup_edge_of_card_two {σ : Config n}
    (h2 : (oddExt σ).card = 2) :
    ∃ u v : ExtV n, u ≠ v ∧ ¬ (extDual σ).Adj u v ∧
      ∃ L : List (SimpleGraph (ExtV n)), (∀ H ∈ L, SimpleGraph.IsCycleGraph H) ∧
        L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = extDual σ ⊔ SimpleGraph.edge u v := by
  classical
  obtain ⟨u, v, hne, hall⟩ := Finset.card_eq_two.mp h2
  have hu : u ∈ oddExt σ := by rw [hall]; exact Finset.mem_insert_self u {v}
  have hv : v ∈ oddExt σ := by
    rw [hall]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  exact ⟨u, v, hne, odd_not_adj hu hv,
    SimpleGraph.exists_cycle_decomposition _ (evenDegrees_extDual_sup_edge hne hall)⟩

end RimParity
