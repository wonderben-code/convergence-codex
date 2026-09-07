import LeftPartDecomposition
import OddPieceSelect
import RayCircuitSurrounding
import EvenDegreesConverse
import DualPathCount

/-!
# The path pieces end at odd vertices, and in the dual graph odd vertices lie on the rim

`LeftPartDecomposition.exists_path_cycle_decomposition` splits any finite graph's edges into
paths and cycles, and `RE-SWEEP #42` recorded what it does not say: *no endpoint identification
and no count*. The first half of that is paid here. The construction behind the decomposition —
add one vertex joined to every odd-degree vertex, decompose the even graph into cycles, delete the
added vertex — already knows where the paths end: at the two neighbours of the added vertex on each
cycle through it, which are odd-degree vertices of the original graph. The theorem never said so.

In the dual graph of a configuration that matters, because `DualDegreeExact.even_degree_iff`
locates the parity of a plaquette's degree in its broken outward sides: a plaquette of odd degree
has a broken side facing out of the box, so it is a rim plaquette. **So a path piece of the dual
graph runs from the rim to the rim.**

## What is proved

**`IsPathGraphBetween`** — a path graph with its two ends named.

**`exists_isPathGraphBetween_leftPart_of_cycle`**, **`…_of_isCycleGraph`** —
`LeftPartPathGraph.isPathGraph_leftPart_of_cycle` with the ends kept: both are adjacent to the
added vertex.

**`exists_path_cycle_decomposition_odd`** — every finite graph's edge set is an edge-disjoint
union of pieces, each a cycle or a path between two **distinct odd-degree vertices**.

**`isBdryPlaq_of_odd_degree`** — a plaquette of odd dual degree is a rim plaquette
(`DualPathCount.IsBdryPlaq`).

**`exists_odd_piece_between`, `exists_odd_piece_rim`** — `OddPieceSelect`'s piece selection with
the ends: a walk crossing the dual graph's bonds oddly crosses oddly a piece that is a cycle or a
**path between two rim plaquettes**, and the piece is a subgraph of the dual graph.

**`exists_odd_piece_rim_leftRay`** — the same along `RayWalk.leftRay`, with no hypothesis beyond
the ray's two endpoint spins: the arc's enclosure statement with the path branch's ends known.

**`distToEdge_le_length_of_mem_support`** — a walk in a subgraph of the dual graph that ends at a
rim plaquette is at least as long as the distance to the rim of every plaquette on it
(`DualPathCount.distToEdge_le_length`, carried along the walk).

## What is NOT here

**NO COUNT, AND NO PROBABILITY.** Nothing here bounds the number of path pieces of a given length,
sums anything over them, or bounds the probability of any event. Trails from one plaquette to the
rim are counted in `DualPathCount.card_trailsTo_bdry_le`; **which** plaquette of the piece the ray
crosses — where such a count would be anchored — is not extracted here: the odd crossing count says
a bond of the piece lies on the ray and stops there. The energy side for *a rim-to-rim path lies in
the contour* is not available either: `FieldEnergy.gibbs_field_bound_of_cut` needs `IsPlusCut`,
which a rim-to-rim path is not. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING HERE MENTIONS A CLUSTER.** The piece is a subgraph of the dual graph of `σ`; relating it
to the down cluster of the site — `WALLS` §W3.7 §4's first item — is untouched, and the path
branch is not shown to be the only branch for a boundary-reaching cluster.

**ODD DEGREE IS SUFFICIENT FOR THE RIM, NOT NECESSARY.** A rim plaquette may have even degree, and
nothing here counts the odd plaquettes (`RimParity` counts odd vertices of the *extended* dual, a
different graph).

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): the decomposition takes `[Fintype W]`
and `[DecidableRel G.Adj]`, as `OddVertexAugment` does; the dual-graph statements take a
configuration and a walk; the ray statement takes the ray's two endpoint spins and the row bounds
`0 < b`, `b + 1 < n` — exactly `RayCircuitSurrounding`'s.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace PathPieceEndpoints

open CycleRestriction LeftPartWalk CyclePathExtract LeftPartPathGraph LeftPartDecomposition
open OddVertexAugment SimpleGraph

section General

variable {V : Type*}

/-- A path graph with its two ends named: `H` is spanned by a path from `y` to `z`. -/
def IsPathGraphBetween (H : SimpleGraph V) (y z : V) : Prop :=
  ∃ p : H.Walk y z, p.IsPath ∧ p.toSubgraph.spanningCoe = H

theorem IsPathGraphBetween.isPathGraph {H : SimpleGraph V} {y z : V}
    (h : IsPathGraphBetween H y z) : IsPathGraph H :=
  let ⟨p, hp, hs⟩ := h
  ⟨y, z, p, hp, hs⟩

variable {H : SimpleGraph (V ⊕ Unit)}

theorem exists_isPathGraphBetween_leftPart_of_cycle (p : H.Walk (Sum.inr ()) (Sum.inr ()))
    (hp : p.IsCycle) (hH : p.toSubgraph.spanningCoe = H) :
    ∃ y z : V, y ≠ z ∧ H.Adj (Sum.inr ()) (Sum.inl y) ∧ H.Adj (Sum.inl z) (Sum.inr ()) ∧
      IsPathGraphBetween (leftPart H) y z := by
  have hpn : ¬ p.Nil := hp.not_nil
  have htn : ¬ p.tail.Nil := by
    rw [Walk.nil_iff_length_eq]
    have h3 := hp.three_le_length
    have := Walk.length_tail_add_one hpn
    omega
  obtain ⟨hnotmem, hnodup⟩ := notMem_support_dropLast_tail p hp
  have hsnd : H.Adj (Sum.inr ()) p.snd := p.adj_snd hpn
  have hpen : H.Adj p.tail.penultimate (Sum.inr ()) := p.tail.adj_penultimate htn
  obtain ⟨y, hy'⟩ := eq_inl_of_ne hsnd.ne'
  obtain ⟨z, hz'⟩ := eq_inl_of_ne hpen.ne
  have hadj1 : H.Adj (Sum.inr ()) (Sum.inl y) := hy' ▸ hsnd
  have hadj2 : H.Adj (Sum.inl z) (Sum.inr ()) := hz' ▸ hpen
  have hpath : (p.tail.dropLast).IsPath := (Walk.isPath_def _).mpr hnodup
  have hne : p.snd ≠ p.tail.penultimate := by
    intro hcon
    have hpath' : ((p.tail.dropLast).copy rfl hcon.symm).IsPath :=
      (Walk.isPath_copy _ rfl hcon.symm).mpr hpath
    have hnil : (p.tail.dropLast).copy rfl hcon.symm = Walk.nil :=
      congrArg Subtype.val (SimpleGraph.Path.loop_eq (⟨_, hpath'⟩ : H.Path p.snd p.snd))
    have hlen0 : ((p.tail.dropLast).copy rfl hcon.symm).length = 0 := by rw [hnil]; rfl
    have hlen : (p.tail.dropLast).length = 0 := by rwa [Walk.length_copy] at hlen0
    have h1 := Walk.length_dropLast_add_one htn
    have h2 := Walk.length_tail_add_one hpn
    have h3 := hp.three_le_length
    omega
  have hyz : y ≠ z := fun hcon =>
    hne ((hy'.trans (congrArg Sum.inl hcon)).trans hz'.symm)
  obtain ⟨q, hs, he⟩ := exists_walk_data_of_notMem ((p.tail.dropLast).copy hy' hz')
    (by rwa [Walk.support_copy])
  refine ⟨y, z, hyz, hadj1, hadj2, q, (Walk.isPath_def q).mpr ?_, ?_⟩
  · exact List.Nodup.of_map Sum.inl (by rw [hs, Walk.support_copy]; exact hnodup)
  · ext a b
    have hq : s(a, b) ∈ q.edges ↔ s(Sum.inl a, Sum.inl b) ∈ (p.tail.dropLast).edges := by
      rw [show s(Sum.inl a, Sum.inl b) = Sym2.map Sum.inl s(a, b) from rfl,
        ← Walk.edges_copy (p.tail.dropLast) hy' hz', ← he]
      exact (List.mem_map_of_injective (Sym2.map.injective Sum.inl_injective)).symm
    rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges, hq,
      ← mem_edges_middle_iff p hpn htn, leftPart_adj, adj_iff_mem_edges hH]

theorem exists_isPathGraphBetween_leftPart_of_isCycleGraph {a : V ⊕ Unit} (p : H.Walk a a)
    (hp : p.IsCycle) (hH : p.toSubgraph.spanningCoe = H) (hmem : Sum.inr () ∈ p.support) :
    ∃ y z : V, y ≠ z ∧ H.Adj (Sum.inr ()) (Sum.inl y) ∧ H.Adj (Sum.inl z) (Sum.inr ()) ∧
      IsPathGraphBetween (leftPart H) y z := by
  classical
  refine exists_isPathGraphBetween_leftPart_of_cycle (p.rotate _ hmem) (hp.rotate hmem) ?_
  ext u v
  rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges,
    (p.rotate_edges _ hmem).mem_iff, ← adj_iff_mem_edges hH]

end General

section Decomposition

variable {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]

theorem exists_path_cycle_decomposition_odd :
    ∃ L : List (SimpleGraph W),
      (∀ K ∈ L, (∃ y z : W, y ≠ z ∧ Odd (G.degree y) ∧ Odd (G.degree z) ∧
        IsPathGraphBetween K y z) ∨ IsCycleGraph K) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = G := by
  classical
  obtain ⟨L, hcyc, hdisj, hjoin⟩ := exists_cycle_decomposition_augment G
  refine ⟨L.map leftPart, ?_, hdisj.map _ fun _ _ h => disjoint_leftPart h, ?_⟩
  · intro K hK
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hK
    obtain ⟨a, p, hp, hspan⟩ := hcyc J hJ
    have hJle : J ≤ augment G := hjoin ▸ le_foldr_sup_of_mem hJ
    by_cases hmem : Sum.inr () ∈ p.support
    · obtain ⟨y, z, hyz, hy, hz, hK⟩ :=
        exists_isPathGraphBetween_leftPart_of_isCycleGraph p hp hspan hmem
      exact Or.inl ⟨y, z, hyz, (adj_inr_inl G () y).mp (hJle hy),
        (adj_inl_inr G z ()).mp (hJle hz), hK⟩
    · exact Or.inr (isCycleGraph_leftPart_of_notMem p hp hspan hmem)
  · rw [foldr_leftPart, hjoin, leftPart_augment]

end Decomposition

section Dual

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open PlaquetteLattice IsingBoundaryField DualObstruction DualGraph DualBonds DualUnique
open OddPieceSelect RayWalk RayBondsParity RayCircuitSurrounding DualDegreeExact
open EvenDegreesConverse DualPathCount ExtendedDual IsingContourSeparation

variable {n : ℕ}

theorem isBdryPlaq_of_odd_degree (σ : Config n) (P : Plaq n)
    (h : ¬ Even ((dualGraph σ).neighborSet P).ncard) : IsBdryPlaq P := by
  classical
  have h1 := h
  rw [even_degree_iff] at h1
  try rw [Finset.filter_congr_decidable] at h1
  obtain ⟨d, hd⟩ : ∃ d : Fin 4, sideOf P d ∈ contour σ ∧ Outward P d := by
    by_contra hcon
    push Not at hcon
    apply h1
    have hempty : (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d)
        = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro d _ hd'
      exact hcon d hd'.1 hd'.2
    rw [hempty, Finset.card_empty]
    exact ⟨0, rfl⟩
  rcases (outward_iff P d).mp hd.2 with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem exists_odd_piece_between (σ : Config n) {x b : Site n} (w : (latticeGraph n).Walk x b)
    (hodd : ¬ Even (crossings (bonds σ (dualGraph σ)) w)) :
    ∃ H : SimpleGraph (Plaq n), H ≤ dualGraph σ ∧
      ((∃ P Q : Plaq n, P ≠ Q ∧ ¬ Even ((dualGraph σ).neighborSet P).ncard ∧
        ¬ Even ((dualGraph σ).neighborSet Q).ncard ∧ IsPathGraphBetween H P Q) ∨
        IsCycleGraph H) ∧
      ¬ Even (crossings (bonds σ H) w) := by
  classical
  obtain ⟨L, hkind, hp, hjoin⟩ := exists_path_cycle_decomposition_odd (dualGraph σ)
  obtain ⟨H, hH, hoddH⟩ := exists_odd_piece_of_decomposition hp hjoin w hodd
  refine ⟨H, hjoin ▸ le_foldr_sup_of_mem hH, ?_, hoddH⟩
  rcases hkind H hH with ⟨P, Q, hPQ, hP, hQ, hpath⟩ | hcyc
  · refine Or.inl ⟨P, Q, hPQ, ?_, ?_, hpath⟩
    · rw [← degree_eq_ncard_neighborSet]; exact Nat.not_even_iff_odd.mpr hP
    · rw [← degree_eq_ncard_neighborSet]; exact Nat.not_even_iff_odd.mpr hQ
  · exact Or.inr hcyc

theorem exists_odd_piece_rim (σ : Config n) {x b : Site n} (w : (latticeGraph n).Walk x b)
    (hodd : ¬ Even (crossings (bonds σ (dualGraph σ)) w)) :
    ∃ H : SimpleGraph (Plaq n), H ≤ dualGraph σ ∧
      ((∃ P Q : Plaq n, P ≠ Q ∧ IsBdryPlaq P ∧ IsBdryPlaq Q ∧ IsPathGraphBetween H P Q) ∨
        IsCycleGraph H) ∧
      ¬ Even (crossings (bonds σ H) w) := by
  obtain ⟨H, hle, hkind, hoddH⟩ := exists_odd_piece_between σ w hodd
  refine ⟨H, hle, ?_, hoddH⟩
  rcases hkind with ⟨P, Q, hPQ, hP, hQ, hpath⟩ | hcyc
  · exact Or.inl ⟨P, Q, hPQ, isBdryPlaq_of_odd_degree σ P hP,
      isBdryPlaq_of_odd_degree σ Q hQ, hpath⟩
  · exact Or.inr hcyc

theorem exists_odd_piece_rim_leftRay (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ∃ H : SimpleGraph (Plaq n), H ≤ dualGraph σ ∧
      ((∃ P Q : Plaq n, P ≠ Q ∧ IsBdryPlaq P ∧ IsBdryPlaq Q ∧ IsPathGraphBetween H P Q) ∨
        IsCycleGraph H) ∧
      ¬ Even (crossings (bonds σ H) (leftRay b k hk)) :=
  exists_odd_piece_rim σ (leftRay b k hk)
    (odd_crossings_bonds_leftRay_of_down σ b hb0 hj k hk hx he)

theorem distToEdge_le_length_of_mem_support (σ : Config n) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) {P Q : Plaq n} (hQ : IsBdryPlaq Q) (p : H.Walk P Q) {R : Plaq n}
    (hR : R ∈ p.support) : distToEdge R ≤ p.length :=
  calc distToEdge R ≤ ((p.dropUntil R hR).mapLe hle).length :=
        distToEdge_le_length ((p.dropUntil R hR).mapLe hle) hQ
    _ = (p.dropUntil R hR).length := Walk.length_map _ _
    _ ≤ p.length := Walk.length_dropUntil_le p hR

end Dual

end PathPieceEndpoints
