import DualUnique
import CircuitCount

/-!
# A circuit's length is the number of contour bonds it accounts for

`DualUnique` finished Peierls' enclosure step. `WALLS.md` W3 then itemised what is left,
and the first item was a bounded build rather than an estimate:

> nothing in this estate relates a dual circuit's `Walk.length` to the number of **primal
> bonds** it crosses.

This file relates them. The bridge is a bijection between the dual edges of a subgraph
and the primal bonds those edges cross, and both halves of it are already proved:
`DualUnique.sideOf_eq_cases` says two dual edges crossing one bond are the same edge, and
`DualGraph.sideOf_partnerOf` says an edge read from its two ends gives the same bond.

## Main results

* `CircuitLength.partnerOf_inj_of_ne` — the four partners of a plaquette are distinct
  wherever they are not the plaquette itself. Sixteen cases, the same shape as
  `sideOf_eq_cases`.
* `CircuitLength.card_bonds_eq_ncard_edgeSet` — for a subgraph of the dual graph, **the
  number of primal bonds it crosses equals its number of dual edges.**
* `CircuitLength.card_bonds_eq_length` — hence for a circuit, the number of contour bonds
  it accounts for is its **length**, and `three_le_card_bonds` gives the `3 ≤` that
  follows.
* `CircuitLength.card_contour_eq_sum` — and over a circuit decomposition the numbers add
  up to **`|γ|` itself**, the cardinality of `IsingContourEnergy.contour`. That is the
  identity the energy side of Peierls' comparison runs on, and it is a statement about the
  contour rather than about abstract edge counts — which is what
  `CircuitCount.three_mul_length_le_ncard_edgeSet` gives and what
  `three_mul_length_le_card_contour` here upgrades.

## What remains

**The shape count**, and it is all that is left on this wall: how many dual circuits of a
given length surround a fixed site — the `3 ^ L`-type bound. That is an estimate and
nothing here begins it. The energy/entropy comparison that would turn it into
`IsingBoundaryField.MagnetisationBound` is downstream of it, and `MagnetisationBound` is
untouched.
-/

namespace CircuitLength

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Distinct directions give distinct partners

Wherever a partner is not the plaquette itself, the four of them are four different
plaquettes: the left and right neighbours differ in the first coordinate and the upper
and lower ones in the second. -/

theorem partnerOf_inj_of_ne {P : Plaq n} {d d' : Fin 4} (hne : partnerOf P d ≠ P)
    (h : partnerOf P d = partnerOf P d') : d = d' := by
  have hPi := P.hi
  have hPj := P.hj
  have hne' : partnerOf P d' ≠ P := h ▸ hne
  fin_cases d <;> fin_cases d' <;>
    [ rfl;
      (exfalso; have h1 := (leftP_eq_self_iff P).not.mp hne
       have h2 := (upP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.j h; simp only [partnerOf, leftP_j, upP_j] at this; omega);
      (exfalso; have h1 := (leftP_eq_self_iff P).not.mp hne
       have h2 := (rightP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.i h; simp only [partnerOf, leftP_i, rightP_i] at this; omega);
      (exfalso; have h1 := (leftP_eq_self_iff P).not.mp hne
       have := congrArg Plaq.i h; simp only [partnerOf, leftP_i, downP_i] at this; omega);
      (exfalso; have h1 := (upP_eq_self_iff P).not.mp hne
       have h2 := (leftP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.j h; simp only [partnerOf, upP_j, leftP_j] at this; omega);
      rfl;
      (exfalso; have h1 := (upP_eq_self_iff P).not.mp hne
       have h2 := (rightP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.j h; simp only [partnerOf, upP_j, rightP_j] at this; omega);
      (exfalso; have h1 := (upP_eq_self_iff P).not.mp hne
       have := congrArg Plaq.j h; simp only [partnerOf, upP_j, downP_j] at this; omega);
      (exfalso; have h1 := (rightP_eq_self_iff P).not.mp hne
       have h2 := (leftP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.i h; simp only [partnerOf, rightP_i, leftP_i] at this; omega);
      (exfalso; have h1 := (rightP_eq_self_iff P).not.mp hne
       have h2 := (upP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.j h; simp only [partnerOf, rightP_j, upP_j] at this; omega);
      rfl;
      (exfalso; have h1 := (rightP_eq_self_iff P).not.mp hne
       have := congrArg Plaq.i h; simp only [partnerOf, rightP_i, downP_i] at this; omega);
      (exfalso; have h1 := (downP_eq_self_iff P).not.mp hne
       have h2 := (leftP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.i h; simp only [partnerOf, downP_i, leftP_i] at this; omega);
      (exfalso; have h1 := (downP_eq_self_iff P).not.mp hne
       have := congrArg Plaq.j h; simp only [partnerOf, downP_j, upP_j] at this; omega);
      (exfalso; have h1 := (downP_eq_self_iff P).not.mp hne
       have h2 := (rightP_eq_self_iff P).not.mp hne'
       have := congrArg Plaq.i h; simp only [partnerOf, downP_i, rightP_i] at this; omega);
      rfl]

/-! ### Naming a witness

`bonds` is defined by an existential, and the counting argument below needs a chosen
witness for each bond. §2 is what makes the choice harmless: any two witnesses for the
same bond give the same dual edge. -/

private theorem exists_pick {σ : Config n} {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ bonds σ H) :
    ∃ pd : Plaq n × Fin 4, H.Adj pd.1 (partnerOf pd.1 pd.2) ∧ sideOf pd.1 pd.2 = e := by
  obtain ⟨-, P, d, h1, h2⟩ := mem_bonds.mp he
  exact ⟨(P, d), h1, h2⟩

private noncomputable def pick {σ : Config n} {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ bonds σ H) : Plaq n × Fin 4 := (exists_pick he).choose

private theorem pick_spec {σ : Config n} {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ bonds σ H) :
    H.Adj (pick he).1 (partnerOf (pick he).1 (pick he).2) ∧
      sideOf (pick he).1 (pick he).2 = e := (exists_pick he).choose_spec

/-! ## 2. Same bond exactly when same dual edge

The two directions are the two lemmas already proved: `sideOf_eq_cases` for one and
`sideOf_partnerOf` for the other. -/

theorem sideOf_eq_iff_edge_eq {H : SimpleGraph (Plaq n)} {P P' : Plaq n} {d d' : Fin 4}
    (hadj : H.Adj P (partnerOf P d)) (hadj' : H.Adj P' (partnerOf P' d')) :
    sideOf P d = sideOf P' d' ↔ s(P, partnerOf P d) = s(P', partnerOf P' d') := by
  have hne : partnerOf P d ≠ P := fun hc => H.irrefl (hc ▸ hadj)
  have hne' : partnerOf P' d' ≠ P' := fun hc => H.irrefl (hc ▸ hadj')
  constructor
  · intro hside
    rcases sideOf_eq_cases hside with ⟨hPP, hdd⟩ | ⟨hPP, hdd⟩
    · rw [hPP, hdd]
    · rw [hPP, hdd, partnerOf_partnerOf P d hne, Sym2.eq_swap]
  · intro hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨rfl, hQ⟩ | ⟨hPQ, hQP⟩
    · rw [partnerOf_inj_of_ne hne hQ]
    · subst hQP
      have hback : partnerOf (partnerOf P d) (opp d) = P := partnerOf_partnerOf P d hne
      have hd' : d' = opp d :=
        (partnerOf_inj_of_ne (P := partnerOf P d) (by rw [hback]; exact Ne.symm hne)
          (hback.trans hPQ)).symm
      rw [hd']
      exact (sideOf_partnerOf P d hne).symm

/-! ## 3. The count -/

/-- **A subgraph of the dual graph crosses as many primal bonds as it has dual edges.**
The bijection is "the bond this edge crosses", and §2 is exactly its well-definedness and
injectivity. -/
theorem card_bonds_eq_ncard_edgeSet {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) : (bonds σ H).card = H.edgeSet.ncard := by
  have hedge : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [hedge]
  refine Finset.card_bij (fun e he => s((pick he).1, partnerOf (pick he).1 (pick he).2))
    (fun e he => ?_) (fun e he e' he' hEq => ?_) (fun f hf => ?_)
  · rw [mem_edgeFinset, mem_edgeSet]
    exact (pick_spec he).1
  · have h1 := pick_spec he
    have h2 := pick_spec he'
    rw [← h1.2, ← h2.2]
    exact (sideOf_eq_iff_edge_eq h1.1 h2.1).mpr hEq
  · rw [mem_edgeFinset] at hf
    induction f using Sym2.ind with
    | _ P Q =>
      have hadj : H.Adj P Q := hf
      obtain ⟨d, hd, hQ, -⟩ := hle hadj
      have hadj' : H.Adj P (partnerOf P d) := hQ ▸ hadj
      have hmem : sideOf P d ∈ bonds σ H := mem_bonds.mpr ⟨hd, P, d, hadj', rfl⟩
      refine ⟨sideOf P d, hmem, ?_⟩
      have h1 := pick_spec hmem
      rw [hQ]
      exact (sideOf_eq_iff_edge_eq h1.1 hadj').mp h1.2

/-- **A circuit accounts for exactly as many contour bonds as it has steps.** -/
theorem card_bonds_eq_length {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) {v : Plaq n} {p : H.Walk v v} (hp : p.IsCycle)
    (hH : p.toSubgraph.spanningCoe = H) : (bonds σ H).card = p.length := by
  rw [card_bonds_eq_ncard_edgeSet hle]
  calc H.edgeSet.ncard = (p.toSubgraph.spanningCoe : SimpleGraph (Plaq n)).edgeSet.ncard := by
        rw [hH]
    _ = p.length := ncard_edgeSet_spanningCoe_toSubgraph hp

/-- **So a circuit accounts for at least three bonds.** -/
theorem three_le_card_bonds {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) : 3 ≤ (bonds σ H).card := by
  rw [card_bonds_eq_ncard_edgeSet hle]
  exact hcyc.three_le_ncard_edgeSet

/-! ## 4. The lengths add up to `|γ|`

The circuits' bond sets are pairwise disjoint and cover the contour, so their sizes sum
to its size. This is the identity the energy side of Peierls' comparison runs on: the
energy of a configuration is fixed by `|γ|`, and `|γ|` is the total length of the
circuits. -/

theorem card_foldr_union {L : List (Finset (Sym2 (Site n)))} (hp : L.Pairwise Disjoint) :
    (L.foldr (· ∪ ·) ∅).card = (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons γ L ih =>
    obtain ⟨hγ, hp'⟩ := List.pairwise_cons.mp hp
    rw [List.foldr_cons,
      Finset.card_union_of_disjoint (SurroundsParity.disjoint_foldr_union hγ), ih hp',
      List.map_cons, List.sum_cons]

/-- **The circuits' lengths add up to `|γ|`.** -/
theorem card_contour_eq_sum {σ : Config n} (hσ : PlusBoundary σ)
    {L : List (SimpleGraph (Plaq n))} (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ⊔ ·) ⊥ = dualGraph σ) :
    (contour σ).card = (L.map fun H => (bonds σ H).card).sum := by
  have hfold : contour σ = (L.map (bonds σ)).foldr (· ∪ ·) ∅ := by
    rw [← bonds_foldr, hsup, bonds_dualGraph hσ]
  rw [hfold, card_foldr_union (pairwise_disjoint_bonds hp), List.map_map]
  rfl

/-- **Three times the number of circuits is at most `|γ|`** — read on the contour itself,
from the lengths rather than from the abstract circuit count. -/
theorem three_mul_length_le_card_contour {σ : Config n} (hσ : PlusBoundary σ)
    {L : List (SimpleGraph (Plaq n))} (hcyc : ∀ H ∈ L, IsCycleGraph H)
    (hp : L.Pairwise Disjoint) (hsup : L.foldr (· ⊔ ·) ⊥ = dualGraph σ) :
    3 * L.length ≤ (contour σ).card := by
  have hle : ∀ H ∈ L, H ≤ dualGraph σ := fun H hH => hsup ▸ le_foldr_sup_of_mem hH
  rw [card_contour_eq_sum hσ hp hsup]
  clear hp hsup hσ
  induction L with
  | nil => simp
  | cons H L ih =>
    have h3 : 3 ≤ (bonds σ H).card :=
      three_le_card_bonds (hle H (List.mem_cons_self ..)) (hcyc H (List.mem_cons_self ..))
    have hrest : 3 * L.length ≤ (L.map fun K => (bonds σ K).card).sum :=
      ih (fun K hK => hcyc K (List.mem_cons_of_mem _ hK))
        (fun K hK => hle K (List.mem_cons_of_mem _ hK))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

end CircuitLength
