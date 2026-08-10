import DualBonds

/-!
# A bond belongs to at most two plaquettes — and the enclosure step, for circuits

`DualBonds` ends by naming the one missing lemma as a single displayed line. This file
proves it and spends it.

## The lemma

> `sideOf P d = sideOf P' d' → (P' = P ∧ d' = d) ∨ (P' = partnerOf P d ∧ d' = opp d)`

A bond is the side of at most two plaquettes, and those two face each other across it.
Sixteen cases, and they collapse fast: a side is **vertical** (`d ∈ {0, 2}`) or
**horizontal** (`d ∈ {1, 3}`), a vertical bond has equal first coordinates and a
horizontal one equal second coordinates, and a bond cannot be both — so the eight mixed
cases die on arithmetic alone. Of the eight remaining, four say `P' = P` and four
identify `P'` as the plaquette across the bond.

## What it buys

Edge-disjoint dual subgraphs cross **disjoint** sets of primal bonds
(`bonds_disjoint`), and the bonds of a sup are the union of the bonds
(`bonds_sup`). With `DualBonds.bonds_dualGraph` that turns
`DualGraph.exists_dual_cycle_decomposition` into a disjoint decomposition of the contour
into bond sets — exactly the hypothesis of `SurroundsParity.odd_countP_iff_down`. So:

> **Under `+` boundary conditions, the number of circuits of the dual decomposition that
> surround a given site is odd exactly when that site is down** — and in particular at
> least one circuit surrounds every down site.

That is Peierls' enclosure step, about circuits, with nothing left conditional except the
boundary condition (`ASSUMPTIONS_LEDGER` §46).

## What remains on this wall

**The count.** How many circuits of a given *length* can surround a fixed site — the
`3 ^ |γ|` bound. Nothing here bounds shapes, and nothing here relates a dual circuit's
length to its bond count. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace DualUnique

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A bond is the side of at most two plaquettes -/

/-- **The uniqueness lemma.** Sixteen cases; the eight mixing a vertical side with a
horizontal one are arithmetic contradictions, and the other eight split evenly between
"the same plaquette" and "the plaquette across". -/
theorem sideOf_eq_cases {P P' : Plaq n} {d d' : Fin 4} (h : sideOf P d = sideOf P' d') :
    (P' = P ∧ d' = d) ∨ (P' = partnerOf P d ∧ d' = opp d) := by
  have hPi := P.hi
  have hPj := P.hj
  have hQi := P'.hi
  have hQj := P'.hj
  fin_cases d <;> fin_cases d' <;>
    simp only [sideOf, sideL, sideU, sideR, sideD, bl, tl, tr, br, Sym2.eq_iff,
      Prod.ext_iff, Fin.ext_iff] at h <;>
    [ (left; exact ⟨Plaq.ext (by omega) (by omega), rfl⟩);
      (exfalso; omega);
      (right; refine ⟨Plaq.ext ?_ ?_, rfl⟩ <;> simp only [partnerOf, leftP_i, leftP_j] <;>
        omega);
      (exfalso; omega);
      (exfalso; omega);
      (left; exact ⟨Plaq.ext (by omega) (by omega), rfl⟩);
      (exfalso; omega);
      (right; refine ⟨Plaq.ext ?_ ?_, rfl⟩ <;> simp only [partnerOf, upP_i, upP_j] <;>
        omega);
      (right; refine ⟨Plaq.ext ?_ ?_, rfl⟩ <;> simp only [partnerOf, rightP_i, rightP_j] <;>
        omega);
      (exfalso; omega);
      (left; exact ⟨Plaq.ext (by omega) (by omega), rfl⟩);
      (exfalso; omega);
      (exfalso; omega);
      (right; refine ⟨Plaq.ext ?_ ?_, rfl⟩ <;> simp only [partnerOf, downP_i, downP_j] <;>
        omega);
      (exfalso; omega);
      (left; exact ⟨Plaq.ext (by omega) (by omega), rfl⟩)]

/-! ## 2. Disjoint dual subgraphs cross disjoint bonds -/

theorem bonds_bot (σ : Config n) : bonds σ (⊥ : SimpleGraph (Plaq n)) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨-, P, d, hadj, -⟩ := mem_bonds.mp he
  exact hadj

theorem bonds_sup (σ : Config n) (H K : SimpleGraph (Plaq n)) :
    bonds σ (H ⊔ K) = bonds σ H ∪ bonds σ K := by
  ext e
  simp only [mem_bonds, Finset.mem_union, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hc, P, d, hadj | hadj, hside⟩
    · exact Or.inl ⟨hc, P, d, hadj, hside⟩
    · exact Or.inr ⟨hc, P, d, hadj, hside⟩
  · rintro (⟨hc, P, d, hadj, hside⟩ | ⟨hc, P, d, hadj, hside⟩)
    · exact ⟨hc, P, d, Or.inl hadj, hside⟩
    · exact ⟨hc, P, d, Or.inr hadj, hside⟩

/-- **Edge-disjoint dual subgraphs cross disjoint sets of primal bonds.** If a bond were
crossed by both, the uniqueness lemma says the two dual edges are the same edge — either
literally, or read from the two ends — and a shared edge is what disjointness forbids. -/
theorem bonds_disjoint {σ : Config n} {H K : SimpleGraph (Plaq n)} (hd : Disjoint H K) :
    Disjoint (bonds σ H) (bonds σ K) := by
  rw [Finset.disjoint_left]
  intro e heH heK
  obtain ⟨-, P, d, hadjH, hside⟩ := mem_bonds.mp heH
  obtain ⟨-, P', d', hadjK, hside'⟩ := mem_bonds.mp heK
  have hne : partnerOf P d ≠ P := by
    intro hc
    rw [hc] at hadjH
    exact H.irrefl hadjH
  rcases sideOf_eq_cases (hside.trans hside'.symm) with ⟨hPP, hdd⟩ | ⟨hPP, hdd⟩
  · rw [hPP, hdd] at hadjK
    exact hd.le_bot (⟨hadjH, hadjK⟩ : (H ⊓ K).Adj P (partnerOf P d))
  · rw [hPP, hdd, partnerOf_partnerOf P d hne] at hadjK
    exact hd.le_bot (⟨hadjH, hadjK.symm⟩ : (H ⊓ K).Adj P (partnerOf P d))

theorem bonds_foldr {σ : Config n} (L : List (SimpleGraph (Plaq n))) :
    bonds σ (L.foldr (· ⊔ ·) ⊥) = (L.map (bonds σ)).foldr (· ∪ ·) ∅ := by
  induction L with
  | nil => simpa using bonds_bot σ
  | cons H L ih => rw [List.foldr_cons, bonds_sup, ih, List.map_cons, List.foldr_cons]

theorem pairwise_disjoint_bonds {σ : Config n} {L : List (SimpleGraph (Plaq n))}
    (hp : L.Pairwise Disjoint) : (L.map (bonds σ)).Pairwise Disjoint := by
  rw [List.pairwise_map]
  exact hp.imp bonds_disjoint

/-! ## 3. The enclosure step, for circuits -/

/-- **PEIERLS' ENCLOSURE STEP, ABOUT CIRCUITS.** Under `+` boundary conditions, for any
circuit decomposition of the dual contour, the number of circuits whose bond set is
crossed an odd number of times by a walk from `x` to the corner is **odd exactly when `x`
is down**.

Everything conditional has been discharged except the boundary condition itself. -/
theorem odd_count_circuits_iff_down {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} {L : List (SimpleGraph (Plaq n))} (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ⊔ ·) ⊥ = dualGraph σ)
    (w : (latticeGraph n).Walk x (SurroundsParity.origin hn)) :
    ¬ Even ((L.map (bonds σ)).countP fun γ =>
        decide ¬ Even (IsingContourClosed.crossings γ w)) ↔ σ x = false := by
  refine SurroundsParity.odd_countP_iff_down hσ hn (pairwise_disjoint_bonds hp) ?_ w
  rw [← bonds_foldr, hsup, bonds_dualGraph hσ]

/-- **In particular, every down site has a circuit around it.** -/
theorem exists_circuit_surrounding {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = false) :
    ∃ (L : List (SimpleGraph (Plaq n))) (w : (latticeGraph n).Walk x
        (SurroundsParity.origin hn)) (H : SimpleGraph (Plaq n)),
      (∀ K ∈ L, IsCycleGraph K) ∧ L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = dualGraph σ ∧ H ∈ L ∧
        ¬ Even (IsingContourClosed.crossings (bonds σ H) w) := by
  obtain ⟨L, hcyc, hp, hsup⟩ := exists_dual_cycle_decomposition hσ
  obtain ⟨w⟩ := (latticeGraph_connected hn).preconnected x (SurroundsParity.origin hn)
  have hodd : ¬ Even (IsingContourClosed.crossings
      ((L.map (bonds σ)).foldr (· ∪ ·) ∅) w) := by
    rw [← bonds_foldr, hsup, bonds_dualGraph hσ]
    exact (SurroundsParity.odd_crossings_iff_down hσ
      (SurroundsParity.isBoundary_origin hn) w).mpr hx
  obtain ⟨γ, hγmem, hγ⟩ :=
    SurroundsParity.exists_odd_of_odd_sum (pairwise_disjoint_bonds hp) w hodd
  obtain ⟨H, hHL, rfl⟩ := List.mem_map.mp hγmem
  exact ⟨L, w, H, hcyc, hp, hsup, hHL, hγ⟩

end DualUnique
