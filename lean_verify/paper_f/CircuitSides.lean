import CircuitLength

/-!
# A single circuit breaks every unit square an even number of times

`PlaqLocal` ended by naming what the Peierls estimate is still missing: that a circuit's
bond set is a **cut** — `∃ τ : Config n, bonds σ H = contour τ` — from which the crossing
parity of that one circuit becomes path-independent, and the enclosure half of the estimate
follows. This file proves the **local** half of that statement, which is the half that
needs no construction:

> for a circuit `H` of the dual graph, **every plaquette has an even number of its sides
> in `bonds σ H`** — as `IsingContourPlaquette.even_plaquette` says for the whole contour.

That is the **necessary** condition for a bond set to be a cut, checked one square at a
time: `even_plaquette` proves it for `contour σ` — for any configuration, long before the
dual lattice existed — and this file proves the same of one circuit's bonds. Whether it is
**sufficient** is a different statement, it is what the missing construction would have to
supply, and it is not proved here.

## How it reduces to the cycle

The step that does the work is `mem_bonds_iff_adj`: for a subgraph of the dual graph, the
`d`-side of `P` is one of its bonds **exactly when the dual edge across that side is an
edge of the subgraph**. Both directions are already-proved uniqueness facts —
`DualUnique.sideOf_eq_cases` for "no third plaquette has this bond as a side" and
`CircuitLength.partnerOf_inj_of_ne` for "no second direction has this partner" — and
neither needs the `+` boundary condition, only `H ≤ dualGraph σ`.

With that, the broken sides of `P` are in bijection with `P`'s neighbours in `H`, so their
number is `P`'s degree in `H`, which is even because `H` is a cycle
(`SimpleGraph.IsCycleGraph.evenDegrees`). Note where the evenness comes from: **not** from
`even_plaquette`, which is about the whole contour and would say nothing about one piece of
it, but from the cycle.

## What this is not

**It is not the cut.** "Every square is broken evenly" is a local condition; being a cut is
a global one, and the passage between them is the construction that is still missing — for
the box it would go through a parity-along-a-ray definition of `τ` and a telescoping sum
over a row of plaquettes, using exactly the identity `sides_ud_eq_lr` below provides. That
construction is **not begun here**.

`IsingBoundaryField.MagnetisationBound` is untouched, and so are the Gibbs weight of a
circuit and the summation over lengths.
-/

namespace CircuitSides

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique CircuitLength
open SimpleGraph

/- `bonds` is defined by a classical filter over `Plaq n`, whose `Fintype` is itself
noncomputable; every statement below inherits that and there is no decidable instance to
state instead. -/
set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A side is a bond of `H` exactly when `H` has the edge across it

The definition of `bonds` quantifies over *some* plaquette and direction giving that bond.
The uniqueness lemmas say the quantifier has at most two witnesses and that they are the
two ends of one dual edge, so the existential collapses to a statement about `P` itself. -/

/-- **For a subgraph of the dual graph, the `d`-side of `P` is one of its bonds exactly
when the dual edge across that side is an edge of the subgraph.** No boundary condition:
`H ≤ dualGraph σ` is the whole hypothesis. -/
theorem mem_bonds_iff_adj {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (P : Plaq n) (d : Fin 4) :
    sideOf P d ∈ bonds σ H ↔ H.Adj P (partnerOf P d) := by
  constructor
  · intro hmem
    obtain ⟨-, P', d', hadj, hside⟩ := mem_bonds.mp hmem
    have hne' : partnerOf P' d' ≠ P' := fun hc => H.irrefl (by rwa [hc] at hadj)
    rcases sideOf_eq_cases hside with ⟨hP, hd⟩ | ⟨hP, hd⟩
    · subst hP; subst hd; exact hadj
    · subst hP; subst hd
      rw [partnerOf_partnerOf P' d' hne']
      exact hadj.symm
  · intro hadj
    obtain ⟨d₀, hc, hQ, hne⟩ := hle hadj
    obtain rfl := partnerOf_inj_of_ne hne hQ
    exact mem_bonds.mpr ⟨hc, P, d, hadj, rfl⟩

/-! ## 2. So the broken sides of `P` are its neighbours in `H` -/

theorem neighborSet_eq_image {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (P : Plaq n) :
    H.neighborSet P = partnerOf P '' {d : Fin 4 | sideOf P d ∈ bonds σ H} := by
  ext Q
  constructor
  · intro hQ
    have hadj : H.Adj P Q := hQ
    obtain ⟨d, -, rfl, -⟩ := hle hadj
    exact ⟨d, (mem_bonds_iff_adj hle P d).mpr hadj, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact (mem_bonds_iff_adj hle P d).mp hd

theorem partnerOf_injOn_bonds {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (P : Plaq n) :
    Set.InjOn (partnerOf P) {d : Fin 4 | sideOf P d ∈ bonds σ H} := by
  intro d hd _d' _hd' hEq
  have hadj := (mem_bonds_iff_adj hle P d).mp hd
  have hne : partnerOf P d ≠ P := fun hc => H.irrefl (by rwa [hc] at hadj)
  exact partnerOf_inj_of_ne hne hEq

/-- **The number of `P`'s sides broken by `H` is `P`'s degree in `H`.** -/
theorem card_filter_eq_ncard_neighborSet {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (P : Plaq n) :
    (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ bonds σ H).card =
      (H.neighborSet P).ncard := by
  classical
  rw [neighborSet_eq_image hle P, (partnerOf_injOn_bonds hle P).ncard_image,
    show {d : Fin 4 | sideOf P d ∈ bonds σ H}
        = ↑(Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ bonds σ H) from by ext d; simp,
    Set.ncard_coe_finset]

/-! ## 3. And a circuit has even degrees, so every square is broken evenly -/

/-- **A circuit of the dual graph breaks an even number of each plaquette's sides.** The
evenness comes from the cycle, not from `even_plaquette`: the latter is a statement about
the whole contour and says nothing about one piece of a decomposition. -/
theorem even_card_sides {σ : Config n} {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    (hcyc : IsCycleGraph H) (P : Plaq n) :
    Even (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ bonds σ H).card := by
  rw [card_filter_eq_ncard_neighborSet hle P]
  exact hcyc.evenDegrees P

/-- The same, written out as `even_plaquette` writes it — the four sides in
`even_plaquette`'s order, which is the order `sideOf` indexes them in. -/
theorem even_sides {σ : Config n} {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    (hcyc : IsCycleGraph H) (P : Plaq n) :
    Even ((if sideL P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)
        + (if sideR P ∈ bonds σ H then 1 else 0)
        + (if sideD P ∈ bonds σ H then 1 else 0)) := by
  have h := even_card_sides hle hcyc P
  rwa [Finset.card_filter, Fin.sum_univ_four] at h

/-- **The identity a cut construction would telescope**: across one plaquette, the two
horizontal sides carry the same parity as the two vertical ones. Crossing a row of
plaquettes and summing this is how the parity of a leftward ray would be shown to jump
exactly at the vertical bonds of `H` — that construction is not built here. -/
theorem sides_ud_eq_lr {σ : Config n} {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    (hcyc : IsCycleGraph H) (P : Plaq n) :
    ((if sideD P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)) % 2 =
      ((if sideL P ∈ bonds σ H then 1 else 0) + (if sideR P ∈ bonds σ H then 1 else 0)) % 2 := by
  obtain ⟨k, hk⟩ := even_sides hle hcyc P
  omega

/-! ## 4. The two facts a telescoping argument would also need

Both are one-liners from what exists, and both are recorded here rather than in the
construction that would use them, because each is a statement about the estate's own
objects and neither depends on the construction. -/

/-- **The right side of a plaquette is the left side of the next one along** — which is
what would make a sum of `sides_ud_eq_lr` across a row telescope. -/
theorem sideR_eq_sideL_rightP (P : Plaq n) (h : P.i + 2 < n) : sideR P = sideL (rightP P) :=
  (sideL_rightP P h).symm

/-- **The leftmost vertical bond of a row is not one of `H`'s** — under `+` boundary
conditions, and for every `H` at once, since `bonds` is a subset of the contour. This is
what would make such a telescoping sum start from zero rather than from an unknown.

The contour half of this is `PlaquetteLattice.sideL_notMem_contour`, which is
`DualObstruction.notMem_contour_of_plusBoundary` applied to a side with both ends on the
left edge; a first draft of this file re-proved that from scratch, and the review caught
it. -/
theorem sideL_notMem_bonds {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    {P : Plaq n} (h : P.i = 0) : sideL P ∉ bonds σ H :=
  fun hc => sideL_notMem_contour hσ P h (bonds_subset σ H hc)

end CircuitSides
