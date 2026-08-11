import DualGraph
import OuterFaceObstruction
import MinimumContour

/-!
# The dual graph with the outer face, and the even-degree theorem without a boundary condition

`DualGraph.evenDegrees_dualGraph` — every plaquette has an even number of dual neighbours —
is the gate to the whole Peierls circuit decomposition, and it carries `PlusBoundary`. The
hypothesis is used in exactly one place: `partnerOf_ne_of_mem`, which says a broken side is
not outward-facing. Without `+` an outward side can be broken, its "partner" is the plaquette
itself, and the neighbour count loses it.

`OuterFaceObstruction` shows the obvious repair fails: a **single** vertex for the outer face
would need two distinct edges to the corner plaquette, and `SimpleGraph` cannot carry them.
**This file does the repair that works, and it is small.** Index the outer face by
**direction** rather than treating it as one place: `Plaq n ⊕ Fin 4`, with `inr d` standing for
the rim that direction `d` points off the box. A plaquette has at most one side in each
direction, so it has at most one edge to each rim vertex, and simplicity is free.

## What comes out

> **`evenDegrees_plaq`** — in the extended dual graph, **every plaquette has even degree, with
> no hypothesis on `σ` at all.** The two kinds of neighbour partition the broken sides — inward
> ones give plaquettes, outward ones give rims — so the degree is the number of broken sides,
> and `IsingContourPlaquette.even_plaquette` never needed a boundary condition either.

The `+` case is recovered exactly: under `PlusBoundary` no outward side is broken
(`no_rim_edge_of_plusBoundary`), the rim vertices are isolated, and the extended graph is the
old one with four spare points.

## What it does not give, and this is now a theorem rather than a worry

**The rim vertices' degrees are not even.** `cornerDown` — down at the corner, up everywhere
else — has a contour of exactly two bonds, and both are outward sides of the corner plaquette,
one in direction `0` and one in direction `3`. So those two rim vertices have degree **one** —
`cornerDown_left_rim_degree_one`, and hence `not_evenDegrees_extDual`.
`CycleDecomposition.exists_cycle_decomposition` wants *all* degrees even and does not apply.

What the picture says should replace it is a decomposition into circuits **plus paths between
the odd vertices** — for `cornerDown`, one path of length two running from the left rim to the
bottom rim through the corner. The estate has no such theorem and neither does Mathlib
(`WALLS.md` W3 records the Euler-direction gap), so `UNLOCK_WATCHLIST`'s S3b-ii covering is
still not proved. **This file moves the obstruction from "the construction cannot be written"
to "the construction is written and one graph theorem is missing", and no further.**

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace ExtendedDual

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open DualObstruction DualGraph MinimumContour

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The vertex type and the graph -/

/-- Plaquettes together with one vertex per direction, standing for the rim that direction
points off the box. Four rather than one is the whole content: `OuterFaceObstruction` shows a
single outer vertex would need two edges to the corner plaquette. -/
abbrev ExtV (n : ℕ) := Plaq n ⊕ Fin 4

/-- Direction `d` of `P` faces the outer face: the partner across it is `P` itself, which is
how `DualGraph`'s truncated-subtraction definitions record "there is no plaquette there". -/
def Outward (P : Plaq n) (d : Fin 4) : Prop := partnerOf P d = P

/-- Adjacency: plaquettes across broken inward sides as before, and a plaquette to the rim
vertex of any direction whose side is broken and outward. -/
def extAdj (σ : Config n) : ExtV n → ExtV n → Prop
  | Sum.inl P, Sum.inl Q => dualAdj σ P Q
  | Sum.inl P, Sum.inr d => sideOf P d ∈ contour σ ∧ Outward P d
  | Sum.inr d, Sum.inl P => sideOf P d ∈ contour σ ∧ Outward P d
  | Sum.inr _, Sum.inr _ => False

/-- **THE EXTENDED DUAL GRAPH.** Simplicity is free: a plaquette has one side per direction,
so at most one edge to each rim vertex. -/
def extDual (σ : Config n) : SimpleGraph (ExtV n) where
  Adj := extAdj σ
  symm := by
    rintro (P | d) (Q | e) h
    · exact (dualGraph σ).symm h
    · exact h
    · exact h
    · exact h.elim
  loopless := ⟨by
    rintro (P | d) h
    · exact (dualGraph σ).irrefl h
    · exact h⟩

@[simp] theorem extDual_adj_inl_inr (σ : Config n) (P : Plaq n) (d : Fin 4) :
    (extDual σ).Adj (Sum.inl P) (Sum.inr d) ↔ sideOf P d ∈ contour σ ∧ Outward P d :=
  Iff.rfl

@[simp] theorem extDual_adj_inl_inl (σ : Config n) (P Q : Plaq n) :
    (extDual σ).Adj (Sum.inl P) (Sum.inl Q) ↔ dualAdj σ P Q :=
  Iff.rfl

/-! ## 2. The partner map is injective on the INWARD broken directions

`DualGraph.partnerOf_injOn` proves this on the broken directions, using `PlusBoundary` only to
know that a broken side is inward. Stated on the inward directions directly, the hypothesis is
not needed — which is the whole reason the extended graph works. -/

theorem partnerOf_injOn_inward (P : Plaq n) :
    Set.InjOn (partnerOf P) {d : Fin 4 | ¬ Outward P d} := by
  have hPi := P.hi
  have hPj := P.hj
  intro d hd d' hd' hEq
  have hL : ¬ Outward P 0 → P.i ≠ 0 := fun hm hc => hm ((leftP_eq_self_iff P).mpr hc)
  have hU : ¬ Outward P 1 → P.j + 2 < n := fun hm => by
    have := P.hj
    by_contra hc
    exact hm ((upP_eq_self_iff P).mpr (by omega))
  have hR : ¬ Outward P 2 → P.i + 2 < n := fun hm => by
    have := P.hi
    by_contra hc
    exact hm ((rightP_eq_self_iff P).mpr (by omega))
  have hD : ¬ Outward P 3 → P.j ≠ 0 := fun hm hc => hm ((downP_eq_self_iff P).mpr hc)
  fin_cases d <;> fin_cases d' <;>
    first
      | rfl
      | (exfalso
         first
           | (have := hL hd) | (have := hU hd) | (have := hR hd) | (have := hD hd)
         first
           | (have := hL hd') | (have := hU hd') | (have := hR hd') | (have := hD hd')
         have e1 := congrArg Plaq.i hEq
         have e2 := congrArg Plaq.j hEq
         simp only [partnerOf, leftP_i, leftP_j, rightP_i, rightP_j, upP_i, upP_j,
           downP_i, downP_j] at e1 e2
         omega)

/-! ## 3. The degree of a plaquette, counted -/

/-- The plaquette neighbours of `P` are the partners across its broken **inward** sides —
with no boundary condition, because "inward" is now said directly instead of being inferred
from `PlusBoundary`. -/
theorem inl_neighbours (σ : Config n) (P : Plaq n) :
    {Q : Plaq n | dualAdj σ P Q}
      = partnerOf P '' {d : Fin 4 | sideOf P d ∈ contour σ ∧ ¬ Outward P d} := by
  ext Q
  constructor
  · rintro ⟨d, hmem, rfl, hne⟩
    exact ⟨d, ⟨hmem, fun hc => hne (by rw [Outward] at hc; rw [hc])⟩, rfl⟩
  · rintro ⟨d, ⟨hmem, hin⟩, rfl⟩
    exact ⟨d, hmem, rfl, fun hc => hin (by rw [Outward, hc])⟩

theorem card_inl_neighbours (σ : Config n) (P : Plaq n) :
    {Q : Plaq n | dualAdj σ P Q}.ncard
      = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ ¬ Outward P d).card := by
  classical
  rw [inl_neighbours σ P,
    (partnerOf_injOn_inward P).mono (fun d hd => hd.2) |>.ncard_image,
    show {d : Fin 4 | sideOf P d ∈ contour σ ∧ ¬ Outward P d}
        = ↑(Finset.univ.filter fun d : Fin 4 =>
            sideOf P d ∈ contour σ ∧ ¬ Outward P d) from by ext d; simp,
    Set.ncard_coe_finset]

theorem card_inr_neighbours (σ : Config n) (P : Plaq n) :
    {d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d}.ncard
      = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d).card := by
  classical
  rw [show {d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d}
      = ↑(Finset.univ.filter fun d : Fin 4 =>
          sideOf P d ∈ contour σ ∧ Outward P d) from by ext d; simp,
    Set.ncard_coe_finset]

/-- The neighbour set of a plaquette splits along `Outward`. -/
theorem neighborSet_inl (σ : Config n) (P : Plaq n) :
    (extDual σ).neighborSet (Sum.inl P)
      = Sum.inl '' {Q : Plaq n | dualAdj σ P Q}
        ∪ Sum.inr '' {d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d} := by
  ext v
  cases v with
  | inl Q =>
    simp only [Set.mem_union, Set.mem_image, SimpleGraph.mem_neighborSet]
    constructor
    · intro h; exact Or.inl ⟨Q, h, rfl⟩
    · rintro (⟨R, hR, hEq⟩ | ⟨d, -, hEq⟩)
      · exact (Sum.inl_injective hEq) ▸ hR
      · exact absurd hEq (by simp)
  | inr d =>
    simp only [Set.mem_union, Set.mem_image, SimpleGraph.mem_neighborSet]
    constructor
    · intro h; exact Or.inr ⟨d, h, rfl⟩
    · rintro (⟨R, -, hEq⟩ | ⟨e, he, hEq⟩)
      · exact absurd hEq (by simp)
      · exact (Sum.inr_injective hEq) ▸ he

/-- **EVERY PLAQUETTE HAS EVEN DEGREE, WITH NO BOUNDARY CONDITION.** The two kinds of
neighbour partition the broken sides of `P` — inward ones give plaquettes, outward ones give
rim vertices — so the degree is the number of broken sides, which
`IsingContourPlaquette.even_plaquette` says is even for every configuration.

Compare `DualGraph.evenDegrees_dualGraph`, which carries `PlusBoundary`. The hypothesis was
there to rule the outward sides out; here they are counted instead. -/
theorem evenDegrees_plaq (σ : Config n) (P : Plaq n) :
    Even ((extDual σ).neighborSet (Sum.inl P)).ncard := by
  classical
  have hdisj : Disjoint (Sum.inl '' {Q : Plaq n | dualAdj σ P Q})
      (Sum.inr '' {d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d}) := by
    rw [Set.disjoint_left]
    rintro v ⟨Q, -, rfl⟩ ⟨d, -, hEq⟩
    exact absurd hEq (by simp)
  have hfin1 : ({Q : Plaq n | dualAdj σ P Q}).Finite := Set.toFinite _
  have hfin2 : ({d : Fin 4 | sideOf P d ∈ contour σ ∧ Outward P d}).Finite := Set.toFinite _
  have htotal : (Finset.univ.filter fun d : Fin 4 =>
        sideOf P d ∈ contour σ ∧ ¬ Outward P d).card
      + (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d).card
      = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ).card := by
    classical
    rw [show (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ ¬ Outward P d)
          = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ).filter
              (fun d => ¬ Outward P d) from by rw [Finset.filter_filter],
      show (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d)
          = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ).filter
              (fun d => Outward P d) from by rw [Finset.filter_filter],
      add_comm]
    exact Finset.card_filter_add_card_filter_not _
  rw [neighborSet_inl σ P, Set.ncard_union_eq hdisj (hfin1.image _) (hfin2.image _),
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective,
    card_inl_neighbours σ P, card_inr_neighbours σ P, htotal,
    Finset.card_filter, Fin.sum_univ_four]
  exact even_plaquette σ P.i P.j P.hi P.hj

/-! ## 4. The `+` case is recovered, and the rim vertices are the obstruction -/

/-- Under `PlusBoundary` no rim edge exists, so the four extra vertices are isolated and the
extended graph is `dualGraph σ` with four spare points. -/
theorem no_rim_edge_of_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (d : Fin 4) : ¬ (extDual σ).Adj (Sum.inl P) (Sum.inr d) := by
  rintro ⟨hmem, hout⟩
  exact partnerOf_ne_of_mem hσ P d hmem hout

/-- **AND WITHOUT IT THE RIM DEGREES ARE ODD.** For `cornerDown` the whole contour is the two
outward sides of the corner plaquette, so the rim vertices in directions `0` and `3` each have
exactly one neighbour. `CycleDecomposition.exists_cycle_decomposition` needs every degree even
and does not apply — the missing theorem is a decomposition into circuits **plus paths between
the odd vertices**, which neither this estate nor Mathlib has. -/
theorem cornerDown_rim_adj (hn : 1 < n) :
    (extDual (cornerDown n)).Adj (Sum.inl (OuterFaceObstruction.cornerPlaq hn)) (Sum.inr 0)
      ∧ (extDual (cornerDown n)).Adj
          (Sum.inl (OuterFaceObstruction.cornerPlaq hn)) (Sum.inr 3) := by
  refine ⟨⟨OuterFaceObstruction.cornerDown_sideL_mem hn, ?_⟩,
    ⟨OuterFaceObstruction.cornerDown_sideD_mem hn, ?_⟩⟩
  · exact (leftP_eq_self_iff _).mpr rfl
  · exact (downP_eq_self_iff _).mpr rfl

/-- The corner plaquette is the **only** plaquette with a broken outward side in direction
`0` for `cornerDown`: the contour is two bonds (`contour_cornerDown_eq`), and a left side on
column `0` can only be the corner's. -/
theorem cornerDown_left_rim_unique (hn : 1 < n) {P : Plaq n}
    (hmem : sideOf P 0 ∈ contour (cornerDown n)) (hout : Outward P 0) :
    P = OuterFaceObstruction.cornerPlaq hn := by
  classical
  have hi : P.i = 0 := (leftP_eq_self_iff P).mp hout
  rw [OuterFaceObstruction.contour_cornerDown_eq hn] at hmem
  have hside : sideOf P 0 = sideL P := rfl
  rw [hside] at hmem
  have hj : P.j = 0 := by
    rcases Finset.mem_insert.mp hmem with h | h
    · -- sideL P = sideL cornerPlaq
      rw [sideL, sideL, Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · have := congrArg (fun s => (Prod.snd s).val) h1
        simpa [bl, OuterFaceObstruction.cornerPlaq] using this
      · -- tl P = bl (corner) forces P.j + 1 = 0
        have e2 := congrArg (fun s => (Prod.snd s).val) h2
        simp only [tl, bl, OuterFaceObstruction.cornerPlaq] at e2
        omega
    · -- sideL P = sideD cornerPlaq, impossible: the left side stays in column P.i = 0
      rw [Finset.mem_singleton, sideL, sideD, Sym2.eq_iff] at h
      rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · have e1 := congrArg (fun s => (Prod.fst s).val) h1
        simp only [bl, br, OuterFaceObstruction.cornerPlaq] at e1
        omega
      · have e2 := congrArg (fun s => (Prod.snd s).val) h2
        simp only [tl, br, OuterFaceObstruction.cornerPlaq] at e2
        omega
  exact Plaq.ext (by rw [hi]; rfl) (by rw [hj]; rfl)

/-- **AND SO THE RIM DEGREE IS ONE — ODD.** The left-rim vertex of `cornerDown` has exactly
one neighbour, so `EvenDegrees` fails for the extended graph and
`CycleDecomposition.exists_cycle_decomposition` does not apply.

This is the precise residue of `UNLOCK_WATCHLIST`'s S3b-ii: the construction exists and its
plaquette degrees are even with no hypothesis, but the theorem that would consume it — a
decomposition into circuits **plus paths between the odd vertices** — is in neither the estate
nor Mathlib. For this configuration that path is the two-bond contour running from the left rim
to the bottom rim through the corner, which is exactly the shape S3b-ii's covering needs. -/
theorem cornerDown_left_rim_degree_one (hn : 1 < n) :
    ((extDual (cornerDown n)).neighborSet (Sum.inr 0)).ncard = 1 := by
  classical
  have hset : (extDual (cornerDown n)).neighborSet (Sum.inr 0)
      = {Sum.inl (OuterFaceObstruction.cornerPlaq hn)} := by
    ext v
    cases v with
    | inl P =>
      simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hmem, hout⟩
        exact congrArg Sum.inl (cornerDown_left_rim_unique hn hmem hout)
      · intro hEq
        rw [Sum.inl_injective hEq]
        exact ((extDual (cornerDown n)).symm (cornerDown_rim_adj hn).1)
    | inr e =>
      simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      exact ⟨fun h => h.elim, fun h => absurd h (by simp)⟩
  rw [hset, Set.ncard_singleton]

/-- **THE EXTENDED GRAPH DOES NOT HAVE ALL DEGREES EVEN**, stated against the property the
decomposition theorem asks for. -/
theorem not_evenDegrees_extDual (hn : 1 < n) :
    ¬ SimpleGraph.EvenDegrees (extDual (cornerDown n)) := by
  intro h
  have := h (Sum.inr 0)
  rw [cornerDown_left_rim_degree_one hn] at this
  exact (Nat.not_even_iff_odd.mpr odd_one) this

end ExtendedDual
