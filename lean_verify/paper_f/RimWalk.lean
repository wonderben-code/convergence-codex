import ExtendedDual

/-!
# A walk to a rim vertex is a walk to the edge of the box, which is what the count counts

`ExtendedDual` builds the graph and proves its plaquette degrees even with no boundary
condition. `DualPathCount` counts dual walks from a fixed plaquette into `bdryPlaq n`, the
plaquettes touching the edge of the box. **Until now the two files did not talk to each
other**, and a route whose construction and whose estimate are about different objects is not
a route.

This file joins them.

> **`exists_dualGraph_walk_to_bdry`** — a walk in the **extended** graph from a plaquette to
> **any** rim vertex yields a walk in the **ordinary** dual graph from that plaquette to a
> plaquette of `DualPathCount.bdryPlaq n`.

So the object `ExtendedDual` would produce is exactly the object that
`DualPathCount.card_walksTo_bdry_le` and `sum_walksTo_bdry_le` bound. The proof is an
induction on the walk with one observation:
the rim vertices are pairwise non-adjacent, so a walk that ends at one ends by stepping off a
plaquette, and that plaquette is on the edge — `outward_isBdryPlaq`, which is the four
`*_eq_self_iff` lemmas read as the four disjuncts of `IsBdryPlaq`.

## What is still missing, unchanged by this file

Nothing here produces such a walk. `ERRATUM 97` records what does: **two** things, not one — a
circuits-plus-paths decomposition for a graph whose odd vertices are the rims, and the
open-path analogue of `RayWalk`'s ray-and-crossing-parity argument, which is what says the
walk starts *near `x`*. This file removes a third thing that would have been needed on top of
those, and which nobody had noticed was missing: the translation between the two graphs.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace RimWalk

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open DualObstruction DualGraph ExtendedDual

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. An outward-facing direction puts the plaquette on the edge -/

/-- **A plaquette with an outward direction is a boundary plaquette.** The four cases are the
four `*_eq_self_iff` lemmas of `DualGraph`, and they are literally the four disjuncts of
`DualPathCount.IsBdryPlaq`. -/
theorem outward_isBdryPlaq {P : Plaq n} {d : Fin 4} (h : Outward P d) :
    DualPathCount.IsBdryPlaq P := by
  fin_cases d
  · exact Or.inl ((leftP_eq_self_iff P).mp h)
  · exact Or.inr (Or.inr (Or.inr ((upP_eq_self_iff P).mp h)))
  · exact Or.inr (Or.inl ((rightP_eq_self_iff P).mp h))
  · exact Or.inr (Or.inr (Or.inl ((downP_eq_self_iff P).mp h)))

theorem outward_mem_bdryPlaq {P : Plaq n} {d : Fin 4} (h : Outward P d) :
    P ∈ DualPathCount.bdryPlaq n :=
  DualPathCount.mem_bdryPlaq.mpr (outward_isBdryPlaq h)

/-! ## 2. Stripping the rim step -/

/-- **THE TRANSLATION.** A walk in the extended graph from a plaquette to a rim vertex gives a
walk in the ordinary dual graph from that plaquette to a plaquette on the edge of the box —
which is exactly what `DualPathCount` counts.

The induction is on the walk. The rim vertices are pairwise non-adjacent, so the walk cannot
pass through one and come back; it therefore consists of dual steps between plaquettes
followed by a single step off the last plaquette, and `outward_isBdryPlaq` says that plaquette
is on the edge. -/
theorem exists_dualGraph_walk_to_bdry {σ : Config n} :
    ∀ {u v : ExtV n} (_w : (extDual σ).Walk u v) {P₀ : Plaq n} {d : Fin 4},
      u = Sum.inl P₀ → v = Sum.inr d →
      ∃ Q ∈ DualPathCount.bdryPlaq n, Nonempty ((dualGraph σ).Walk P₀ Q) := by
  intro u v w
  induction w with
  | nil =>
    intro P₀ d hu hv
    exact absurd (hu.symm.trans hv) (by simp)
  | @cons a b _ hadj w' ih =>
    intro P₀ d hu hv
    subst hu
    cases b with
    | inl Q' =>
      obtain ⟨Q, hQ, ⟨p⟩⟩ := ih rfl hv
      exact ⟨Q, hQ, ⟨SimpleGraph.Walk.cons hadj p⟩⟩
    | inr e =>
      -- the step lands on a rim, so this plaquette is already on the edge
      exact ⟨P₀, outward_mem_bdryPlaq hadj.2, ⟨SimpleGraph.Walk.nil⟩⟩

/-- The same with the hypothesis in the shape a caller has it: reachability. -/
theorem exists_walk_to_bdry_of_reachable {σ : Config n} {P₀ : Plaq n} {d : Fin 4}
    (h : (extDual σ).Reachable (Sum.inl P₀) (Sum.inr d)) :
    ∃ Q ∈ DualPathCount.bdryPlaq n, Nonempty ((dualGraph σ).Walk P₀ Q) := by
  obtain ⟨w⟩ := h
  exact exists_dualGraph_walk_to_bdry w rfl rfl

/-! ## 3. What the odd vertices are

`ExtendedDual.evenDegrees_plaq` says every plaquette has even degree. So the odd-degree
vertices of the extended graph are **all** rim vertices, with no exception — which is what
makes "circuits plus paths between the odd vertices" the right shape to ask for, and what a
decomposition theorem would have to consume. -/

/-- **EVERY ODD-DEGREE VERTEX IS A RIM VERTEX.** Immediate from `evenDegrees_plaq`, and worth
naming because it is the hypothesis any circuits-plus-paths theorem would be applied under:
the paths this construction can produce run rim to rim, never plaquette to plaquette. -/
theorem odd_degree_isRim {σ : Config n} {v : ExtV n}
    (h : ¬ Even ((extDual σ).neighborSet v).ncard) : ∃ d : Fin 4, v = Sum.inr d := by
  cases v with
  | inl P => exact absurd (evenDegrees_plaq σ P) h
  | inr d => exact ⟨d, rfl⟩

end RimWalk
