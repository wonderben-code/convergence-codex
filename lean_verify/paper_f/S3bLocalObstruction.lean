/-
  S3bLocalObstruction.lean — why no condition on the BOUNDARY can repair
  `ClusterReachesRim`: the obstruction is at `x`.

  WHY. `S3bRefutation` proves `S3bResidue.ClusterReachesRim` false and offers a
  repair two ways: restrict to configurations *"whose cluster has a nonempty
  boundary near `x`"*, or weaken *"the plaquette at `x`"* to *"some plaquette
  within `L + 1` of `x`"*, the second reintroducing a length `L` and with it the
  length-control DECISION NEEDED. `RimBoundary` then supplied NECESSARY
  conditions — some boundary site, and then some site on a named side of the
  box, lies outside the cluster — and called that *"the shape of the constraint
  any repaired S3b-ii statement must satisfy"*.

  **Those conditions are about the edge of the box, and the obstruction is not.**
  This file proves the necessary condition at radius ZERO, and it is a condition
  on `x` itself.

  WHAT THIS FILE PROVES:
  1. **`not_mem_contour_of_const`** — a bond whose two ends carry the same value
     is not in the contour. Immediate, and named because §1 uses it four times.
  2. **`not_adj_of_no_side_in_contour`** — **a plaquette none of whose four
     sides is broken is ISOLATED in the extended dual graph.** Both kinds of edge
     out of a plaquette, to another plaquette and to a rim vertex, carry the same
     requirement `sideOf P d ∈ contour τ`; with no broken side there is neither.
     `ExtendedDual` records the mirror fact for the rim vertices and this one was
     missing.
  3. **`not_reachable_rim_of_plaq_const`** — hence such a plaquette reaches no
     rim, whatever the configuration does anywhere else.
  4. **`exists_side_in_contour_of_reaches_rim`** — contrapositive, and the point:
     reaching a rim FORCES a broken side on the plaquette one started from.
  5. **`clusterReachesRim_forces_broken_side_at_x`** — so if `ClusterReachesRim n`
     held, then for **every** configuration and **every** boundary-reaching down
     site `x`, a side of the plaquette **at `x`** would be broken in the cluster's
     own contour. **`x` would have to lie on the boundary of its own cluster.**

  WHAT THIS SETTLES ABOUT THE REPAIR, and it is the reason to write it down.
  The two routes `S3bRefutation` offers are **not alternatives**. Route (i) at
  radius zero is (5), and (5) is close to vacuous: it excludes every site
  strictly inside a droplet, which is most of a droplet. So a usable route (i)
  must allow a positive radius — and at that point it IS route (ii), the length
  `L` is back, and the same DECISION NEEDED applies. **Whichever route is taken,
  the length-control decision is unavoidable**, and choosing quickly to make the
  list tidy is what `ERRATUM 89` is about.

  WHAT THIS IS NOT.
  **It is not the repair and it does not attempt one.** It removes one candidate
  shape — a purely boundary-side hypothesis — by showing the failure is local,
  and it says what any repair must contain at radius zero. `WALLS` §W3 does not
  move. Nothing here touches `S3bResidue.walk_to_bdry_of_gap`, which remains a
  true implication from a false hypothesis, or `IsingBoundaryField`.

  **AND IT DOES NOT SAY THE PHYSICS IS WRONG.** A site deep inside a droplet
  genuinely has no broken bond on its own plaquette; that is a fact about the
  lattice, not a defect in the model. What was wrong was a specification that
  asked for one anyway.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import RimBoundary

namespace S3bLocalObstruction

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph ExtendedDual FieldCover FieldBoundaryEnergy PeierlsCover
open S3bResidue RimBoundary

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A plaquette with no broken side is isolated

Both clauses of `ExtendedDual.extAdj` that touch a plaquette — the one joining it to another
plaquette (`DualGraph.dualAdj`) and the one joining it to a rim vertex — require the same thing,
`sideOf P d ∈ contour τ`. So the four sides control every edge at `P` at once. -/

/-- A bond whose two ends carry the same value is not in the contour. -/
theorem not_mem_contour_of_const {τ : Config n} {s : Sym2 (Site n)} {b : Bool}
    (h : ∀ p ∈ s, τ p = b) : s ∉ contour τ := by
  induction s using Sym2.ind with
  | _ p q =>
    rw [mem_contour]
    rintro ⟨-, hne⟩
    exact hne ((h p (by simp)).trans (h q (by simp)).symm)

/-- **A PLAQUETTE WITH NO BROKEN SIDE IS ISOLATED IN THE EXTENDED DUAL GRAPH.** `ExtendedDual`
records the mirror statement for the rim vertices under `PlusBoundary`; this is the one for a
plaquette, and it needs no hypothesis on the configuration anywhere else. -/
theorem not_adj_of_no_side_in_contour {τ : Config n} {P : Plaq n}
    (h : ∀ d : Fin 4, sideOf P d ∉ contour τ) (v : ExtV n) :
    ¬ (extDual τ).Adj (Sum.inl P) v := by
  rcases v with Q | d
  · rintro ⟨e, hmem, -, -⟩
    exact h e hmem
  · rintro ⟨hmem, -⟩
    exact h d hmem

/-- So a walk out of it never leaves it. -/
theorem eq_of_reachable_of_no_side_in_contour {τ : Config n} {P : Plaq n}
    (h : ∀ d : Fin 4, sideOf P d ∉ contour τ) {v : ExtV n}
    (hr : (extDual τ).Reachable (Sum.inl P) v) : v = Sum.inl P := by
  obtain ⟨w⟩ := hr
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (not_adj_of_no_side_in_contour h _)

/-! ## 2. Hence reaching a rim forces a broken side where the walk starts -/

/-- **REACHING A RIM FORCES A BROKEN SIDE ON THE PLAQUETTE ONE STARTED FROM.** -/
theorem exists_side_in_contour_of_reaches_rim {τ : Config n} {P : Plaq n} {d : Fin 4}
    (h : (extDual τ).Reachable (Sum.inl P) (Sum.inr d)) :
    ∃ e : Fin 4, sideOf P e ∈ contour τ := by
  by_contra hc
  have hall : ∀ e : Fin 4, sideOf P e ∉ contour τ := fun e he => hc ⟨e, he⟩
  have hcon := eq_of_reachable_of_no_side_in_contour hall h
  simp at hcon

/-- **AND A PLAQUETTE WHOSE FOUR SIDES ALL CARRY ONE VALUE REACHES NO RIM**, whatever the
configuration does elsewhere. This is the local obstruction in its plainest form. -/
theorem not_reachable_rim_of_plaq_const {τ : Config n} {P : Plaq n} {b : Bool}
    (h : ∀ e : Fin 4, ∀ p ∈ sideOf P e, τ p = b) (d : Fin 4) :
    ¬ (extDual τ).Reachable (Sum.inl P) (Sum.inr d) := by
  intro hr
  obtain ⟨e, hmem⟩ := exists_side_in_contour_of_reaches_rim hr
  exact not_mem_contour_of_const (h e) hmem

/-! ## 3. What that says about `ClusterReachesRim`

Instantiated at the plaquette the specification names — the one **at `x`** — and at the cluster's
own indicator. -/

/-- **`ClusterReachesRim` WOULD FORCE EVERY BOUNDARY-REACHING DOWN SITE TO LIE ON THE BOUNDARY OF
ITS OWN CLUSTER.** A side of the plaquette at `x` broken in `contour (clusterOn σ x)` says exactly
that the cluster indicator changes value across a bond of that plaquette.

**This is a condition at `x`, and every necessary condition `RimBoundary` supplies is a condition
at the edge of the box** — so no hypothesis about the boundary, however sharpened, can imply it.
That is what removes route (i) at radius zero; see this file's header. -/
theorem clusterReachesRim_forces_broken_side_at_x (hgap : ClusterReachesRim n)
    (σ : Config n) (x : Site n) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n)
    (hx : σ x = false) (hb : ReachesBoundary σ x) :
    ∃ e : Fin 4, sideOf (plaqOf x hi hj) e ∈ contour (clusterOn σ x) := by
  obtain ⟨d, hd⟩ := hgap σ x hi hj hx hb
  exact exists_side_in_contour_of_reaches_rim hd

end S3bLocalObstruction
