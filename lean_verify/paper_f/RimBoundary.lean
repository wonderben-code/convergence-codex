import S3bRefutation

/-!
# Reaching a rim requires the configuration to change value along the edge of the box

`ERRATUM 108` refuted `S3bResidue.ClusterReachesRim` with one witness: all sites down, so the
cluster is the whole box, its indicator is constant, the contour is empty and the plaquette at
`x` reaches nothing. A witness says the statement is false. It does not say **why**, and it does
not tell the author what a repaired statement must look like.

This file replaces the witness with a criterion.

> **`not_reachable_rim_of_boundary_const`** — if a configuration takes the **same value at every
> boundary site**, then no plaquette reaches any rim vertex in its extended dual graph. Not "the
> ones we tried": none, for every configuration constant on the edge of the box.

and hence, for the object S3b-ii is about:

> **`exists_boundary_outside_cluster_of_reaches_rim`** — if the plaquette at `x` reaches a rim in
> `extDual (clusterOn σ x)`, then **some boundary site is not in the cluster of `x`**.

That is a *necessary condition on any repair*, derived rather than guessed, and it is sharper
than the refutation it generalises: `ReachesBoundary` says some boundary site **is** in the
cluster, so a repaired statement must also require some boundary site **outside** it. A cluster
that swallows the whole edge of the box reaches no rim, however large it is and however much
contour it has elsewhere.

## The geometry it turns on

**`outward_side_isBoundary`** — a side facing the outer face has **both endpoints on the boundary
of the box**. Immediate from the four `*_eq_self_iff` lemmas once the sides are unfolded: a left
side with `P.i = 0` is `{(0, j), (0, j+1)}`, a top side with `P.j + 2 = n` is
`{(i, n-1), (i+1, n-1)}`, and so on. So a rim edge needs a **broken** bond with both ends on the
boundary, which a configuration constant there cannot supply.

## What this deepens

`ExtendedDual.no_rim_edge_of_plusBoundary` is the same conclusion under `PlusBoundary` — every
boundary site **up**. The hypothesis used is not that the common value is `true`; it is only that
there **is** a common value. `no_rim_edge_of_boundary_const` is that theorem with the value
forgotten, and `no_rim_edge_of_plusBoundary` follows from it.

## And §5 localises it to one side of the box

Asking for constancy on the *whole* boundary is more than the proof needs. `Outward P 0` forces
`P.i = 0`, so a left-rim edge needs a broken bond in **column zero** — each direction pins its own
edge of the box. Hence

> **`exists_onSide_outside_cluster_of_reaches_rim`** — if the plaquette at `x` reaches the rim in
> direction `d`, then some site **on side `d`** is outside the cluster of `x`.

which names *which* of the four sides §4 was talking about. `starts_at_rim` carries the walk
argument per direction, where `stays_inl` needs every rim edge gone at once: a walk may legally
visit the other three rims and come back, so the one-sided statement cannot reuse it.

## And §6 makes both criteria corollaries, by saying what reaching a rim IS

A walk arriving at `inr d` cannot have come from another rim — `extAdj` sends `inr, inr` to
`False` — so its last step comes from a plaquette already carrying a broken outward side in
direction `d`. That is two-way:

> **`reachable_rim_iff`** — `P` reaches the rim in direction `d` **exactly when** it reaches some
> plaquette `Q` with `sideOf Q d ∈ contour τ` and `Outward Q d`.

The rim vertices were scaffolding for the construction; the question they encode is a question
about plaquettes, and §6 states it without them. `not_reachable_rim_of_side_const'` re-derives §5
from it, which is the evidence that the subsumption claimed here is real rather than asserted.

**Note what it does not reduce to.** `(extDual τ).Reachable (inl P) (inl Q)` is **not**
`(dualGraph τ).Reachable P Q`: a walk between two plaquettes in the extended graph may hop
through a rim, so two plaquettes with broken outward sides on the *same* side of the box are
joined even when the ordinary dual graph separates them. That is what the extra vertices were for,
and it is why §6 is stated in `extDual` and not transported down.

## What it does not do

It gives a necessary condition for the repair, not a sufficient one, and it does not repair
`ClusterReachesRim`. Requiring a boundary site outside the cluster is **not** enough — a cluster
can leave part of the edge alone and still have the plaquette at `x` sitting on a closed loop
around an interior hole, connected to nothing. That case is not treated here and is not claimed
to be. `ClusterReachesRim` stays refuted and unrepaired, and the length-control DECISION NEEDED
in `S3bResidue` is untouched. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace RimBoundary

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph ExtendedDual FieldCover FieldBoundaryEnergy PeierlsCover
open S3bResidue

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. An outward side lies along the edge of the box -/

/-- **A SIDE FACING THE OUTER FACE HAS BOTH ENDS ON THE BOUNDARY.** One case per direction, each
of them the corresponding `*_eq_self_iff` read into the coordinates of the two corners. -/
theorem outward_side_isBoundary {P : Plaq n} {d : Fin 4} (h : Outward P d) :
    ∀ y ∈ sideOf P d, isBoundary y = true := by
  have hi := P.hi
  have hj := P.hj
  fin_cases d
  · -- left: `P.i = 0`, side is `{(0, j), (0, j+1)}`
    have h0 : P.i = 0 := (leftP_eq_self_iff P).mp h
    intro y hy
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;>
      simp only [isBoundary, bl, tl, decide_eq_true_eq] <;> omega
  · -- up: `P.j + 2 = n`, side is `{(i, j+1), (i+1, j+1)}`
    have h0 : P.j + 2 = n := (upP_eq_self_iff P).mp h
    intro y hy
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;>
      simp only [isBoundary, tl, tr, decide_eq_true_eq] <;> omega
  · -- right: `P.i + 2 = n`, side is `{(i+1, j+1), (i+1, j)}`
    have h0 : P.i + 2 = n := (rightP_eq_self_iff P).mp h
    intro y hy
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;>
      simp only [isBoundary, tr, br, decide_eq_true_eq] <;> omega
  · -- down: `P.j = 0`, side is `{(i+1, 0), (i, 0)}`
    have h0 : P.j = 0 := (downP_eq_self_iff P).mp h
    intro y hy
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;>
      simp only [isBoundary, br, bl, decide_eq_true_eq] <;> omega

/-! ## 2. So a configuration constant on the boundary has no rim edge

`ExtendedDual.no_rim_edge_of_plusBoundary` assumes every boundary site is **up**. Only the
constancy is used, never the value. -/

/-- **NO RIM EDGE, FOR ANY CONFIGURATION CONSTANT ON THE BOUNDARY.** A rim edge needs a broken
bond that is an outward side; `outward_side_isBoundary` puts both its ends on the boundary, and
there the configuration does not change, so the bond is not broken. -/
theorem no_rim_edge_of_boundary_const {τ : Config n}
    (hconst : ∀ p q : Site n, isBoundary p = true → isBoundary q = true → τ p = τ q)
    (P : Plaq n) (d : Fin 4) : ¬ (extDual τ).Adj (Sum.inl P) (Sum.inr d) := by
  rintro ⟨hmem, hout⟩
  -- both ends of the side are boundary sites
  have hb := outward_side_isBoundary hout
  -- and a bond in the contour has ends where `τ` differs
  revert hmem hb
  refine Sym2.ind (fun a b hmem hb => ?_) (sideOf P d)
  rw [mem_contour] at hmem
  exact hmem.2 (hconst a b (hb a (Sym2.mem_mk_left a b)) (hb b (Sym2.mem_mk_right a b)))

/-- The `+` case is the special value `true`: `ExtendedDual.no_rim_edge_of_plusBoundary` is this
theorem with the value remembered, and is recovered here to show nothing was lost. -/
theorem no_rim_edge_of_plusBoundary' {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (d : Fin 4) : ¬ (extDual σ).Adj (Sum.inl P) (Sum.inr d) :=
  no_rim_edge_of_boundary_const
    (fun p q hp hq => by rw [hσ p hp, hσ q hq]) P d

/-! ## 3. And therefore no plaquette reaches a rim -/

/-- With no rim edge, a walk that starts at a plaquette stays at plaquettes. -/
theorem stays_inl {τ : Config n}
    (h : ∀ (P : Plaq n) (d : Fin 4), ¬ (extDual τ).Adj (Sum.inl P) (Sum.inr d)) :
    ∀ {a b : ExtV n}, (extDual τ).Walk a b → (∃ P, a = Sum.inl P) → ∃ Q, b = Sum.inl Q := by
  intro a b w
  induction w with
  | nil => exact id
  | @cons u v _ hadj _ ih =>
    rintro ⟨P, rfl⟩
    cases v with
    | inl Q => exact ih ⟨Q, rfl⟩
    | inr e => exact absurd hadj (h P e)

/-- **CONSTANT ON THE BOUNDARY ⟹ NO PLAQUETTE REACHES ANY RIM.** -/
theorem not_reachable_rim_of_boundary_const {τ : Config n}
    (hconst : ∀ p q : Site n, isBoundary p = true → isBoundary q = true → τ p = τ q)
    (P : Plaq n) (d : Fin 4) :
    ¬ (extDual τ).Reachable (Sum.inl P) (Sum.inr d) := by
  rintro ⟨w⟩
  obtain ⟨Q, hQ⟩ := stays_inl (no_rim_edge_of_boundary_const hconst) w ⟨P, rfl⟩
  exact absurd hQ (by simp)

/-! ## 4. The necessary condition on any repair of `ClusterReachesRim` -/

/-- **REACHING A RIM FORCES A BOUNDARY SITE OUTSIDE THE CLUSTER.** Contrapositive of §3 for the
cluster indicator, with the two boundary sites at which it differs resolved: `clusterOn` is
`true` exactly on the cluster, so a disagreement along the edge of the box is a boundary site the
cluster does not contain.

This is the shape of the constraint any repaired S3b-ii statement must satisfy.
`ReachesBoundary` gives a boundary site **inside** the cluster; this gives one **outside**. -/
theorem exists_boundary_outside_cluster_of_reaches_rim {σ : Config n} {x : Site n}
    {P : Plaq n} {d : Fin 4}
    (h : (extDual (clusterOn σ x)).Reachable (Sum.inl P) (Sum.inr d)) :
    ∃ p : Site n, isBoundary p = true ∧ ¬ (downGraph σ).Reachable x p := by
  by_contra hc
  refine not_reachable_rim_of_boundary_const (τ := clusterOn σ x) ?_ P d h
  intro p q hp hq
  have hall : ∀ y : Site n, isBoundary y = true → (downGraph σ).Reachable x y := by
    intro y hy
    by_contra hny
    exact hc ⟨y, hy, hny⟩
  rw [show clusterOn σ x p = true from clusterOn_eq_true_iff.mpr (hall p hp),
    show clusterOn σ x q = true from clusterOn_eq_true_iff.mpr (hall q hq)]

/-- **THE REFUTATION OF `ERRATUM 108`, RE-DERIVED FROM THE CRITERION.** All sites down: every
boundary site is in the cluster, so §4 leaves nothing outside it and no rim is reached. The
original proof computed the contour and found it empty; this one never mentions the contour. -/
theorem not_reachable_rim_allDown (hn : 0 < n) (x : Site n) (P : Plaq n) (d : Fin 4) :
    ¬ (extDual (clusterOn (S3bRefutation.allDown n) x)).Reachable (Sum.inl P) (Sum.inr d) := by
  intro h
  obtain ⟨p, hp, hnr⟩ := exists_boundary_outside_cluster_of_reaches_rim h
  refine hnr ?_
  rw [S3bRefutation.downGraph_allDown]
  exact (latticeGraph_connected hn).preconnected x p

/-! ## 5. The criterion localises to a single side of the box

§2 asks the configuration to be constant on the **whole** boundary. That is more than the proof
needs. A rim edge in direction `d` needs an outward side in direction `d`, and `Outward P 0`
forces `P.i = 0`, so the bond lies in **column zero** — not merely somewhere on the boundary.
Each direction pins its own side of the box, so the obstruction is one-sided. -/

/-- The side of the box that direction `d` points off: left, top, right, bottom. -/
-- Written as a disjunction guarded on `d.val` rather than a chain of `if`s: after `fin_cases d`
-- the guards are closed by `rfl` and nothing has to reduce a decidable equality on `Fin 4`.
def OnSide (d : Fin 4) (y : Site n) : Prop :=
  (d.val = 0 ∧ y.1.val = 0) ∨ (d.val = 1 ∧ y.2.val + 1 = n)
    ∨ (d.val = 2 ∧ y.1.val + 1 = n) ∨ (d.val = 3 ∧ y.2.val = 0)

/-- **AN OUTWARD SIDE LIES ALONG ITS OWN SIDE OF THE BOX**, which is sharper than
`outward_side_isBoundary`: not just on the boundary, but on the one edge direction `d` faces. -/
theorem outward_side_onSide {P : Plaq n} {d : Fin 4} (h : Outward P d) :
    ∀ y ∈ sideOf P d, OnSide d y := by
  have hi := P.hi
  have hj := P.hj
  fin_cases d
  · have h0 : P.i = 0 := (leftP_eq_self_iff P).mp h
    intro y hy
    refine Or.inl ⟨rfl, ?_⟩
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;> simp only [bl, tl] <;> omega
  · have h0 : P.j + 2 = n := (upP_eq_self_iff P).mp h
    intro y hy
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;> simp only [tl, tr] <;> omega
  · have h0 : P.i + 2 = n := (rightP_eq_self_iff P).mp h
    intro y hy
    refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;> simp only [tr, br] <;> omega
  · have h0 : P.j = 0 := (downP_eq_self_iff P).mp h
    intro y hy
    refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
    rcases Sym2.mem_iff.mp hy with rfl | rfl <;> simp only [br, bl] <;> omega

/-- **CONSTANT ALONG ONE SIDE KILLS THAT ONE RIM.** No hypothesis at all about the other three
sides of the box. -/
theorem no_rim_edge_of_side_const {τ : Config n} {d : Fin 4}
    (hconst : ∀ p q : Site n, OnSide d p → OnSide d q → τ p = τ q) (P : Plaq n) :
    ¬ (extDual τ).Adj (Sum.inl P) (Sum.inr d) := by
  rintro ⟨hmem, hout⟩
  have hb := outward_side_onSide hout
  revert hmem hb
  refine Sym2.ind (fun a b hmem hb => ?_) (sideOf P d)
  rw [mem_contour] at hmem
  exact hmem.2 (hconst a b (hb a (Sym2.mem_mk_left a b)) (hb b (Sym2.mem_mk_right a b)))

/-- With no edge into rim `d`, that rim is isolated, so a walk ending there began there. Stated
per direction, unlike `stays_inl`, which needs every rim edge gone at once — a walk may legally
visit the other three rims and come back. -/
theorem starts_at_rim {τ : Config n} {d : Fin 4}
    (h : ∀ Q : Plaq n, ¬ (extDual τ).Adj (Sum.inl Q) (Sum.inr d)) :
    ∀ {a b : ExtV n}, (extDual τ).Walk a b → b = Sum.inr d → a = Sum.inr d := by
  intro a b w
  induction w with
  | nil => exact id
  | @cons u v _ hadj _ ih =>
    intro hb
    have hv := ih hb
    subst hv
    cases u with
    | inl Q => exact absurd hadj (h Q)
    | inr e => exact hadj.elim

/-- **REACHING RIM `d` NEEDS THE CONFIGURATION TO CHANGE ALONG SIDE `d`.** -/
theorem not_reachable_rim_of_side_const {τ : Config n} {d : Fin 4}
    (hconst : ∀ p q : Site n, OnSide d p → OnSide d q → τ p = τ q) (P : Plaq n) :
    ¬ (extDual τ).Reachable (Sum.inl P) (Sum.inr d) := by
  rintro ⟨w⟩
  exact absurd (starts_at_rim (no_rim_edge_of_side_const hconst) w rfl) (by simp)

/-- **THE LOCALISED NECESSARY CONDITION.** If the plaquette at `x` reaches the rim in direction
`d`, then some site **on side `d` of the box** is outside the cluster of `x`. §4 gives a site
somewhere on the boundary; this names which of the four sides it is on. -/
theorem exists_onSide_outside_cluster_of_reaches_rim {σ : Config n} {x : Site n}
    {P : Plaq n} {d : Fin 4}
    (h : (extDual (clusterOn σ x)).Reachable (Sum.inl P) (Sum.inr d)) :
    ∃ p : Site n, OnSide d p ∧ ¬ (downGraph σ).Reachable x p := by
  by_contra hc
  refine not_reachable_rim_of_side_const (τ := clusterOn σ x) ?_ P h
  intro p q hp hq
  have hall : ∀ y : Site n, OnSide d y → (downGraph σ).Reachable x y := by
    intro y hy
    by_contra hny
    exact hc ⟨y, hy, hny⟩
  rw [show clusterOn σ x p = true from clusterOn_eq_true_iff.mpr (hall p hp),
    show clusterOn σ x q = true from clusterOn_eq_true_iff.mpr (hall q hq)]

/-! ## 6. The exact characterisation, which makes §§2 and 5 corollaries

Both criteria above are one-way: constancy along a side forbids reaching that rim. The
two-way statement is available and it is better, because it says what reaching a rim **is**.

A walk that arrives at `inr d` cannot have arrived from another rim — `extAdj` sends `inr, inr`
to `False` — so its last step comes from a plaquette carrying a broken outward side in direction
`d`. That is the whole content, and it turns "does `P` reach the rim" into "does `P` reach a
plaquette that is **already** at the edge, in direction `d`". -/

/-- A walk that **starts** at a rim either never leaves it or steps immediately to a plaquette
carrying a broken outward side in that direction. -/
theorem walk_from_rim {τ : Config n} :
    ∀ {a b : ExtV n}, (extDual τ).Walk a b → ∀ d : Fin 4, a = Sum.inr d →
      b = Sum.inr d ∨ ∃ Q : Plaq n, (extDual τ).Adj (Sum.inl Q) (Sum.inr d)
        ∧ (extDual τ).Reachable (Sum.inl Q) b := by
  intro a b w
  induction w with
  | nil => exact fun d h => Or.inl h
  | @cons u v _ hadj w' _ =>
    rintro d rfl
    cases v with
    | inl Q => exact Or.inr ⟨Q, hadj.symm, ⟨w'⟩⟩
    | inr e => exact hadj.elim

/-- **REACHING A RIM IS REACHING A PLAQUETTE THAT IS ALREADY AT THE EDGE.** `P` reaches the rim
in direction `d` exactly when it reaches, inside the extended graph, some plaquette `Q` whose
side `d` is broken and faces the outer face.

This is the residue of S3b-ii stated without any reference to the rim vertices: they were
scaffolding for the construction, and the question they encode is a question about plaquettes. -/
theorem reachable_rim_iff {τ : Config n} {P : Plaq n} {d : Fin 4} :
    (extDual τ).Reachable (Sum.inl P) (Sum.inr d) ↔
      ∃ Q : Plaq n, (sideOf Q d ∈ contour τ ∧ Outward Q d)
        ∧ (extDual τ).Reachable (Sum.inl P) (Sum.inl Q) := by
  constructor
  · intro h
    obtain ⟨w⟩ := h.symm
    rcases walk_from_rim w d rfl with hc | ⟨Q, hadj, hre⟩
    · exact absurd hc (by simp)
    · exact ⟨Q, hadj, hre.symm⟩
  · rintro ⟨Q, hadj, hre⟩
    exact hre.trans (SimpleGraph.Adj.reachable hadj)

/-- §5 falls out: with no broken outward side on that side of the box there is no such `Q`. -/
theorem not_reachable_rim_of_side_const' {τ : Config n} {d : Fin 4}
    (hconst : ∀ p q : Site n, OnSide d p → OnSide d q → τ p = τ q) (P : Plaq n) :
    ¬ (extDual τ).Reachable (Sum.inl P) (Sum.inr d) := by
  rw [reachable_rim_iff]
  rintro ⟨Q, hQ, -⟩
  exact no_rim_edge_of_side_const hconst Q hQ

end RimBoundary
