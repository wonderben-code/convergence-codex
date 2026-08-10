import DualObstruction
import IsingContourPlaquette

/-!
# Plaquettes as objects, their four sides, and which sides face outwards

`DualObstruction` ends by saying that the remaining steps of the dual-lattice plan are
"geometry about faces, which this estate has no object for". This file supplies the
object. It is the first half of the dual construction: the plaquettes as a type, their
four sides as bonds of the box, the fact that the four are four *distinct* bonds, and
the correspondence

> a side of `P` faces the outside of the box **exactly** when `P` sits at the
> corresponding extreme of the plaquette array — and otherwise the plaquette on the
> other side of it exists and has that same bond as *its* opposite side.

That correspondence is the whole content of "a broken bond off the outer edge separates
two distinct unit squares", which `DualObstruction` could only state. Combined with
`PlusBoundary`, it gives that **no broken bond of a `+`-boundary configuration is a
side facing outwards** — the fact that makes the dual a simple graph rather than a
multigraph.

## Indexing

`Plaq n` is a structure carrying `i`, `j` and the two bounds `i + 1 < n`, `j + 1 < n`,
which is exactly the parametrisation `IsingContourPlaquette` already uses for its
corners. Nothing is re-derived: `bl`, `tl`, `tr`, `br` and the four adjacency witnesses
are that file's, and the four sides below are its four `even_plaquette` terms in the
same order, so that theorem will transfer verbatim when the dual graph is built.

## What this file does not do

It does not build the dual graph and it does not mention degrees. The remaining step is
the count: that the dual neighbours of `P` are in bijection with the broken sides of
`P`, whose evenness is `IsingContourPlaquette.even_plaquette`. Every ingredient for the
existence half of that bijection is here — `sideR_leftPlaq`, `sideL_rightPlaq`,
`sideU_downPlaq`, `sideD_upPlaq` — and so is the injectivity half, the six pairwise
distinctness lemmas `sideL_ne_sideU` … `sideR_ne_sideD`. Nothing here mentions
"surrounds" or `3 ^ |γ|`, which remain undefined in this estate.
-/

namespace PlaquetteLattice

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField IsingContourPlaquette
open DualObstruction

variable {n : ℕ}

/-! ## 1. The type of plaquettes

A plaquette of the `n × n` box is a unit square, named by its bottom-left corner
together with the two bounds that make its top-right corner a site. Carrying the bounds
in the structure is what lets every corner and side below be a total function. -/

/-- A unit square of the `n × n` box, named by its bottom-left corner. -/
@[ext]
structure Plaq (n : ℕ) where
  /-- First coordinate of the bottom-left corner. -/
  i : ℕ
  /-- Second coordinate of the bottom-left corner. -/
  j : ℕ
  /-- The square fits: its right edge is still inside the box. -/
  hi : i + 1 < n
  /-- The square fits: its top edge is still inside the box. -/
  hj : j + 1 < n

instance : DecidableEq (Plaq n) := fun P Q => by
  rw [Plaq.ext_iff]
  exact inferInstanceAs (Decidable (_ ∧ _))

/-- The bottom-left corner, as a site. -/
def corner (P : Plaq n) : Site n :=
  (⟨P.i, by have := P.hi; omega⟩, ⟨P.j, by have := P.hj; omega⟩)

theorem corner_injective : Function.Injective (corner (n := n)) := by
  intro P Q h
  have h1 : P.i = Q.i := congrArg (fun p => (p.1 : Fin n).val) h
  have h2 : P.j = Q.j := congrArg (fun p => (p.2 : Fin n).val) h
  exact Plaq.ext h1 h2

noncomputable instance : Fintype (Plaq n) := Fintype.ofInjective corner corner_injective

/-! ## 2. The four sides

Written in the order `IsingContourPlaquette.even_plaquette` uses them — left, top,
right, bottom, i.e. `bl–tl`, `tl–tr`, `tr–br`, `br–bl` — so that the evenness theorem
transfers term by term. Each is a genuine bond of the box, which is that file's four
adjacency witnesses. -/

/-- The left side of `P`: the bond at first coordinate `P.i`. -/
def sideL (P : Plaq n) : Sym2 (Site n) := s(bl P.i P.j P.hi P.hj, tl P.i P.j P.hi P.hj)
/-- The top side of `P`: the bond at second coordinate `P.j + 1`. -/
def sideU (P : Plaq n) : Sym2 (Site n) := s(tl P.i P.j P.hi P.hj, tr P.i P.j P.hi P.hj)
/-- The right side of `P`: the bond at first coordinate `P.i + 1`. -/
def sideR (P : Plaq n) : Sym2 (Site n) := s(tr P.i P.j P.hi P.hj, br P.i P.j P.hi P.hj)
/-- The bottom side of `P`: the bond at second coordinate `P.j`. -/
def sideD (P : Plaq n) : Sym2 (Site n) := s(br P.i P.j P.hi P.hj, bl P.i P.j P.hi P.hj)

theorem adj_sideL (P : Plaq n) : adj (bl P.i P.j P.hi P.hj) (tl P.i P.j P.hi P.hj) :=
  adj_bl_tl P.i P.j P.hi P.hj
theorem adj_sideU (P : Plaq n) : adj (tl P.i P.j P.hi P.hj) (tr P.i P.j P.hi P.hj) :=
  adj_tl_tr P.i P.j P.hi P.hj
theorem adj_sideR (P : Plaq n) : adj (tr P.i P.j P.hi P.hj) (br P.i P.j P.hi P.hj) :=
  adj_tr_br P.i P.j P.hi P.hj
theorem adj_sideD (P : Plaq n) : adj (br P.i P.j P.hi P.hj) (bl P.i P.j P.hi P.hj) :=
  adj_br_bl P.i P.j P.hi P.hj

/-! ### The four sides are four distinct bonds

Needed for the injectivity half of the degree count: two different sides of one
plaquette must not be the same bond, or the count would collapse. -/

theorem sideL_ne_sideU (P : Plaq n) : sideL P ≠ sideU P := by
  rw [sideL, sideU, Ne, Sym2.eq_iff]
  simp only [bl, tl, tr, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

theorem sideL_ne_sideR (P : Plaq n) : sideL P ≠ sideR P := by
  rw [sideL, sideR, Ne, Sym2.eq_iff]
  simp only [bl, tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

theorem sideL_ne_sideD (P : Plaq n) : sideL P ≠ sideD P := by
  rw [sideL, sideD, Ne, Sym2.eq_iff]
  simp only [bl, tl, br, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

theorem sideU_ne_sideR (P : Plaq n) : sideU P ≠ sideR P := by
  rw [sideU, sideR, Ne, Sym2.eq_iff]
  simp only [tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

theorem sideU_ne_sideD (P : Plaq n) : sideU P ≠ sideD P := by
  rw [sideU, sideD, Ne, Sym2.eq_iff]
  simp only [tl, tr, br, bl, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

theorem sideR_ne_sideD (P : Plaq n) : sideR P ≠ sideD P := by
  rw [sideR, sideD, Ne, Sym2.eq_iff]
  simp only [tr, br, bl, Prod.mk.injEq, Fin.mk.injEq, not_or]
  omega

/-! ## 3. The neighbouring plaquette across a side

A side of `P` that does not face outwards is shared with exactly one other plaquette,
and these four definitions produce it. The four `side.._..Plaq` lemmas say the shared
bond really is the same bond seen from the other side — the existence half of the
bijection the degree count needs. -/

/-- The plaquette to the left of `P`, when `P` is not at the left edge. -/
def leftPlaq (P : Plaq n) (_h : P.i ≠ 0) : Plaq n :=
  ⟨P.i - 1, P.j, by have := P.hi; omega, P.hj⟩
/-- The plaquette to the right of `P`, when its right side is not the box's edge. -/
def rightPlaq (P : Plaq n) (h : P.i + 2 < n) : Plaq n := ⟨P.i + 1, P.j, h, P.hj⟩
/-- The plaquette below `P`, when `P` is not at the bottom edge. -/
def downPlaq (P : Plaq n) (_h : P.j ≠ 0) : Plaq n :=
  ⟨P.i, P.j - 1, P.hi, by have := P.hj; omega⟩
/-- The plaquette above `P`, when its top side is not the box's edge. -/
def upPlaq (P : Plaq n) (h : P.j + 2 < n) : Plaq n := ⟨P.i, P.j + 1, P.hi, h⟩

/-- The left neighbour's right side is `P`'s left side. -/
theorem sideR_leftPlaq (P : Plaq n) (h : P.i ≠ 0) : sideR (leftPlaq P h) = sideL P := by
  have hP := P.hi
  rw [sideR, sideL, Sym2.eq_iff]
  simp only [leftPlaq, bl, tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, and_true]
  all_goals omega

/-- The right neighbour's left side is `P`'s right side. -/
theorem sideL_rightPlaq (P : Plaq n) (h : P.i + 2 < n) : sideL (rightPlaq P h) = sideR P := by
  rw [sideL, sideR, Sym2.eq_iff]
  simp only [rightPlaq, bl, tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, and_true,
    true_and, or_true]

/-- The lower neighbour's top side is `P`'s bottom side. -/
theorem sideU_downPlaq (P : Plaq n) (h : P.j ≠ 0) : sideU (downPlaq P h) = sideD P := by
  have hP := P.hj
  rw [sideU, sideD, Sym2.eq_iff]
  simp only [downPlaq, bl, tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, true_and]
  all_goals omega

/-- The upper neighbour's bottom side is `P`'s top side. -/
theorem sideD_upPlaq (P : Plaq n) (h : P.j + 2 < n) : sideD (upPlaq P h) = sideU P := by
  rw [sideD, sideU, Sym2.eq_iff]
  simp only [upPlaq, bl, tl, tr, br, Prod.mk.injEq, Fin.mk.injEq, and_true, or_true]

theorem leftPlaq_ne (P : Plaq n) (h : P.i ≠ 0) : leftPlaq P h ≠ P := by
  intro hEq
  have : P.i - 1 = P.i := congrArg Plaq.i hEq
  omega

theorem rightPlaq_ne (P : Plaq n) (h : P.i + 2 < n) : rightPlaq P h ≠ P := by
  intro hEq
  have : P.i + 1 = P.i := congrArg Plaq.i hEq
  omega

theorem downPlaq_ne (P : Plaq n) (h : P.j ≠ 0) : downPlaq P h ≠ P := by
  intro hEq
  have : P.j - 1 = P.j := congrArg Plaq.j hEq
  omega

theorem upPlaq_ne (P : Plaq n) (h : P.j + 2 < n) : upPlaq P h ≠ P := by
  intro hEq
  have : P.j + 1 = P.j := congrArg Plaq.j hEq
  omega

/-! ## 4. The sides that face outwards

A side faces the outside of the box exactly when the neighbour across it does not
exist, and in that case both of its endpoints are boundary sites. That is the
hypothesis `DualObstruction.notMem_contour_of_plusBoundary` consumes, so §5 closes the
loop: under `+` boundary conditions an outward-facing side is never broken. -/

/-- **The left side of `P` faces outwards exactly when `P` is at the left edge.**
Both directions are proved: the interesting one is `→`, which has to rule out a side
being outward-facing *by accident* — both its endpoints lying on the boundary for
unrelated reasons, one via a row and one via a column. It cannot happen, and the
arithmetic that says so is the two bounds carried in `Plaq`. -/
theorem bl_tl_boundary_iff (P : Plaq n) :
    (isBoundary (bl P.i P.j P.hi P.hj) = true ∧ isBoundary (tl P.i P.j P.hi P.hj) = true)
      ↔ P.i = 0 := by
  have h1 := P.hi
  have h2 := P.hj
  simp only [isBoundary, bl, tl, decide_eq_true_eq]
  omega

/-- The right side faces outwards exactly at the right edge. -/
theorem tr_br_boundary_iff (P : Plaq n) :
    (isBoundary (tr P.i P.j P.hi P.hj) = true ∧ isBoundary (br P.i P.j P.hi P.hj) = true)
      ↔ P.i + 2 = n := by
  have h1 := P.hi
  have h2 := P.hj
  simp only [isBoundary, tr, br, decide_eq_true_eq]
  omega

/-- The bottom side faces outwards exactly at the bottom edge. -/
theorem br_bl_boundary_iff (P : Plaq n) :
    (isBoundary (br P.i P.j P.hi P.hj) = true ∧ isBoundary (bl P.i P.j P.hi P.hj) = true)
      ↔ P.j = 0 := by
  have h1 := P.hi
  have h2 := P.hj
  simp only [isBoundary, br, bl, decide_eq_true_eq]
  omega

/-- The top side faces outwards exactly at the top edge. -/
theorem tl_tr_boundary_iff (P : Plaq n) :
    (isBoundary (tl P.i P.j P.hi P.hj) = true ∧ isBoundary (tr P.i P.j P.hi P.hj) = true)
      ↔ P.j + 2 = n := by
  have h1 := P.hi
  have h2 := P.hj
  simp only [isBoundary, tl, tr, decide_eq_true_eq]
  omega

theorem isBoundary_of_i_zero (P : Plaq n) (h : P.i = 0) :
    isBoundary (bl P.i P.j P.hi P.hj) = true ∧ isBoundary (tl P.i P.j P.hi P.hj) = true :=
  (bl_tl_boundary_iff P).mpr h

theorem isBoundary_of_i_top (P : Plaq n) (h : P.i + 2 = n) :
    isBoundary (tr P.i P.j P.hi P.hj) = true ∧ isBoundary (br P.i P.j P.hi P.hj) = true :=
  (tr_br_boundary_iff P).mpr h

theorem isBoundary_of_j_zero (P : Plaq n) (h : P.j = 0) :
    isBoundary (br P.i P.j P.hi P.hj) = true ∧ isBoundary (bl P.i P.j P.hi P.hj) = true :=
  (br_bl_boundary_iff P).mpr h

theorem isBoundary_of_j_top (P : Plaq n) (h : P.j + 2 = n) :
    isBoundary (tl P.i P.j P.hi P.hj) = true ∧ isBoundary (tr P.i P.j P.hi P.hj) = true :=
  (tl_tr_boundary_iff P).mpr h

/-! ## 5. Under `+` boundary conditions, an outward-facing side is never broken

This is the sentence `DualObstruction` could only state, now proved for each of the
four sides. It is what makes every broken bond of a `+`-boundary configuration an
*interior* side, shared with a second plaquette that exists — so the dual is a simple
graph and its degree at `P` counts broken sides of `P`. -/

theorem sideL_notMem_contour {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (h : P.i = 0) : sideL P ∉ contour σ := by
  obtain ⟨h1, h2⟩ := isBoundary_of_i_zero P h
  exact notMem_contour_of_plusBoundary hσ h1 h2

theorem sideR_notMem_contour {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (h : P.i + 2 = n) : sideR P ∉ contour σ := by
  obtain ⟨h1, h2⟩ := isBoundary_of_i_top P h
  exact notMem_contour_of_plusBoundary hσ h1 h2

theorem sideD_notMem_contour {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (h : P.j = 0) : sideD P ∉ contour σ := by
  obtain ⟨h1, h2⟩ := isBoundary_of_j_zero P h
  exact notMem_contour_of_plusBoundary hσ h1 h2

theorem sideU_notMem_contour {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (h : P.j + 2 = n) : sideU P ∉ contour σ := by
  obtain ⟨h1, h2⟩ := isBoundary_of_j_top P h
  exact notMem_contour_of_plusBoundary hσ h1 h2

/-- **Every broken side of a `+`-boundary configuration has a plaquette on the other
side of it.** The four cases above, assembled: the missing-neighbour condition is
exactly the outward-facing condition, and outward-facing sides are unbroken. -/
theorem exists_leftPlaq_of_sideL_mem {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (hmem : sideL P ∈ contour σ) : P.i ≠ 0 := fun h => sideL_notMem_contour hσ P h hmem

theorem exists_rightPlaq_of_sideR_mem {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (hmem : sideR P ∈ contour σ) : P.i + 2 < n := by
  have hne : P.i + 2 ≠ n := fun h => sideR_notMem_contour hσ P h hmem
  have := P.hi
  omega

theorem exists_downPlaq_of_sideD_mem {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (hmem : sideD P ∈ contour σ) : P.j ≠ 0 := fun h => sideD_notMem_contour hσ P h hmem

theorem exists_upPlaq_of_sideU_mem {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n)
    (hmem : sideU P ∈ contour σ) : P.j + 2 < n := by
  have hne : P.j + 2 ≠ n := fun h => sideU_notMem_contour hσ P h hmem
  have := P.hj
  omega

end PlaquetteLattice
