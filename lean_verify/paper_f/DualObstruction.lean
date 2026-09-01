import IsingBoundaryField
import ContourCircuits

/-!
# The boundary hypothesis the dual lattice needs, and the corner that forces it

`ContourCircuits` showed that the circuit decomposition applies to this estate's
contour the moment the broken-bond graph has even degrees, and that in the primal it
does not. The evenness lives on the **dual** lattice, and `WALLS.md` W3 records the
plan for building one. This file is the part of that plan that can be checked before
the dual exists, and it is here because checking it found a hole.

## The hole

The dual of the box needs a vertex for the unbounded face as well as one per unit
square. **The corner square has two of its four sides on the outer boundary of the
box**, and both of them separate it from that same unbounded face — so the dual of the
free-boundary box has two edges between one pair of vertices, which `SimpleGraph`
cannot express, and a dual degree computed in a `SimpleGraph` would come out one short
there. `corner_bonds_mem_contour` shows this is not hypothetical: both of those bonds
are broken at once for the configuration that is down at the corner and up elsewhere.

## The repair, stated on this estate's own objects

Hold the boundary up. Then no bond with **both** ends on the boundary is ever broken
(`notMem_contour_of_plusBoundary`), so every broken bond has an interior end
(`exists_interior_end_of_mem_contour`). A bond lying on the outer edge of the box
*has* both ends on the boundary — that direction is all this needs, and the converse
is not used — so no broken bond lies on the outer edge, so every broken bond separates
two distinct unit squares, and two distinct unit squares share at most one side.

**Only the first two of those steps are theorems here.** The rest is geometry about
faces, which this estate has no object for; it is stated so the next unit knows what
it is committing to, not asserted as proved. What *is* proved is the part that
mentions configurations, which is the part a witness could refute.

## What this does not do

It does not build the dual, it does not give even degrees (the `+` boundary makes the
dual *simple*; it does nothing to make the *primal* even, and
`ContourCircuits.not_evenDegrees_brokenGraph_sigmaOdd` is unaffected by it), and it
says nothing about "surrounds" or `3 ^ |γ|`.
`IsingBoundaryField.MagnetisationBound` is untouched.


## ⚠ "THIS ESTATE HAS NO OBJECT FOR" WAS FALSE THIRTEEN MINUTES LATER. Annotated 1 September 2026

Kept as written (`ERRATUM 94`). This header says the remaining steps are *"geometry about faces,
which this estate has no object for"* at **2026-08-10 15:38**. `paper_f/PlaquetteLattice.lean` was
committed at **15:51** — thirteen minutes — and its opening sentence quotes this one and says *"This
file supplies the object."* `paper_f/DualGraph.lean` (16:02) and `paper_f/DualUnique.lean` (16:43)
complete the construction.

**So the successor knew and this file never learned**, which is the one-directional habit
`ERRATUM 389` records. The stated obstruction was accurate, was acted on immediately, and reads
here as though it still stands.
-/

namespace DualObstruction

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField

variable {n : ℕ}

/-! ## 1. The `+` boundary condition

`IsingBoundaryField.isBoundary` already names the first or last row or column. The
condition below is the textbook `+` boundary condition written against it, as a
predicate on configurations rather than as a term in an energy — `IsingBoundaryField`
takes the other route, rewarding boundary spins with a field, and the two are
different objects for different purposes. -/

/-- The `+` boundary condition: every boundary site is up. -/
def PlusBoundary (σ : Config n) : Prop := ∀ p : Site n, isBoundary p = true → σ p = true

/-- **Under `+` boundary conditions, no bond with both ends on the boundary is
broken.** Immediate — both ends are up, so they agree — and it is the whole content
of the repair: the bonds lying on the outer edge of the box are exactly these. -/
theorem notMem_contour_of_plusBoundary {σ : Config n} (h : PlusBoundary σ) {p q : Site n}
    (hp : isBoundary p = true) (hq : isBoundary q = true) : s(p, q) ∉ contour σ := by
  rw [mem_contour]
  rintro ⟨-, hne⟩
  exact hne ((h p hp).trans (h q hq).symm)

/-- Equivalently: every broken bond has an end in the interior. -/
theorem exists_interior_end_of_mem_contour {σ : Config n} (h : PlusBoundary σ)
    {p q : Site n} (hmem : s(p, q) ∈ contour σ) :
    isBoundary p = false ∨ isBoundary q = false := by
  cases hp : isBoundary p with
  | false => exact Or.inl rfl
  | true =>
    cases hq : isBoundary q with
    | false => exact Or.inr rfl
    | true => exact absurd hmem (notMem_contour_of_plusBoundary h hp hq)

/-- The all-up configuration satisfies it, so the condition is not empty. -/
theorem plusBoundary_allTrue : PlusBoundary (fun _ : Site n => true) := fun _ _ => rfl

/-! ## 2. The corner, and why the condition is not decoration

Without it the two outer sides of the corner square can both be broken at once, which
is exactly the configuration that makes the free-boundary dual a multigraph. The
witness is the smallest one: turn the corner site down. -/

/-- Down at the corner of the 3×3 box, up everywhere else. -/
def cornerDown : Config 3 := fun p => decide (p ≠ ((0 : Fin 3), (0 : Fin 3)))

/-- **Both bonds at the corner are broken at once.** These are the two sides of the
corner square that lie on the outer edge of the box, and both separate that square
from the unbounded face — the two parallel dual edges a `SimpleGraph` cannot hold. -/
theorem corner_bonds_mem_contour :
    s(((0 : Fin 3), (0 : Fin 3)), ((0 : Fin 3), (1 : Fin 3))) ∈ contour cornerDown ∧
      s(((0 : Fin 3), (0 : Fin 3)), ((1 : Fin 3), (0 : Fin 3))) ∈ contour cornerDown := by
  constructor <;> decide

/-- All four endpoints of those two bonds are boundary sites of the box, so both bonds
lie on the outer edge — which is what makes them share a face. -/
theorem corner_bonds_boundary :
    isBoundary ((0 : Fin 3), (0 : Fin 3)) = true ∧
      isBoundary ((0 : Fin 3), (1 : Fin 3)) = true ∧
      isBoundary ((1 : Fin 3), (0 : Fin 3)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- And the witness is exactly a violation of the `+` condition, which is the point:
`notMem_contour_of_plusBoundary` and `corner_bonds_mem_contour` are consistent, and
the hypothesis is what separates them. -/
theorem not_plusBoundary_cornerDown : ¬ PlusBoundary cornerDown := by
  intro h
  have := h ((0 : Fin 3), (0 : Fin 3)) (by decide)
  simp [cornerDown] at this

/-- The `+` condition kills this witness and every other one of its shape: under it
neither corner bond can be broken. -/
theorem corner_bonds_notMem_of_plusBoundary {σ : Config 3} (h : PlusBoundary σ) :
    s(((0 : Fin 3), (0 : Fin 3)), ((0 : Fin 3), (1 : Fin 3))) ∉ contour σ ∧
      s(((0 : Fin 3), (0 : Fin 3)), ((1 : Fin 3), (0 : Fin 3))) ∉ contour σ :=
  ⟨notMem_contour_of_plusBoundary h (by decide) (by decide),
    notMem_contour_of_plusBoundary h (by decide) (by decide)⟩

end DualObstruction
