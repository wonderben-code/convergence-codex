import FieldAutInvariance
import Mathlib.Combinatorics.SimpleGraph.Circulant
import ReflectedFormCongr

/-!
# A non-involutive graph automorphism, so that the weakening is exercised

`FieldAutInvariance` weakened `GraphReflection.IsRefl` — adjacency preservation **bundled with**
`Function.Involutive` — down to `IsGraphAut`, adjacency preservation alone, and proved the Gaussian
field invariant under every such map. Its own §3 says the estate's only constructed automorphisms
are the box reflections, and the watchlist item for the OS axioms records the consequence under the
heading **HONEST WEAKNESS**: *"the estate constructs no non-involutive automorphism — no torus
translation, no coordinate permutation — so nothing exercises the weakening."*

**This file is one such automorphism.** Rotation of a cycle by one step: `cycleRot n : u ↦ u + 1` on
`Fin (n + 3)`, which preserves `SimpleGraph.cycleGraph`'s adjacency because that adjacency is
stated as a **difference**, `u - v = 1 ∨ v - u = 1`, and a common shift cancels in a difference.

> **§1. It is an automorphism.** `isGraphAut_cycleRot`. One `sub` cancellation; no case split
> and no orientation argument, which is the whole reason a rotation is the cheapest witness
> available.
>
> **§2. It is not involutive.** `cycleRot_not_involutive` — it applied twice is `+2`, and `2 ≠ 0` in
> `Fin (n + 3)` for every `n`, since `2 < n + 3`. **This is what makes the file a witness rather
> than a second example**: `IsRefl` bundles involutivity, so `cycleRot` satisfies `IsGraphAut` and
> cannot satisfy `IsRefl` — the weaker hypothesis is **strictly** weaker, exhibited and not
> asserted.
>
> **§3. The field is invariant under it.** `gaussianField_map_cycleRot` —
> `FieldAutInvariance`'s theorem at it.
>
> **§4. And at the map the estate already had.** `isGraphAut_torusRot` is
> `ReflectedFormCongr.rot_adj` read as an `IsGraphAut` — the two are the same statement, so this is
> a citation and not a proof. `torusRot_not_involutive` and `gaussianField_map_torusRot` complete
> the connection nobody had made.

**WHAT THIS IS NOT, as of 2026-09-02.** **It moves no OS axiom and no wall.** The watchlist item's
`STILL OPEN` line — OS0, OS1, OS4 — is untouched, and `FieldAutInvariance`'s capitalised warning
stands as written: **a symmetry is not an axiom**, invariance under a graph automorphism is not OS3,
and a finite graph has an automorphism group where OS3 asks for the Euclidean group. Nothing here is
attempted toward OS1 and no cost is claimed (`ERRATUM 194`, `ERRATUM 246`).

**Nor is it a new invariance theorem.** Every step of the mathematics is
`FieldAutInvariance.gaussianField_map_perm`'s; this file supplies the hypothesis. **What it removes
is not a hypothesis but a doubt** — that the generalisation might have been vacuous, covering
exactly the involutions the estate already had. **And §4 cites `rot_adj` rather than reproving it**:
`ReflectedFormCongr` proves that statement by `decide` over a four-element graph and nothing here
improves on it. Nothing earlier is restated, deleted or deprecated, and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleRotationAut

open SimpleGraph FieldAutInvariance

/-! ### §1. Rotation of a cycle is a graph automorphism -/

/-- **ROTATION BY ONE STEP**, on a cycle of length at least three. -/
def cycleRot (n : ℕ) : Fin (n + 3) ≃ Fin (n + 3) := Equiv.addRight 1

@[simp] theorem cycleRot_apply (n : ℕ) (u : Fin (n + 3)) : cycleRot n u = u + 1 := rfl

/-- **IT PRESERVES ADJACENCY**, because `cycleGraph`'s adjacency is a statement about a
DIFFERENCE and a common shift cancels in a difference. -/
theorem isGraphAut_cycleRot (n : ℕ) : IsGraphAut (cycleGraph (n + 3)) (cycleRot n) := by
  intro p q
  simp only [cycleRot_apply]
  rw [show n + 3 = (n + 1) + 2 from rfl] at *
  rw [cycleGraph_adj, cycleGraph_adj]
  simp [add_sub_add_right_eq_sub]

/-! ### §2. And it is not involutive -/

/-- `1 + 1 ≠ 0` in `Fin (n + 3)`, which is the whole of §2: the shift is by two and the cycle has
at least three vertices. Stated in the `1 + 1` form the double shift produces, so that §2 needs no
conversion between it and `2`. -/
theorem one_add_one_ne_zero (n : ℕ) : (1 : Fin (n + 3)) + 1 ≠ 0 := by
  have h : (((1 : Fin (n + 3)) + 1 : Fin (n + 3)) : ℕ) = 2 := by
    simp [Fin.val_add, Nat.mod_eq_of_lt]
  intro hc
  rw [hc] at h
  simp at h

/-- **THE WITNESS.** `cycleRot` applied twice is a shift by `2`, so it is not the identity; it
satisfies `IsGraphAut` and **cannot** satisfy `GraphReflection.IsRefl`, which bundles
`Function.Involutive`. The weakening `FieldAutInvariance` performed is therefore strict. -/
theorem cycleRot_not_involutive (n : ℕ) : ¬ Function.Involutive (cycleRot n) := by
  intro h
  have h0 := h 0
  simp only [cycleRot_apply, zero_add] at h0
  exact one_add_one_ne_zero n h0

/-! ### §3. The Gaussian field is invariant under it -/

/-- **`FieldAutInvariance`'s THEOREM AT A NON-INVOLUTIVE MAP.** Every step is that theorem's; what
this supplies is the hypothesis at a map the estate did not have. -/
theorem gaussianField_map_cycleRot (n : ℕ) [DecidableRel (cycleGraph (n + 3)).Adj] {m : ℝ}
    (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (cycleGraph (n + 3)) m).map (permField (cycleRot n))
      = GraphLaplacian.gaussianField (cycleGraph (n + 3)) m :=
  gaussianField_map_perm (isGraphAut_cycleRot n) hm

/-! ### §4. And at the map the estate already had -/

/-- **`ReflectedFormCongr.rot_adj` IS THE `IsGraphAut` STATEMENT**, and saying so is the whole of
this theorem — the estate has had a non-involutive adjacency-preserving bijection since that file
was written, under a name that never mentions automorphisms. -/
theorem isGraphAut_torusRot :
    IsGraphAut (TorusReflection.torusGraph 1 4) ReflectedFormCongr.rot :=
  fun p q => ReflectedFormCongr.rot_adj p q

/-- **AND IT IS NOT INVOLUTIVE EITHER**: two steps round a four-cycle is not the identity. -/
theorem torusRot_not_involutive : ¬ Function.Involutive ReflectedFormCongr.rot := by
  intro h
  have h0 := h ((TorusCycleGraph.siteEquiv 4).symm 0)
  revert h0
  decide

/-- **THE CONNECTION NOBODY HAD MADE.** `FieldAutInvariance`'s theorem at the estate's own
rotation. -/
theorem gaussianField_map_torusRot {m : ℝ} (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (TorusReflection.torusGraph 1 4) m).map
        (permField ReflectedFormCongr.rot)
      = GraphLaplacian.gaussianField (TorusReflection.torusGraph 1 4) m :=
  gaussianField_map_perm isGraphAut_torusRot hm

end CycleRotationAut
