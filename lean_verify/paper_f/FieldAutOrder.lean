import FieldSimpleBox

/-!
# A graph with an automorphism that is not an involution has a repeated Laplacian eigenvalue

`FieldSimpleAut.graphAut_involutive` proves a fact about **graphs** from a fact about the
**measure**: if the propagator's spectrum is simple, every automorphism of the graph is an
involution. Its contrapositive is a **sufficient condition for failure**, and until this morning it
could only be stated about the propagator, because that is what its hypothesis is about.
`FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective` removed the propagator from the
statement. So the contrapositive can now be written with no mass, no propagator and no measure in
it, and it is a theorem about graphs and their Laplacians.

## What is proved

**`not_finrank_lapMatrix_le_one_of_not_involutive`** — a graph carrying an automorphism `θ` and a
vertex `p` with `θ(θ p) ≠ p` fails the eigenspace hypothesis the whole symmetry chain runs on.
**The mass is chosen, not carried**: the proof instantiates the chain at `m = 1`, which is legal
precisely because the conclusion does not mention a mass.

**`not_injective_lapMatrix_eigenvalues_of_not_involutive`** — **so such a graph has a repeated
Laplacian eigenvalue.** This is the statement worth having: an entirely graph-theoretic hypothesis
and an entirely graph-theoretic conclusion, whose only proof in this estate runs out through the
Gaussian field on the graph and back.

**`isGraphAut_top`** — every permutation is an automorphism of the complete graph, adjacency there
being `≠`, which a bijection preserves both ways.

**`i0`, `i1`, `i2`, `rot3`, `rot3_i0`, `rot3_i2`, `rot3_not_involutive`** — the three-cycle on the
first three vertices of `Fin (n + 3)`, and that it is not an involution.

**`not_injective_lapMatrix_eigenvalues_top`** — **so the complete graph on three or more vertices
has a repeated Laplacian eigenvalue**, from its rotational symmetry alone. Counted before the
sentence was written (`ERRATUM 450`): four files in `paper_f` mention the complete graph and
**this is the only one that mentions it beside a Laplacian**, so nothing in the estate had said
anything about its spectrum.

## What is NOT here

**THIS IS A SUFFICIENT CONDITION FOR FAILURE AND NOT A CHARACTERISATION, AND THE OTHER DIRECTION IS
ALREADY KNOWN TO BE FALSE.** `FieldInvolutionConverse.not_equiv_graphAut_involutive` exhibits two
vertices with no edge: every automorphism is an involution and the spectrum is degenerate anyway.
So the two conditions are related in exactly one direction and the estate now proves both halves of
that sentence.

**NO FAMILY IS RE-DERIVED THROUGH THIS.** The periodic lattices fail by
`FieldSimpleConnected.not_eigenvalues_injective_torus` and the boxes by
`FieldSimpleBox.not_eigenvalues_injective_box`, both through **frequencies**, not through
automorphisms. A cycle's rotation and a box's axis permutation are the obvious candidates for
re-deriving them here, and **neither is proved to be a graph automorphism anywhere in this estate**,
so neither is used and no claim of subsumption is made. **A `d = 2` box would not fall to this
argument in any case**: its axis swap is an involution.

**NO EIGENVALUE OF THE COMPLETE GRAPH IS COMPUTED.** Classically its Laplacian spectrum is
`0` together with `n` repeated `n − 1` times; **none of that is proved here** and the file says only
that two of them coincide.

**NO ORDER, NO GROUP, NO ACTION.** The hypothesis is `θ (θ p) ≠ p` at a single vertex, not *`θ` has
order greater than two* — the two are the same for a permutation but the file states the pointwise
form, which is what the chain's involution theorem gives. **No automorphism group is constructed**
and `Equiv.Perm` never appears as a group.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement in this file takes a
mass**, and that is the point of it — the mass is chosen inside the proof of the first theorem
and never reaches a conclusion. `isGraphAut_top` takes neither `Fintype` nor `DecidableEq` nor
`DecidableRel`, all three being `omit`ted; the two main theorems take all three, because a Laplacian
matrix needs them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldAutOrder

open Matrix GraphLaplacian FieldAutInvariance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. A non-involutive automorphism forces a degenerate Laplacian spectrum -/

theorem not_finrank_lapMatrix_le_one_of_not_involutive {θ : V ≃ V} (hθ : IsGraphAut G θ)
    {p : V} (hp : θ (θ p) ≠ p) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  refine hp (FieldSimpleAut.graphAut_involutive (m := 1) one_ne_zero
    (green_posDef G one_ne_zero).isHermitian ?_ hθ p)
  exact (FieldSimpleConverse.finrank_lapMatrix_le_one_iff one_ne_zero
    (green_posDef G one_ne_zero).isHermitian).mp hdim

/-- **A GRAPH WITH AN AUTOMORPHISM THAT IS NOT AN INVOLUTION HAS A REPEATED LAPLACIAN
EIGENVALUE.** No mass, no propagator and no measure appears in the statement; the proof runs
through the Gaussian field on the graph and back. -/
theorem not_injective_lapMatrix_eigenvalues_of_not_involutive {θ : V ≃ V} (hθ : IsGraphAut G θ)
    {p : V} (hp : θ (θ p) ≠ p) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := fun hinj =>
  not_finrank_lapMatrix_le_one_of_not_involutive hθ hp
    (FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj)

/-! ## 2. Every permutation is an automorphism of the complete graph -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isGraphAut_top (θ : V ≃ V) : IsGraphAut (⊤ : SimpleGraph V) θ := by
  intro p q
  simp [θ.injective.ne_iff]

/-! ## 3. The three-cycle on the first three vertices -/

def i0 (n : ℕ) : Fin (n + 3) := ⟨0, by omega⟩
def i1 (n : ℕ) : Fin (n + 3) := ⟨1, by omega⟩
def i2 (n : ℕ) : Fin (n + 3) := ⟨2, by omega⟩

theorem i2_ne_i0 (n : ℕ) : i2 n ≠ i0 n := by simp [i0, i2]
theorem i2_ne_i1 (n : ℕ) : i2 n ≠ i1 n := by simp [i1, i2]
theorem i1_ne_i0 (n : ℕ) : i1 n ≠ i0 n := by simp [i0, i1]

/-- The three-cycle on `0, 1, 2`, fixing everything else. -/
def rot3 (n : ℕ) : Fin (n + 3) ≃ Fin (n + 3) :=
  (Equiv.swap (i0 n) (i1 n)).trans (Equiv.swap (i1 n) (i2 n))

theorem rot3_i0 (n : ℕ) : rot3 n (i0 n) = i2 n := by
  rw [rot3, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]

theorem rot3_i2 (n : ℕ) : rot3 n (i2 n) = i1 n := by
  rw [rot3, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (i2_ne_i0 n) (i2_ne_i1 n), Equiv.swap_apply_right]

theorem rot3_not_involutive (n : ℕ) : rot3 n (rot3 n (i0 n)) ≠ i0 n := by
  rw [rot3_i0, rot3_i2]
  exact i1_ne_i0 n

/-- **SO THE COMPLETE GRAPH ON THREE OR MORE VERTICES HAS A REPEATED LAPLACIAN EIGENVALUE**, from
its rotational symmetry alone. -/
theorem not_injective_lapMatrix_eigenvalues_top (n : ℕ) :
    ¬ Function.Injective
      (FieldSimpleConverse.lapMatrix_isHermitian (⊤ : SimpleGraph (Fin (n + 3)))).eigenvalues :=
  not_injective_lapMatrix_eigenvalues_of_not_involutive (isGraphAut_top (rot3 n))
    (rot3_not_involutive n)

end FieldAutOrder
