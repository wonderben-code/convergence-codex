import NeumannTailSharper
import TorusNormSharp

/-!
# The adjacency norm is exactly the degree on a regular graph

`SymmetricOpNorm` fences its own bound in its own words:

> *"It is not sharp and does not claim to be. `‖G.adjMatrix ℝ‖ ≤ Δ` is the standard degree bound on
> the spectral radius; nothing here says it is attained, and **the graphs where it is are not
> identified** (not attempted, not costed)."*

**A class where it is attained is identified here, and it is the one this project's field lives
on.** On a `Δ`-regular graph with at least one vertex the all-ones vector is an eigenvector of the
adjacency matrix at `Δ` — Mathlib's `adjMatrix_mulVec_const_apply_of_regular` — so
`GreenNormExact.abs_le_opNorm_of_mulVec_smul` (2026-09-03) gives `Δ ≤ ‖A‖`, and the bound closes:

```
‖G.adjMatrix ℝ‖ = Δ           on a Δ-regular graph
‖(torusGraph d n).adjMatrix ℝ‖ = 2d      at side length ≥ 3, every dimension
```

## What it makes exact, which is why it was written

`NeumannTailSharper` lists the tail constant's five factors and which stay inequalities:
`‖adjMatrix‖ ≤ Δ` was one of the two. **On a regular graph it is now an equality**, so of the five
factors in `Δ²/(m²(δ + m²)²)` — `‖green‖`, `‖A‖`, `‖Dinv‖`, `‖A‖`, `‖Dinv‖` — **all five are exact
there**, and the only remaining slack in the whole constant is the product inequality
`Matrix.l2_opNorm_mul`, which is slack for any pair that does not commute and is not a degree bound
at all. **That is a different kind of looseness and it is not addressed here.**

## What is NOT here

**Not the characterisation.** For a *connected* graph, `‖A‖ = Δ` holds **only** for regular graphs —
classical Perron–Frobenius — and that direction is **not proved here and not costed**
(`ERRATUM 246`, `ERRATUM 194`). This file gives the sufficient direction, which is the one the
constant needs.

**And the bound really is loose off this class**, which is why `SymmetricOpNorm`'s fence stands
where it stands: on the star `K_{1,n}` the adjacency eigenvalues are `±√n`, so `‖A‖ = √n` against
`Δ = n`. **That example is stated and not formalised.**

**No wall moves.** `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`), and a sharper factor in a
necessary condition is not a converse.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjNormRegular

open Matrix SimpleGraph BoxGraph TorusReflection
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The equality -/

/-- **`‖G.adjMatrix ℝ‖ = Δ` ON A `Δ`-REGULAR GRAPH.** The `≤` is `SymmetricOpNorm.norm_adjMatrix_le`
and the `≥` is the all-ones vector, which is an eigenvector at `Δ` there. -/
theorem norm_adjMatrix_eq_of_regular [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) : ‖G.adjMatrix ℝ‖ = (Δ : ℝ) := by
  classical
  have hle : ‖G.adjMatrix ℝ‖ ≤ (Δ : ℝ) :=
    SymmetricOpNorm.norm_adjMatrix_le G (fun p => le_of_eq (by rw [hreg p]))
  have hone : G.adjMatrix ℝ *ᵥ (fun _ => (1 : ℝ)) = (Δ : ℝ) • (fun _ => (1 : ℝ)) := by
    ext v
    have h := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := (1 : ℝ)) hreg
      (v := v)
    simpa using h
  have hvv : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) ≠ 0 := by
    rw [dotProduct]
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hge : |(Δ : ℝ)| ≤ ‖G.adjMatrix ℝ‖ :=
    GreenNormExact.abs_le_opNorm_of_mulVec_smul hvv hone
  rw [abs_of_nonneg (Nat.cast_nonneg Δ)] at hge
  exact le_antisymm hle hge

/-! ## 2. The periodic lattice -/

/-- **`‖(torusGraph d n).adjMatrix ℝ‖ = 2d`**, at every side length at least three and in every
dimension, off `RegularSelfEmbedding.torusGraph_isRegularOfDegree`. -/
theorem norm_adjMatrix_torus_eq {d n : ℕ} (hn : 3 ≤ n) :
    ‖(torusGraph d n).adjMatrix ℝ‖ = 2 * (d : ℝ) := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site (by omega)
  rw [norm_adjMatrix_eq_of_regular (torusGraph d n)
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn)]
  push_cast
  ring

end AdjNormRegular
