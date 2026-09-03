import OpNormTopEigenvalue

/-!
# A lower bound on the Laplacian's operator norm — the estate's first

`LaplacianOpNorm` bounds `‖G.lapMatrix ℝ‖ ≤ 2Δ` and `LaplacianNormSharp` says when that is an
equality. **No lower bound on either graph operator's norm existed**, at any graph. Measured
2026-09-03 before this file: of the 80 lines in `paper_f/` carrying `≤ ‖`, every one outside the
day's own norm chain is a Cauchy–Schwarz bound, a coordinate bound, an inner-product estimate or a
`ContinuousLinearMap` bound — **not one has `‖lapMatrix …‖` or `‖massive …‖` on the large side**.
The nearest neighbour is `FrobeniusTopBound`, which sandwiches a top eigenvalue as
`‖A‖_F / √N ≤ λ_top ≤ ‖A‖_F` — the **Frobenius** norm, with `opNorm` occurring nowhere in it
(`ERRATUM 438`'s addendum measured that), and no graph in sight. So a reader of the Laplacian chain
had `0 ≤ ‖L‖` and nothing else.

```
(deg u + deg v + 2) / 2  ≤  ‖G.lapMatrix ℝ‖        whenever u ∼ v
```

and the massive form adds `m²`. **On a `Δ`-regular graph this is `Δ + 1`**, so with
`LaplacianOpNorm.norm_lapMatrix_le` the norm is pinned in `[Δ + 1, 2Δ]`, and with
`LaplacianNormSharp.norm_lapMatrix_lt_of_no_component_colorable` a regular graph with no
two-colourable component has `Δ + 1 ≤ ‖L‖ < 2Δ` — the first two-sided statement about this object.

## The witness and the tool

The vector is `Pi.single u 1 - Pi.single v 1`, and the whole computation is four matrix entries:
`x ⬝ᵥ L *ᵥ x = L u u - L u v - L v u + L v v = deg u + deg v + 2`, with `x ⬝ᵥ x = 2`. No edge sum
is expanded and Mathlib's `lapMatrix_toLinearMap₂'` is not used.

**`le_opNorm_of_le_quadForm`** is the general tool, and it is the third and weakest of three the
day has produced. `OpNormLoewnerConverse.le_smul_one_of_opNorm_le` at `r = ‖A‖` makes `‖A‖ • 1 - A`
positive semidefinite for any symmetric `A`, so **one** vector with `r · (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x`
forces `r ≤ ‖A‖`. Compare: `OpNormLowerBound.le_opNorm_of_smul_one_le` wants a **Loewner floor**, a
statement about every vector, and `GreenNormExact.abs_le_opNorm_of_mulVec_smul` wants an
**eigenvector**. This wants a witness, which is the cheapest of the three to supply and the only
one an arbitrary graph hands you.

## What is NOT here

**Not `Δ + 1` in general.** The classical bound is `Δ + 1 ≤ ‖L‖` at **every** graph with an edge,
off the witness `Δ • Pi.single v 1 - ∑_{u ∼ v} Pi.single u 1`, whose quadratic form is
`Δ³ + 2Δ² + ∑_{u ∼ v} deg u - 2·e(N(v))` against `‖x‖² = Δ² + Δ`, and needs
`2·e(N(v)) ≤ ∑_{u ∼ v} (deg u - 1)` — each neighbour of `v` spends one edge on `v` itself.
**That is NOT attempted here and no cost is claimed for it** (`ERRATUM 246`, `ERRATUM 194`); the
route is written down so the next unit does not have to derive it. On a **regular** graph the
edge bound below already gives `Δ + 1`, which is why this file stops where it does; on a star it
gives `(n + 3)/2` where the truth is `n + 1`.

**Not sharp in general**, and the star is the witness to that, stated rather than formalised.

**Not a statement about `green`.** `GreenSpectrumRange.isLeast_eigenvalue_green` uses `‖massive‖`
as its constant, so a lower bound here is an **upper** bound on the propagator's least eigenvalue;
that reading is available and is not drawn here.

**No wall moves**, and no measure or field appears.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianNormLowerBound

open Matrix Finset GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. One vector is enough -/

/-- **A SINGLE WITNESS BOUNDS THE OPERATOR NORM FROM BELOW**, for any symmetric real matrix.
`OpNormLowerBound.le_opNorm_of_smul_one_le` wants a Loewner floor, which quantifies over every
vector; this wants one. -/
theorem le_opNorm_of_le_quadForm {A : Matrix V V ℝ} (hT : Aᵀ = A) {r : ℝ} {x : V → ℝ}
    (hx : x ≠ 0) (h : r * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x) : r ≤ ‖A‖ := by
  have hps : (‖A‖ • (1 : Matrix V V ℝ) - A).PosSemidef :=
    Matrix.le_iff.mp (OpNormLoewnerConverse.le_smul_one_of_opNorm_le hT le_rfl)
  have hnn : 0 ≤ x ⬝ᵥ (‖A‖ • (1 : Matrix V V ℝ) - A) *ᵥ x := by
    simpa using hps.dotProduct_mulVec_nonneg x
  have hxx : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hsplit : x ⬝ᵥ (‖A‖ • (1 : Matrix V V ℝ) - A) *ᵥ x
      = ‖A‖ * (x ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hsplit] at hnn
  nlinarith

/-! ## 2. The witness at an edge -/

/-- The difference of two coordinate vectors, which is the witness. -/
private noncomputable def edgeVec (u v : V) : V → ℝ := Pi.single u 1 - Pi.single v 1

omit [Fintype V] in
private theorem edgeVec_ne_zero {u v : V} (huv : u ≠ v) : edgeVec u v ≠ 0 := by
  intro h0
  have := congrFun h0 u
  simp [edgeVec, huv] at this

private theorem dotProduct_edgeVec (u v : V) (y : V → ℝ) :
    edgeVec u v ⬝ᵥ y = y u - y v := by
  simp [edgeVec, sub_dotProduct, single_dotProduct]

private theorem quadForm_edgeVec (A : Matrix V V ℝ) (u v : V) :
    edgeVec u v ⬝ᵥ A *ᵥ edgeVec u v = A u u - A u v - A v u + A v v := by
  have hmv : A *ᵥ edgeVec u v = fun i => A i u - A i v := by
    ext i
    simp [edgeVec, Matrix.mulVec_sub, Matrix.mulVec_single]
  rw [dotProduct_edgeVec, hmv]
  ring

/-- **`(deg u + deg v + 2)/2 ≤ ‖L‖` AT EVERY EDGE.** Four matrix entries and no edge sum. -/
theorem le_norm_lapMatrix_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : G.Adj u v) :
    ((G.degree u : ℝ) + (G.degree v : ℝ) + 2) / 2 ≤ ‖G.lapMatrix ℝ‖ := by
  have hne : u ≠ v := G.ne_of_adj huv
  have hT : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := G.isSymm_lapMatrix (R := ℝ)
  refine le_opNorm_of_le_quadForm hT (edgeVec_ne_zero hne) ?_
  rw [dotProduct_edgeVec, quadForm_edgeVec]
  have hself : edgeVec u v u - edgeVec u v v = 2 := by
    simp [edgeVec, hne, Ne.symm hne]
    norm_num
  rw [hself]
  have hd : ∀ p : V, (G.lapMatrix ℝ) p p = (G.degree p : ℝ) := by
    intro p
    simp [SimpleGraph.lapMatrix, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]
  have hoff : ∀ p q : V, G.Adj p q → (G.lapMatrix ℝ) p q = -1 := by
    intro p q hpq
    have hpq' : p ≠ q := G.ne_of_adj hpq
    simp [SimpleGraph.lapMatrix, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hpq',
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, hpq]
  rw [hd u, hd v, hoff u v huv, hoff v u huv.symm]
  ring_nf
  linarith

/-! ## 3. The same for the massive operator, and the sandwich on a regular graph -/

/-- **`(deg u + deg v + 2)/2 + m² ≤ ‖massive G m‖` AT EVERY EDGE.** -/
theorem le_norm_massive_of_adj (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (huv : G.Adj u v) (m : ℝ) :
    ((G.degree u : ℝ) + (G.degree v : ℝ) + 2) / 2 + m ^ 2 ≤ ‖massive G m‖ := by
  have hne : u ≠ v := G.ne_of_adj huv
  have hT : (massive G m)ᵀ = massive G m := massive_isSymm G m
  refine le_opNorm_of_le_quadForm hT (edgeVec_ne_zero hne) ?_
  rw [dotProduct_edgeVec, quadForm_edgeVec]
  have hself : edgeVec u v u - edgeVec u v v = 2 := by
    simp [edgeVec, hne, Ne.symm hne]
    norm_num
  rw [hself]
  have hd : ∀ p : V, (massive G m) p p = (G.degree p : ℝ) + m ^ 2 := by
    intro p
    simp [GraphLaplacian.massive, SimpleGraph.lapMatrix, Matrix.add_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_eq, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]
  have hoff : ∀ p q : V, G.Adj p q → (massive G m) p q = -1 := by
    intro p q hpq
    have hpq' : p ≠ q := G.ne_of_adj hpq
    simp [GraphLaplacian.massive, SimpleGraph.lapMatrix, Matrix.add_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hpq', SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, hpq]
  rw [hd u, hd v, hoff u v huv, hoff v u huv.symm]
  ring_nf
  linarith

/-- **ON A `Δ`-REGULAR GRAPH WITH AN EDGE, `Δ + 1 ≤ ‖L‖`** — and `LaplacianOpNorm` caps it at
`2Δ`, so the norm is pinned inside `[Δ + 1, 2Δ]`. -/
theorem succ_le_norm_lapMatrix_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) {u v : V} (huv : G.Adj u v) :
    (Δ : ℝ) + 1 ≤ ‖G.lapMatrix ℝ‖ := by
  have h := le_norm_lapMatrix_of_adj G huv
  rw [hreg u, hreg v] at h
  linarith

end LaplacianNormLowerBound
