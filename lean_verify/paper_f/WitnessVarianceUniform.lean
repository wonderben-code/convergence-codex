import LatticeUniformStein
import LatticeFieldWitness
import LaplacianDegreeBound

/-!
# The witness's variance, uniformly in the box — the fence's own application

`LatticeUniformStein`'s "What this is NOT" says:

> **The constant is uniform in the graph; that does not make every APPLICATION uniform.** Applying
> this to `LatticeFieldWitness.absCoordField` gives a bound whose `L` involves `(√G)⁻¹`, and
> **nothing here analyses how that grows with the box**.

This file does that analysis, and **the answer is an identity rather than an estimate.**

## The column norm is a diagonal entry of `massive`, exactly

The Stein tuple of the witness is `γ j ω = ((√G)⁻¹) j v · sgn(…)`, so the quantity
`poincare_uniform_stein_of_bounded` consumes is `∑ⱼ (γⱼ ω)² ≤ ∑ⱼ ((√G)⁻¹ j v)²` — **the squared
norm of one column of `(√G)⁻¹`**, the sign contributing at most `1`.

That column norm is not estimated here. It is computed. `(√G)⁻¹ · (√G)⁻¹ = (√G · √G)⁻¹ = green⁻¹ =
massive`, and `(√G)⁻¹` is symmetric, so

```
∑ⱼ ((√G)⁻¹ j v)²  =  (massive G m) v v  =  deg(v) + m²
```

— **`sqrtGreenInv_col_sq`**, an equality, by `GraphLaplacian.lapMatrix_diag`.

## Hence the bound, and on the box it does not see the side length

* **`absCoordField_var_le`** — `Var(absCoordField v) ≤ m⁻²·(deg v + m²)`, at every graph.
* **`absCoordField_var_le_of_degree`** — `≤ m⁻²·(Δ + m²)` under a degree bound.
* **`absCoordField_var_le_boxGraph`** — `≤ m⁻²·(2d + m²)` on the `d`-dimensional box at **every**
  side length. **That is the fence's sentence, closed.**

## AND IT DOES NOT USE `SqrtGreenBound`, WHICH IS THE HONEST PART

The unit before this one proved `(CFC.sqrt (green G m))⁻¹ ≼ √(2Δ + m²) • 1` — a Loewner bound on
the whole matrix — and its header called that *"the object `LatticeUniformStein`'s fence names"*.
**The application does not need the whole matrix. It needs one column, and that column's squared
norm is an exact diagonal entry.** So `SqrtGreenBound` is not on the path from that fence to this
bound, and its stated motivation overstated its role; the theorems in it are unaffected and
`sqrt_le_sqrt_real` — operator monotonicity of the square root over ℝ — is new and stands on its
own. **Recorded here rather than left for a reader to notice** (`ERRATUM 204`, `ERRATUM 247`).

**What this does NOT do.** It bounds the variance of ONE observable, `absCoordField v`, and says
nothing about a family of them or about any limit. `OS4` does not move: a constant that does not
blow up is an ingredient of a tightness argument and not one. No sequence of measures, no
compactness. **No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace WitnessVarianceUniform

open MeasureTheory Matrix GraphLaplacian
open LatticeSqrtEquiv LatticeFieldProduct LatticeFieldWitness LatticeUniformStein
open AbsSteinWitness LatticeGradientForm
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W] {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The column norm, computed rather than estimated -/

/-- `(√G)⁻¹` is symmetric, being the inverse of a symmetric matrix. -/
theorem isSymm_sqrtGreenInv : ((CFC.sqrt (green K m))⁻¹).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv]
  congr 1
  exact isSymm_sqrt_green (G := K) (m := m)

/-- **`(√G)⁻¹ · (√G)⁻¹ = massive`.** The square root squares to `green`, inverting reverses the
product, and `green` is `massive`'s inverse. -/
theorem sqrtGreenInv_mul_self (hm : m ≠ 0) :
    (CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m))⁻¹ = massive K m := by
  rw [← Matrix.mul_inv_rev, sqrt_green_mul_self_general (H := K) hm, green,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit K hm))]

/-- **THE COLUMN NORM IS A DIAGONAL ENTRY OF `massive`, AND SO IS `deg(v) + m²` EXACTLY.**
No estimate anywhere: `∑ⱼ ((√G)⁻¹ j v)²` is `(massive) v v`, and `massive`'s diagonal is the degree
plus the mass squared. -/
theorem sqrtGreenInv_col_sq (hm : m ≠ 0) (v : W) :
    ∑ j, ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 = (K.degree v : ℝ) + m ^ 2 := by
  have hsym : ((CFC.sqrt (green K m))⁻¹).IsSymm := isSymm_sqrtGreenInv
  have hmul := sqrtGreenInv_mul_self (K := K) hm
  have hentry : ((CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m))⁻¹) v v
      = ∑ j, ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (CFC.sqrt (green K m))⁻¹ v j = (CFC.sqrt (green K m))⁻¹ j v :=
      congrFun (congrFun hsym j) v
    rw [this, sq]
  rw [← hentry, hmul, massive_apply, if_pos rfl, if_neg (K.irrefl), sub_zero]

/-! ## 2. The variance bound -/

/-- **`Var(absCoordField v) ≤ m⁻²·(deg v + m²)`**, at every graph, with the constant computed. -/
theorem absCoordField_var_le (hm : m ≠ 0) (v : W) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
        - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2) := by
  classical
  have hL : ∀ ω, ∑ j, (sgnCoordField K m v j ω) ^ 2
      ≤ (Real.sqrt ((K.degree v : ℝ) + m ^ 2)) ^ 2 := by
    intro ω
    have hnn : (0 : ℝ) ≤ (K.degree v : ℝ) + m ^ 2 := by positivity
    rw [Real.sq_sqrt hnn, ← sqrtGreenInv_col_sq (K := K) hm v]
    refine Finset.sum_le_sum fun j _ => ?_
    have hs : (sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)) ^ 2 ≤ 1 := by
      have := abs_sgn_le (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)
      nlinarith [abs_nonneg (sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)),
        sq_abs (sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v))]
    have hcol : (0 : ℝ) ≤ ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 := sq_nonneg _
    calc (sgnCoordField K m v j ω) ^ 2
        = ((CFC.sqrt (green K m))⁻¹ j v) ^ 2
          * (sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)) ^ 2 := by
          rw [sgnCoordField, mul_pow]
      _ ≤ ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hs hcol
      _ = ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 := mul_one _
  have h := poincare_uniform_stein_of_bounded (K := K) hm
    (absCoordField_steinPairField (K := K) hm v) hL
  rwa [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (K.degree v : ℝ) + m ^ 2)] at h

/-- **Under a degree bound the constant loses the vertex too.** -/
theorem absCoordField_var_le_of_degree (hm : m ≠ 0) {Δ : ℝ}
    (hΔ : ∀ p : W, (K.degree p : ℝ) ≤ Δ) (v : W) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
        - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (Δ + m ^ 2) := by
  refine (absCoordField_var_le hm v).trans ?_
  have hpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith [hΔ v]) hpos

open BoxGraph BoxDegree in
/-- **THE FENCE'S SENTENCE, CLOSED.** On the `d`-dimensional box the variance of the witness at
any site is at most `m⁻²·(2d + m²)`, **at every side length `n`** — the constant names the dimension
and the mass and nothing else. `BoxDegree.boxGraph_degree_le` is the only input beyond the previous
theorem. -/
theorem absCoordField_var_le_boxGraph (d n : ℕ) {m : ℝ} (hm : m ≠ 0) (v : Site d n) :
    (∫ ω, absCoordField (boxGraph d n) m v ω * absCoordField (boxGraph d n) m v ω
        ∂(gaussianField (boxGraph d n) m))
        - (∫ ω, absCoordField (boxGraph d n) m v ω ∂(gaussianField (boxGraph d n) m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (2 * (d : ℝ) + m ^ 2) := by
  refine absCoordField_var_le_of_degree hm (fun p => ?_) v
  have h := boxGraph_degree_le (d := d) (n := n) p
  have : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
  simpa using this

end WitnessVarianceUniform
