import BoxModeOrthogonal
import BoxSpectrumComplete
import OrthogonalQuadForm
import LaplacianDegreeBound
import BoxDegree

/-!
# A better constant for the box's massive Laplacian than any degree bound can give

`LaplacianDegreeBound.massive_le_smul_one` gives `−Δ_G + m² ≼ (2Δ + m²)·1` on **any** graph of
degree at most `Δ`, which on `boxGraph d n` reads **`4d + m²`**. That constant is what the estate
has used ever since — `SqrtGreenBound.inv_sqrt_green_boxGraph_le` carries `√(4d + m²)` — and it
comes from bounding the whole Laplacian by its degree twice over.

**On the box the second half is not worth `2d`.** `BoxSpectrumComplete` computes the adjacency
spectrum exactly and its radius is `2d·cos(π/(n+1))`, strictly inside `2d`; `BoxModeOrthogonal`
makes the modes an orthogonal basis; and `OrthogonalQuadForm` turns those two facts into a bound on
the quadratic form. This file spends all three.

> **`massive_le_smul_one_box`** — `massive (boxGraph d n) m ≼ (2d + 2d·cos(π/(n+1)) + m²)·1`, at
> every dimension and every side length, **strictly better than `4d + m²`** whenever `d ≥ 1`.
>
> **`const_lt_degree_const`** — and the improvement is **proved, not asserted**: at every `d ≥ 1`
> and every side length, `2d + 2d·cos(π/(n+1)) + m² < 4d + m²`, the whole gap being
> `2d·(1 − cos(π/(n+1)))`.
>
> **`smul_one_le_green_box`** — hence `(2d + 2d·cos(π/(n+1)) + m²)⁻¹·1 ≼ green (boxGraph d n) m`,
> the same improvement on the propagator's lower bound.

## Where the improvement comes from, and where it does not

`L = D − A`. The degree route bounds `x ⬝ᵥ L *ᵥ x` by `2Δ` because it bounds **both** `D` and `−A`
by the degree. Here `D` is still bounded by its degree — `BoxDegree.boxGraph_degree_le`, and
**that half does not improve**, because a corner site really does have `d` neighbours and an
interior one really has `2d` — but `−A` is bounded by the **spectral radius**
`2d·cos(π/(n+1))` instead. The gain is exactly the difference between the two, and it is the
boundary that creates it: a graph with no boundary would have `cos` replaced by `1` on the relevant
mode.

## What this is NOT

**It is not the box's `massive` spectrum**, which is what `UNLOCK_WATCHLIST`'s *a BOX is not a
circulant* item asks for. `D` is **not** a scalar on the box (`PathDegreeBoundary.pathGraph_degree`
already shows this at `d = 1`), so `A`'s eigenvectors are not `massive`'s, and **no eigenvalue of
`massive` is computed here**. **That item does not move.** What this delivers is a strictly better
**constant** in an inequality the estate already had.

**It is not sharp.** `2d + 2d·cos(π/(n+1))` is the sum of two separately-attained bounds, and there
is no reason a single vector attains both at once; **no claim of sharpness is made** and no lower
bound on the true constant is proved. As of 31 Aug 2026 neither is costed (`ERRATUM 194`,
`ERRATUM 246`).

**Nothing downstream is rewired.** `SqrtGreenBound`, `LatticeWitnessBound` and the rest keep the
constants they have; this adds a statement beside them rather than editing them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxMassiveBound

open Finset Matrix SimpleGraph BoxGraph BoxAdjSpectrum BoxAdjBasis GraphLaplacian
open scoped MatrixOrder

variable {d n : ℕ}

/-- The box's adjacency spectral radius, named once. **Spelled out rather than called `ρ`**:
`rho` is already taken three times over in this estate — a quaternion algebra map, a `Fin 4`
reflection and a Gaussian density — and none of them is this (`newnames_scan`, 31 Aug 2026). -/
noncomputable def adjRadius (d n : ℕ) : ℝ := 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1))

/-! ## 1. The adjacency quadratic form, both signs -/

theorem boxBasis_eigen [NeZero n] (k : Site d n) :
    (boxGraph d n).adjMatrix ℝ *ᵥ boxBasis d n k
      = boxEig d n (fun i => (k i).val + 1) • boxBasis d n k := by
  rw [boxBasis_apply]
  exact adjMatrix_mulVec_siteVec n d k

theorem boxBasis_orth [NeZero n] (k l : Site d n) (hkl : k ≠ l) :
    boxBasis d n k ⬝ᵥ boxBasis d n l = 0 := by
  rw [boxBasis_apply, boxBasis_apply]
  exact BoxModeOrthogonal.siteVec_dotProduct_eq_zero hkl

theorem boxBasis_self_nonneg [NeZero n] (k : Site d n) :
    0 ≤ boxBasis d n k ⬝ᵥ boxBasis d n k := by
  rw [boxBasis_apply]
  exact le_of_lt
    (BoxModeOrthogonal.siteVec_dotProduct_self_pos (Nat.pos_of_ne_zero (NeZero.ne n)) k)

/-- **`x ⬝ᵥ A *ᵥ x ≤ adjRadius·(x ⬝ᵥ x)`.** -/
theorem adj_quadForm_le [NeZero n] (x : Site d n → ℝ) :
    x ⬝ᵥ (boxGraph d n).adjMatrix ℝ *ᵥ x ≤ adjRadius d n * (x ⬝ᵥ x) :=
  OrthogonalQuadForm.quadForm_le_of_orthogonal_eigenbasis (boxBasis d n)
    (ν := fun k => boxEig d n fun i => (k i).val + 1) boxBasis_eigen
    (fun k l h => boxBasis_orth k l h) boxBasis_self_nonneg
    (fun k => (abs_le.1 (BoxSpectrumComplete.abs_boxEig_le d n
      (fun _ => Nat.le_add_left 1 _) fun i => (k i).isLt)).2) x

/-- **AND THE SAME BOUND ON `−A`**, which is the half the Laplacian needs. -/
theorem neg_adj_quadForm_le [NeZero n] (x : Site d n → ℝ) :
    x ⬝ᵥ (-((boxGraph d n).adjMatrix ℝ)) *ᵥ x ≤ adjRadius d n * (x ⬝ᵥ x) :=
  OrthogonalQuadForm.quadForm_le_of_orthogonal_eigenbasis (boxBasis d n)
    (ν := fun k => -(boxEig d n fun i => (k i).val + 1))
    (fun k => by rw [Matrix.neg_mulVec, boxBasis_eigen, neg_smul])
    (fun k l h => boxBasis_orth k l h) boxBasis_self_nonneg
    (fun k => by
      have h := BoxSpectrumComplete.abs_boxEig_le d n (k := fun i => (k i).val + 1)
        (fun _ => Nat.le_add_left 1 _) fun i => (k i).isLt
      have h1 := (abs_le.1 h).1
      simp only [adjRadius]
      linarith) x

/-! ## 2. The degree half, which does not improve -/

/-- **`x ⬝ᵥ D *ᵥ x ≤ 2d·(x ⬝ᵥ x)`.** This half is the ordinary degree bound and there is nothing
better to say: an interior site really does have `2d` neighbours. -/
theorem degMatrix_quadForm_le (d n : ℕ) (x : Site d n → ℝ) :
    x ⬝ᵥ (SimpleGraph.degMatrix ℝ (boxGraph d n)) *ᵥ x ≤ 2 * d * (x ⬝ᵥ x) := by
  classical
  have hstep : ∀ p : Site d n,
      x p * ((SimpleGraph.degMatrix ℝ (boxGraph d n)) *ᵥ x) p ≤ 2 * d * (x p * x p) := by
    intro p
    rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]
    have hd : ((boxGraph d n).degree p : ℝ) ≤ 2 * d := by
      have := BoxDegree.boxGraph_degree_le (d := d) (n := n) p
      have hc : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast this
      simpa using hc
    nlinarith [mul_self_nonneg (x p)]
  calc x ⬝ᵥ (SimpleGraph.degMatrix ℝ (boxGraph d n)) *ᵥ x
      = ∑ p, x p * ((SimpleGraph.degMatrix ℝ (boxGraph d n)) *ᵥ x) p := rfl
    _ ≤ ∑ _p : Site d n, 2 * d * (x _p * x _p) := Finset.sum_le_sum fun p _ => hstep p
    _ = 2 * d * (x ⬝ᵥ x) := by rw [dotProduct, Finset.mul_sum]

/-! ## 3. The Loewner bound, and the improvement -/

/-- **`massive (boxGraph d n) m ≼ (2d + adjRadius + m²)·1`**, with
`adjRadius d n = 2d·cos(π/(n+1))`. -/
theorem massive_le_smul_one_box (d n : ℕ) [NeZero n] (m : ℝ) :
    massive (boxGraph d n) m
      ≤ (2 * d + adjRadius d n + m ^ 2) • (1 : Matrix (Site d n) (Site d n) ℝ) := by
  classical
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ (massive_isSymm (boxGraph d n) m)
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have hconst : x ⬝ᵥ ((2 * d + adjRadius d n + m ^ 2) • (1 : Matrix (Site d n) (Site d n) ℝ)) *ᵥ x
        = (2 * d + adjRadius d n + m ^ 2) * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have hmass : x ⬝ᵥ (massive (boxGraph d n) m) *ᵥ x
        = (x ⬝ᵥ (SimpleGraph.degMatrix ℝ (boxGraph d n)) *ᵥ x)
          + (x ⬝ᵥ (-((boxGraph d n).adjMatrix ℝ)) *ᵥ x)
          + m ^ 2 * (x ⬝ᵥ x) := by
      rw [massive, SimpleGraph.lapMatrix]
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub]
      have hm2 : x ⬝ᵥ (Matrix.diagonal fun _ : Site d n => m ^ 2) *ᵥ x = m ^ 2 * (x ⬝ᵥ x) := by
        rw [dotProduct, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mulVec_diagonal]; ring
      have hneg : x ⬝ᵥ (-((boxGraph d n).adjMatrix ℝ)) *ᵥ x
          = -(x ⬝ᵥ ((boxGraph d n).adjMatrix ℝ) *ᵥ x) := by
        rw [Matrix.neg_mulVec, dotProduct_neg]
      rw [hm2, hneg]
      ring
    rw [hconst, hmass]
    have h1 := degMatrix_quadForm_le d n x
    have h2 := neg_adj_quadForm_le (d := d) (n := n) x
    nlinarith [h1, h2]

/-- **AND IT REALLY IS AN IMPROVEMENT**, proved rather than asserted: at every dimension `d ≥ 1`
and every side length, the constant here is **strictly** below `LaplacianDegreeBound`'s `4d + m²`
on this graph. The whole gap is `2d·(1 − cos(π/(n+1)))`, and it is the box's boundary. -/
theorem const_lt_degree_const (d n : ℕ) (hd : 0 < d) (m : ℝ) :
    2 * (d : ℝ) + adjRadius d n + m ^ 2 < 4 * (d : ℝ) + m ^ 2 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcos := BoxSpectrumComplete.cos_base_lt_one n
  have hr : adjRadius d n = 2 * (d : ℝ) * Real.cos (Real.pi / ((n : ℝ) + 1)) := rfl
  rw [hr]
  nlinarith

/-- **HENCE THE PROPAGATOR'S LOWER BOUND IMPROVES BY THE SAME AMOUNT.** -/
theorem smul_one_le_green_box (d n : ℕ) [NeZero n] {m : ℝ} (hm : m ≠ 0) :
    (2 * d + adjRadius d n + m ^ 2)⁻¹ • (1 : Matrix (Site d n) (Site d n) ℝ)
      ≤ green (boxGraph d n) m := by
  have hpos : (0 : ℝ) < 2 * d + adjRadius d n + m ^ 2 := by
    have hcos : -1 ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) := Real.neg_one_le_cos _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hm2 : (0 : ℝ) < m ^ 2 := by positivity
    have : adjRadius d n = 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1)) := rfl
    nlinarith [this]
  have hle := massive_le_smul_one_box d n m
  have hinv := MatrixLoewner.posDef_inv_le_inv (massive_posDef (boxGraph d n) hm) hle
  have hd : ((2 * (d : ℝ) + adjRadius d n + m ^ 2) • (1 : Matrix (Site d n) (Site d n) ℝ))⁻¹
      = (2 * (d : ℝ) + adjRadius d n + m ^ 2)⁻¹ • (1 : Matrix (Site d n) (Site d n) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  rwa [hd] at hinv

end BoxMassiveBound
