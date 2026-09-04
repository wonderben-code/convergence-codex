import LatticeRegularityFloor
import LatticeRegularitySharp

/-!
# The floor's constant is optimal too — and the top eigenvector is not needed

`LatticeRegularityFloor` proved `exp(‖f‖² / (2‖massive G m‖)) ≤ ∫ exp ⟪f, ω⟫`, settled optimality
**at the level of the Loewner order** (`greatest_smul_one_le_green`), and fenced the
functional-level question:

> *Exhibiting an `f` at which `exp(‖f‖²/(2‖massive G m‖))` is an equality would need the top
> eigenvector of `massive G m`, which this estate produces only on named families … **Not attempted
> and no cost claimed.***

**That fence named the wrong obligation, and `ERRATUM 452` records it.** *Optimality of the
constant* is not *attainment at a test function*: the first says no larger constant works, the
second exhibits where the bound is met. **The first needs no eigenvector at all**, because a floor
that holds at every test function IS a Loewner floor — a symmetric matrix whose quadratic form
dominates `c·‖x‖²` everywhere is `≽ c·1` by definition — and the biconditional already caps every
Loewner floor.

`PROOF_STRATEGY` §6 question 3, taken literally: the previous unit was a `B`, so `B → C` was retried
before touching the queue.

## What is proved

**`smul_one_le_of_quadForm`** — for the propagator, a quadratic-form floor at every vector is a
Loewner floor. `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` against `green_isSymm`.

**`le_of_le_generatingFunctional`** — **so the floor's constant cannot be raised.** If
`exp(c‖f‖²) ≤ ∫ exp ⟪f, ω⟫` at every test function then `c ≤ (2‖massive G m‖)⁻¹`. Exactly the
mirror of `LatticeRegularitySharp.le_of_generatingFunctional_le`, and proved by a different
mechanism: the ceiling's optimality came from an equality at one named vector, the floor's from the
fact that failure of a Loewner bound is failure at *some* vector, which is all the biconditional
needs.

**`generatingFunctional_constants_optimal`** — both ends in one statement. The functional sits
between two Gaussians and **neither constant can be moved towards the other**.

## What is NOT here

**Still no attaining test function**, for either end of the floor — that is the question the fence
above actually asked, it remains open, and this file does not answer it. What is settled is that no
better constant exists, which is a different claim and is the one the sandwich needs.

**Nothing about `m = 0` or an empty vertex type.** `Nonempty V` is what makes `‖massive G m‖`
positive; `0 < c` is what lets the biconditional be applied.

**`OS0` in the continuum sense and `OS4` are untouched. No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeFloorOptimal

open Matrix GraphLaplacian MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A quadratic-form floor is a Loewner floor -/

/-- **A FLOOR AT EVERY VECTOR IS A LOEWNER FLOOR**, for the propagator — which is symmetric, so
`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` applies. This is the step the previous unit's fence
did not see, and it is why no eigenvector is needed. -/
theorem smul_one_le_of_quadForm (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0) {c : ℝ}
    (h : ∀ x : V → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ green G m *ᵥ x) :
    c • (1 : Matrix V V ℝ) ≤ green G m := by
  classical
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub (green_isSymm G hm) ?_
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have hconst : x ⬝ᵥ (c • (1 : Matrix V V ℝ)) *ᵥ x = c * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hconst]
    exact h x

/-! ## 2. And so the floor's constant is the largest that works -/

/-- **THE FLOOR'S CONSTANT CANNOT BE RAISED.** The mirror of
`LatticeRegularitySharp.le_of_generatingFunctional_le`, by a different mechanism: that one exhibits
an equality at the all-ones vector, this one uses that a Loewner bound which fails, fails
*somewhere*. -/
theorem le_of_le_generatingFunctional [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) {c : ℝ} (hc : 0 < c)
    (h : ∀ f : EuclideanSpace ℝ V,
      Real.exp (c * ‖f‖ ^ 2) ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m)) :
    c ≤ (2 * ‖massive G m‖)⁻¹ := by
  have hquad : ∀ x : V → ℝ, (2 * c) * (x ⬝ᵥ x) ≤ x ⬝ᵥ green G m *ᵥ x := by
    intro x
    have hx := h (WithLp.toLp 2 x)
    rw [LatticeGeneratingFunctional.generatingFunctional (G := G) (m := m) hm,
      Real.exp_le_exp] at hx
    have hn : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ V)‖ ^ 2 = x ⬝ᵥ x :=
      PosSemidefNormBound.norm_sq_eq_dotProduct _
    rw [hn] at hx
    linarith
  have hloew := smul_one_le_of_quadForm G hm hquad
  have hcap := LatticeRegularityFloor.greatest_smul_one_le_green G hm (by positivity) hloew
  rw [mul_inv]
  linarith [hcap]

/-- **BOTH ENDS ARE OPTIMAL.** The functional sits between two Gaussians and neither constant can be
moved towards the other. -/
theorem generatingFunctional_constants_optimal [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hm : m ≠ 0) :
    (∀ c : ℝ, (∀ f : EuclideanSpace ℝ V,
        ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ≤ Real.exp (c * ‖f‖ ^ 2)) →
        (2 * m ^ 2)⁻¹ ≤ c) ∧
      (∀ c : ℝ, 0 < c → (∀ f : EuclideanSpace ℝ V,
        Real.exp (c * ‖f‖ ^ 2) ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m)) →
        c ≤ (2 * ‖massive G m‖)⁻¹) :=
  ⟨fun _ hc => LatticeRegularitySharp.le_of_generatingFunctional_le G hm hc,
    fun _ hpos hc => le_of_le_generatingFunctional G hm hpos hc⟩

end LatticeFloorOptimal
