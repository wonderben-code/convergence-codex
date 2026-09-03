import GreenLoewnerFloorSharp

/-!
# A symmetric matrix's quadratic form attains its bound exactly at an eigenvector

`TorusAttainmentBridge` joins two characterisations of *the degree bound is reached* on the periodic
lattice — one by a supplied vector, one by an eigenvalue — and its *What this is NOT* section names
the general theorem it had to work around:

> *"**THIS IS NOT THE RAYLEIGH STATEMENT.** A symmetric matrix's quadratic form attains its upper
> bound exactly when that bound is an eigenvalue is a general theorem about symmetric matrices.
> **It is not proved here and it is not used here.**"*

That file's biconditional is a **one-family** result, available only because both sides happened to
reduce to the same third condition (`Even n`). **The general statement is proved here**, and it
needs no spectral theorem, no eigenbasis and no positivity:

> **`quadForm_eq_opNorm_iff_mulVec`** — for a symmetric real matrix `A` and **any** vector `v`,
> `v ⬝ᵥ A *ᵥ v = ‖A‖ · (v ⬝ᵥ v)` **iff** `A *ᵥ v = ‖A‖ • v`.

## The proof is one observation

`OpNormLoewnerConverse.le_smul_one_of_opNorm_le` at `r = ‖A‖` gives `A ≼ ‖A‖ • 1` for **any**
symmetric `A` — that direction carries no positivity hypothesis and no `Nonempty V`. So
`P = ‖A‖ • 1 − A` is positive semidefinite, and `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` says
a positive semidefinite matrix's form vanishes at `v` exactly when it **annihilates** `v`. The
quadratic form of `P` at `v` is `‖A‖·(v ⬝ᵥ v) − v ⬝ᵥ A *ᵥ v`, so *attaining the bound* and
*being an eigenvector at `‖A‖`* are the same equation read twice.

**This is the same shape as `LaplacianSharpEquality`'s own headline** — *the inequality was an
identity all along, and equality forces every summand to vanish* — with the sum of squares replaced
by a positive semidefinite form. That file needed the graph; this needs nothing.

## What it is and is not

* **It is stated at `‖A‖`, not at an arbitrary upper bound.** For `r` with `A ≼ r • 1` and `r > ‖A‖`
  the form is never attained, which is `LaplacianNormSharp.opNorm_eq_iff_min_smul_one` and not this.
* **It says nothing about existence.** Whether some `v ≠ 0` attains the bound is exactly whether
  `‖A‖` is an eigenvalue, and this file supplies the equivalence, not the eigenvector.
  `RayleighMatrix.mv_eigenvectorBasis` is the estate's route to existence and is untouched here.
* **`TorusAttainmentBridge` is not superseded and nothing there is edited.** Its biconditional is
  between the quadratic-form condition and `4d + m²` being an eigenvalue **of a specific family**,
  and it is proved through `Even n` rather than through this; that route also yields
  `quadForm_attained_iff_isGreatest`, which this file does not. What changes is that the general
  statement its header calls absent is no longer absent.
* **No wall moves.** `W1` asks for a lower bound on the cross form (`WALLS.md` §W1.5).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RayleighAttainment

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **ATTAINING THE OPERATOR-NORM BOUND IS BEING AN EIGENVECTOR AT IT.** For a symmetric real
matrix and any vector, `v ⬝ᵥ A *ᵥ v = ‖A‖ · (v ⬝ᵥ v)` **iff** `A *ᵥ v = ‖A‖ • v`. **No positivity,
no `Nonempty V`, no spectral theorem and no eigenbasis** — `‖A‖ • 1 − A` is positive semidefinite
because `‖A‖ ≤ ‖A‖`, and a positive semidefinite form vanishes exactly where its matrix annihilates.
-/
theorem quadForm_eq_opNorm_iff_mulVec {A : Matrix V V ℝ} (hT : Aᵀ = A) (v : V → ℝ) :
    v ⬝ᵥ A *ᵥ v = ‖A‖ * (v ⬝ᵥ v) ↔ A *ᵥ v = ‖A‖ • v := by
  have hps : (‖A‖ • (1 : Matrix V V ℝ) - A).PosSemidef :=
    Matrix.le_iff.mp (OpNormLoewnerConverse.le_smul_one_of_opNorm_le hT le_rfl)
  have hquad : v ⬝ᵥ (‖A‖ • (1 : Matrix V V ℝ) - A) *ᵥ v = ‖A‖ * (v ⬝ᵥ v) - v ⬝ᵥ A *ᵥ v := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hzero := hps.dotProduct_mulVec_zero_iff v
  rw [star_trivial, hquad] at hzero
  constructor
  · intro h
    have h0 : (‖A‖ • (1 : Matrix V V ℝ) - A) *ᵥ v = 0 := hzero.mp (by rw [h]; ring)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  · intro h
    have h0 : (‖A‖ • (1 : Matrix V V ℝ) - A) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]
    have := hzero.mpr h0
    linarith

/-- **HENCE THE EXISTENCE FORMS AGREE**: some non-zero vector attains the bound **iff** `‖A‖` is an
eigenvalue. This is the statement `TorusAttainmentBridge` had to reach through `Even n` for one
family. -/
theorem exists_quadForm_eq_opNorm_iff {A : Matrix V V ℝ} (hT : Aᵀ = A) :
    (∃ v : V → ℝ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = ‖A‖ * (v ⬝ᵥ v))
      ↔ ∃ v : V → ℝ, v ≠ 0 ∧ A *ᵥ v = ‖A‖ • v := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (quadForm_eq_opNorm_iff_mulVec hT v).mp h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (quadForm_eq_opNorm_iff_mulVec hT v).mpr h⟩

/-- **AND THE PROPAGATOR'S CASE IS THE CONSTANT FIELD**, which `GreenNormExact` computed directly:
`‖green G m‖ = (m²)⁻¹` and the all-ones vector is an eigenvector there, so the bound is attained at
every finite graph. Read here through the general statement rather than through the norm. -/
theorem quadForm_green_eq_opNorm [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}
    (hm : m ≠ 0) :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ GraphLaplacian.green G m *ᵥ (fun _ : V => (1 : ℝ))
      = ‖GraphLaplacian.green G m‖ * ((fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ))) := by
  have hT : (GraphLaplacian.green G m)ᵀ = GraphLaplacian.green G m :=
    GraphLaplacian.green_isSymm G hm
  refine (quadForm_eq_opNorm_iff_mulVec hT _).mpr ?_
  rw [GreenNormExact.norm_green_eq G hm, GreenExpansion.green_mulVec_one (G := G) hm]
  ext p; simp

end RayleighAttainment
