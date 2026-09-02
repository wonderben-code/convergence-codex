import SqrtGreenBound

/-!
# From a Loewner bound to an operator-norm bound, for a positive semidefinite real matrix

`SqrtGreenBound.inv_sqrt_green_boxGraph_le` bounds `(√green)⁻¹` **in the Loewner order** by
`√(4d + m²) • 1`, with the constant naming the dimension and not the side length. The variance
argument the watchlist item is about wants that constant on the **operator norm**, and the
watchlist calls the passage *"a separate join. Not attempted."* This file is the algebraic half of
that join, over `ℝ`.

**WHY THE OBVIOUS ROUTE IS UNAVAILABLE** (`ERRATUM 425`). Mathlib has the join outright —
`CStarAlgebra.norm_le_iff_le_algebraMap` : `0 ≤ r → 0 ≤ a → (‖a‖ ≤ r ↔ a ≤ algebraMap ℝ A r)`. It
cannot be used here: `CStarAlgebra` is declared `extends … NormedAlgebra ℂ A`, and `Matrix V V ℝ`
is not a `ℂ`-algebra. The obstacle is the scalar field of a type class, not the mathematics, and
`MatrixLoewner.cx` carries order and positivity across but says nothing about norms.

> **THE ONE STEP.** `sq_le_smul_of_le_smul_one` — if `0 ≤ A` and `A ≤ r • 1` then `A * A ≤ r • A`.
> **Conjugation, not spectral theory**: `r • 1 − A` is positive semidefinite, so
> `Matrix.PosSemidef.conjTranspose_mul_mul_same` at `B = √A` — which is its own conjugate transpose
> — makes `√A * (r • 1 − A) * √A` positive semidefinite. Expanding it with
> `CFC.sqrt_mul_sqrt_self` turns that into `r • A − A * A`, and **that is the statement**. No
> eigenvalues are named and no diagonalisation is performed.

**WHAT THIS IS NOT.** **It is not the join and the watchlist item does not move.** The norm half —
`‖A x‖² = ⟪x, (A * A) x⟫ ≤ r ⟪x, A x⟫ ≤ r² ‖x‖²`, then `‖A‖ ≤ r` through
`Matrix.l2_opNorm_toEuclideanCLM` and `ContinuousLinearMap.opNorm_le_bound` — is **not proved here**
and is not attempted in this file; no cost is claimed for it (`ERRATUM 194`, `ERRATUM 246`), and
that chain's record of four wrong difficulty estimates out of five is why no estimate is offered
(`ERRATUM 183`). **Nothing in `SqrtGreenBound` is restated**, nothing earlier is deleted or
deprecated, and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PosSemidefNormBound

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`A * A ≤ r • A` FROM `A ≤ r • 1`**, for a positive semidefinite real matrix. The load-bearing
algebraic step between a Loewner bound and an operator-norm bound, proved by conjugating
`r • 1 − A` with `√A` rather than by any spectral argument. -/
theorem sq_le_smul_of_le_smul_one {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) : A * A ≤ r • A := by
  have hsub : (r • (1 : Matrix V V ℝ) - A).PosSemidef := Matrix.le_iff.mp hle
  have hsqrt : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A
  have hherm : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    have hps : (CFC.sqrt A).PosSemidef := by
      simpa using Matrix.le_iff.mp (CFC.sqrt_nonneg A)
    exact hps.isHermitian
  have hconj := hsub.conjTranspose_mul_mul_same (CFC.sqrt A)
  rw [hherm] at hconj
  have hexp : CFC.sqrt A * (r • (1 : Matrix V V ℝ) - A) * CFC.sqrt A = r • A - A * A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hsqrt]
    congr 1
    calc CFC.sqrt A * A * CFC.sqrt A
        = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt A) * CFC.sqrt A := by rw [hsqrt]
      _ = (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A * CFC.sqrt A) := by
          simp [Matrix.mul_assoc]
      _ = A * A := by rw [hsqrt]
  rw [hexp] at hconj
  exact Matrix.le_iff.mpr hconj

end PosSemidefNormBound
