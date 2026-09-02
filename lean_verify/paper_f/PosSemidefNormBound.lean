import SqrtGreenBound

/-!
# From a Loewner bound to an operator-norm bound, for a positive semidefinite real matrix

`SqrtGreenBound.inv_sqrt_green_boxGraph_le` bounds `(√green)⁻¹` **in the Loewner order** by
`√(4d + m²) • 1`, with the constant naming the dimension and not the side length. The variance
argument the watchlist item is about wants that constant on the **operator norm**, and the
watchlist calls the passage *"a separate join. Not attempted."* This file is the algebraic half of
that join, over `ℝ`. **⚠ THAT LAST SENTENCE STOPPED BEING TRUE THE SAME DAY: §2 BELOW PROVES THE
NORM HALF TOO**, and the note under `WHAT THIS IS NOT` says how. It is left standing rather than
edited (`ERRATUM 94`), with the pointer here so that no reader meets the false clause without the
correction attached — which is `ERRATUM 421`'s defect, a closure sitting far below the sentence it
refutes, avoided rather than repeated.

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

**⚠ IT IS DONE, THE SAME DAY, AND THE PARAGRAPH ABOVE IS KEPT AS WRITTEN** (`ERRATUM 94`). §2
proves `l2_opNorm_le` : `0 ≤ A → A ≤ r • 1 → ‖A‖ ≤ r`, and the norm is the `l²` operator norm —
read off the elaborated statement as `Matrix.instL2OpNormedRing` under `pp.explicit`, not inferred
from the `open scoped` line. **The chain is `sq_le_smul_of_le_smul_one` twice over**: the Loewner
order is an inequality of quadratic forms (`dotProduct_mono`), so `A ≤ r • 1` bounds `x ⬝ᵥ A *ᵥ x`
and §1 bounds `x ⬝ᵥ (A * A) *ᵥ x` by `r` times it; `A` symmetric turns the left side into
`(A *ᵥ x) ⬝ᵥ (A *ᵥ x)`, and `‖A x‖² ≤ r² ‖x‖²` is `dotProduct_mulVec_self_le`.

**TWO PLACES WHERE THE PLAN ABOVE WAS WRONG, AND BOTH ARE RECORDED RATHER THAN QUIETLY FIXED.**
(i) It routed through `⟪x, (A * A) x⟫`; `EuclideanSpace.inner_eq_star_dotProduct` **does not rewrite
the goal it exactly matches**, an instance-path mismatch of the kind `ERRATUM 274` names, so §2
carries `norm_sq_eq_dotProduct` — `‖y‖ ^ 2 = y.ofLp ⬝ᵥ y.ofLp` via `EuclideanSpace.norm_eq` and
`Real.sq_sqrt` — and never mentions an inner product. (ii) **It omitted a hypothesis that the
theorem cannot do without**: `Nonempty V`. On an empty vertex type every matrix is `0`, every
Loewner inequality holds, `r` may be negative and `‖A‖ ≤ r` is FALSE. `nonneg_of_le_smul_one` is
where it enters, and it enters through one diagonal entry of `r • 1`, so the constraint is real and
not an artefact of the proof. **A plan is not a proof and this one was short by a hypothesis.**

**WHAT §2 IS STILL NOT.** It is the algebra-to-norm join alone, and **the item does not close**:
threading `SqrtGreenBound.inv_sqrt_green_boxGraph_le` through it and into the variance argument is
untouched here, not attempted, not costed (`ERRATUM 246`) and not estimated (`ERRATUM 183`). The
converse direction of `CStarAlgebra.norm_le_iff_le_algebraMap` — `‖A‖ ≤ r → A ≤ r • 1` — is **not**
proved; only the direction the estate needs is.

**⚠ IT IS PROVED, 2026-09-02, AND THE SENTENCE IS KEPT AS WRITTEN** (`ERRATUM 94`).
`paper_f/OpNormLoewnerConverse.lean` : `l2_opNorm_le_iff_le_smul_one` is this fence's own statement
as a biconditional, and `l2_opNorm_le_iff_abs_le` is the symmetric two-sided form. **Cauchy–Schwarz
and nothing else** — `|x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ (x ⬝ᵥ x)`, which squeezes the quadratic form between
`±‖A‖ (x ⬝ᵥ x)`. **And the converse needs no `Nonempty V`**, where this file's forward direction
does: it reads an inequality off every vector and an empty type supplies none.

Nothing in `SqrtGreenBound` is restated and no published tag moves.

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

/-! ## 2. The norm half, so that the file's name is earned

The Loewner order on real matrices is an inequality between quadratic forms, and everything below
is that reading applied twice: once to `A ≤ r • 1` and once to §1's `A * A ≤ r • A`. -/

omit [DecidableEq V] in
/-- **THE LOEWNER ORDER READ AS AN INEQUALITY OF QUADRATIC FORMS.** `A ≤ B` says exactly that
`B - A` is positive semidefinite, which is a statement about `x ⬝ᵥ (B - A) *ᵥ x`; over `ℝ` the
`star` is the identity and the difference splits. -/
theorem dotProduct_mono {A B : Matrix V V ℝ} (h : A ≤ B) (x : V → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x := by
  have hps := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hps
  linarith

/-- `A ≤ r • 1` bounds the quadratic form of `A` by `r` times the squared length. -/
theorem quadForm_le_smul_one {A : Matrix V V ℝ} {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) (x : V → ℝ) : x ⬝ᵥ A *ᵥ x ≤ r * (x ⬝ᵥ x) := by
  have h := dotProduct_mono hle x
  simpa [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] using h

omit [Fintype V] in
/-- **`0 ≤ r` IS FORCED, AND ONLY BY THE PRESENCE OF A VERTEX.** `0 ≤ A ≤ r • 1` makes `r • 1`
positive semidefinite, and a positive semidefinite matrix has non-negative diagonal — so it is
read off one diagonal entry, with no basis vector and no quadratic form. **On an empty vertex type
the conclusion is false**: every matrix is `0`, every inequality holds, and `r` may be negative.
That is why `Nonempty V` appears from here on, and why it is a hypothesis and not an oversight. -/
theorem nonneg_of_le_smul_one [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) : 0 ≤ r := by
  classical
  have hps : (r • (1 : Matrix V V ℝ)).PosSemidef := by
    simpa using Matrix.le_iff.mp (le_trans hA hle)
  simpa using hps.diag_nonneg (i := Classical.arbitrary V)

/-- **THE NORM HALF IN `dotProduct` FORM**, which is where the content is: `‖A x‖² ≤ r² ‖x‖²`,
with no norm and no inner product yet. `A` is symmetric, so the left side is the quadratic form of
`A * A`; §1 bounds that by `r` times the quadratic form of `A`; and `A ≤ r • 1` bounds that in
turn. The two `≤` signs are the two uses of the hypothesis. -/
theorem dotProduct_mulVec_self_le [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) (x : V → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ (r * r) * (x ⬝ᵥ x) := by
  have hps : A.PosSemidef := by simpa using Matrix.le_iff.mp hA
  have hT : Aᵀ = A := by
    have h := hps.isHermitian
    simpa [Matrix.conjTranspose, Matrix.map] using h
  have hr : 0 ≤ r := nonneg_of_le_smul_one hA hle
  have hsplit : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
    calc (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
        = (Aᵀ *ᵥ x) ⬝ᵥ (A *ᵥ x) := by rw [hT]
      _ = (x ᵥ* A) ⬝ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_transpose]
      _ = x ⬝ᵥ A *ᵥ (A *ᵥ x) := (Matrix.dotProduct_mulVec x A (A *ᵥ x)).symm
      _ = x ⬝ᵥ (A * A) *ᵥ x := by rw [Matrix.mulVec_mulVec]
  have hsmul : x ⬝ᵥ (r • A) *ᵥ x = r * (x ⬝ᵥ A *ᵥ x) := by
    simp [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hsplit]
  calc x ⬝ᵥ (A * A) *ᵥ x
      ≤ x ⬝ᵥ (r • A) *ᵥ x := dotProduct_mono (sq_le_smul_of_le_smul_one hA hle) x
    _ = r * (x ⬝ᵥ A *ᵥ x) := hsmul
    _ ≤ r * (r * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left (quadForm_le_smul_one hle x) hr
    _ = (r * r) * (x ⬝ᵥ x) := by ring

omit [DecidableEq V] in
/-- The squared Euclidean norm of a vector, as the `dotProduct` of its underlying function with
itself. The bridge between §2's matrix algebra and the analytic statement below. -/
theorem norm_sq_eq_dotProduct (y : EuclideanSpace ℝ V) : ‖y‖ ^ 2 = y.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [dotProduct, Real.norm_eq_abs, pow_two]

/-- **`‖A x‖ ≤ r ‖x‖` ON `EuclideanSpace ℝ V`.** The previous theorem with the squared norm
identified as a `dotProduct` on both sides, then square roots. -/
theorem norm_mulVec_le [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) (x : EuclideanSpace ℝ V) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ≤ r * ‖x‖ := by
  have hr : 0 ≤ r := nonneg_of_le_smul_one hA hle
  have hsq : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 = (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
      rw [norm_sq_eq_dotProduct, Matrix.ofLp_toEuclideanCLM]
    rw [h1, mul_pow, norm_sq_eq_dotProduct, pow_two r]
    exact dotProduct_mulVec_self_le hA hle x.ofLp
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hr (norm_nonneg x))] at h

/-- **THE JOIN, OVER `ℝ`, AND WITHOUT A `CStarAlgebra` INSTANCE.** For a positive semidefinite real
matrix, a Loewner bound `A ≤ r • 1` gives the same constant on the `l²` operator norm. This is the
forward direction of `CStarAlgebra.norm_le_iff_le_algebraMap`, which that theorem cannot supply
here because `CStarAlgebra` extends `NormedAlgebra ℂ A` (`ERRATUM 425`). -/
theorem l2_opNorm_le [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) : ‖A‖ ≤ r := by
  have hr : 0 ≤ r := nonneg_of_le_smul_one hA hle
  rw [← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A]
  exact ContinuousLinearMap.opNorm_le_bound _ hr (fun x => norm_mulVec_le hA hle x)

end PosSemidefNormBound
