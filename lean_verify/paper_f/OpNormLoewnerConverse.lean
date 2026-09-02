import EntrywiseFromOpNorm
import SymmetricOpNorm

/-!
# The converse: an operator-norm bound is a two-sided Loewner bound

`paper_f/PosSemidefNormBound.lean` closes with a fence in its own words: *"The converse direction of
`CStarAlgebra.norm_le_iff_le_algebraMap` — `‖A‖ ≤ r → A ≤ r • 1` — is **not** proved; only the
direction the estate needs is."* `PROOF_STRATEGY` §7 rule 2 — *finish every unfinished chain* — and
this is the chain's own fence rather than someone else's.

**IT IS PROVED HERE, AND FOR SYMMETRIC MATRICES RATHER THAN POSITIVE ONES.**
`l2_opNorm_le_iff_abs_le`: for a symmetric real matrix, `‖A‖ ≤ r` **if and only if**
`−r • 1 ≼ A ≼ r • 1`. That is `CStarAlgebra.norm_le_iff_le_algebraMap`'s statement over `ℝ`, which
that theorem cannot supply because `CStarAlgebra extends NormedAlgebra ℂ A` (`ERRATUM 425`), and
`l2_opNorm_le_iff_le_smul_one` is the positive-semidefinite case the fence actually names.

**THE PROOF IS CAUCHY–SCHWARZ AND NOTHING ELSE.** `abs_dotProduct_mulVec_le`:
`|x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ · (x ⬝ᵥ x)`, from `Finset.sum_mul_sq_le_sq_mul_sq` on the pairing and
`RemainderFormBound.dotProduct_mulVec_sq_le` on the second factor. A quadratic form squeezed between
`±‖A‖ (x ⬝ᵥ x)` is exactly a two-sided Loewner bound, once `Matrix.PosSemidef.
of_dotProduct_mulVec_nonneg` is given the symmetry.

**AND THE TWO DIRECTIONS ARE NOT SYMMETRIC IN THEIR HYPOTHESES**, which is the honest shape of the
biconditional and is stated rather than buried. **The converse proved here needs no `Nonempty V`**:
it reads an inequality off every vector, and on an empty type there are none to read and both sides
are trivially true. **The forward direction does need it** —
`SymmetricOpNorm.l2_opNorm_le_of_abs_le` runs through `PosSemidefNormBound.l2_opNorm_le`, which
is FALSE on an empty vertex type
(`ERRATUM 426`) — so the `iff` carries `[Nonempty V]` and each one-directional theorem is stated
separately without it where it can be.

**WHAT THIS IS NOT.**
* **No wall moves.** W1's ask is a lower bound on the cross form; this is a fact about matrices and
  is not about any graph. It is cited by nothing yet and that is stated rather than implied.
* **It is not new mathematics.** Over `ℂ` this is a line of `CStarAlgebra` theory; what is proved is
  that the real case does not need it, by an argument with no algebra in it.
* **Nothing is sharp** and nothing here claims the two-sided bound is attained.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace OpNormLoewnerConverse

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Cauchy–Schwarz on the quadratic form -/

/-- **`|x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ · (x ⬝ᵥ x)`.** Cauchy–Schwarz pairs `x` against `A *ᵥ x`, and
`RemainderFormBound.dotProduct_mulVec_sq_le` bounds the second factor by `‖A‖² (x ⬝ᵥ x)`. -/
theorem abs_dotProduct_mulVec_le (A : Matrix V V ℝ) (x : V → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have hxx : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun v => (A *ᵥ x) v)
  have hxs : ∑ v, (x v) ^ 2 = x ⬝ᵥ x := by
    rw [dotProduct]; exact Finset.sum_congr rfl fun v _ => (pow_two _)
  have hys : ∑ v, ((A *ᵥ x) v) ^ 2 = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    rw [dotProduct]; exact Finset.sum_congr rfl fun v _ => (pow_two _)
  have hpair : ∑ v, x v * (A *ᵥ x) v = x ⬝ᵥ A *ᵥ x := by rw [dotProduct]
  rw [hxs, hys, hpair] at hcs
  have hA := RemainderFormBound.dotProduct_mulVec_sq_le A x
  have hsq : (x ⬝ᵥ A *ᵥ x) ^ 2 ≤ (‖A‖ * (x ⬝ᵥ x)) ^ 2 := by nlinarith [hcs, hA, hxx, norm_nonneg A]
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (mul_nonneg (norm_nonneg A) hxx))

/-! ## 2. The converse, one side at a time, with no `Nonempty` -/

/-- **`‖A‖ ≤ r` GIVES `A ≼ r • 1`** for a symmetric real matrix. **No `Nonempty V`**: the argument
reads an inequality off every vector, and an empty type supplies none. -/
theorem le_smul_one_of_opNorm_le {A : Matrix V V ℝ} (hT : Aᵀ = A) {r : ℝ} (hr : ‖A‖ ≤ r) :
    A ≤ r • (1 : Matrix V V ℝ) := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ hT
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · have hxx : 0 ≤ x ⬝ᵥ x := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
    have hb := abs_le.mp (abs_dotProduct_mulVec_le A x)
    have hone : x ⬝ᵥ (r • (1 : Matrix V V ℝ)) *ᵥ x = r * (x ⬝ᵥ x) := by
      simp [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, hone]
    nlinarith [hb.2, hxx, norm_nonneg A, hr]

/-- **`‖A‖ ≤ r` GIVES `−r • 1 ≼ A`**, the other side, and again with no `Nonempty V`. -/
theorem neg_smul_one_le_of_opNorm_le {A : Matrix V V ℝ} (hT : Aᵀ = A) {r : ℝ} (hr : ‖A‖ ≤ r) :
    -(r • (1 : Matrix V V ℝ)) ≤ A := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub hT ?_
    rw [Matrix.IsSymm, Matrix.transpose_neg, Matrix.smul_one_eq_diagonal]
    exact congrArg Neg.neg (Matrix.isSymm_diagonal _)
  · have hxx : 0 ≤ x ⬝ᵥ x := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
    have hb := abs_le.mp (abs_dotProduct_mulVec_le A x)
    have hone : x ⬝ᵥ (-(r • (1 : Matrix V V ℝ))) *ᵥ x = -(r * (x ⬝ᵥ x)) := by
      simp [Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
        smul_eq_mul, dotProduct_neg]
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, hone]
    nlinarith [hb.1, hxx, norm_nonneg A, hr]

/-! ## 3. The biconditional, and the fence's own statement -/

/-- **`‖A‖ ≤ r ↔ −r • 1 ≼ A ≼ r • 1`, FOR A SYMMETRIC REAL MATRIX.**
`CStarAlgebra.norm_le_iff_le_algebraMap`'s statement over `ℝ`, which that theorem cannot supply
(`ERRATUM 425`). **`Nonempty V` is needed only for the forward direction** and §2's two theorems are
stated without it. -/
theorem l2_opNorm_le_iff_abs_le [Nonempty V] {A : Matrix V V ℝ} (hT : Aᵀ = A) {r : ℝ} :
    ‖A‖ ≤ r ↔ (-(r • (1 : Matrix V V ℝ)) ≤ A ∧ A ≤ r • (1 : Matrix V V ℝ)) :=
  ⟨fun hr => ⟨neg_smul_one_le_of_opNorm_le hT hr, le_smul_one_of_opNorm_le hT hr⟩,
   fun h => SymmetricOpNorm.l2_opNorm_le_of_abs_le h.1 h.2⟩

/-- **THE FENCE'S OWN STATEMENT**: for a positive semidefinite real matrix, `‖A‖ ≤ r` **iff**
`A ≼ r • 1`. The lower bound is free once `0 ≼ A`, given `0 ≤ r`, which either side supplies. -/
theorem l2_opNorm_le_iff_le_smul_one [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ} :
    ‖A‖ ≤ r ↔ A ≤ r • (1 : Matrix V V ℝ) := by
  have hps : A.PosSemidef := by simpa using Matrix.le_iff.mp hA
  have hT : Aᵀ = A := by simpa [Matrix.conjTranspose, Matrix.map] using hps.isHermitian
  refine ⟨fun hr => le_smul_one_of_opNorm_le hT hr, fun hle => ?_⟩
  exact PosSemidefNormBound.l2_opNorm_le hA hle

end OpNormLoewnerConverse
