/-
  StarStructureHermitian: the twist can be taken HERMITIAN, so the classification is a
  signature

  SPINE LINK L11 — `UNLOCK_WATCHLIST` 266's item (1), which that entry called the cheapest
  remaining step.

  WHERE THIS PICKS UP. `StarStructureMatrix.exists_inner_conjTranspose` proved that every
  ⋆-structure on `Mₙ(ℂ)` is `X ↦ (P X P⁻¹)ᴴ` for an invertible `P`, and
  `involution_scalar` priced involutivity: `Pᴴ = c • P` for some `c`. **That left the twist
  determined only up to an unknown scalar, and the orthogonal/symplectic fork located rather
  than taken.** Two steps close it.

  WHAT IS PROVED.
  * **`involution_norm_one`** — `c` has modulus one. Conjugate-transposing `Pᴴ = c • P` twice
    gives `P = (conj c · c) • P`, and `P` is invertible so it is not zero. **The invertibility
    is used exactly once and this is where.**
  * **`exists_hermitian_twist`** — **the classification in normal form**:

    > every ⋆-structure on `Mₙ(ℂ)` is `X ↦ (P X P⁻¹)ᴴ` with `P` invertible **and HERMITIAN**.

    Rescale `P` by a square root `d` of `c`. Because `|c| = 1` the root has modulus one too, so
    `conj d = d⁻¹` and `(d • P)ᴴ = conj d · c • P = d⁻¹ · d² • P = d • P`. `ℂ` being
    algebraically closed supplies the root (`IsAlgClosed.exists_pow_nat_eq`); **that is the only
    place the field's algebraic closure is used, and over `ℝ` it is exactly what fails** —
    which is the shape of the real-form story rather than a proof of it.
  * **`star_eq_conj_hermitian`** — and in normal form the map reads
    `s X = P⁻¹ Xᴴ P`, with no transpose on the twist. So **what remains of the classification
    is `P` itself, a non-degenerate Hermitian form up to real scalars — that is, a SIGNATURE.**

  WHAT IS **NOT** CLAIMED.
  * **The signature is not computed, and no two ⋆-structures are shown equivalent or
    inequivalent.** The classification is reduced to a Hermitian form; which forms give the same
    ⋆-structure, and what the invariant is, are not stated. Calling the residue "a signature" is
    a description of the remaining object, not a theorem about it.
  * **Nothing is proved over `ℝ`.** The sentence about algebraic closure failing there points at
    where the real-form classification differs, and **it is a pointer to the classical statement,
    not to a theorem of this estate.** Said precisely, because the loose version would be false:
    the estate has **108 declarations naming quaternions** and eight of those also name a
    `star`-family notion — `QuaternionTensor.rmulStar` and its neighbours. **What it has none of
    is a declaration connecting `Mₙ(ℝ)` or `Mₙ(ℍ)` to a ⋆-structure on a MATRIX algebra**, which
    is the question this file is about. The absence is narrow and the count is the grep's.
  * **The PRODUCT case is still not done for `n` FACTORS** — `∏ Mₐᵢ(Dᵢ)`, which is what both
    L6 rung 2 and L11's three-factor statement actually need. The **two**-factor case landed in
    the two units after this one: `StarStructureProduct.prod_dichotomy` for the dichotomy and
    `StarStructureProductMatrix.classification_of_ne_size` for the normal form at unequal sizes,
    the latter consuming `exists_hermitian_twist` on each factor. **Those two call sites are the
    only consumers `exists_hermitian_twist` has anywhere in the estate, and
    `star_eq_conj_hermitian` still has none** — grepped, not assumed. Worth saying plainly: the
    normal form was proved before anything needed it, and the two-factor product classification
    is the thing that turned out to need it.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35).

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import StarStructureMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace StarStructureHermitian

open Matrix StarStructureMatrix

noncomputable section

variable {n : ℕ}

/-! ## 1. The scalar has modulus one -/

/-- **`c` has modulus one.** Conjugate-transposing `Pᴴ = c • P` returns
`P = (conj c · c) • P`, and `P` is a unit so it is non-zero. **Invertibility of `P` is used
exactly once in this whole development, and this is the use.** -/
theorem involution_norm_one [NeZero n] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) (c : ℂ)
    (hc : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = c • (P : Matrix (Fin n) (Fin n) ℂ)) :
    (starRingEnd ℂ) c * c = 1 := by
  have hPne : (P : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
    intro h
    have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
      have hmi := P.mul_inv
      rw [h, Matrix.zero_mul] at hmi
      exact hmi.symm
    have h2 := congrFun (congrFun h1 ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    simp at h2
  have hround : (P : Matrix (Fin n) (Fin n) ℂ)
      = ((starRingEnd ℂ) c * c) • (P : Matrix (Fin n) (Fin n) ℂ) := by
    have h := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul, hc, smul_smul] at h
    exact h
  have hzero : (1 - (starRingEnd ℂ) c * c) • (P : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    rw [sub_smul, one_smul, ← hround, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · linear_combination -h
  · exact absurd h hPne

/-! ## 2. The twist can be taken Hermitian -/

/-- `conj z * z = 1` says exactly that `z` has modulus one. -/
theorem norm_eq_one_of_conj_mul {z : ℂ} (h : (starRingEnd ℂ) z * z = 1) : ‖z‖ = 1 := by
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow] at h
  have h2 : ‖z‖ ^ 2 = (1 : ℝ) := Complex.ofReal_eq_one.mp h
  nlinarith [norm_nonneg z]

/-- and back again. -/
theorem conj_mul_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [RCLike.conj_mul, h]
  norm_num

/-- **THE CLASSIFICATION IN NORMAL FORM.** Every ⋆-structure on `Mₙ(ℂ)` is `X ↦ (P X P⁻¹)ᴴ`
with `P` invertible **and Hermitian**. The rescaling is by a square root `d` of `c`: modulus
one forces `conj d · d = 1`, so `(d • P)ᴴ = (conj d · c) • P = (conj d · d²) • P = d • P`.
**`ℂ` being algebraically closed is used exactly here**, to produce `d`, and over `ℝ` it is
exactly what fails. -/
theorem exists_hermitian_twist [NeZero n] (s : StarStructure n) :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ,
      (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ) ∧
      ∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
        * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  obtain ⟨P, hP⟩ := exists_inner_conjTranspose s
  obtain ⟨c, hc⟩ := involution_scalar s P hP
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) c (n := 2) (by norm_num)
  have hcn : ‖c‖ = 1 := norm_eq_one_of_conj_mul (involution_norm_one P c hc)
  have hdn : ‖d‖ = 1 := by
    have h : ‖d‖ ^ 2 = 1 := by rw [← norm_pow, hd, hcn]
    nlinarith [norm_nonneg d]
  have hdc : (starRingEnd ℂ) d * d = 1 := conj_mul_of_norm_eq_one hdn
  have hdne : d ≠ 0 := by
    intro h; rw [h] at hdn; simp at hdn
  have hmi : (P : Matrix (Fin n) (Fin n) ℂ)
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
  have him : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
  refine ⟨⟨d • (P : Matrix (Fin n) (Fin n) ℂ),
    d⁻¹ • ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hdne, hmi, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hdne, him,
      one_smul]⟩, ?_, ?_⟩
  · change (d • (P : Matrix (Fin n) (Fin n) ℂ))ᴴ = d • (P : Matrix (Fin n) (Fin n) ℂ)
    rw [Matrix.conjTranspose_smul, hc, smul_smul]
    congr 1
    calc (starRingEnd ℂ) d * c = (starRingEnd ℂ) d * (d ^ 2) := by rw [hd]
      _ = ((starRingEnd ℂ) d * d) * d := by ring
      _ = d := by rw [hdc, one_mul]
  · intro X
    have hsc : (d • (P : Matrix (Fin n) (Fin n) ℂ)) * X
        * (d⁻¹ • ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        = (P : Matrix (Fin n) (Fin n) ℂ) * X
          * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ hdne, one_smul]
    change s.map X = ((d • (P : Matrix (Fin n) (Fin n) ℂ)) * X
      * (d⁻¹ • ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))ᴴ
    rw [hsc, hP]

/-! ## 3. In normal form the map has no transpose on the twist -/

/-- **`s X = P⁻¹ Xᴴ P` when `P` is Hermitian.** So what remains of the classification is `P`
itself — a non-degenerate Hermitian form up to scalars, that is, a SIGNATURE. Calling the
residue that is a description of the remaining object and not a theorem about it. -/
theorem star_eq_conj_hermitian [NeZero n] (s : StarStructure n)
    (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hherm : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hP : ∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    s.map X = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Xᴴ
      * (P : Matrix (Fin n) (Fin n) ℂ) := by
  have hinvherm : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    have h1 : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
        * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [← hherm, ← Matrix.conjTranspose_mul]
      simp
    have h2 : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
    calc ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
        = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
          * ((P : Matrix (Fin n) (Fin n) ℂ)
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by simp
      _ = (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
            * (P : Matrix (Fin n) (Fin n) ℂ))
          * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [Matrix.mul_assoc]
      _ = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [h1, Matrix.one_mul]
  rw [hP X, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hherm, hinvherm,
    Matrix.mul_assoc]

end

end StarStructureHermitian
