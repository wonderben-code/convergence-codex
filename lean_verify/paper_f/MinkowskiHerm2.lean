/-
  MinkowskiHerm2: The Minkowski Form on 2×2 Hermitian Matrices
  ============================================================

  Stage 1 of the SL₂(ℂ) ≅ Spin(3,1) gap (tree §6.2/§7.1, old gap #7; spine
  L9). What was in Lean before: GravityLineage's det-preservation
  det(A·H·A*) = det(H), |center SL₂| = 2, spinor-rep faithfulness; F1_7b's
  arithmetic exclusions. What was missing: the Minkowski structure itself.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `pauliHerm t x y z` — the Hermitian matrix t·1 + x·σ₁ + y·σ₂ + z·σ₃,
     with `pauliHerm_isHermitian` (entrywise conjugation check).
  2. `pauliHerm_surjective` — EVERY 2×2 Hermitian matrix is of this form:
     the Pauli coordinates (t,x,y,z) ∈ ℝ⁴ parametrise Herm₂(ℂ) fully
     (coefficients recovered from the entries).
  3. `det_pauliHerm` — det(pauliHerm t x y z) = t² − x² − y² − z², as an
     identity in ℂ with a real right-hand side: THE MINKOWSKI QUADRATIC
     FORM of signature (1,3), exhibited diagonally in the Pauli
     coordinates. (Combined with 2: the determinant form on Herm₂ IS the
     Minkowski form — "the signature is (1,3)" in explicit-diagonal terms.)
  4. `det_conj_invariant` — for A ∈ SL₂(ℂ): det(A·H·Aᴴ) = det(H) — the
     SL₂(ℂ) action preserves the form (self-contained one-line proof via
     det multiplicativity; GravityLineage proves the same fact — restated
     here to keep this file standalone).
  5. `conj_action_hermitian`, `conj_action_one`, `conj_action_mul` — the
     conjugation map H ↦ A·H·Aᴴ preserves Herm₂ and satisfies the action
     axioms (identity and compatibility), stated as equations. (No bundled
     `MulAction` instance is built — noted below.)
  6. `kernel_of_conj_action` + `pm_one_in_kernel` — BOTH inclusions of
     "the kernel is {±1}": if det(A) = 1 and A·H·Aᴴ = H for every
     Hermitian H then A = ±1; and conversely ±1 do fix every Hermitian
     matrix. The ℤ/2 of the double cover. (Route for ⊆: fixing 1 gives
     A·Aᴴ = 1, turning fixing into commuting; commuting with σ₃ and σ₁
     forces A scalar; det = 1 then forces the scalar c to satisfy c² = 1,
     so c = ±1.)
  7. `pauliHerm_injective` and `pauliHerm_eq_combination` — the Pauli
     parametrisation is injective (coefficients are unique) and equals the
     linear combination t·1 + x·σ₁ + y·σ₂ + z·σ₃ (proven entrywise), so
     "Pauli coordinates" is earned: a bijective parametrisation of Herm₂.

  NOT proven here (the remaining stairs of gap #7, stated so the tag stays
  honest): the bundled Mathlib `QuadraticForm`/`QuadraticForm.Signature`
  packaging of item 3, INCLUDING Sylvester invariance (that (1,3) is THE
  signature, invariant under change of basis, is not formalised — what is
  proven is the explicit diagonalisation with signs (+,−,−,−) in an
  injective, surjective, linear parametrisation); a bundled `MulAction` of
  SL₂(ℂ) on Herm₂ (the action equations of item 5 are proven, the
  typeclass object is not constructed); SURJECTIVITY of SL₂(ℂ) → SO⁺(1,3)
  (the actual covering statement — needs polar decomposition/connectedness);
  any identification with `CliffordAlgebra.spinGroup`. Those remain open.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open Matrix Complex

noncomputable section

namespace MinkowskiHerm2

/-! ## 1–2. The Pauli parametrisation of Herm₂(ℂ) -/

/-- The Hermitian matrix with Pauli coordinates (t, x, y, z):
    t·1 + x·σ₁ + y·σ₂ + z·σ₃. -/
def pauliHerm (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t : ℂ) + z, (x : ℂ) - (y : ℂ) * I;
     (x : ℂ) + (y : ℂ) * I, (t : ℂ) - z]

theorem pauliHerm_isHermitian (t x y z : ℝ) :
    (pauliHerm t x y z)ᴴ = pauliHerm t x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliHerm, Matrix.conjTranspose_apply, Complex.conj_ofReal,
      Complex.conj_I, sub_eq_add_neg]

/-- Every 2×2 Hermitian matrix has Pauli coordinates: the parametrisation is
    surjective onto Herm₂(ℂ). Coefficients: t = (Re H₀₀ + Re H₁₁)/2,
    z = (Re H₀₀ − Re H₁₁)/2, x = Re H₀₁, y = −Im H₀₁. -/
theorem pauliHerm_surjective (H : Matrix (Fin 2) (Fin 2) ℂ)
    (hH : Hᴴ = H) :
    ∃ t x y z : ℝ, H = pauliHerm t x y z := by
  have hst00 : (starRingEnd ℂ) (H 0 0) = H 0 0 := by
    have := congrFun (congrFun hH 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have hst11 : (starRingEnd ℂ) (H 1 1) = H 1 1 := by
    have := congrFun (congrFun hH 1) 1
    simpa [Matrix.conjTranspose_apply] using this
  have h00 : H 0 0 = ((H 0 0).re : ℂ) := by
    have him : (H 0 0).im = 0 := Complex.conj_eq_iff_im.mp hst00
    exact Complex.ext_iff.mpr ⟨(Complex.ofReal_re _).symm, by simp [him]⟩
  have h11 : H 1 1 = ((H 1 1).re : ℂ) := by
    have him : (H 1 1).im = 0 := Complex.conj_eq_iff_im.mp hst11
    exact Complex.ext_iff.mpr ⟨(Complex.ofReal_re _).symm, by simp [him]⟩
  have h10 : H 1 0 = (starRingEnd ℂ) (H 0 1) := by
    have := congrFun (congrFun hH 1) 0
    simpa [Matrix.conjTranspose_apply] using this.symm
  refine ⟨((H 0 0).re + (H 1 1).re) / 2, (H 0 1).re, -(H 0 1).im,
    ((H 0 0).re - (H 1 1).re) / 2, ?_⟩
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  constructor
  · rw [Fin.forall_fin_two]
    constructor
    · conv_lhs => rw [h00]
      simp only [pauliHerm, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.of_apply]
      push_cast
      ring
    · simp only [pauliHerm, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply]
      rw [Complex.ext_iff]
      constructor <;> simp
  · rw [Fin.forall_fin_two]
    constructor
    · conv_lhs => rw [h10]
      simp only [pauliHerm, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.of_apply]
      rw [Complex.ext_iff]
      constructor <;> simp [Complex.conj_re, Complex.conj_im]
    · conv_lhs => rw [h11]
      simp only [pauliHerm, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.of_apply]
      push_cast
      ring

/-- The Pauli parametrisation is injective: coefficients are unique
    (recovered from the matrix entries). With `pauliHerm_surjective`:
    a bijective parametrisation of Herm₂(ℂ) by ℝ⁴. -/
theorem pauliHerm_injective (t x y z t' x' y' z' : ℝ)
    (h : pauliHerm t x y z = pauliHerm t' x' y' z') :
    t = t' ∧ x = x' ∧ y = y' ∧ z = z' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp only [pauliHerm, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply] at h00 h01 h11
  have e00 := congrArg Complex.re h00
  have e11 := congrArg Complex.re h11
  have e01r := congrArg Complex.re h01
  have e01i := congrArg Complex.im h01
  simp at e00 e11 e01r e01i
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The three Pauli matrices (σ₂ included), for the combination identity. -/
private def pSigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
private def pSigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
private def pSigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `pauliHerm` IS the linear combination t·1 + x·σ₁ + y·σ₂ + z·σ₃,
    entrywise — the docstring gloss as a theorem. Linearity of the
    parametrisation follows (a linear combination of fixed matrices). -/
theorem pauliHerm_eq_combination (t x y z : ℝ) :
    pauliHerm t x y z
      = (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (x : ℂ) • pSigma1
        + (y : ℂ) • pSigma2 + (z : ℂ) • pSigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliHerm, pSigma1, pSigma2, pSigma3, Matrix.one_fin_two] <;>
    ring

/-! ## 3. The determinant is the Minkowski form: signature (1,3) exhibited -/

/-- **The Minkowski form**: det(t·1 + x·σ₁ + y·σ₂ + z·σ₃) = t² − x² − y² − z².
    One plus, three minuses — the (1,3) signature of spacetime, exhibited
    diagonally in the (surjective) Pauli coordinates of Herm₂(ℂ). -/
theorem det_pauliHerm (t x y z : ℝ) :
    det (pauliHerm t x y z)
      = ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  rw [pauliHerm, Matrix.det_fin_two_of]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## 4–5. SL₂(ℂ) acts on Herm₂ preserving the form -/

/-- SL₂(ℂ) preserves the determinant form on Herm₂:
    det(A·H·Aᴴ) = det(H) for det(A) = 1. -/
theorem det_conj_invariant (A H : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : det A = 1) : det (A * H * Aᴴ) = det H := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hA]
  simp

/-- The conjugation action maps Hermitian matrices to Hermitian matrices:
    SL₂(ℂ) genuinely acts on Herm₂(ℂ). -/
theorem conj_action_hermitian (A H : Matrix (Fin 2) (Fin 2) ℂ)
    (hH : Hᴴ = H) : (A * H * Aᴴ)ᴴ = A * H * Aᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]

/-- Action axiom (identity): conjugation by 1 is the identity. -/
theorem conj_action_one (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) * H * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = H := by
  simp

/-- Action axiom (compatibility): conjugation by A·B is conjugation by B
    then by A. -/
theorem conj_action_mul (A B H : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * B) * H * (A * B)ᴴ = A * (B * H * Bᴴ) * Aᴴ := by
  rw [Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## 6. The kernel of the action is exactly {±1} -/

/-- σ₃ and σ₁, used as probe matrices for the kernel computation. -/
private def sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
private def sigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

private theorem sigma3_hermitian : sigma3ᴴ = sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma3]

private theorem sigma1_hermitian : sigma1ᴴ = sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma1]

/-- **The kernel of the SL₂(ℂ) action on Herm₂ is {±1}** — the ℤ/2 of the
    double cover SL₂(ℂ) → SO⁺(1,3). If det(A) = 1 and A·H·Aᴴ = H for every
    Hermitian H, then A = 1 or A = −1. -/
theorem kernel_of_conj_action (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : det A = 1)
    (hfix : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, Hᴴ = H → A * H * Aᴴ = H) :
    A = 1 ∨ A = -1 := by
  -- Fixing H = 1 gives A·Aᴴ = 1, so Aᴴ is a right inverse of A
  have hone : A * Aᴴ = 1 := by
    have := hfix 1 (by simp)
    simpa using this
  -- hence A·H·Aᴴ = H rearranges to A·H = H·A for every Hermitian H
  have hcomm : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, Hᴴ = H → A * H = H * A := by
    intro H hH
    have hfixH := hfix H hH
    calc A * H = A * H * (Aᴴ * A) := by
          rw [mul_eq_one_comm.mp hone, Matrix.mul_one]
      _ = (A * H * Aᴴ) * A := by noncomm_ring
      _ = H * A := by rw [hfixH]
  -- commuting with σ₃ forces A diagonal
  have h3 := hcomm sigma3 sigma3_hermitian
  have hA01 : A 0 1 = 0 := by
    have := congrFun (congrFun h3 0) 1
    simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this / 2
  have hA10 : A 1 0 = 0 := by
    have := congrFun (congrFun h3 1) 0
    simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this / 2
  -- commuting with σ₁ forces the diagonal entries equal
  have h1 := hcomm sigma1 sigma1_hermitian
  have hdiag : A 0 0 = A 1 1 := by
    have h01 := congrFun (congrFun h1 0) 1
    simpa [sigma1, Matrix.mul_apply, Fin.sum_univ_two, hA01] using h01
  -- so A = c·1 with c² = det A = 1
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hA
  rw [hA01, hA10] at hdet
  simp only [mul_zero, sub_zero] at hdet
  rw [← hdiag] at hdet
  -- c² = 1 in ℂ: c = 1 or c = −1
  have hc : A 0 0 = 1 ∨ A 0 0 = -1 :=
    mul_self_eq_one_iff.mp (by linear_combination hdet)
  rcases hc with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hA01, hA10, h, ← hdiag]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hA01, hA10, h, ← hdiag]

/-- The converse inclusion: ±1 genuinely lie in the kernel — both have
    det = 1 and fix every Hermitian matrix. With `kernel_of_conj_action`:
    the kernel is EXACTLY {±1}. -/
theorem pm_one_in_kernel :
    (det (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      ∀ H : Matrix (Fin 2) (Fin 2) ℂ, Hᴴ = H →
        (1 : Matrix (Fin 2) (Fin 2) ℂ) * H * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = H) ∧
    (det (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      ∀ H : Matrix (Fin 2) (Fin 2) ℂ, Hᴴ = H →
        (-1 : Matrix (Fin 2) (Fin 2) ℂ) * H * (-1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = H) := by
  refine ⟨⟨by simp, fun H _ => by simp⟩,
    ⟨?_, fun H _ => by
      simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_one,
        Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.one_mul]
      exact neg_neg H⟩⟩
  rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1 by simp]
  rw [Matrix.det_smul]
  simp

end MinkowskiHerm2
