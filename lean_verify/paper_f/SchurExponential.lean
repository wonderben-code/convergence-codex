/-
  SchurExponential: the Entrywise Exponential Preserves Positive
  Semidefiniteness
  ==============================================================

  Stair E1–E3 of the exponential-algebra OS2 item (UNLOCK_WATCHLIST): the
  pairing of exponential observables against the Gaussian field produces
  kernel matrices of the shape e^{cᵢ + cⱼ + Bᵢⱼ} with B PSD, and their
  positivity is exactly the SCHUR-EXPONENTIAL closure: if B is positive
  semidefinite then so is the ENTRYWISE exponential [e^{Bᵢⱼ}].

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `hadamardPow_posSemidef` — entrywise powers A^{∘k} of a PSD matrix are
     PSD (the iterated Schur theorem at a constant family).
  2. `quadForm_hasSum` — the quadratic form of the entrywise exponential is
     the SUM of the quadratic forms of the entrywise powers over k!, via
     the exponential series termwise (`NormedSpace.expSeries_div_hasSum_exp`)
     and a finite-by-infinite sum swap (`hasSum_sum`). No matrix limits, no
     operator topology: the series is summed at the level of the scalar
     quadratic form.
  3. **`posSemidef_entrywise_exp`** — THE SCHUR-EXPONENTIAL THEOREM:
     B PSD ⟹ [e^{Bᵢⱼ}] PSD. Each summand of the form is nonnegative by
     item 1, so the sum is (`tsum_nonneg`).
  4. **`posSemidef_gaussian_kernel`** — the shape the OS pairing actually
     produces: for ANY vector c and PSD B, the matrix [e^{cᵢ + cⱼ + Bᵢⱼ}]
     is PSD — a rank-one Gram conjugation (the cᵢ + cⱼ part) Hadamard the
     entrywise exponential of B. This is the exact kernel-positivity input
     for the exponential-observable OS2 statement, staged on the watchlist.
  5. Concrete witnesses: the entrywise exponential of !![1,1;1,1] is
     !![e,e;e,e], PSD with the theorem applicable; and the hypothesis
     bites — [e^{Bᵢⱼ}] of the NON-PSD !![0,1;1,0] is !![1,e;e,1], which is
     NOT PSD (its form at (1,−1) is 2 − 2e < 0) — entrywise exponentials
     do not manufacture positivity from nothing.

  Scope honesty: real matrices, finite index types. The complex-coefficient
  form of kernel positivity (a real symmetric PSD matrix is PSD as a
  Hermitian form over ℂ) is one small bridging lemma away and belongs to
  the exponential-OS2 assembly unit, not here.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import SchurProduct
import Mathlib.Analysis.SpecialFunctions.Exponential

open Matrix Real Finset

noncomputable section

namespace SchurExponential

variable {n : Type*}

/-! ## 1. Entrywise powers of a PSD matrix -/

/-- Entrywise powers of a PSD real matrix are PSD: the iterated Schur
    theorem applied to the constant family. -/
theorem hadamardPow_posSemidef [Finite n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (k : ℕ) :
    (Matrix.of fun i j => A i j ^ k).PosSemidef := by
  have h := SchurProduct.posSemidef_entrywise_prod
    (fun _ : Fin k => A) (fun _ => hA)
  have heq : (Matrix.of fun i j => ∏ _l : Fin k, A i j)
      = (Matrix.of fun i j => A i j ^ k) := by
    ext i j
    simp [Finset.prod_const]
  rwa [heq] at h

/-! ## 2. The quadratic form of the entrywise exponential, as a series -/

/-- The quadratic form of [e^{Bᵢⱼ}] at x is the sum over k of the quadratic
    forms of the entrywise powers B^{∘k}/k! at x. -/
theorem quadForm_hasSum [Fintype n] (B : Matrix n n ℝ) (x : n → ℝ) :
    HasSum
      (fun k : ℕ => ∑ i, ∑ j, x i * x j * (B i j ^ k / (k.factorial : ℝ)))
      (∑ i, ∑ j, x i * x j * Real.exp (B i j)) := by
  refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
  have h := NormedSpace.expSeries_div_hasSum_exp (B i j)
  have h2 := h.mul_left (x i * x j)
  simpa [Real.exp_eq_exp_ℝ, mul_assoc] using h2

/-! ## 3. The Schur-exponential theorem -/

/-- **The entrywise exponential of a PSD real matrix is PSD.** Each term of
    the exponential series contributes a nonnegative quadratic form
    (entrywise powers are PSD), and the form of [e^{Bᵢⱼ}] is their sum. -/
theorem posSemidef_entrywise_exp [Finite n] {B : Matrix n n ℝ}
    (hB : B.PosSemidef) :
    (Matrix.of fun i j => Real.exp (B i j)).PosSemidef := by
  have := Fintype.ofFinite n
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    have h := congrFun (congrFun hB.1 i) j
    simp only [Matrix.conjTranspose_apply, star_trivial] at h
    rw [h]
  · intro x
    have heq : star x ⬝ᵥ (Matrix.of fun i j => Real.exp (B i j)) *ᵥ x
        = ∑ i, ∑ j, x i * x j * Real.exp (B i j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    have hsum := quadForm_hasSum B x
    rw [← hsum.tsum_eq]
    refine tsum_nonneg fun k => ?_
    have hk := (hadamardPow_posSemidef hB k).dotProduct_mulVec_nonneg x
    have heq2 : star x ⬝ᵥ (Matrix.of fun i j => B i j ^ k) *ᵥ x
        = ∑ i, ∑ j, x i * x j * B i j ^ k := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq2] at hk
    have hfac : (0 : ℝ) ≤ ((k.factorial : ℝ))⁻¹ := by positivity
    calc (0 : ℝ) ≤ ((k.factorial : ℝ))⁻¹ * ∑ i, ∑ j, x i * x j * B i j ^ k :=
          mul_nonneg hfac hk
      _ = ∑ i, ∑ j, x i * x j * (B i j ^ k / (k.factorial : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          field_simp

/-! ## 4. The Gaussian kernel shape -/

/-- **The kernel matrix of the exponential OS pairing is PSD**: for any
    vector c and PSD B, the matrix [e^{cᵢ + cⱼ + Bᵢⱼ}] is positive
    semidefinite — the rank-one factor e^{cᵢ}e^{cⱼ} Hadamard the entrywise
    exponential of B. -/
theorem posSemidef_gaussian_kernel [Finite n]
    (c : n → ℝ) {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    (Matrix.of fun i j => Real.exp (c i + c j + B i j)).PosSemidef := by
  have h1 : (Matrix.of fun i j => Real.exp (c i + c j)).PosSemidef := by
    have h := posSemidef_vecMulVec_star_self (fun i => Real.exp (c i))
    have hg : star (fun i => Real.exp (c i)) = fun i => Real.exp (c i) := by
      ext i
      simp
    rw [hg] at h
    have heq : (Matrix.of fun i j => Real.exp (c i + c j))
        = vecMulVec (fun i => Real.exp (c i)) (fun i => Real.exp (c i)) := by
      ext i j
      simp only [Matrix.of_apply, vecMulVec_apply, ← Real.exp_add]
    rw [heq]
    exact h
  have h2 := SchurProduct.posSemidef_hadamard h1 (posSemidef_entrywise_exp hB)
  have heq : (Matrix.of fun i j => Real.exp (c i + c j + B i j))
      = (Matrix.of fun i j => Real.exp (c i + c j))
          ⊙ (Matrix.of fun i j => Real.exp (B i j)) := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.of_apply, ← Real.exp_add]
  rwa [heq]

/-! ## 5. The theorem bites, the hypothesis excludes -/

/-- The all-ones 2×2 matrix is PSD, so the theorem applies to it: its
    entrywise exponential [e,e;e,e] is PSD. -/
theorem exp_allOnes_posSemidef :
    (Matrix.of fun _ _ : Fin 2 => Real.exp 1).PosSemidef := by
  have hall : (Matrix.of fun _ _ : Fin 2 => (1 : ℝ)).PosSemidef :=
    SchurProduct.posSemidef_allOnes
  have h := posSemidef_entrywise_exp (B := Matrix.of fun _ _ : Fin 2 => (1 : ℝ)) hall
  simpa using h

/-- The hypothesis bites: the entrywise exponential of the NON-PSD matrix
    !![0,1;1,0] is !![1,e;e,1], and that is NOT PSD — its quadratic form at
    (1, −1) is 2 − 2e < 0. Entrywise exponentials do not manufacture
    positivity. -/
theorem exp_offDiag_not_posSemidef :
    ¬ (Matrix.of fun i j : Fin 2 =>
        Real.exp ((!![(0 : ℝ), 1; 1, 0]) i j)).PosSemidef := by
  intro h
  have h2 := h.dotProduct_mulVec_nonneg ![1, -1]
  have hval : (star ![(1 : ℝ), -1]) ⬝ᵥ ((Matrix.of fun i j : Fin 2 =>
      Real.exp ((!![(0 : ℝ), 1; 1, 0]) i j)) *ᵥ ![1, -1])
      = 2 - 2 * Real.exp 1 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply]
    ring
  rw [hval] at h2
  have hgt : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  linarith

end SchurExponential
