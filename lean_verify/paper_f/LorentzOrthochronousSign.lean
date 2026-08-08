/-
  LorentzOrthochronousSign.lean — the sign of Λ⁰₀ is multiplicative.

  WHY. `LorentzGroup.orthochronous_mul` proves that two Lorentz matrices
  with positive time-time entry have a product with positive time-time
  entry. That is the one non-formal step in making SO⁺(1,3) a subgroup,
  it is a Cauchy–Schwarz argument, and it was proved months ago. What it
  does NOT give is the other three sign cases, and a chain that has to
  track the sign through a product of matrices whose signs are unknown —
  which is exactly what an induction over a group's generators is —
  needs all four.

  THE OBSERVATION THAT MAKES THE OTHER THREE FREE. If `M` is a Lorentz
  matrix then so is `−M`, since `(−M)ᵀ G (−M) = MᵀGM`. And `(−M)⁰₀ =
  −M⁰₀`, while `(−M)(−N) = MN`. So a matrix with a NEGATIVE time-time
  entry is the negative of one with a positive entry, and every case
  reduces to the one already proved. No time-reversal matrix, no second
  Cauchy–Schwarz, no case analysis on the space part.

  WHAT THIS FILE PROVES:
  1. **`isLorentzMat_neg`** — the observation.
  2. **`orthochronous_mul_neg_neg`**, **`antichronous_mul_left`**,
     **`antichronous_mul_right`** — the remaining three cases.
  3. **`sign_mul`** — the packaged form, stated for arbitrary nonzero
     real weights rather than for `±1`, because that is the shape an
     induction wants: if `0 < a · M⁰₀` and `0 < b · N⁰₀` then
     `0 < (ab) · (MN)⁰₀`.
  4. **`exists_sign`** and **`zero_zero_ne_zero`** — every Lorentz matrix
     has a sign, because `Λ⁰₀` is never zero (`|Λ⁰₀| ≥ 1`).

  WHAT THIS DOES NOT DO. Nothing here is about the spin group, and
  nothing here mentions `det`. This is general Lorentz-matrix arithmetic;
  the consumer is the next file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LorentzGroup

namespace LorentzOrthochronousSign

open MinkowskiSignature LorentzGroup
open scoped Matrix

/-! ## 1. The negative of a Lorentz matrix is a Lorentz matrix -/

theorem isLorentzMat_neg {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    IsLorentzMat (-M) := by
  have heq : (-M)ᵀ * gram * (-M) = Mᵀ * gram * M := by
    simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg]
    exact neg_neg _
  rw [IsLorentzMat, heq]
  exact h

@[simp] theorem neg_zero_zero (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (-M) 0 0 = -(M 0 0) := rfl

/-! ## 2. `Λ⁰₀` is never zero

From `ΛᵀGΛ = G` the (0,0) entry reads `Λ⁰₀² − Λ⁰₁² − Λ⁰₂² − Λ⁰₃² = 1`,
so `Λ⁰₀² ≥ 1`. The estate had this only in the form `1 ≤ Λ⁰₀` under the
hypothesis `0 < Λ⁰₀`, which assumes what one wants to decide.
-/

theorem one_le_sq_zero_zero {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    1 ≤ (M 0 0) ^ 2 := by
  have hr := row_zero_norm h
  nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 0 2), sq_nonneg (M 0 3)]

theorem zero_zero_ne_zero {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    M 0 0 ≠ 0 := by
  intro hz
  have := one_le_sq_zero_zero h
  rw [hz] at this
  norm_num at this

/-- Every Lorentz matrix is orthochronous or antichronous, with nothing
    in between. -/
theorem exists_sign {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧ 0 < δ * M 0 0 := by
  rcases lt_trichotomy (M 0 0) 0 with hlt | heq | hgt
  · exact ⟨-1, Or.inr rfl, by nlinarith⟩
  · exact absurd heq (zero_zero_ne_zero h)
  · exact ⟨1, Or.inl rfl, by nlinarith⟩

/-! ## 3. The three cases `orthochronous_mul` does not cover -/

theorem orthochronous_mul_neg_neg {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N)
    (hM0 : M 0 0 < 0) (hN0 : N 0 0 < 0) : 0 < (M * N) 0 0 := by
  have h := orthochronous_mul (isLorentzMat_neg hM) (isLorentzMat_neg hN)
    (by simpa using hM0) (by simpa using hN0)
  simpa using h

theorem antichronous_mul_left {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N)
    (hM0 : M 0 0 < 0) (hN0 : 0 < N 0 0) : (M * N) 0 0 < 0 := by
  have h := orthochronous_mul (isLorentzMat_neg hM) hN (by simpa using hM0) hN0
  rw [Matrix.neg_mul] at h
  simpa using h

theorem antichronous_mul_right {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N)
    (hM0 : 0 < M 0 0) (hN0 : N 0 0 < 0) : (M * N) 0 0 < 0 := by
  have h := orthochronous_mul hM (isLorentzMat_neg hN) hM0 (by simpa using hN0)
  rw [Matrix.mul_neg] at h
  simpa using h

/-! ## 4. The packaged form

Stated with arbitrary nonzero real weights rather than `±1`, because an
induction over a group's generators carries whatever scalar the generator
supplies and it is a nuisance to normalise it at every step. The content
is that the sign of `Λ⁰₀` is a homomorphism.
-/

/-- **The sign of `Λ⁰₀` is multiplicative.** -/
theorem sign_mul {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N) {a b : ℝ}
    (ha : 0 < a * M 0 0) (hb : 0 < b * N 0 0) :
    0 < (a * b) * (M * N) 0 0 := by
  rcases lt_trichotomy a 0 with hA | hA | hA
  · rcases lt_trichotomy b 0 with hB | hB | hB
    · -- a < 0, b < 0: both entries negative, product positive
      have hM0 : M 0 0 < 0 := by nlinarith
      have hN0 : N 0 0 < 0 := by nlinarith
      exact mul_pos (mul_pos_of_neg_of_neg hA hB)
        (orthochronous_mul_neg_neg hM hN hM0 hN0)
    · exact absurd hb (by rw [hB]; simp)
    · -- a < 0, b > 0
      have hM0 : M 0 0 < 0 := by nlinarith
      have hN0 : 0 < N 0 0 := by nlinarith
      exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hA hB)
        (antichronous_mul_left hM hN hM0 hN0)
  · exact absurd ha (by rw [hA]; simp)
  · rcases lt_trichotomy b 0 with hB | hB | hB
    · -- a > 0, b < 0
      have hM0 : 0 < M 0 0 := by nlinarith
      have hN0 : N 0 0 < 0 := by nlinarith
      exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hA hB)
        (antichronous_mul_right hM hN hM0 hN0)
    · exact absurd hb (by rw [hB]; simp)
    · -- a > 0, b > 0
      have hM0 : 0 < M 0 0 := by nlinarith
      have hN0 : 0 < N 0 0 := by nlinarith
      exact mul_pos (mul_pos hA hB) (orthochronous_mul hM hN hM0 hN0)

/-- The identity's sign, for the induction's base. -/
theorem sign_one : 0 < (1 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) 0 0 := by
  rw [Matrix.one_apply_eq]
  norm_num

/-! ## 5. Why the four cases are genuinely four

If the sign were always positive the file would be vacuous, and if it
were always the same for a matrix and its negative the reduction would
be circular. The Gram matrix is orthochronous, its negative is not, and
both are Lorentz.
-/

theorem gram_chron : IsLorentzMat gram ∧ 0 < gram 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [IsLorentzMat, gram, Matrix.diagonal_transpose, ← gram, gram_mul_gram,
      Matrix.one_mul]
  · rw [gram, Matrix.diagonal_apply_eq]
    simp [mw]

theorem neg_gram_antichron : IsLorentzMat (-gram) ∧ (-gram) 0 0 < 0 := by
  refine ⟨isLorentzMat_neg gram_chron.1, ?_⟩
  rw [neg_zero_zero]
  simpa using gram_chron.2

/-- …and the product of the two antichronous copies is orthochronous, so
    §3's first case is not vacuous either. -/
theorem neg_gram_sq_chron : 0 < ((-gram) * (-gram)) 0 0 :=
  orthochronous_mul_neg_neg neg_gram_antichron.1 neg_gram_antichron.1
    neg_gram_antichron.2 neg_gram_antichron.2

end LorentzOrthochronousSign
