/-
  LorentzGroup: O(1,3) as a Bundled Group, and Where SL₂(ℂ) Lands In It
  ====================================================================

  Campaign-3 unit 2, steps (i) and (ii) of the staircase that
  `MinkowskiSignature.lean` wrote down for itself.

  That file proved the SL₂(ℂ) conjugation action on Herm₂(ℂ), read in Pauli
  coordinates, is an ℝ-linear self-map of ℝ⁴ preserving the Minkowski form,
  and then said what was still missing: "(i) exhibit the image inside the
  orthogonal group of `minkowskiForm` as a bundled object; (ii) define the
  orthochronous and proper conditions (Λ⁰₀ > 0 and det = 1) — Mathlib has no
  Lorentz group; (iii) surjectivity itself."

  This file does (i) and (ii), and then reduces (iii) to a single classical
  theorem that is not about Lorentz transformations at all: SU(2) ↠ SO(3).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `O13` — **the Lorentz group O(1,3) as a genuine `Subgroup` of GL₄(ℝ)**,
     carrier {Λ : Λᵀ G Λ = G} for G = diag(1,−1,−1,−1). Closed under
     multiplication and inverse, so it is a group and not merely a set.
  2. `lorentzMat_mul`, `lorentzMat_one` — the SL₂(ℂ) action is
     **multiplicative**: Λ(AB) = Λ(A)Λ(B), Λ(1) = 1. This is the fact that
     makes it a homomorphism rather than a family of maps, and it is what
     everything downstream (properness by squares, the group structure of the
     image) rests on.
  3. `lorentzMat_gram` — Λ(A)ᵀ G Λ(A) = G: the image lies in O(1,3), now at
     the level of matrices, which is what a determinant argument needs.
  4. `lorentzUnit`, `lorentzUnit_mem_O13` — the image as elements of the
     bundled subgroup; and `lorentzSOplusHom` / `lorentzHom`, the action
     bundled as a `MonoidHom` from Mathlib's `SpecialLinearGroup (Fin 2) ℂ`
     into SO⁺(1,3) (resp. O(1,3)). Step (i), done. (An adversarial review
     caught an earlier version of this header naming these homs before they
     existed; they exist now, at the end of §8.)
  5. `det_lorentzMat_sq` — det Λ(A)² = 1 for any isometry; then
     **`det_lorentzMat` — det Λ(A) = +1: the image is PROPER.** The proof is
     not the usual connectedness argument: `exists_sqrt_of_trace_ne`
     constructs a square root N of A inside SL₂(ℂ) explicitly, by
     N = (A + 1)/√(tr A + 2) — legitimate exactly when tr A ≠ −2 — and when
     tr A = −2 uses A = (J·J)·(N·N) with J = [[0,−1],[1,0]], N² = −A. So
     every A ∈ SL₂(ℂ) is a product of squares, det Λ is multiplicative, and a
     square of ±1 is +1. This is elementary and needs no topology.
  6. `lorentzMat_zero_zero` — Λ(A)⁰₀ = ½(|a|²+|b|²+|c|²+|d|²), and
     **`one_le_lorentzMat_zero_zero` — Λ(A)⁰₀ ≥ 1 > 0: the image is
     ORTHOCHRONOUS**, from |ad − bc| = 1 and AM–GM. Step (ii), done, and
     with a sharp constant: 1 is attained (`lorentzMat_one`).
  7. `SOplus13` — **the proper orthochronous Lorentz group SO⁺(1,3) as a
     `Subgroup`**. The non-obvious closure is orthochronicity: (ΛΛ′)⁰₀ > 0
     needs a Cauchy–Schwarz argument (`orthochronous_mul`) on the space
     directions, proved here from the Lagrange identity.
  8. `lorentzUnit_mem_SOplus13` — **the image of SL₂(ℂ) lies in SO⁺(1,3)**,
     and `lorentzSOplusHom`, the bundled `MonoidHom` SL₂(ℂ) →* SO⁺(1,3),
     with kernel {±1} by `MinkowskiHerm2.kernel_of_conj_action` (both
     directions assembled in `LorentzSurjectivity.kernel_iff`).

  9. `exists_hermitian_sqrt` — **the boost half of surjectivity**. For a unit
     future timelike (t,x,y,z), P = t·1 + x·σ₁ + y·σ₂ + z·σ₃ has det 1 and
     tr 2t ≥ 2, so S = (P + 1)/√(2t + 2) is a HERMITIAN element of SL₂(ℂ)
     with S² = P — the same square-root formula as §5, now with a real
     positive scalar so that Hermitianness survives.
  10. `exists_boost_factor` — hence every Λ ∈ SO⁺(1,3) factors as Λ = Λ(S)·Λ′
     with S Hermitian in SL₂(ℂ) and Λ′ ∈ SO⁺(1,3) fixing the time axis; and
     `surjective_of_stabiliser_surjective` — **surjectivity onto SO⁺(1,3)
     follows from surjectivity onto the stabiliser of the time axis alone.**
  11. `stabiliser_is_rotation` — that stabiliser is SO(3): a Lorentz matrix
     whose first column is the time axis has first row the time axis too, and
     its lower 3×3 block has orthonormal columns.

  NOT proven here:

  * **Surjectivity — PROVEN DOWNSTREAM.** When this file was written the
    reduction of items 9–11 left SU(2) ↠ SO(3) as the remaining leg;
    `LorentzSurjectivity.lean` has since proven it (algebraically — the
    Euler-fixed-axis route this header once prescribed was not needed) and
    with it full surjectivity: see `LorentzSurjectivity.lorentz_surjective`,
    `SOplus13_surjective`, `double_cover`. Cite that file for the covering.
  * That SO⁺(1,3) is the identity component (a topological statement; the
    definition used here is the algebraic one, det = 1 and Λ⁰₀ > 0, which is
    equivalent but not proven equivalent here).
  * Any identification of SL₂(ℂ) with Mathlib's `spinGroup`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import MinkowskiSignature
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix MinkowskiHerm2 MinkowskiSignature

noncomputable section

namespace LorentzGroup

/-! ## 1. The Minkowski Gram matrix and its bilinear form

    `minkowskiForm` is a `QuadraticForm`; a determinant argument needs the
    matrix identity ΛᵀGΛ = G, so we need the associated bilinear form and
    its Gram matrix explicitly. -/

/-- The Gram matrix G = diag(1, −1, −1, −1) of the Minkowski form. -/
def gram : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal mw

@[simp] theorem gram_mul_gram : gram * gram = 1 := by
  rw [gram, Matrix.diagonal_mul_diagonal]
  rw [show (fun i => mw i * mw i) = fun _ : Fin 4 => (1 : ℝ) by
    funext i; fin_cases i <;> norm_num [mw]]
  exact Matrix.diagonal_one

theorem det_gram : gram.det = -1 := by
  rw [gram, Matrix.det_diagonal, Fin.prod_univ_four, show mw 0 = 1 from rfl,
    show mw 1 = -1 from rfl, show mw 2 = -1 from rfl, show mw 3 = -1 from rfl]
  norm_num

/-- The Minkowski bilinear form, written out. -/
def bil (v w : Fin 4 → ℝ) : ℝ :=
  v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3

theorem bil_self (v : Fin 4 → ℝ) : bil v v = minkowskiForm v := by
  rw [minkowskiForm_apply, bil]; ring

/-- Polarisation: the quadratic form determines the bilinear form. -/
theorem polarization (v w : Fin 4 → ℝ) :
    minkowskiForm (v + w) = minkowskiForm v + minkowskiForm w + 2 * bil v w := by
  simp only [minkowskiForm_apply, bil, Pi.add_apply]; ring

/-! ## 2. The action is multiplicative

    This is the step that turns `lorentzLin` from a family of isometries into
    a group homomorphism. -/

theorem lorentzMap_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) :
    lorentzMap (A * B) v = lorentzMap A (lorentzMap B v) := by
  have hherm : (B * pauliHerm (v 0) (v 1) (v 2) (v 3) * Bᴴ)ᴴ
      = B * pauliHerm (v 0) (v 1) (v 2) (v 3) * Bᴴ :=
    conj_action_hermitian B _ (pauliHerm_isHermitian _ _ _ _)
  have hround := pauliHerm_pauliCoord _ hherm
  change pauliCoord ((A * B) * pauliHerm (v 0) (v 1) (v 2) (v 3) * (A * B)ᴴ)
      = pauliCoord (A * pauliHerm (lorentzMap B v 0) (lorentzMap B v 1)
          (lorentzMap B v 2) (lorentzMap B v 3) * Aᴴ)
  rw [show lorentzMap B v = pauliCoord (B * pauliHerm (v 0) (v 1) (v 2) (v 3) * Bᴴ)
      from rfl, hround]
  exact congrArg pauliCoord (conj_action_mul A B _)

theorem lorentzLin_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzLin (A * B) = (lorentzLin A) ∘ₗ (lorentzLin B) :=
  LinearMap.ext fun v => lorentzMap_mul A B v

theorem lorentzLin_one : lorentzLin (1 : Matrix (Fin 2) (Fin 2) ℂ) = LinearMap.id :=
  LinearMap.ext fun v => lorentzMap_one v

/-! ## 3. The Lorentz matrix -/

/-- **Λ(A)**: the 4×4 real matrix of the action of A ∈ SL₂(ℂ) on ℝ⁴. -/
def lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' (lorentzLin A)

theorem lorentzMat_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) :
    lorentzMat A *ᵥ v = lorentzMap A v :=
  LinearMap.toMatrix'_mulVec (lorentzLin A) v

/-- **Λ is multiplicative.** -/
theorem lorentzMat_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzMat (A * B) = lorentzMat A * lorentzMat B := by
  rw [lorentzMat, lorentzLin_mul, LinearMap.toMatrix'_comp, lorentzMat, lorentzMat]

@[simp] theorem lorentzMat_one : lorentzMat (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [lorentzMat, lorentzLin_one, LinearMap.toMatrix'_id]

theorem lorentzMat_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 4) :
    lorentzMat A i j = lorentzMap A (Pi.single j 1) i := by
  rw [lorentzMat, LinearMap.toMatrix'_apply]; rfl

/-! ## 4. The image lies in the orthogonal group of the form -/

theorem bil_preserved (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (v w : Fin 4 → ℝ) :
    bil (lorentzMap A v) (lorentzMap A w) = bil v w := by
  have hsum : lorentzMap A (v + w) = lorentzMap A v + lorentzMap A w :=
    lorentzMap_add A v w
  have h1 := minkowskiForm_lorentzMap A hA (v + w)
  rw [hsum, polarization, polarization] at h1
  rw [minkowskiForm_lorentzMap A hA v, minkowskiForm_lorentzMap A hA w] at h1
  linarith

theorem bil_single (i j : Fin 4) :
    bil (Pi.single i (1 : ℝ)) (Pi.single j 1) = gram i j := by
  fin_cases i <;> fin_cases j <;>
    simp [bil, gram, mw]

/-- **The image lies in O(1,3)**, as a matrix identity. -/
theorem lorentzMat_gram (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (lorentzMat A)ᵀ * gram * lorentzMat A = gram := by
  ext i j
  have hb := bil_preserved A hA (Pi.single i 1) (Pi.single j 1)
  rw [bil_single] at hb
  have hcol : ∀ (k l : Fin 4),
      lorentzMap A (Pi.single l (1 : ℝ)) k = lorentzMat A k l := fun k l =>
    (lorentzMat_apply A k l).symm
  rw [bil] at hb
  rw [hcol, hcol, hcol, hcol, hcol, hcol, hcol, hcol] at hb
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.transpose_apply, gram, Matrix.diagonal_mul]
  rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
    show mw 3 = -1 from rfl]
  rw [gram] at hb
  linarith [hb]

/-- Any isometry of the Minkowski form has determinant ±1. -/
theorem det_lorentzMat_sq (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (lorentzMat A).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (lorentzMat_gram A hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_gram] at h
  nlinarith [h]


/-! ## 5. Properness: det Λ(A) = +1, by square roots inside SL₂(ℂ)

    The usual proof that the image is proper is topological: det Λ is
    continuous, valued in {±1}, and SL₂(ℂ) is connected. That argument is not
    available here, and it is not needed. Every element of SL₂(ℂ) is a
    product of squares, by an explicit formula, and det Λ of a square is a
    square of ±1. -/

/-- Cayley–Hamilton in 2×2, proved entrywise. -/
theorem cayley_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = (A 0 0 + A 1 1) • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    ring

/-- **An explicit square root inside SL₂(ℂ)**: if tr A ≠ −2 then
    N = (A + 1)/s with s² = tr A + 2 satisfies det N = 1 and N² = A.
    The verification is Cayley–Hamilton: (A + 1)² = (tr A + 2)·A when
    det A = 1. -/
theorem exists_sqrt_of_trace_ne (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (htr : A 0 0 + A 1 1 + 2 ≠ 0) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℂ, N.det = 1 ∧ N * N = A := by
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (A 0 0 + A 1 1 + 2) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h
    apply htr
    rw [← hs, h]
    ring
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hA
  have hkey : (A + 1) * (A + 1) = (A 0 0 + A 1 1 + 2) • A := by
    have hc := cayley_two A
    rw [hA] at hc
    have hexp : (A + 1) * (A + 1) = A * A + A + A + 1 := by noncomm_ring
    rw [hexp, hc, one_smul]
    module
  refine ⟨s⁻¹ • (A + 1), ?_, ?_⟩
  · have hdet1 : (A + 1).det = A 0 0 + A 1 1 + 2 := by
      rw [Matrix.det_fin_two]
      have h00 : (A + 1) 0 0 = A 0 0 + 1 := by
        rw [Matrix.add_apply, Matrix.one_apply_eq]
      have h11 : (A + 1) 1 1 = A 1 1 + 1 := by
        rw [Matrix.add_apply, Matrix.one_apply_eq]
      have h01 : (A + 1) 0 1 = A 0 1 := by
        rw [Matrix.add_apply, Matrix.one_apply_ne (by decide), add_zero]
      have h10 : (A + 1) 1 0 = A 1 0 := by
        rw [Matrix.add_apply, Matrix.one_apply_ne (by decide), add_zero]
      rw [h00, h11, h01, h10]
      linear_combination hd
    rw [Matrix.det_smul, Fintype.card_fin, hdet1, ← hs]
    field_simp
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hkey, smul_smul, ← hs]
    rw [show s⁻¹ * s⁻¹ * (s ^ 2) = 1 by field_simp, one_smul]

/-- J = [[0, −1], [1, 0]]: a square root of −1 inside SL₂(ℂ). It is what
    makes the exceptional trace = −2 case go through. -/
def Jmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

theorem det_Jmat : Jmat.det = 1 := by
  rw [Matrix.det_fin_two]; simp [Jmat]

theorem Jmat_mul_Jmat : Jmat * Jmat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The image is PROPER**: det Λ(A) = +1 for every A ∈ SL₂(ℂ). -/
theorem det_lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (lorentzMat A).det = 1 := by
  by_cases htr : A 0 0 + A 1 1 + 2 = 0
  · have hA' : (-A).det = 1 := by
      rw [Matrix.det_neg, Fintype.card_fin, hA]; norm_num
    have htr' : (-A) 0 0 + (-A) 1 1 + 2 ≠ 0 := by
      simp only [Matrix.neg_apply]
      intro h
      have h4 : (4 : ℂ) = 0 := by linear_combination htr + h
      norm_num at h4
    obtain ⟨N, hNdet, hN⟩ := exists_sqrt_of_trace_ne (-A) hA' htr'
    have hfac : A = (Jmat * Jmat) * (N * N) := by
      rw [Jmat_mul_Jmat, hN]
      ext i j
      simp
    have h1 := det_lorentzMat_sq Jmat det_Jmat
    have h2 := det_lorentzMat_sq N hNdet
    rw [hfac]
    simp only [lorentzMat_mul, Matrix.det_mul]
    nlinarith [h1, h2]
  · obtain ⟨N, hNdet, hN⟩ := exists_sqrt_of_trace_ne A hA htr
    rw [← hN, lorentzMat_mul, Matrix.det_mul, ← sq]
    exact det_lorentzMat_sq N hNdet

/-! ## 6. Orthochronicity: Λ(A)⁰₀ ≥ 1

    The time-time entry of the Lorentz matrix is half the squared
    Frobenius norm of A, and det A = 1 forces that to be at least 2. -/

theorem lorentzMat_zero_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzMat A 0 0 =
      (Complex.normSq (A 0 0) + Complex.normSq (A 0 1) + Complex.normSq (A 1 0)
        + Complex.normSq (A 1 1)) / 2 := by
  have e0 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 0 = 1 := by simp
  have e1 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 1 = 0 := by simp
  have e2 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 2 = 0 := by simp
  have e3 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 3 = 0 := by simp
  have hone : pauliHerm (1 : ℝ) 0 0 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliHerm]
  rw [lorentzMat_apply]
  change pauliCoord (A * pauliHerm ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 0)
      ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 1) ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 2)
      ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 3) * Aᴴ) 0 = _
  rw [e0, e1, e2, e3]
  rw [hone, Matrix.mul_one]
  simp only [pauliCoord, Matrix.cons_val_zero, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply, RCLike.star_def]
  ring

/-- **The image is ORTHOCHRONOUS**, with the sharp constant: Λ(A)⁰₀ ≥ 1, and
    equality holds at A = 1. The proof is |ad − bc| = 1 plus AM–GM. -/
theorem one_le_lorentzMat_zero_zero (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    1 ≤ lorentzMat A 0 0 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hA
  have h1 : ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ = 1 := by rw [hd]; simp
  have h2 : (1 : ℝ) ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ :=
    calc (1 : ℝ) = ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ := h1.symm
      _ ≤ ‖A 0 0 * A 1 1‖ + ‖A 0 1 * A 1 0‖ := norm_sub_le _ _
      _ = ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by rw [norm_mul, norm_mul]
  rw [lorentzMat_zero_zero, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [two_mul_le_add_sq ‖A 0 0‖ ‖A 1 1‖, two_mul_le_add_sq ‖A 0 1‖ ‖A 1 0‖, h2]

/-! ## 7. O(1,3) and SO⁺(1,3) as bundled subgroups of GL₄(ℝ)

    Mathlib has `Matrix.orthogonalGroup` for the standard (definite) form and
    `unitaryGroup`, but no group of isometries of an indefinite form. These
    are built here from the Gram identity. -/

/-- The Lorentz condition on a 4×4 real matrix: it preserves the Minkowski
    Gram matrix. -/
def IsLorentzMat (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Mᵀ * gram * M = gram

theorem IsLorentzMat.mul {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N) : IsLorentzMat (M * N) :=
  calc (M * N)ᵀ * gram * (M * N) = Nᵀ * (Mᵀ * gram * M) * N := by
        rw [Matrix.transpose_mul]; noncomm_ring
    _ = gram := by rw [hM]; exact hN

theorem IsLorentzMat.one : IsLorentzMat (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [IsLorentzMat, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- If M is Lorentz and B is a right inverse of M, then B is Lorentz. -/
theorem IsLorentzMat.of_mul_eq_one {M B : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (h : M * B = 1) : IsLorentzMat B :=
  calc Bᵀ * gram * B = Bᵀ * (Mᵀ * gram * M) * B := by rw [hM]
    _ = (M * B)ᵀ * gram * (M * B) := by rw [Matrix.transpose_mul]; noncomm_ring
    _ = gram := by rw [h, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- **The Lorentz group O(1,3)**: the isometries of the Minkowski form, as a
    genuine subgroup of GL₄(ℝ). -/
def O13 : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℝ) where
  carrier := {M | IsLorentzMat (M : Matrix (Fin 4) (Fin 4) ℝ)}
  mul_mem' := by
    intro M N hM hN
    change IsLorentzMat _
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact hM.mul hN
  one_mem' := by
    change IsLorentzMat _
    rw [Units.val_one]
    exact IsLorentzMat.one
  inv_mem' := by
    intro M hM
    exact IsLorentzMat.of_mul_eq_one hM (Units.mul_inv M)

theorem mem_O13 {M : Matrix.GeneralLinearGroup (Fin 4) ℝ} :
    M ∈ O13 ↔ IsLorentzMat (M : Matrix (Fin 4) (Fin 4) ℝ) := Iff.rfl

/-- The inverse of a Lorentz matrix is G Mᵀ G — the familiar index-lowering
    formula, here as a theorem. -/
theorem inv_eq_gram_conj {M B : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzMat M)
    (h : M * B = 1) : B = gram * Mᵀ * gram := by
  have hleft : (gram * Mᵀ * gram) * M = 1 :=
    calc (gram * Mᵀ * gram) * M = gram * (Mᵀ * gram * M) := by noncomm_ring
      _ = gram * gram := by rw [hM]
      _ = 1 := gram_mul_gram
  calc B = ((gram * Mᵀ * gram) * M) * B := by rw [hleft, Matrix.one_mul]
    _ = (gram * Mᵀ * gram) * (M * B) := by noncomm_ring
    _ = gram * Mᵀ * gram := by rw [h, Matrix.mul_one]

/-- The column form of the Gram identity implies the row form. -/
theorem gram_row {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    M * gram * Mᵀ = gram := by
  have hleft : (gram * Mᵀ * gram) * M = 1 :=
    calc (gram * Mᵀ * gram) * M = gram * (Mᵀ * gram * M) := by noncomm_ring
      _ = gram * gram := by rw [h]
      _ = 1 := gram_mul_gram
  have hright : M * (gram * Mᵀ * gram) = 1 := mul_eq_one_comm.mp hleft
  calc M * gram * Mᵀ = M * gram * Mᵀ * (gram * gram) := by
        rw [gram_mul_gram, Matrix.mul_one]
    _ = (M * (gram * Mᵀ * gram)) * gram := by noncomm_ring
    _ = gram := by rw [hright, Matrix.one_mul]

/-- The first row of a Lorentz matrix is a unit timelike vector. -/
theorem row_zero_norm {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    M 0 0 ^ 2 - M 0 1 ^ 2 - M 0 2 ^ 2 - M 0 3 ^ 2 = 1 := by
  have hr := congrFun (congrFun (gram_row h) 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_four] at hr
  simp only [gram, Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.diagonal_apply_eq] at hr
  rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
    show mw 3 = -1 from rfl] at hr
  nlinarith [hr]

/-- The first column of a Lorentz matrix is a unit timelike vector. -/
theorem col_zero_norm {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    M 0 0 ^ 2 - M 1 0 ^ 2 - M 2 0 ^ 2 - M 3 0 ^ 2 = 1 := by
  have hr := congrFun (congrFun h 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_four] at hr
  simp only [gram, Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.diagonal_apply_eq] at hr
  rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
    show mw 3 = -1 from rfl] at hr
  nlinarith [hr]

/-- **Orthochronicity is closed under multiplication.** This is the one
    non-formal step in making SO⁺(1,3) a group: it is a Cauchy–Schwarz
    argument on the space directions, and it is why the orthochronous
    transformations form a subgroup while, say, {Λ⁰₀ ≥ 2} does not. -/
theorem orthochronous_mul {M N : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) (hN : IsLorentzMat N)
    (hM0 : 0 < M 0 0) (hN0 : 0 < N 0 0) : 0 < (M * N) 0 0 := by
  have hx := row_zero_norm hM
  have hy := col_zero_norm hN
  have ha1 : 1 ≤ M 0 0 := by
    nlinarith [sq_nonneg (M 0 1), sq_nonneg (M 0 2), sq_nonneg (M 0 3)]
  have hb1 : 1 ≤ N 0 0 := by
    nlinarith [sq_nonneg (N 1 0), sq_nonneg (N 2 0), sq_nonneg (N 3 0)]
  have hcs : (M 0 1 * N 1 0 + M 0 2 * N 2 0 + M 0 3 * N 3 0) ^ 2
      ≤ (M 0 0 ^ 2 - 1) * (N 0 0 ^ 2 - 1) := by
    nlinarith [sq_nonneg (M 0 1 * N 2 0 - M 0 2 * N 1 0),
      sq_nonneg (M 0 1 * N 3 0 - M 0 3 * N 1 0),
      sq_nonneg (M 0 2 * N 3 0 - M 0 3 * N 2 0), hx, hy]
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  by_contra hcon
  rw [not_lt] at hcon
  have hprod : 0 < M 0 0 * N 0 0 := mul_pos hM0 hN0
  have hgap : 1 ≤ (M 0 0 * N 0 0) ^ 2
      - (M 0 1 * N 1 0 + M 0 2 * N 2 0 + M 0 3 * N 3 0) ^ 2 := by
    nlinarith [hcs, ha1, hb1]
  nlinarith [hgap, hcon, hprod]

/-- **The proper orthochronous Lorentz group SO⁺(1,3)**, as a subgroup of
    GL₄(ℝ): isometries of the Minkowski form with det = 1 that preserve the
    direction of time. -/
def SOplus13 : Subgroup (Matrix.GeneralLinearGroup (Fin 4) ℝ) where
  carrier := {M | IsLorentzMat (M : Matrix (Fin 4) (Fin 4) ℝ)
      ∧ (M : Matrix (Fin 4) (Fin 4) ℝ).det = 1 ∧ 0 < (M : Matrix (Fin 4) (Fin 4) ℝ) 0 0}
  mul_mem' := by
    rintro M N ⟨hM, hMd, hM0⟩ ⟨hN, hNd, hN0⟩
    refine ⟨?_, ?_, ?_⟩
    · change IsLorentzMat _
      rw [Matrix.GeneralLinearGroup.coe_mul]; exact hM.mul hN
    · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hMd, hNd, mul_one]
    · rw [Matrix.GeneralLinearGroup.coe_mul]
      exact orthochronous_mul hM hN hM0 hN0
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · change IsLorentzMat _
      rw [Units.val_one]; exact IsLorentzMat.one
    · rw [Units.val_one, Matrix.det_one]
    · rw [Units.val_one, Matrix.one_apply_eq]; norm_num
  inv_mem' := by
    rintro M ⟨hM, hMd, hM0⟩
    have hinv : ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
        = gram * (M : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * gram :=
      inv_eq_gram_conj hM (Units.mul_inv M)
    refine ⟨IsLorentzMat.of_mul_eq_one hM (Units.mul_inv M), ?_, ?_⟩
    · rw [hinv, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_gram, hMd]
      norm_num
    · rw [hinv, Matrix.mul_assoc]
      simp only [gram, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
      rw [show mw 0 = 1 from rfl]
      simpa using hM0

/-! ## 8. The homomorphism SL₂(ℂ) → SO⁺(1,3) -/

/-- Λ(A) as an element of GL₄(ℝ). -/
def lorentzUnit (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    Matrix.GeneralLinearGroup (Fin 4) ℝ where
  val := lorentzMat A
  inv := lorentzMat A⁻¹
  val_inv := by
    rw [← lorentzMat_mul, Matrix.mul_nonsing_inv A (by rw [hA]; exact isUnit_one),
      lorentzMat_one]
  inv_val := by
    rw [← lorentzMat_mul, Matrix.nonsing_inv_mul A (by rw [hA]; exact isUnit_one),
      lorentzMat_one]

@[simp] theorem lorentzUnit_val (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (lorentzUnit A hA : Matrix (Fin 4) (Fin 4) ℝ) = lorentzMat A := rfl

/-- **Step (i): the image is inside the orthogonal group of the form**, as a
    bundled subgroup element. -/
theorem lorentzUnit_mem_O13 (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    lorentzUnit A hA ∈ O13 := lorentzMat_gram A hA

/-- **Step (ii): the image is inside SO⁺(1,3)** — proper and orthochronous. -/
theorem lorentzUnit_mem_SOplus13 (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    lorentzUnit A hA ∈ SOplus13 :=
  ⟨lorentzMat_gram A hA, det_lorentzMat A hA,
    lt_of_lt_of_le zero_lt_one (one_le_lorentzMat_zero_zero A hA)⟩


/-- SO⁺(1,3) is a subgroup of O(1,3). -/
theorem SOplus_le_O13 : SOplus13 ≤ O13 := fun _ hM => hM.1

/-- The special linear group SL₂(ℂ), as Mathlib's bundled group. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- **The bundled homomorphism SL₂(ℂ) →* SO⁺(1,3)** — the object the
    header promised and an adversarial review found missing: the whole
    action packaged as a `MonoidHom` into the subgroup, with
    multiplicativity carried by `lorentzMat_mul`. -/
def lorentzSOplusHom : SL2C →* SOplus13 where
  toFun A := ⟨lorentzUnit A.1 A.2, lorentzUnit_mem_SOplus13 A.1 A.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show lorentzMat ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [Subgroup.coe_one, Units.val_one, Matrix.SpecialLinearGroup.coe_one]
    exact lorentzMat_one
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    show lorentzMat ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact lorentzMat_mul A.1 B.1

@[simp] theorem lorentzSOplusHom_apply (A : SL2C) :
    ((lorentzSOplusHom A : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ) = lorentzMat A.1 := rfl

/-- The same map, valued in O(1,3): the composition with the inclusion
    SO⁺(1,3) ≤ O(1,3). -/
def lorentzHom : SL2C →* O13 :=
  (Subgroup.inclusion SOplus_le_O13).comp lorentzSOplusHom

/-- **The whole content of this file in one statement**: the SL₂(ℂ) action on
    Minkowski space is a multiplicative map into the proper orthochronous
    Lorentz group, with trivial-kernel-up-to-sign
    (`MinkowskiHerm2.kernel_of_conj_action`; the two directions of "exactly
    {±1}" are assembled in `LorentzSurjectivity.kernel_iff`). Surjectivity is
    NOT in this file — it is proven downstream, in
    `LorentzSurjectivity.lorentz_surjective`. -/
theorem lorentz_action_summary :
    (∀ A B : Matrix (Fin 2) (Fin 2) ℂ, lorentzMat (A * B) = lorentzMat A * lorentzMat B)
      ∧ lorentzMat (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
      ∧ (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1), lorentzUnit A hA ∈ SOplus13)
      ∧ (∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 →
          (∀ H : Matrix (Fin 2) (Fin 2) ℂ, Hᴴ = H → A * H * Aᴴ = H) → A = 1 ∨ A = -1) :=
  ⟨lorentzMat_mul, lorentzMat_one, lorentzUnit_mem_SOplus13,
    fun A hA hfix => kernel_of_conj_action A hA hfix⟩

/-! ## 9. The boost half of surjectivity

    Surjectivity onto SO⁺(1,3) is still open, but it is no longer opaque.
    This section removes the boost half of it completely, and leaves exactly
    one classical theorem standing: SU(2) ↠ SO(3).

    The mechanism is the square-root formula of §5 again. If Λ ∈ SO⁺(1,3)
    then its first column (t,x,y,z) is a unit future timelike vector, so
    P = t·1 + x·σ₁ + y·σ₂ + z·σ₃ is Hermitian with det P = 1 and tr P = 2t ≥ 2,
    and S = (P + 1)/√(2t + 2) is a HERMITIAN element of SL₂(ℂ) with S² = P.
    Then Λ(S) has the same first column as Λ, so Λ(S)⁻¹Λ fixes the time axis
    — and what is left to hit is the stabiliser of the time axis. -/

theorem mulVec_single_one (M : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (M *ᵥ Pi.single j (1 : ℝ)) i = M i j := by
  simp [Matrix.mulVec_single]

/-- The Pauli parametrisation read backwards on the parametrised matrices. -/
theorem pauliCoord_pauliHerm (t x y z : ℝ) :
    pauliCoord (pauliHerm t x y z) = ![t, x, y, z] := by
  funext i
  fin_cases i <;> simp [pauliCoord, pauliHerm] <;> ring

theorem gram_conj_mul {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    (gram * Mᵀ * gram) * M = 1 :=
  calc (gram * Mᵀ * gram) * M = gram * (Mᵀ * gram * M) := by noncomm_ring
    _ = gram * gram := by rw [h]
    _ = 1 := gram_mul_gram

theorem mul_gram_conj {M : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentzMat M) :
    M * (gram * Mᵀ * gram) = 1 := mul_eq_one_comm.mp (gram_conj_mul h)

/-- **The Hermitian square root of a unit future timelike vector**, written
    down explicitly. This is the boost that carries the time axis to
    (t,x,y,z). -/
theorem exists_hermitian_sqrt (t x y z : ℝ)
    (hq : t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 = 1) (ht : 0 < t) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℂ, S.det = 1 ∧ Sᴴ = S ∧
      S * Sᴴ = pauliHerm t x y z := by
  have ht1 : 1 ≤ t := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hpos : (0 : ℝ) < 2 * t + 2 := by linarith
  set c : ℝ := (Real.sqrt (2 * t + 2))⁻¹ with hc
  have hcc : c * c = (2 * t + 2)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hpos.le]
  have hreal : c * c * (2 * t + 2) = 1 := by
    rw [hcc]; field_simp
  set P : Matrix (Fin 2) (Fin 2) ℂ := pauliHerm t x y z with hP
  have hPdet : P.det = 1 := by rw [hP, det_pauliHerm, hq]; norm_num
  have hPtr : P 0 0 + P 1 1 = 2 * (t : ℂ) := by
    have e00 : P 0 0 = (t : ℂ) + (z : ℂ) := rfl
    have e11 : P 1 1 = (t : ℂ) - (z : ℂ) := rfl
    rw [e00, e11]; ring
  have hc2 : (c : ℂ) * (c : ℂ) * (2 * (t : ℂ) + 2) = 1 := by
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at hcast
    linear_combination hcast
  have hPherm : Pᴴ = P := pauliHerm_isHermitian t x y z
  have hkey : (P + 1) * (P + 1) = (2 * (t : ℂ) + 2) • P := by
    have hcay := cayley_two P
    rw [hPdet, hPtr] at hcay
    have hexp : (P + 1) * (P + 1) = P * P + P + P + 1 := by noncomm_ring
    rw [hexp, hcay, one_smul]
    module
  refine ⟨(c : ℂ) • (P + 1), ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]
    have hdet1 : (P + 1).det = 2 * (t : ℂ) + 2 := by
      rw [Matrix.det_fin_two, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
        Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_eq,
        Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, add_zero]
      have hd2 : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 1 := by
        rw [← Matrix.det_fin_two]; exact hPdet
      linear_combination hd2 + hPtr
    rw [hdet1, sq]
    exact hc2
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, hPherm]
    congr 1
    simp
  · have hherm : ((c : ℂ) • (P + 1))ᴴ = (c : ℂ) • (P + 1) := by
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_one, hPherm]
      congr 1
      simp
    rw [hherm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hkey, smul_smul, hc2,
      one_smul]

/-- **The first column of Λ(A) is the Pauli image of A·Aᴴ.** -/
theorem lorentzMat_col_zero (A : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) :
    lorentzMat A i 0 = pauliCoord (A * Aᴴ) i := by
  have e0 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 0 = 1 := by simp
  have e1 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 1 = 0 := by simp
  have e2 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 2 = 0 := by simp
  have e3 : (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 3 = 0 := by simp
  have hone : pauliHerm (1 : ℝ) 0 0 0 = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [pauliHerm]
  rw [lorentzMat_apply]
  change pauliCoord (A * pauliHerm ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 0)
      ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 1) ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 2)
      ((Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) 3) * Aᴴ) i = _
  rw [e0, e1, e2, e3, hone, Matrix.mul_one]

/-- **Every Λ ∈ SO⁺(1,3) factors as a boost times a rotation**: Λ = Λ(S)·Λ′
    with S ∈ SL₂(ℂ) Hermitian and Λ′ ∈ SO⁺(1,3) fixing the time axis. The
    boost half of surjectivity, in full. -/
theorem exists_boost_factor {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsLorentzMat L)
    (hdet : L.det = 1) (h0 : 0 < L 0 0) :
    ∃ (S : Matrix (Fin 2) (Fin 2) ℂ) (R : Matrix (Fin 4) (Fin 4) ℝ),
      S.det = 1 ∧ Sᴴ = S ∧ IsLorentzMat R ∧ R.det = 1 ∧
      (∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) ∧ L = lorentzMat S * R := by
  obtain ⟨S, hSdet, hSherm, hSS⟩ :=
    exists_hermitian_sqrt (L 0 0) (L 1 0) (L 2 0) (L 3 0) (col_zero_norm hL) h0
  -- Λ(S) and L agree on the time axis
  have hcol : ∀ i, lorentzMat S i 0 = L i 0 := by
    intro i
    rw [lorentzMat_col_zero, hSS, pauliCoord_pauliHerm]
    fin_cases i <;> rfl
  have hSL : IsLorentzMat (lorentzMat S) := lorentzMat_gram S hSdet
  have hSdet4 : (lorentzMat S).det = 1 := det_lorentzMat S hSdet
  set B : Matrix (Fin 4) (Fin 4) ℝ := gram * (lorentzMat S)ᵀ * gram with hB
  have hBL : B * lorentzMat S = 1 := gram_conj_mul hSL
  have hLB : lorentzMat S * B = 1 := mul_gram_conj hSL
  have hBLor : IsLorentzMat B := IsLorentzMat.of_mul_eq_one hSL hLB
  have hBdet : B.det = 1 := by
    have := congrArg Matrix.det hBL
    rw [Matrix.det_mul, hSdet4, mul_one, Matrix.det_one] at this
    exact this
  refine ⟨S, B * L, hSdet, hSherm, hBLor.mul hL, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hBdet, hdet, mul_one]
  · intro i
    have hvec : L *ᵥ (Pi.single (0 : Fin 4) (1 : ℝ)) = lorentzMat S *ᵥ Pi.single 0 1 := by
      funext k
      rw [mulVec_single_one, mulVec_single_one, hcol k]
    calc (B * L) i 0 = ((B * L) *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) i :=
          (mulVec_single_one _ i 0).symm
      _ = (B *ᵥ (L *ᵥ Pi.single (0 : Fin 4) (1 : ℝ))) i := by rw [Matrix.mulVec_mulVec]
      _ = ((B * lorentzMat S) *ᵥ Pi.single (0 : Fin 4) (1 : ℝ)) i := by
          rw [hvec, Matrix.mulVec_mulVec]
      _ = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i := by rw [hBL, Matrix.one_mulVec]
  · rw [← Matrix.mul_assoc, hLB, Matrix.one_mul]

/-- **The reduction**: surjectivity of SL₂(ℂ) → SO⁺(1,3) follows from
    surjectivity onto the stabiliser of the time axis alone — which, by
    `stabiliser_is_rotation` below, is SO(3). The boost direction is closed;
    what is left is exactly the classical SU(2) ↠ SO(3). -/
theorem surjective_of_stabiliser_surjective
    (hrot : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat R → R.det = 1 →
      (∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) →
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ lorentzMat A = R) :
    ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat L → L.det = 1 → 0 < L 0 0 →
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ lorentzMat A = L := by
  intro L hL hdet h0
  obtain ⟨S, R, hSdet, _, hRlor, hRdet, hRcol, hfac⟩ := exists_boost_factor hL hdet h0
  obtain ⟨A, hAdet, hA⟩ := hrot R hRlor hRdet hRcol
  exact ⟨S * A, by rw [Matrix.det_mul, hSdet, hAdet, mul_one],
    by rw [lorentzMat_mul, hA, hfac]⟩

/-- **The stabiliser of the time axis is SO(3)**: a Lorentz matrix whose
    first column is the time axis also has first row the time axis, and its
    lower 3×3 block has orthonormal columns. Together with det = 1 that is
    exactly a rotation — so the residual problem really is SU(2) ↠ SO(3) and
    nothing larger. -/
theorem stabiliser_is_rotation {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : IsLorentzMat R)
    (hcol : ∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) :
    (∀ j, R 0 j = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) j) ∧
      (∀ a b : Fin 4, a ≠ 0 → b ≠ 0 →
        R 1 a * R 1 b + R 2 a * R 2 b + R 3 a * R 3 b = if a = b then 1 else 0) := by
  have hentry : ∀ a b : Fin 4,
      R 0 a * R 0 b - R 1 a * R 1 b - R 2 a * R 2 b - R 3 a * R 3 b = gram a b := by
    intro a b
    have hij := congrFun (congrFun hR a) b
    rw [Matrix.mul_apply, Fin.sum_univ_four] at hij
    simp only [gram, Matrix.mul_diagonal, Matrix.transpose_apply] at hij
    rw [show mw 0 = 1 from rfl, show mw 1 = -1 from rfl, show mw 2 = -1 from rfl,
      show mw 3 = -1 from rfl] at hij
    rw [gram]
    linarith [hij]
  have h00 : R 0 0 = 1 := by rw [hcol 0]; simp
  have hrow := row_zero_norm hR
  rw [h00] at hrow
  have hs1 : R 0 1 ^ 2 = 0 := by
    linarith [sq_nonneg (R 0 1), sq_nonneg (R 0 2), sq_nonneg (R 0 3)]
  have hs2 : R 0 2 ^ 2 = 0 := by
    linarith [sq_nonneg (R 0 1), sq_nonneg (R 0 2), sq_nonneg (R 0 3)]
  have hs3 : R 0 3 ^ 2 = 0 := by
    linarith [sq_nonneg (R 0 1), sq_nonneg (R 0 2), sq_nonneg (R 0 3)]
  have hz1 : R 0 1 = 0 := by exact pow_eq_zero_iff two_ne_zero |>.mp hs1
  have hz2 : R 0 2 = 0 := by exact pow_eq_zero_iff two_ne_zero |>.mp hs2
  have hz3 : R 0 3 = 0 := by exact pow_eq_zero_iff two_ne_zero |>.mp hs3
  have hrow0 : ∀ a : Fin 4, a ≠ 0 → R 0 a = 0 := by
    intro a ha
    fin_cases a
    · exact absurd rfl ha
    · simpa using hz1
    · simpa using hz2
    · simpa using hz3
  refine ⟨fun j => by fin_cases j <;> simp [h00, hz1, hz2, hz3], ?_⟩
  intro a b ha hb
  have h := hentry a b
  rw [hrow0 a ha, zero_mul] at h
  have hg : gram a b = if a = b then (-1 : ℝ) else 0 := by
    rw [gram, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      fin_cases a
      · exact absurd rfl ha
      · rfl
      · rfl
      · rfl
    · simp [hab]
  rw [hg] at h
  by_cases hab : a = b
  · rw [if_pos hab] at h ⊢; linarith
  · rw [if_neg hab] at h ⊢; linarith

/-! ## 10. Where the chain ends

    Putting §9 together: SL₂(ℂ) → SO⁺(1,3) is surjective as soon as every
    rotation is hit, and `stabiliser_is_rotation` says the residual target is
    exactly SO(3). When this section was written that leg was open;
    `LorentzSurjectivity.lean` has since climbed it — algebraically, with
    half-angle pairs and no Euler fixed-axis theorem — and the covering is
    now a theorem: `LorentzSurjectivity.lorentz_surjective` and
    `double_cover`. This section stays as the honest record of the
    reduction. -/

end LorentzGroup
