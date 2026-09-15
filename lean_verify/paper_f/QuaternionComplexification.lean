/-
  QuaternionComplexification: `M₂(ℂ)` IS the complexification of the quaternions, stated without
  a tensor product — and the blocker I recorded one unit ago against this very route was wrong

  SPINE LINK L14, Caesar item 6. **This file exists because the unit before it got a blocker
  wrong, and the correction is the first thing to say.**

  THE STORY, IN ORDER, BECAUSE THE ORDER IS THE POINT.
  * The campaign's task list carried `ℂ ⊗[ℝ] M₂(ℍ) ≃ₐ M₄(ℂ)` for many units as *"deferred —
    Mathlib has no quaternion complexification"*. `ERRATUM 582` refuted that: the route is three
    library names, and worse, **`ERRATUM 410` had already recorded the same discovery weeks
    earlier** and the deferral stood against it.
  * That probe then measured a REAL blocker — an instance diamond on `ℂ` itself, where
    `Module ℝ ℂ` resolves through the inner-product hierarchy while `Algebra ℝ ℂ` resolves
    through `RCLike`, so `Semiring (ℂ ⊗[ℝ] ℂ)` does not synthesise although the library's
    instance typechecks as a term for that exact type. **That measurement stands.**
  * It also recorded a SECOND claim, and that one is false: that stating the content *without* a
    tensor product hits the same diamond in the `ℝ`-scalar arithmetic. **It does not.**
    `module` and `match_scalars` need `Algebra ℝ ℂ` and report *"ℂ is not an ℝ-algebra"*; going
    to matrix ENTRIES needs nothing of the kind, and `ext i j; simp [Complex.real_smul]` closes
    every one of those goals. **That was a tactic-selection problem reported as a structural
    one** (`ERRATUM 583`), and the difference is a whole theorem.

  WHAT IS PROVED, and it is the content of `ℂ ⊗[ℝ] ℍ ≃ₐ[ℂ] M₂(ℂ)` in vocabulary this estate can
  hold.
  * **`qBasis`** — `i ↦ i·σ₁`, `j ↦ i·σ₃` is a `QuaternionAlgebra.Basis` in `M₂(ℂ)`: both square
    to `-1` because `σ₁² = σ₃² = 1` and `i² = -1`, and they anticommute because the Paulis do.
    The three inputs are this estate's own `pauli1_sq`, `pauli3_sq` and `pauli1_anticomm`.
  * **`qToM`** — hence an `ℝ`-algebra map `ℍ → M₂(ℂ)`, with nothing chosen by hand: it is
    `QuaternionAlgebra.Basis.liftHom` applied to the basis.
  * **`qToM_one`, `qToM_i`, `qToM_j`, `qToM_k`** — the four images computed.
  * **`images_span`** — **every complex `2 × 2` matrix is a `ℂ`-linear combination of the
    four**, by an
    explicit formula rather than a dimension argument: `a = (M₀₀+M₁₁)/2`,
    `b = -i(M₀₁+M₁₀)/2`, `c = -i(M₀₀-M₁₁)/2`, `d = (M₀₁-M₁₀)/2`. **Constructive**, so this is
    not an existence claim in disguise.
  * **`images_linearIndependent`** — and the four are `ℂ`-linearly independent, so the
    combination is unique.
  * Faithfulness of `ℍ → M₂(ℂ)` follows from `images_linearIndependent` read at real
    coefficients, and is not separately stated.
  **`images_span` and `images_linearIndependent` together are the statement that `M₂(ℂ)` is
  `ℍ` complexified**: a
  `ℂ`-basis of `M₂(ℂ)` consisting of the images of `1, i, j, k`.

  WHAT IS **NOT** CLAIMED.
  * **No tensor product appears, and `ℂ ⊗[ℝ] ℍ ≃ₐ[ℂ] M₂(ℂ)` is NOT stated.** The diamond
    `ERRATUM 582` measured is real and unfixed; what this file does is state the same
    mathematics without needing it. Whether the two are interchangeable in Lean is exactly what
    the diamond obstructs, and saying they are would be the overclaim this unit exists to avoid.
  * **The four images are not packaged as a `Basis` object.** `images_span` and
    `images_linearIndependent` are
    halves; assembling `Basis (Fin 4) ℂ (M₂(ℂ))` from them is not done, so nothing here says
    `finrank ℂ (M₂(ℂ)) = 4` by this route (Mathlib says it directly anyway).
  * **This is `ℍ`, not `M₂(ℍ)`.** L14's Caesar item asks for `ℂ ⊗[ℝ] M₂(ℍ) ≃ₐ M₄(ℂ)`; this is
    the single-quaternion case, which is what the deferral was blocked on. Moving through a
    matrix algebra and folding `M₂(M₂(ℂ))` into `M₄(ℂ)` are not written.
  * **No star structure.** Nothing says `qToM` carries quaternionic conjugation to the conjugate
    transpose, which is what a real-form statement needs.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35); exhibiting a complexification does not choose a
    real form, which is the whole point of L14 being about real forms.

  0 sorry. 0 new axioms. 11 declarations, all on
  `[propext, Classical.choice, Quot.sound]`.
-/

import SpectralTripleBimodule
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis

namespace QuaternionComplexification

open Matrix SpectralTripleBimodule
open scoped Quaternion

noncomputable section

/-! ## 1. A quaternion basis inside `M₂(ℂ)` -/

/-- **`i ↦ i·σ₁`, `j ↦ i·σ₃`.** Both square to `-1` because the Paulis are involutions and
`i² = -1`; they anticommute because `σ₁σ₃ = -σ₃σ₁`. Those are this estate's `pauli1_sq`,
`pauli3_sq` and `pauli1_anticomm`. **Every field goal is closed at matrix ENTRIES**, which is
the step `ERRATUM 583` is about: `module` cannot do it and `ext i j; simp` can. -/
def qBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (-1 : ℝ) 0 (-1) where
  i := Complex.I • pauli1
  j := Complex.I • pauli3
  k := (Complex.I • pauli1) * (Complex.I • pauli3)
  i_mul_i := by
    rw [smul_mul_smul_comm, pauli1_sq, Complex.I_mul_I]
    ext p q; simp [Complex.real_smul]
  j_mul_j := by
    rw [smul_mul_smul_comm, pauli3_sq, Complex.I_mul_I]
    ext p q; simp [Complex.real_smul]
  i_mul_j := rfl
  j_mul_i := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, pauli1_anticomm]
    ext p q; simp [Complex.real_smul]

/-- The `ℝ`-algebra map `ℍ → M₂(ℂ)` the basis determines. -/
def qToM : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := QuaternionAlgebra.Basis.liftHom qBasis

/-! ## 2. The four images -/

@[simp] theorem qBasis_i : qBasis.i = Complex.I • pauli1 := rfl
@[simp] theorem qBasis_j : qBasis.j = Complex.I • pauli3 := rfl
@[simp] theorem qBasis_k :
    qBasis.k = (Complex.I • pauli1) * (Complex.I • pauli3) := rfl

theorem qToM_one : qToM 1 = 1 := map_one _

theorem qToM_i : qToM ⟨0, 1, 0, 0⟩ = Complex.I • pauli1 := by
  change qBasis.lift ⟨0, 1, 0, 0⟩ = _
  rw [QuaternionAlgebra.Basis.lift]
  ext p q; simp [Complex.real_smul]

theorem qToM_j : qToM ⟨0, 0, 1, 0⟩ = Complex.I • pauli3 := by
  change qBasis.lift ⟨0, 0, 1, 0⟩ = _
  rw [QuaternionAlgebra.Basis.lift]
  ext p q; simp [Complex.real_smul]

theorem qToM_k :
    qToM ⟨0, 0, 0, 1⟩ = (Complex.I • pauli1) * (Complex.I • pauli3) := by
  change qBasis.lift ⟨0, 0, 0, 1⟩ = _
  rw [QuaternionAlgebra.Basis.lift]
  ext p q; simp [Complex.real_smul]

/-! ## 3. They span `M₂(ℂ)` over `ℂ`, constructively -/

/-- **Every complex `2 × 2` matrix is a `ℂ`-combination of the four images**, with the
coefficients written down rather than shown to exist. -/
theorem images_span (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ a b c d : ℂ, M = a • qToM 1 + b • qToM ⟨0, 1, 0, 0⟩ + c • qToM ⟨0, 0, 1, 0⟩
      + d • qToM ⟨0, 0, 0, 1⟩ := by
  refine ⟨(M 0 0 + M 1 1) / 2, -Complex.I * (M 0 1 + M 1 0) / 2,
    -Complex.I * (M 0 0 - M 1 1) / 2, (M 0 1 - M 1 0) / 2, ?_⟩
  rw [qToM_one, qToM_i, qToM_j, qToM_k]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [pauli1, pauli3] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-! ## 4. And the combination is unique -/

/-- **The four images are `ℂ`-linearly independent.** With `images_span` this says they are a
`ℂ`-basis of `M₂(ℂ)`, which is the statement that `M₂(ℂ)` is `ℍ` complexified. -/
theorem images_linearIndependent (a b c d : ℂ)
    (h : a • qToM 1 + b • qToM ⟨0, 1, 0, 0⟩ + c • qToM ⟨0, 0, 1, 0⟩
      + d • qToM ⟨0, 0, 0, 1⟩ = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  rw [qToM_one, qToM_i, qToM_j, qToM_k] at h
  have h00 := congrArg (fun N => N (0 : Fin 2) (0 : Fin 2)) h
  have h01 := congrArg (fun N => N (0 : Fin 2) (1 : Fin 2)) h
  have h10 := congrArg (fun N => N (1 : Fin 2) (0 : Fin 2)) h
  have h11 := congrArg (fun N => N (1 : Fin 2) (1 : Fin 2)) h
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.zero_apply, pauli1, pauli3, Fin.sum_univ_succ, Fin.isValue,
    smul_eq_mul] at h00 h01 h10 h11
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01 h10 h11
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (h00 + h11) / 2
  · linear_combination (-Complex.I * (h01 + h10)) / 2 + b * hI
  · linear_combination (-Complex.I * (h00 - h11)) / 2 + c * hI
  · linear_combination (h01 - h10) / 2

end

end QuaternionComplexification
