/-
  KOSixRealStructure: A Real Structure with the KO-dimension-6 Signs
  =================================================================

  Campaign-3 unit 5. The Phase-0 audit found a contradiction inside the
  estate: `ConnesNCG.lean` assigned KO-dimension 0 (signs +1,+1,+1) to the
  cascade triple while `ConnesClassification.lean` required KO-dimension 6
  (1,1,−1) for the same object. That was resolved by withdrawing the toy
  assignment and recording the Standard-Model signs — but the signs were
  ASSERTED from the literature, and the withdrawal note recorded the real
  task as open: **no J had ever been constructed**.

  This file constructs one.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  On the doubled space H = V ⊕ V with V = ℂⁿ — particles and antiparticles,
  the standard shape of a finite real spectral triple — with

    J(x, y) = (conj y, conj x)          the antilinear swap,
    γ(x, y) = (x, −y)                   the grading,
    D(x, y) = (M ⬝ y, Mᴴ ⬝ x)           for a SYMMETRIC matrix M,

  all three KO-dimension signs are theorems about actual operators:

  1. `J_antilinear`, `J_add` — J is genuinely antilinear, not linear.
  2. `J_involutive` — **J² = +1** (ε = +1).
  3. `J_comm_D` — **JD = +DJ** (ε′ = +1), which is where the symmetry of M
     is used and is the only place any hypothesis on M is needed.
  4. `J_anticomm_gamma` — **Jγ = −γJ** (ε″ = −1).
  5. `D_anticomm_gamma` — {D, γ} = 0, so the triple is genuinely EVEN and D
     is odd for the grading: without this the sign table would be about a
     degenerate object.
  6. `gamma_involutive`, and `exists_nonzero_D` — non-vacuity: γ² = 1, and
     there is a symmetric M making D ≠ 0, so nothing above is satisfied
     trivially.

  The sign triple (ε, ε′, ε″) = (1, 1, −1) is exactly KO-dimension 6, the
  value `ConnesClassification` requires and the value `ConnesNCG` now records
  after its withdrawal.

  NOT proven here, and none of it is small:

  * **That this is THE cascade's real structure.** V = ℂⁿ here is any finite
    space; nothing identifies it with the cascade's 96 fermion degrees of
    freedom, and nothing derives M from the cascade. What is shown is that
    the KO-6 sign table is REALISABLE by an explicit finite construction —
    which is more than the estate had, and less than the claim it makes.
  * The order-one condition, the first-order condition on the algebra
    representation, and the algebra action itself: this file has J, γ and D
    but no algebra, so it is not yet a spectral triple.
  * Any statement about the Standard Model's specific finite geometry.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

open Matrix ComplexConjugate

noncomputable section

namespace KOSixRealStructure

variable {n : ℕ}

/-- The doubled space: particles ⊕ antiparticles. -/
abbrev H (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

/-- Entrywise conjugation of a vector. -/
def cvec (v : Fin n → ℂ) : Fin n → ℂ := fun i => conj (v i)

@[simp] theorem cvec_cvec (v : Fin n → ℂ) : cvec (cvec v) = v := by
  funext i
  simp [cvec]

/-- Conjugation intertwines matrix action with entrywise-conjugated matrices. -/
theorem cvec_mulVec (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    cvec (M *ᵥ v) = (M.map conj) *ᵥ cvec v := by
  funext i
  simp only [cvec, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul]

/-- **The real structure**: the antilinear swap of particles and
    antiparticles. -/
def J (v : H n) : H n := (cvec v.2, cvec v.1)

/-- **The grading**: +1 on particles, −1 on antiparticles. -/
def gamma (v : H n) : H n := (v.1, -v.2)

/-- **The Dirac operator**: off-diagonal, built from a matrix M. -/
def D (M : Matrix (Fin n) (Fin n) ℂ) (v : H n) : H n := (M *ᵥ v.2, Mᴴ *ᵥ v.1)

/-! ## 1. J is antilinear, and an involution -/

theorem J_add (u v : H n) : J (u + v) = J u + J v := by
  unfold J cvec
  ext i <;> simp [Prod.fst_add, Prod.snd_add]

/-- **J is ANTILINEAR**: it conjugates scalars. This is what makes it a real
    structure rather than an operator. -/
theorem J_antilinear (c : ℂ) (v : H n) : J (c • v) = (conj c) • J v := by
  unfold J cvec
  ext i <;> simp [map_mul]

/-- **ε = +1**: J² = 1. -/
@[simp] theorem J_involutive (v : H n) : J (J v) = v := by
  unfold J
  simp

/-! ## 2. The grading -/

@[simp] theorem gamma_involutive (v : H n) : gamma (gamma v) = v := by
  unfold gamma
  simp

/-- **ε″ = −1**: Jγ = −γJ. This is the sign that distinguishes KO-dimension 6
    from KO-dimension 0, and it holds for the swap structure automatically. -/
theorem J_anticomm_gamma (v : H n) : J (gamma v) = -(gamma (J v)) := by
  unfold J gamma cvec
  ext i <;> simp

/-- The triple is genuinely EVEN: D is odd for the grading, {D, γ} = 0. -/
theorem D_anticomm_gamma (M : Matrix (Fin n) (Fin n) ℂ) (v : H n) :
    D M (gamma v) = -(gamma (D M v)) := by
  unfold D gamma
  ext i <;> simp [Matrix.mulVec_neg]

/-! ## 3. The commutation of J with D — where symmetry of M is used -/

/-- **ε′ = +1**: JD = DJ, for a symmetric M. This is the only place any
    hypothesis on M is needed, and it is exactly symmetry: Mᵀ = M. -/
theorem J_comm_D (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᵀ = M) (v : H n) :
    J (D M v) = D M (J v) := by
  have hsym : ∀ i j, M j i = M i j := fun i j => congrFun (congrFun hM i) j
  have hconj : M.map conj = Mᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply, hsym, Complex.star_def]
  have hconjH : Mᴴ.map conj = M := by
    ext i j
    simp [Matrix.conjTranspose_apply, hsym, Complex.star_def]
  unfold J D
  ext i
  · change cvec (Mᴴ *ᵥ v.1) i = (M *ᵥ cvec v.1) i
    rw [cvec_mulVec, hconjH]
  · change cvec (M *ᵥ v.2) i = (Mᴴ *ᵥ cvec v.2) i
    rw [cvec_mulVec, hconj]

/-! ## 4. The sign table, and non-vacuity -/

/-- **THE KO-DIMENSION-6 SIGN TABLE**, as three theorems about actual
    operators rather than three asserted numbers: J² = +1, JD = +DJ,
    Jγ = −γJ. -/
theorem ko_six_signs (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᵀ = M) :
    (∀ v : H n, J (J v) = v)
      ∧ (∀ v : H n, J (D M v) = D M (J v))
      ∧ (∀ v : H n, J (gamma v) = -(gamma (J v))) :=
  ⟨J_involutive, J_comm_D M hM, J_anticomm_gamma⟩

/-- Non-vacuity: there is a symmetric M whose Dirac operator is not zero, so
    the sign table above is not satisfied by a degenerate triple. -/
theorem exists_nonzero_D :
    ∃ M : Matrix (Fin 1) (Fin 1) ℂ, Mᵀ = M ∧ D M ((fun _ => 1), (fun _ => 1)) ≠ 0 := by
  refine ⟨1, by simp, ?_⟩
  intro h
  have h1 := congrFun (congrArg Prod.fst h) 0
  simp [D] at h1

end KOSixRealStructure
