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
  6. `gamma_involutive`, and `signs_with_nonzero_D` — non-vacuity, in ONE
     statement: γ² = 1, and there is a symmetric M for which D ≠ 0 AND all
     the signs hold. (An adversarial review pointed out, correctly, that the
     earlier pair `ko_six_signs` + `exists_nonzero_D` never said this: the
     signs alone hold vacuously for M = 0, where D ≡ 0.)
  7. `D_add`, `D_smul`, `gamma_add`, `gamma_smul` — D and γ are ℂ-linear, so
     "operator" is earned rather than assumed; and `J_not_linear`, the other
     half of `J_antilinear`.
  8. **The Hilbert-space structure.** A real structure in NCG is an
     ANTIUNITARY J and the Dirac operator is required SELF-ADJOINT; neither
     can even be stated without an inner product, and the first draft of this
     file had none. So `ip` is the standard Hermitian form on the doubled
     space, with `ip_self` (⟪v,v⟫ is a nonnegative real) and
     `ip_self_eq_zero_iff` (nondegenerate), and then:
       * `J_antiunitary` — ⟪Ju, Jv⟫ = conj⟪u, v⟫,
       * `D_selfadjoint` — ⟪Du, v⟫ = ⟪u, Dv⟫, for EVERY M (the off-diagonal
         shape [[0, M], [Mᴴ, 0]] is self-adjoint by construction; the
         symmetry hypothesis is needed only for JD = DJ),
       * `gamma_selfadjoint` — the grading is an observable.

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
    representation, and the algebra action itself: this file has J, γ, D and
    an inner product, but no algebra, so it is not yet a spectral triple.
  * Completeness of H and boundedness/compact-resolvent statements: H is
    finite-dimensional here, so these are not obstacles, but nor are they
    stated.
  * Any statement about the Standard Model's specific finite geometry.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.BigOperators

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

/-! ## 5. Linearity: D and γ really are operators -/

theorem D_add (M : Matrix (Fin n) (Fin n) ℂ) (u v : H n) :
    D M (u + v) = D M u + D M v := by
  unfold D
  ext i <;> simp [Matrix.mulVec_add]

theorem D_smul (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : H n) :
    D M (c • v) = c • D M v := by
  unfold D
  ext i <;> simp [Matrix.mulVec_smul]

theorem gamma_add (u v : H n) : gamma (u + v) = gamma u + gamma v := by
  unfold gamma
  ext i
  · simp
  · simp; ring

theorem gamma_smul (c : ℂ) (v : H n) : gamma (c • v) = c • gamma v := by
  unfold gamma
  ext i <;> simp

/-- **J is NOT linear** — the other half of `J_antilinear`, which on its own
    is compatible with linearity only if the space is real. At n = 1,
    J(i·(1,1)) = (−i,−i) while i·J(1,1) = (i,i). -/
theorem J_not_linear : ∃ (c : ℂ) (v : H 1), J (c • v) ≠ c • J v := by
  refine ⟨Complex.I, ((fun _ => 1), (fun _ => 1)), ?_⟩
  intro h
  have h1 := congrFun (congrArg Prod.fst h) 0
  simp [J, cvec] at h1
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact Complex.I_ne_zero h3

/-! ## 6. The Hilbert-space structure: J is ANTIUNITARY, D and γ self-adjoint

    A real structure in noncommutative geometry is an antiunitary J, and the
    Dirac operator is required self-adjoint. Without an inner product on H
    neither statement can even be made, so the standard Hermitian form is put
    on the doubled space here and both are proven. -/

/-- The standard Hermitian inner product on H = V ⊕ V. -/
def ip (u v : H n) : ℂ :=
  (∑ i, conj (u.1 i) * v.1 i) + ∑ i, conj (u.2 i) * v.2 i

/-- The inner product is positive: ⟪v,v⟫ is a nonnegative real. -/
theorem ip_self (v : H n) :
    ip v v = (((∑ i, Complex.normSq (v.1 i)) + ∑ i, Complex.normSq (v.2 i) : ℝ) : ℂ) := by
  have h : ∀ a : Fin n → ℂ,
      (∑ i, conj (a i) * a i) = ((∑ i, Complex.normSq (a i) : ℝ) : ℂ) := by
    intro a
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_conj_mul_self.symm
  unfold ip
  rw [h v.1, h v.2]
  push_cast
  ring

/-- **Nondegeneracy**: ⟪v,v⟫ = 0 only for v = 0, so `ip` is a genuine inner
    product and not a degenerate form. -/
theorem ip_self_eq_zero_iff (v : H n) : ip v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [ip_self] at h
    have hreal : (∑ i, Complex.normSq (v.1 i)) + ∑ i, Complex.normSq (v.2 i) = 0 := by
      exact_mod_cast h
    have h1 : ∀ i, (0 : ℝ) ≤ Complex.normSq (v.1 i) := fun i => Complex.normSq_nonneg _
    have h2 : ∀ i, (0 : ℝ) ≤ Complex.normSq (v.2 i) := fun i => Complex.normSq_nonneg _
    have s1 : (0 : ℝ) ≤ ∑ i, Complex.normSq (v.1 i) :=
      Finset.sum_nonneg fun i _ => h1 i
    have s2 : (0 : ℝ) ≤ ∑ i, Complex.normSq (v.2 i) :=
      Finset.sum_nonneg fun i _ => h2 i
    have e1 : ∑ i, Complex.normSq (v.1 i) = 0 := by linarith
    have e2 : ∑ i, Complex.normSq (v.2 i) = 0 := by linarith
    have f1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h1 i).mp e1
    have f2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => h2 i).mp e2
    ext i
    · exact Complex.normSq_eq_zero.mp (f1 i (Finset.mem_univ i))
    · exact Complex.normSq_eq_zero.mp (f2 i (Finset.mem_univ i))
  · intro h
    rw [h]
    unfold ip
    simp

/-- **J IS ANTIUNITARY**: ⟪Ju, Jv⟫ = conj ⟪u, v⟫. With `J_antilinear` and
    `J_involutive` this is the definition of a real structure on H, and it is
    the statement that could not be made before an inner product was put on
    the space. -/
theorem J_antiunitary (u v : H n) : ip (J u) (J v) = conj (ip u v) := by
  unfold ip J cvec
  rw [map_add, map_sum, map_sum, add_comm]
  congr 1 <;>
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul]

/-- The adjoint identity for a matrix acting on one summand. -/
private theorem sum_conj_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    (∑ i, conj ((A *ᵥ a) i) * b i) = ∑ i, conj (a i) * (Aᴴ *ᵥ b) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Complex.star_def]
    ring

/-- **D IS SELF-ADJOINT**: ⟪Du, v⟫ = ⟪u, Dv⟫, for every M. This is the
    remaining spectral-triple requirement on D that can be stated without an
    algebra, and it needs no hypothesis on M — the off-diagonal shape
    [[0, M], [Mᴴ, 0]] is self-adjoint by construction. -/
theorem D_selfadjoint (M : Matrix (Fin n) (Fin n) ℂ) (u v : H n) :
    ip (D M u) v = ip u (D M v) := by
  unfold ip D
  rw [sum_conj_mulVec M u.2 v.1, sum_conj_mulVec Mᴴ u.1 v.2,
    Matrix.conjTranspose_conjTranspose, add_comm]

/-- γ is self-adjoint too, so the grading is an observable and not merely an
    involution. -/
theorem gamma_selfadjoint (u v : H n) : ip (gamma u) v = ip u (gamma v) := by
  unfold ip gamma
  simp only [Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]

/-! ## 7. Non-vacuity, stated together with the signs -/

/-- **The sign table for a NON-DEGENERATE D**, in one statement. The earlier
    `ko_six_signs` holds vacuously for M = 0 (where D ≡ 0), and
    `exists_nonzero_D` was a separate theorem about a different M; a review
    pointed out that no single statement said the signs hold for a D that is
    not zero. This one does. -/
theorem signs_with_nonzero_D :
    ∃ M : Matrix (Fin 1) (Fin 1) ℂ,
      Mᵀ = M
      ∧ D M ((fun _ => 1), (fun _ => 1)) ≠ 0
      ∧ (∀ v : H 1, J (J v) = v)
      ∧ (∀ v : H 1, J (D M v) = D M (J v))
      ∧ (∀ v : H 1, J (gamma v) = -(gamma (J v)))
      ∧ (∀ (u v : H 1), ip (D M u) v = ip u (D M v))
      ∧ (∀ (u v : H 1), ip (J u) (J v) = conj (ip u v)) := by
  obtain ⟨M, hMs, hMne⟩ := exists_nonzero_D
  exact ⟨M, hMs, hMne, J_involutive, J_comm_D M hMs, J_anticomm_gamma,
    D_selfadjoint M, J_antiunitary⟩

end KOSixRealStructure
