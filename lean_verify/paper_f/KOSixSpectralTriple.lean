/-
  KOSixSpectralTriple: A Finite Real Spectral Triple of KO-Dimension 6
  ===================================================================

  `KOSixRealStructure.lean` constructed J, γ and D with the KO-6 signs on the
  doubled space V ⊕ V, and closed with an honest disclaimer: *"this file has
  J, γ and D but no algebra, so it is not yet a spectral triple."* That is the
  next leg, and this file takes it.

  WHY A DIFFERENT SPACE. On V ⊕ V the grading γ separates particles from
  antiparticles, and D is off-diagonal for THAT splitting. With an algebra
  acting on the particle sector, the order-one condition then fails — one can
  compute the double commutator and it is not zero. The obstruction is
  structural, not a bad choice of D: the grading has to be CHIRALITY, and the
  particle/antiparticle splitting has to be the one J exchanges. So the space
  here is four blocks,

      H = (V_L ⊕ V_R) ⊕ (V̄_L ⊕ V̄_R),

  with γ the chirality grading — and, this being KO-dimension 6, with the
  OPPOSITE sign on the antiparticle sector, which is exactly what makes
  Jγ = −γJ.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `J_involutive` (**ε = +1**), `J_comm_D` (**ε′ = +1**), `J_anticomm_gamma`
     (**ε″ = −1**) — the KO-dimension-6 sign table, and now with NO hypothesis
     on M whatsoever. (The V ⊕ V model needed Mᵀ = M for ε′; the four-block
     model does not, because the antiparticle sector carries M̄ and Mᵀ rather
     than M and Mᴴ.)
  2. `J_antilinear`, `J_add`; `D_add`, `D_smul`, `gamma_add`, `gamma_smul` —
     antilinearity of J and linearity of D and γ.
  3. `D_anticomm_gamma` — {D, γ} = 0, so the triple is genuinely even.
  4. `ip`, `ip_self`, `ip_self_eq_zero_iff`, `J_antiunitary`, `D_selfadjoint`,
     `gamma_selfadjoint` — the Hilbert-space requirements: J is antiunitary
     and D is self-adjoint, again with no hypothesis on M.
  5. **The algebra.** `piRep` is a unital *-representation of Mₙ(ℂ):
     `piRep_one`, `piRep_mul`, `piRep_add`, `piRep_smul`, `piRep_adjoint`
     (π(aᴴ) is the adjoint of π(a)), and `piRep_injective` (faithful, so the
     representation is not the zero map in disguise).
  6. **`commutant_condition`** — [π(a), Jπ(b)J⁻¹] = 0, the zeroth-order
     axiom: the algebra and its opposite commute.
  7. **`order_one_condition`** — [[D, π(a)], Jπ(b)J⁻¹] = 0, the first-order
     axiom. This is the one the V ⊕ V model could not satisfy and the reason
     this file exists.
  8. `order_one_fails_on_doubled` — **the obstruction, as a theorem.** The
     paragraph above says the V ⊕ V model cannot carry this algebra; an
     unverifiable negative claim in a docstring is the pattern this project
     removes, so it is proven, with an explicit witness (n = 1, M = 1, a = 2,
     b = 3). Precisely: THE SAME SHAPE OF ACTION fails on the doubled space —
     the theorem rules out that shape, not every conceivable algebra action
     there.
  9. `spectral_triple_axioms` — all of it in one statement, with
     `exists_nonzero_D` and `piRep_injective` alongside so that nothing above
     is satisfied vacuously.

  So: (Mₙ(ℂ), H, D, J, γ) is a finite real spectral triple of KO-dimension 6,
  every axiom a theorem.

  NOT proven here, and it remains the whole distance to the estate's claim:

  * **That this is THE cascade's spectral triple.** V = ℂⁿ is any finite
    space; nothing identifies it with the cascade's 96 fermion degrees of
    freedom, nothing derives M from the cascade, and nothing selects
    Mₙ(ℂ) over the Standard Model's ℂ ⊕ ℍ ⊕ M₃(ℂ). What is shown is that the
    KO-6 axioms are SATISFIABLE by an explicit finite construction with an
    algebra — which is strictly more than a sign table, and strictly less
    than the claim the tree makes.
  * The spectral action, the Higgs from inner fluctuations, and everything
    downstream of them.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import KOSixRealStructure

open Matrix ComplexConjugate

noncomputable section

namespace KOSixSpectralTriple

open KOSixRealStructure (cvec cvec_cvec cvec_mulVec)

variable {n : ℕ}

/-- The four-block space: (left, right) particles, then (left, right)
    antiparticles. -/
abbrev Hf (n : ℕ) :=
  ((Fin n → ℂ) × (Fin n → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ))

/-! ## 0. Entrywise conjugation of matrices, and the four identities used -/

/-- Entrywise conjugate of a matrix. -/
def mbar (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := M.map conj

@[simp] theorem mbar_mbar (M : Matrix (Fin n) (Fin n) ℂ) : mbar (mbar M) = M := by
  ext i j; simp [mbar]

theorem mbar_transpose (M : Matrix (Fin n) (Fin n) ℂ) : (mbar M)ᵀ = Mᴴ := by
  ext i j; simp [mbar, Matrix.conjTranspose_apply, Complex.star_def]

theorem mbar_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ) : mbar Mᴴ = Mᵀ := by
  ext i j; simp [mbar, Matrix.conjTranspose_apply, Complex.star_def]

theorem mbar_of_transpose (M : Matrix (Fin n) (Fin n) ℂ) : mbar Mᵀ = Mᴴ := by
  ext i j; simp [mbar, Matrix.conjTranspose_apply, Complex.star_def]

theorem conjTranspose_mbar (M : Matrix (Fin n) (Fin n) ℂ) : (mbar M)ᴴ = Mᵀ := by
  ext i j; simp [mbar, Matrix.conjTranspose_apply, Complex.star_def]

theorem conjTranspose_transpose' (M : Matrix (Fin n) (Fin n) ℂ) : (Mᵀ)ᴴ = mbar M := by
  ext i j; simp [mbar, Matrix.conjTranspose_apply, Complex.star_def]

/-! ## 1. The operators -/

/-- **The real structure**: conjugate and exchange particles with
    antiparticles. -/
def J (v : Hf n) : Hf n := ((cvec v.2.1, cvec v.2.2), (cvec v.1.1, cvec v.1.2))

/-- **The grading**: chirality, with the opposite sign on antiparticles. That
    sign flip is the whole content of KO-dimension 6. -/
def gamma (v : Hf n) : Hf n := ((v.1.1, -v.1.2), (-v.2.1, v.2.2))

/-- **The Dirac operator**: off-diagonal in chirality, acting by M on
    particles and by its conjugate on antiparticles. -/
def D (M : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n :=
  ((M *ᵥ v.1.2, Mᴴ *ᵥ v.1.1), (mbar M *ᵥ v.2.2, Mᵀ *ᵥ v.2.1))

/-- **The algebra action**: Mₙ(ℂ) acts on the particle sector. -/
def piRep (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n :=
  ((a *ᵥ v.1.1, a *ᵥ v.1.2), (v.2.1, v.2.2))

/-- The opposite action, J π(b) J⁻¹ — and since J² = 1, J⁻¹ = J. -/
def piOp (b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n := J (piRep b (J v))

/-! ## 2. Linearity and antilinearity -/

theorem J_add (u v : Hf n) : J (u + v) = J u + J v := by
  unfold J cvec
  ext i <;> simp

theorem J_antilinear (c : ℂ) (v : Hf n) : J (c • v) = (conj c) • J v := by
  unfold J cvec
  ext i <;> simp [map_mul]

theorem D_add (M : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n) :
    D M (u + v) = D M u + D M v := by
  unfold D
  ext i <;> simp [Matrix.mulVec_add]

theorem D_smul (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : Hf n) :
    D M (c • v) = c • D M v := by
  unfold D
  ext i <;> simp [Matrix.mulVec_smul]

theorem gamma_add (u v : Hf n) : gamma (u + v) = gamma u + gamma v := by
  unfold gamma
  ext i <;> simp <;> ring

theorem gamma_smul (c : ℂ) (v : Hf n) : gamma (c • v) = c • gamma v := by
  unfold gamma
  ext i <;> simp

theorem piRep_add (a : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n) :
    piRep a (u + v) = piRep a u + piRep a v := by
  unfold piRep
  ext i <;> simp [Matrix.mulVec_add]

theorem piRep_smul (a : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : Hf n) :
    piRep a (c • v) = c • piRep a v := by
  unfold piRep
  ext i <;> simp [Matrix.mulVec_smul]

/-! ## 3. The KO-dimension-6 sign table -/

/-- **ε = +1**: J² = 1. -/
@[simp] theorem J_involutive (v : Hf n) : J (J v) = v := by
  unfold J
  simp

@[simp] theorem gamma_involutive (v : Hf n) : gamma (gamma v) = v := by
  unfold gamma
  simp

/-- **ε″ = −1**: Jγ = −γJ. The sign that separates KO-dimension 6 from
    KO-dimension 0, and here it comes from the antiparticle sector carrying
    the opposite chirality sign. -/
theorem J_anticomm_gamma (v : Hf n) : J (gamma v) = -(gamma (J v)) := by
  unfold J gamma cvec
  ext i <;> simp

/-- The triple is genuinely EVEN: D is odd for the grading. -/
theorem D_anticomm_gamma (M : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    D M (gamma v) = -(gamma (D M v)) := by
  unfold D gamma
  ext i <;> simp [Matrix.mulVec_neg]

/-- **ε′ = +1**: JD = DJ — and unlike the V ⊕ V model, for EVERY M. -/
theorem J_comm_D (M : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    J (D M v) = D M (J v) := by
  unfold J D
  ext i
  · change cvec (mbar M *ᵥ v.2.2) i = (M *ᵥ cvec v.2.2) i
    rw [cvec_mulVec, ← mbar, mbar_mbar]
  · change cvec (Mᵀ *ᵥ v.2.1) i = (Mᴴ *ᵥ cvec v.2.1) i
    rw [cvec_mulVec, ← mbar, mbar_of_transpose]
  · change cvec (M *ᵥ v.1.2) i = (mbar M *ᵥ cvec v.1.2) i
    rw [cvec_mulVec, ← mbar]
  · change cvec (Mᴴ *ᵥ v.1.1) i = (Mᵀ *ᵥ cvec v.1.1) i
    rw [cvec_mulVec, ← mbar, mbar_conjTranspose]

/-- **THE KO-DIMENSION-6 SIGN TABLE**, with no hypothesis on M. -/
theorem ko_six_signs (M : Matrix (Fin n) (Fin n) ℂ) :
    (∀ v : Hf n, J (J v) = v)
      ∧ (∀ v : Hf n, J (D M v) = D M (J v))
      ∧ (∀ v : Hf n, J (gamma v) = -(gamma (J v))) :=
  ⟨J_involutive, J_comm_D M, J_anticomm_gamma⟩

/-! ## 4. The Hilbert-space structure -/

/-- The standard Hermitian inner product on the four blocks. -/
def ip (u v : Hf n) : ℂ :=
  ((∑ i, conj (u.1.1 i) * v.1.1 i) + ∑ i, conj (u.1.2 i) * v.1.2 i)
    + ((∑ i, conj (u.2.1 i) * v.2.1 i) + ∑ i, conj (u.2.2 i) * v.2.2 i)

private theorem sum_conj_self (a : Fin n → ℂ) :
    (∑ i, conj (a i) * a i) = ((∑ i, Complex.normSq (a i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_conj_mul_self.symm

theorem ip_self (v : Hf n) :
    ip v v = ((((∑ i, Complex.normSq (v.1.1 i)) + ∑ i, Complex.normSq (v.1.2 i))
      + ((∑ i, Complex.normSq (v.2.1 i)) + ∑ i, Complex.normSq (v.2.2 i)) : ℝ) : ℂ) := by
  unfold ip
  rw [sum_conj_self, sum_conj_self, sum_conj_self, sum_conj_self]
  push_cast
  ring

/-- Nondegeneracy: `ip` is a genuine inner product. -/
theorem ip_self_eq_zero_iff (v : Hf n) : ip v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [ip_self] at h
    have hreal : ((∑ i, Complex.normSq (v.1.1 i)) + ∑ i, Complex.normSq (v.1.2 i))
        + ((∑ i, Complex.normSq (v.2.1 i)) + ∑ i, Complex.normSq (v.2.2 i)) = 0 := by
      exact_mod_cast h
    have key : ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (0 : ℝ) ≤ ∑ i, a i :=
      fun a ha => Finset.sum_nonneg fun i _ => ha i
    have n11 := key _ fun i => Complex.normSq_nonneg (v.1.1 i)
    have n12 := key _ fun i => Complex.normSq_nonneg (v.1.2 i)
    have n21 := key _ fun i => Complex.normSq_nonneg (v.2.1 i)
    have n22 := key _ fun i => Complex.normSq_nonneg (v.2.2 i)
    have z11 : ∑ i, Complex.normSq (v.1.1 i) = 0 := by linarith
    have z12 : ∑ i, Complex.normSq (v.1.2 i) = 0 := by linarith
    have z21 : ∑ i, Complex.normSq (v.2.1 i) = 0 := by linarith
    have z22 : ∑ i, Complex.normSq (v.2.2 i) = 0 := by linarith
    have e : ∀ (a : Fin n → ℂ), (∑ i, Complex.normSq (a i)) = 0 → a = 0 := by
      intro a ha
      funext i
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg
          fun j _ => Complex.normSq_nonneg (a j)).mp ha i (Finset.mem_univ i))
    ext i <;> simp [e _ z11, e _ z12, e _ z21, e _ z22]
  · intro h
    rw [h]
    unfold ip
    simp

/-- **J is ANTIUNITARY.** -/
theorem J_antiunitary (u v : Hf n) : ip (J u) (J v) = conj (ip u v) := by
  unfold ip J cvec
  rw [map_add, map_add, map_add, map_sum, map_sum, map_sum, map_sum, add_comm]
  congr 1 <;>
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun i _ => by rw [map_mul])
      (Finset.sum_congr rfl fun i _ => by rw [map_mul])

private theorem sum_conj_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    (∑ i, conj ((A *ᵥ a) i) * b i) = ∑ i, conj (a i) * (Aᴴ *ᵥ b) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Complex.star_def]
    ring

/-- **D is SELF-ADJOINT**, for every M. -/
theorem D_selfadjoint (M : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n) :
    ip (D M u) v = ip u (D M v) := by
  unfold ip D
  rw [sum_conj_mulVec M u.1.2 v.1.1, sum_conj_mulVec Mᴴ u.1.1 v.1.2,
    sum_conj_mulVec (mbar M) u.2.2 v.2.1, sum_conj_mulVec Mᵀ u.2.1 v.2.2,
    Matrix.conjTranspose_conjTranspose]
  rw [conjTranspose_mbar, conjTranspose_transpose']
  ring

theorem gamma_selfadjoint (u v : Hf n) : ip (gamma u) v = ip u (gamma v) := by
  unfold ip gamma
  simp only [Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]

/-- π(aᴴ) is the adjoint of π(a): the representation is a *-representation. -/
theorem piRep_adjoint (a : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n) :
    ip (piRep a u) v = ip u (piRep aᴴ v) := by
  unfold ip piRep
  rw [sum_conj_mulVec a u.1.1 v.1.1, sum_conj_mulVec a u.1.2 v.1.2]

/-! ## 5. The algebra is represented -/

@[simp] theorem piRep_one (v : Hf n) : piRep (1 : Matrix (Fin n) (Fin n) ℂ) v = v := by
  unfold piRep
  simp

theorem piRep_mul (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRep (a * b) v = piRep a (piRep b v) := by
  unfold piRep
  ext i <;> simp [Matrix.mulVec_mulVec]

/-- The representation is FAITHFUL: distinct matrices act differently, so
    nothing below is about a collapsed algebra. -/
theorem piRep_injective (a b : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ v : Hf n, piRep a v = piRep b v) : a = b := by
  ext i j
  have hv := h (((Pi.single j 1, 0), (0, 0)) : Hf n)
  have h1 := congrFun (congrArg Prod.fst (congrArg Prod.fst hv)) i
  simpa [piRep, Matrix.mulVec_single] using h1

/-! ## 6. The two order conditions — the reason this file exists -/

/-- The opposite action, computed: J π(b) J⁻¹ acts by b̄ on antiparticles. -/
theorem piOp_apply (b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piOp b v = ((v.1.1, v.1.2), (mbar b *ᵥ v.2.1, mbar b *ᵥ v.2.2)) := by
  unfold piOp J piRep
  ext i
  · simp [cvec_cvec]
  · simp [cvec_cvec]
  · change cvec (b *ᵥ cvec v.2.1) i = (mbar b *ᵥ v.2.1) i
    rw [cvec_mulVec, cvec_cvec, ← mbar]
  · change cvec (b *ᵥ cvec v.2.2) i = (mbar b *ᵥ v.2.2) i
    rw [cvec_mulVec, cvec_cvec, ← mbar]

/-- **THE ZEROTH-ORDER (COMMUTANT) CONDITION**: [π(a), Jπ(b)J⁻¹] = 0. The
    algebra and its opposite commute, so H is an A-bimodule. -/
theorem commutant_condition (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRep a (piOp b v) = piOp b (piRep a v) := by
  rw [piOp_apply, piOp_apply]
  unfold piRep
  ext i <;> simp

/-- The commutator [D, π(a)], written out. -/
def commDpi (M a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n :=
  D M (piRep a v) - piRep a (D M v)

/-- [D, π(a)] acts only on the particle sector — which is why it commutes
    with the opposite action. -/
theorem commDpi_apply (M a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    commDpi M a v
      = (((M * a - a * M) *ᵥ v.1.2, (Mᴴ * a - a * Mᴴ) *ᵥ v.1.1), (0, 0)) := by
  unfold commDpi D piRep
  ext i <;>
    simp [Matrix.sub_mulVec, Matrix.mulVec_mulVec]

/-- **THE FIRST-ORDER (ORDER-ONE) CONDITION**: [[D, π(a)], Jπ(b)J⁻¹] = 0.
    This is the axiom the V ⊕ V model of `KOSixRealStructure` could not
    satisfy, and the reason this four-block model exists. -/
theorem order_one_condition (M a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    commDpi M a (piOp b v) = piOp b (commDpi M a v) := by
  rw [piOp_apply, commDpi_apply, commDpi_apply, piOp_apply]
  ext i <;> simp

/-- Non-vacuity of the ORDER-ONE condition: [D, π(a)] is not identically
    zero, so `order_one_condition` constrains a genuinely nonzero operator.
    (At n = 1 the commutator DOES vanish — 1×1 matrices commute — which is
    why the witness lives at n = 2.) -/
theorem exists_nonzero_commDpi :
    ∃ (M a : Matrix (Fin 2) (Fin 2) ℂ) (v : Hf 2), commDpi M a v ≠ 0 := by
  refine ⟨!![0, 1; 1, 0], !![1, 0; 0, 0], (((fun _ => 0), (fun _ => 1)), (0, 0)), ?_⟩
  intro h
  have h1 := congrFun (congrArg Prod.fst (congrArg Prod.fst h)) 0
  rw [commDpi_apply] at h1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

/-! ## 7. The obstruction, as a theorem rather than a remark

    The header claims the V ⊕ V model of `KOSixRealStructure` cannot carry
    this algebra. An unverifiable negative claim in a docstring is exactly the
    pattern this project removes, so here it is as a theorem: with the same
    shape of action on the doubled space, the order-one condition FAILS. -/

/-- The analogue of `piRep` on the doubled space V ⊕ V. -/
def piRep2 (a : Matrix (Fin n) (Fin n) ℂ) (v : KOSixRealStructure.H n) :
    KOSixRealStructure.H n := (a *ᵥ v.1, v.2)

/-- The opposite action there. -/
def piOp2 (b : Matrix (Fin n) (Fin n) ℂ) (v : KOSixRealStructure.H n) :
    KOSixRealStructure.H n :=
  KOSixRealStructure.J (piRep2 b (KOSixRealStructure.J v))

/-- [D, π(a)] there. -/
def commDpi2 (M a : Matrix (Fin n) (Fin n) ℂ) (v : KOSixRealStructure.H n) :
    KOSixRealStructure.H n :=
  KOSixRealStructure.D M (piRep2 a v) - piRep2 a (KOSixRealStructure.D M v)

/-- **The order-one condition FAILS on V ⊕ V.** Explicit witness: n = 1,
    M = 1, a = 2, b = 3. So the four-block space of this file is not a
    stylistic preference — the two-block one cannot support the axiom. -/
theorem order_one_fails_on_doubled :
    ∃ (M a b : Matrix (Fin 1) (Fin 1) ℂ) (v : KOSixRealStructure.H 1),
      commDpi2 M a (piOp2 b v) ≠ piOp2 b (commDpi2 M a v) := by
  refine ⟨1, 2, 3, ((fun _ => 0), (fun _ => 1)), ?_⟩
  intro h
  have h1 := congrFun (congrArg Prod.fst h) 0
  simp [commDpi2, piOp2, piRep2, KOSixRealStructure.D, KOSixRealStructure.J,
    KOSixRealStructure.cvec] at h1
  norm_num [Complex.ext_iff] at h1

/-! ## 8. Non-vacuity, and the whole thing in one statement -/

theorem exists_nonzero_D :
    ∃ (M : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1), D M v ≠ 0 := by
  refine ⟨1, (((fun _ => 0), (fun _ => 1)), ((fun _ => 0), (fun _ => 0))), ?_⟩
  intro h
  have h1 := congrFun (congrArg Prod.fst (congrArg Prod.fst h)) 0
  simp [D] at h1

/-- **A FINITE REAL SPECTRAL TRIPLE OF KO-DIMENSION 6**, every axiom a
    theorem IN THIS ONE STATEMENT — including faithfulness of π, which an
    adversarial review noted was previously only a separate theorem while
    this docstring claimed it: the sign table (ε, ε′, ε″) = (+1, +1, −1);
    J antiunitary; D self-adjoint and odd for the grading; π a unital
    *-representation, FAITHFUL (last conjunct); the commutant condition;
    the order-one condition. Vacuity caveat unchanged from the header: the
    signs hold for every M including M = 0; the nonzero-D witnesses are
    `exists_nonzero_D` and `exists_nonzero_commDpi` at fixed n. -/
theorem spectral_triple_axioms (M : Matrix (Fin n) (Fin n) ℂ) :
    -- KO-6 signs
    (∀ v : Hf n, J (J v) = v)
      ∧ (∀ v : Hf n, J (D M v) = D M (J v))
      ∧ (∀ v : Hf n, J (gamma v) = -(gamma (J v)))
    -- even, and D odd for the grading
      ∧ (∀ v : Hf n, gamma (gamma v) = v)
      ∧ (∀ v : Hf n, D M (gamma v) = -(gamma (D M v)))
    -- Hilbert-space axioms
      ∧ (∀ u v : Hf n, ip (J u) (J v) = conj (ip u v))
      ∧ (∀ u v : Hf n, ip (D M u) v = ip u (D M v))
    -- the algebra
      ∧ (∀ (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n),
          piRep (a * b) v = piRep a (piRep b v))
      ∧ (∀ v : Hf n, piRep (1 : Matrix (Fin n) (Fin n) ℂ) v = v)
      ∧ (∀ (a : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n),
          ip (piRep a u) v = ip u (piRep aᴴ v))
    -- the two order conditions
      ∧ (∀ (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n),
          piRep a (piOp b v) = piOp b (piRep a v))
      ∧ (∀ (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n),
          commDpi M a (piOp b v) = piOp b (commDpi M a v))
    -- faithfulness
      ∧ (∀ a b : Matrix (Fin n) (Fin n) ℂ,
          (∀ v : Hf n, piRep a v = piRep b v) → a = b) :=
  ⟨J_involutive, J_comm_D M, J_anticomm_gamma, gamma_involutive, D_anticomm_gamma M,
    J_antiunitary, D_selfadjoint M, piRep_mul, piRep_one, piRep_adjoint,
    commutant_condition, order_one_condition M, piRep_injective⟩

end KOSixSpectralTriple
