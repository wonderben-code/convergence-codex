/-
  StarStructureInequivalent: two ⋆-structures on `M₂(ℂ)` that no algebra automorphism relates —
  the first inequivalence this estate has

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39104, item (1)'s residue.

  WHERE THIS PICKS UP. Three units have narrowed the same residue. Unit 69 computed the fibre of
  `P ↦ s_P` and separated two ⋆-structures **as maps**; unit 70 constructed the signature and
  proved it congruence-invariant. Both then recorded the same gap in their own words:

  > **No two ⋆-structures are shown INEQUIVALENT.** … `signature_congr` is exactly the invariance
  > that statement needs … **What is missing is the bookkeeping, not the mathematics.** Until it is
  > a theorem, *inequivalent* is not a word this estate has earned.

  **This file writes the bookkeeping and earns the word.** The estimate was right: the identity
  unit 70's header wrote out is `hermitianStar_congrTwist` below, and it took `noncomm_ring` and
  one congruence lemma.

  WHAT IS PROVED.
  * **`hermitianStar_congrTwist`** — **conjugation CONGRUES the twist.** With `s X = (P X P⁻¹)ᴴ`
    and `α X = S X S⁻¹`, the structure `α⁻¹ ∘ s ∘ α` is the one presented by `Sᴴ P S`. The route
    is `conjTransposeUnit` (the conjugate transpose of a unit is a unit) and `congrTwist`, and the
    whole proof is: conjugate-transpose both twists, use that `P` and `P⁻¹` are Hermitian, and
    observe both sides are `S⁻¹ P⁻¹ (S⁻¹)ᴴ · Xᴴ · Sᴴ P S`.
  * **`Conjugate` and `ConjugateAlg`** — the inner notion and the general one, kept apart on
    purpose. `ConjugateAlg s t` asks for SOME algebra automorphism with `t = α⁻¹ ∘ s ∘ α`, which
    is what the classification literature means; `Conjugate` asks for an inner one.
  * **`conjugate_of_conjugateAlg`** — **and they agree, off this estate's own Skolem–Noether.**
    `SkolemNoether.skolemNoether` gives `α A = S A S⁻¹`, and `α.symm Y = S⁻¹ Y S` follows from
    `AlgEquiv.symm_apply_eq`. **So taking `α` inner costs no generality, and that is a theorem
    here rather than a remark.**
  * **`conjugateAlg_symm`** — conjugacy is symmetric, via `α⁻¹`. **Without it the negative results
    below would be statements about one ordering**, which is not what *inequivalent* means.
  * **`signature_eq_or_swap_of_conjugate`** — **CONJUGATE ⋆-STRUCTURES HAVE THE SAME SIGNATURE, UP
    TO EXCHANGING ITS HALVES.** Three earlier results compose and nothing new is needed: the
    bookkeeping turns conjugation into congruence of twists, `HermitianRealForm.signature_congr`
    says the signature cannot see a congruence, and unit 69's fibre contributes the one real
    scalar left over, whose sign contributes the exchange.
  * **`not_conjugate_of_signature_ne`** — the contrapositive, as a usable tool: signatures neither
    equal nor exchanged ⇒ the ⋆-structures are not conjugate.
  * **`signature_diagTwist = (2, 2)`** — **the first signature this estate computes that is not
    definite.** `realQuad diag(1,-1) x = ‖x₀‖² − ‖x₁‖²`; the coordinate kernels `coordKer 1` and
    `coordKer 0` are `ℝ`-subspaces of dimension 2 each (`finrank_coordKer`, by rank–nullity on
    `LinearMap.proj`), the form is positive definite on the first and non-positive on the second,
    and `QuadraticForm.sigPos_add_finrank_le_of_nonpos` with `le_sigPos_of_posDef` squeezes
    `sigPos` to exactly 2. The same argument on `-Q` gives `sigNeg = 2`. **No diagonalisation and
    no weighted-sum-of-squares presentation is built**; the two bounds are enough.
  * **`not_conjugateAlg_conjTransposeStar_diagTwist`** and its mirror — **THE RESULT.** On
    `M₂(ℂ)`, the conjugate transpose `X ↦ Xᴴ` and the indefinite twist `X ↦ D Xᴴ D` for
    `D = diag(1,-1)` are **not carried onto one another by any algebra automorphism**, in either
    direction. Their signatures are `(4, 0)` and `(2, 2)`, which are neither equal nor each
    other's exchange. **The estate had no inequivalence statement of any kind before this.**

  WHAT IS **NOT** CLAIMED.
  * **The classification is not finished.** Nothing here says how many ⋆-structures `Mₙ(ℂ)` has up
    to conjugacy, and the signature is not shown to be a COMPLETE invariant: that needs the
    existence half of the inertia law — any two Hermitian forms of equal signature are congruent —
    which is `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` in Mathlib and is
    **not consumed here**. Without it, equal signatures do not give conjugacy.
  * **The signature is computed at `±1` and at `diag(1,-1)` only.** Three values, not a formula.
    A general `diag(1,…,1,-1,…,-1)` would need the argument above run at every split, and the
    general Hermitian twist would need a diagonalisation.
  * **`ConjugateAlg` is about ⋆-structures on ONE algebra.** Nothing compares ⋆-structures across
    different `n`, and nothing here is about the `StarStr`/`StarStrC` notions on products.
  * **Nothing over `ℝ` or `ℍ`.**
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). **Two inequivalent ⋆-structures on `M₂(ℂ)` do not
    prefer a factorisation of `M₁₆`**; what they show is that the residue this chain has been
    narrowing is not empty, which is a different thing and the honest reading of it.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import HermitianRealForm
import SkolemNoether

namespace StarStructureInequivalent

open Matrix StarStructureMatrix StarStructureTwistFibre HermitianRealForm

noncomputable section

variable {n : ℕ}

/-- The conjugate transpose of a unit is a unit. -/
def conjTransposeUnit (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := (S : Matrix (Fin n) (Fin n) ℂ)ᴴ
  inv := ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

@[simp] theorem conjTransposeUnit_val (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    ((conjTransposeUnit S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = (S : Matrix (Fin n) (Fin n) ℂ)ᴴ := rfl

@[simp] theorem conjTransposeUnit_inv_val (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (((conjTransposeUnit S)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ := rfl

/-- The congruent twist `Sᴴ P S`, as a unit. -/
def congrTwist (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  conjTransposeUnit S * P * S

@[simp] theorem congrTwist_val (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    ((congrTwist P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = (S : Matrix (Fin n) (Fin n) ℂ)ᴴ * (P : Matrix (Fin n) (Fin n) ℂ)
        * (S : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem congrTwist_inv (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (congrTwist P S)⁻¹ = S⁻¹ * P⁻¹ * (conjTransposeUnit S)⁻¹ := by
  rw [congrTwist, _root_.mul_inv_rev, _root_.mul_inv_rev, ← mul_assoc]

@[simp] theorem congrTwist_inv_val (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (((congrTwist P S)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  rw [congrTwist_inv]
  simp only [Units.val_mul, conjTransposeUnit_inv_val]

/-- A congruent twist of a Hermitian twist is Hermitian. -/
theorem congrTwist_hermitian (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    ((congrTwist P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((congrTwist P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [congrTwist_val, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP]
  rw [Matrix.mul_assoc]

/-! ## The bookkeeping: conjugation congrues the twist -/

/-- **Conjugating a ⋆-structure by an inner automorphism CONGRUES ITS TWIST.** With
`s X = (P X P⁻¹)ᴴ` and `α X = S X S⁻¹`, the structure `α⁻¹ ∘ s ∘ α` is the one presented by the
CONGRUENT twist `Sᴴ P S`. **This is the identity `StarStructureTwistFibre`'s header wrote out and
called bookkeeping**; here it is as a theorem. -/
theorem hermitianStar_congrTwist (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (hermitianStar (congrTwist P S) (congrTwist_hermitian P S hP)).map X
      = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (hermitianStar P hP).map ((S : Matrix (Fin n) (Fin n) ℂ) * X
          * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        * (S : Matrix (Fin n) (Fin n) ℂ) := by
  have hPi := inv_hermitian P hP
  simp only [hermitianStar_map, twistMap_apply, congrTwist_val, congrTwist_inv_val,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP, hPi]
  noncomm_ring

/-- Two ⋆-structures are CONJUGATE when an inner automorphism carries one to the other. By
`SkolemNoether.skolemNoether` every algebra automorphism of `Mₙ(ℂ)` is inner, so this is
conjugation by an arbitrary automorphism and not a restricted notion. -/
def Conjugate (s t : StarStructure n) : Prop :=
  ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X : Matrix (Fin n) (Fin n) ℂ,
    t.map X = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      * s.map ((S : Matrix (Fin n) (Fin n) ℂ) * X
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      * (S : Matrix (Fin n) (Fin n) ℂ)

/-- Conjugation is realised at every congruent twist: `hermitianStar P` and
`hermitianStar (Sᴴ P S)` are conjugate, so the notion is not empty. -/
theorem conjugate_hermitianStar_congrTwist (P S : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    Conjugate (hermitianStar P hP)
      (hermitianStar (congrTwist P S) (congrTwist_hermitian P S hP)) :=
  ⟨S, hermitianStar_congrTwist P S hP⟩

/-! ## The payoff: a signature that separates ⋆-structures up to conjugation -/

/-- **CONJUGATE ⋆-STRUCTURES HAVE THE SAME SIGNATURE, UP TO EXCHANGING ITS HALVES.** The
bookkeeping above turns conjugation into congruence of twists; `HermitianRealForm.signature_congr`
says the signature cannot see a congruence; the fibre contributes the one real scalar that is
left, and its sign contributes the exchange. -/
theorem signature_eq_or_swap_of_conjugate [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : Conjugate (hermitianStar P hP) (hermitianStar Q hQ)) :
    signature (Q : Matrix (Fin n) (Fin n) ℂ) = signature (P : Matrix (Fin n) (Fin n) ℂ)
      ∨ signature (Q : Matrix (Fin n) (Fin n) ℂ)
        = (signature (P : Matrix (Fin n) (Fin n) ℂ)).swap := by
  obtain ⟨S, hS⟩ := h
  have hmap : (hermitianStar Q hQ).map
      = (hermitianStar (congrTwist P S) (congrTwist_hermitian P S hP)).map := by
    funext X
    rw [hS X, hermitianStar_congrTwist P S hP X]
  have heq := starStructure_eq_of_map hmap
  obtain ⟨r, hr, hQr⟩ :=
    (hermitianStar_eq_iff Q (congrTwist P S) hQ (congrTwist_hermitian P S hP)).1 heq
  have hcg : signature ((congrTwist P S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ) = signature (P : Matrix (Fin n) (Fin n) ℂ) := by
    rw [congrTwist_val]
    exact signature_congr _ _
  rw [hQr]
  rcases lt_trichotomy r 0 with hlt | he | hgt
  · refine Or.inr ?_
    rw [signature_real_smul_neg _ hlt, hcg]
  · exact absurd he hr
  · refine Or.inl ?_
    rw [signature_real_smul_pos _ hgt, hcg]

/-- **INEQUIVALENCE, as a usable tool.** If two Hermitian twists have signatures that are neither
equal nor each other's exchange, the ⋆-structures they present are NOT conjugate — not merely
different maps. This is the statement `StarStructureTwistFibre` and `HermitianRealForm` both
recorded as unearned. -/
theorem not_conjugate_of_signature_ne [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h1 : signature (Q : Matrix (Fin n) (Fin n) ℂ) ≠ signature (P : Matrix (Fin n) (Fin n) ℂ))
    (h2 : signature (Q : Matrix (Fin n) (Fin n) ℂ)
      ≠ (signature (P : Matrix (Fin n) (Fin n) ℂ)).swap) :
    ¬ Conjugate (hermitianStar P hP) (hermitianStar Q hQ) := fun h =>
  (signature_eq_or_swap_of_conjugate P Q hP hQ h).elim h1 h2

/-! ## The first inequivalent pair: computing the signature of `diag(1,-1)` -/

theorem realQuad_diagTwist_apply (x : Fin 2 → ℂ) :
    realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) x
      = Complex.normSq (x 0) - Complex.normSq (x 1) := by
  change realQuad (Matrix.diagonal ![(1 : ℂ), -1]) x = _
  simp only [realQuad_apply, dotProduct, Pi.star_apply, RCLike.star_def,
    Matrix.mulVec_diagonal, Fin.sum_univ_two]
  simp [Complex.normSq_apply]
  ring

/-- The `ℝ`-subspace of `Fin 2 → ℂ` on which coordinate `i` vanishes. -/
def coordKer (i : Fin 2) : Submodule ℝ (Fin 2 → ℂ) :=
  LinearMap.ker (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℝ] ℂ)

theorem mem_coordKer {i : Fin 2} {x : Fin 2 → ℂ} : x ∈ coordKer i ↔ x i = 0 := Iff.rfl

theorem finrank_coordKer (i : Fin 2) : Module.finrank ℝ (coordKer i) = 2 := by
  have hsurj : Function.Surjective (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℝ] ℂ) := by
    intro c
    exact ⟨Function.update (0 : Fin 2 → ℂ) i c, by simp⟩
  have hrange : LinearMap.range (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℝ] ℂ) = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  have h : Module.finrank ℝ (LinearMap.range (LinearMap.proj i : (Fin 2 → ℂ) →ₗ[ℝ] ℂ))
      + Module.finrank ℝ (coordKer i) = Module.finrank ℝ (Fin 2 → ℂ) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h2 : Module.finrank ℝ (⊤ : Submodule ℝ ℂ) = 2 := by
    rw [_root_.finrank_top]
    exact Complex.finrank_real_complex
  rw [hrange, h2, finrank_real_pi_complex] at h
  omega

theorem posDef_realQuad_diagTwist_one :
    ((realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)).restrict
      (coordKer 1)).PosDef := by
  intro x hx
  have hx1 : (x : Fin 2 → ℂ) 1 = 0 := x.2
  have hne : (x : Fin 2 → ℂ) ≠ 0 := by simpa [Submodule.coe_eq_zero] using hx
  have h0 : (x : Fin 2 → ℂ) 0 ≠ 0 := by
    intro h
    apply hne
    funext j
    fin_cases j <;> simp [h, hx1]
  simp only [QuadraticMap.restrict_apply, realQuad_diagTwist_apply, hx1]
  simpa using Complex.normSq_pos.2 h0

theorem nonpos_realQuad_diagTwist_zero (x : Fin 2 → ℂ) (hx : x ∈ coordKer 0) :
    realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) x ≤ 0 := by
  have hx0 : x 0 = 0 := hx
  rw [realQuad_diagTwist_apply, hx0]
  simpa using Complex.normSq_nonneg (x 1)

theorem posDef_neg_realQuad_diagTwist_zero :
    ((-realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℂ)).restrict (coordKer 0)).PosDef := by
  intro x hx
  have hx0 : (x : Fin 2 → ℂ) 0 = 0 := x.2
  have hne : (x : Fin 2 → ℂ) ≠ 0 := by simpa [Submodule.coe_eq_zero] using hx
  have h1 : (x : Fin 2 → ℂ) 1 ≠ 0 := by
    intro h
    apply hne
    funext j
    fin_cases j <;> simp [h, hx0]
  simp only [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, realQuad_diagTwist_apply, hx0]
  simpa using Complex.normSq_pos.2 h1

theorem nonpos_neg_realQuad_diagTwist_one (x : Fin 2 → ℂ) (hx : x ∈ coordKer 1) :
    (-realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
      Matrix (Fin 2) (Fin 2) ℂ)) x ≤ 0 := by
  have hx1 : x 1 = 0 := hx
  rw [QuadraticMap.neg_apply, realQuad_diagTwist_apply, hx1]
  simpa using Complex.normSq_nonneg (x 0)

/-- **The signature of `diag(1,-1)` is `(2, 2)`.** -/
theorem signature_diagTwist :
    signature ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) = (2, 2) := by
  have hdim : Module.finrank ℝ (Fin 2 → ℂ) = 4 := by
    rw [finrank_real_pi_complex]
  refine Prod.ext ?_ ?_
  · refine le_antisymm ?_ ?_
    · have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos
        (Q := realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))
        (V := coordKer 0) nonpos_realQuad_diagTwist_zero
      rw [finrank_coordKer, hdim] at h
      simpa using h
    · have h := le_sigPos_of_posDef
        (Q := realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))
        posDef_realQuad_diagTwist_one
      rw [finrank_coordKer] at h
      simpa using h
  · change _root_.sigNeg _ = 2
    rw [← sigPos_neg]
    refine le_antisymm ?_ ?_
    · have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos
        (Q := -realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))
        (V := coordKer 1) nonpos_neg_realQuad_diagTwist_one
      rw [finrank_coordKer, hdim] at h
      omega
    · have h := le_sigPos_of_posDef
        (Q := -realQuad ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))
        posDef_neg_realQuad_diagTwist_zero
      rw [finrank_coordKer] at h
      exact h

theorem signature_one_two :
    signature (((1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)) = (4, 0) := by
  have h : (((1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp
  rw [h, signature_one]

/-- **THE FIRST INEQUIVALENT PAIR THIS ESTATE HAS.** On `M₂(ℂ)` the conjugate transpose
`X ↦ Xᴴ` and the indefinite twist `X ↦ D Xᴴ D` for `D = diag(1,-1)` are **not conjugate** — not
merely different maps. Their signatures are `(4, 0)` and `(2, 2)`, which are neither equal nor
each other's exchange, and `signature_eq_or_swap_of_conjugate` rules the rest out. -/
theorem not_conjugate_conjTransposeStar_diagTwist :
    ¬ Conjugate (hermitianStar (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (by simp))
      (hermitianStar diagTwist diagTwist_hermitian) := by
  refine not_conjugate_of_signature_ne 1 diagTwist (by simp) diagTwist_hermitian ?_ ?_
  · rw [signature_diagTwist, signature_one_two]
    decide
  · rw [signature_diagTwist, signature_one_two]
    decide

/-- The same statement with the estate's own `conjTransposeStar` on the left. -/
theorem not_conjugate_conjTransposeStar :
    ¬ Conjugate (conjTransposeStar 2) (hermitianStar diagTwist diagTwist_hermitian) := by
  rw [← hermitianStar_one 2]
  exact not_conjugate_conjTransposeStar_diagTwist

/-! ## Conjugation by an ARBITRARY algebra automorphism -/

/-- Two ⋆-structures are conjugate when SOME algebra automorphism carries one to the other:
`t = α⁻¹ ∘ s ∘ α`. This is the notion the classification literature uses. -/
def ConjugateAlg (s t : StarStructure n) : Prop :=
  ∃ α : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ,
    ∀ X : Matrix (Fin n) (Fin n) ℂ, t.map X = α.symm (s.map (α X))

theorem conjugateAlg_refl (s : StarStructure n) : ConjugateAlg s s :=
  ⟨AlgEquiv.refl, fun X => by simp⟩

/-- **Conjugation by an arbitrary automorphism is conjugation by an INNER one**, because
`SkolemNoether.skolemNoether` says every automorphism of `Mₙ(ℂ)` is inner. So the inner notion
loses no generality and the negative results below are about the full relation. -/
theorem conjugate_of_conjugateAlg [NeZero n] (s t : StarStructure n)
    (h : ConjugateAlg s t) : Conjugate s t := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨S, hS⟩ := SkolemNoether.skolemNoether ℂ n α
  have h1 : (S : Matrix (Fin n) (Fin n) ℂ)
      * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
  have hsymm : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      α.symm Y = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
        * (S : Matrix (Fin n) (Fin n) ℂ) := by
    intro Y
    have hback : α (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
        * (S : Matrix (Fin n) (Fin n) ℂ)) = Y := by
      calc α (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
              * (S : Matrix (Fin n) (Fin n) ℂ))
          = (S : Matrix (Fin n) (Fin n) ℂ)
            * (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
              * (S : Matrix (Fin n) (Fin n) ℂ))
            * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := hS _
        _ = ((S : Matrix (Fin n) (Fin n) ℂ)
              * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) * Y
            * ((S : Matrix (Fin n) (Fin n) ℂ)
              * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
              noncomm_ring
        _ = Y := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [AlgEquiv.symm_apply_eq]
    exact hback.symm
  refine ⟨S, fun X => ?_⟩
  rw [hα X, hsymm, hS X]

/-- Conjugacy by an automorphism is symmetric: use `α⁻¹`. Without this the negative results
below would be about one direction only. -/
theorem conjugateAlg_symm {s t : StarStructure n} (h : ConjugateAlg s t) : ConjugateAlg t s := by
  obtain ⟨α, hα⟩ := h
  have key : ∀ Y : Matrix (Fin n) (Fin n) ℂ, α (t.map (α.symm Y)) = s.map Y := by
    intro Y
    have hY := hα (α.symm Y)
    rw [AlgEquiv.apply_symm_apply] at hY
    rw [hY, AlgEquiv.apply_symm_apply]
  refine ⟨α.symm, fun X => ?_⟩
  rw [AlgEquiv.symm_symm]
  exact (key X).symm

/-- **The first pair of ⋆-structures this estate can call INEQUIVALENT.** On `M₂(ℂ)` the
conjugate transpose and the indefinite twist `X ↦ D Xᴴ D`, `D = diag(1,-1)`, are not carried onto
one another by ANY algebra automorphism. -/
theorem not_conjugateAlg_conjTransposeStar_diagTwist :
    ¬ ConjugateAlg (conjTransposeStar 2) (hermitianStar diagTwist diagTwist_hermitian) := by
  intro h
  exact not_conjugate_conjTransposeStar (conjugate_of_conjugateAlg _ _ h)

/-- The same pair in the other direction, off `conjugateAlg_symm`, so *inequivalent* is
unambiguous rather than a statement about one ordering. -/
theorem not_conjugateAlg_diagTwist_conjTransposeStar :
    ¬ ConjugateAlg (hermitianStar diagTwist diagTwist_hermitian) (conjTransposeStar 2) :=
  fun h => not_conjugateAlg_conjTransposeStar_diagTwist (conjugateAlg_symm h)

end

end StarStructureInequivalent
