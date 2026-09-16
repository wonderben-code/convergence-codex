/-
  HermitianSignatureComplete: equal signature implies CONJUGATE — the ⋆-structure classification
  on `Mₙ(ℂ)` closed up to the one exchange that cannot be removed

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39104, item (1)'s residue. **This is the last piece.**

  WHERE THIS PICKS UP. Four units narrowed one question and each left the same thing behind.
  Unit 69 computed the fibre of `P ↦ s_P`; unit 70 built the signature and proved it
  congruence-invariant; unit 71 proved two ⋆-structures on `M₂(ℂ)` inequivalent; unit 73 gave the
  signature of every twist as a count of eigenvalue signs. All four recorded **completeness** as
  open, in the same words: *equal signature does not yet give conjugacy*. The route was named in
  unit 73's header — normalise the diagonal to `±1`, then permute — with the permutation called
  **the step with real content**. That estimate was right.

  WHAT IS PROVED.
  * **`Congruent` with `refl`, `symm`, `trans`** — the relation the signature is an invariant of,
    named at last. `signature_eq_of_congruent` is unit 70's `signature_congr` read through it.
    **The estate has used congruence for three units without having the word** — unit 70's
    `signature_congr` and `realQuad_congr_apply`, unit 71's `congrTwist` family, unit 73's
    `conjTranspose_mul_mul_eq_diagonal`, all carrying the `Sᴴ · - · S` shape and none naming it
    — which is why the transitivity chain at the end of this file could not be written before.
    **THREE, not four**: unit 69 is the one unit of this chain that never used a congruence, and
    the first draft of this sentence said four by counting the units in the chain rather than the
    units that used the thing. `estateclaim_scan` asked for the query, and the query answered a
    different number.
  * **`congruent_diagonal_signVec`** — **normalisation.** A nowhere-zero real diagonal is
    congruent to its own sign pattern, by the real diagonal congruence `diag(|dᵢ|^{-1/2})`. The
    scaling is a `diagUnit`, and the two sign cases are `inv_mul_cancel₀` and its negation.
  * **`congruent_diagonal_comp`** — **permutation.** Reindexing a diagonal by a permutation is a
    congruence, via `Equiv.Perm.permMatrix` as a `permUnit` and the two `PEquiv` identities
    `toMatrix_toPEquiv_mul` and `mul_toMatrix_toPEquiv`, which turn the double product into a
    `submatrix` and then `submatrix_diagonal_equiv` finishes it. **No entrywise computation.**
  * **`exists_perm_signVec_eq`** — **the matching, and it needed LESS than expected.** Two real
    vectors with the same number of positive entries have the same sign pattern up to a
    permutation: glue a bijection of the positive index sets to one of their complements through
    `Equiv.sumCompl`. **The nowhere-zero hypotheses were written and then removed — the linter
    reported them unused, and it was right**: `signVec` is total, so the matching holds for any
    two real vectors whatever. That is one hypothesis fewer than the route predicted.
  * **`congruent_signVec_of_unit`** — every invertible Hermitian matrix is congruent to a `±1`
    diagonal, by composing normalisation with unit 73's spectral congruence. That lemma was
    **exported from unit 73's proof in this unit** rather than re-derived here, which is
    `ERRATUM 348`'s rule.
  * **`congruent_of_signature_eq`** — **EQUAL SIGNATURE IMPLIES CONGRUENT.** Equal signature gives
    equal positive-eigenvalue counts by unit 73's formula; the matching gives a permutation; and
    the chain `P ~ diag(sign λ_P) ~ diag(sign λ_Q) ~ Q` runs through `Congruent.trans`.
  * **`conjugate_of_signature_eq`** — **and so the signature is a COMPLETE invariant.** Equal
    signature gives CONJUGATE ⋆-structures, off unit 71's `hermitianStar_congrTwist`. With unit
    71's `signature_eq_or_swap_of_conjugate` in the other direction, the classification of
    ⋆-structures on `Mₙ(ℂ)` is closed **up to exchanging the signature's two halves, which unit
    70's `hermitianStar_neg` proves cannot be removed.**

  WHAT IS **NOT** CLAIMED.
  * ~~**The two directions are not yet packaged as one `iff`**, and their hypotheses differ: this
    file's forward direction takes `IsHermitian` and equality on the nose, while unit 71's
    converse delivers *equal or exchanged*. Composing them into a single statement about
    `ℝˣ`-orbits is bookkeeping and is not done here.~~ **PACKAGED THE NEXT UNIT (75),**
    `HermitianSignatureClassification.conjugate_iff_signature` and
    `conjugate_iff_usignature`. **AND THIS BULLET UNDERPRICED IT — it is not bookkeeping.**
    Matching the sides needs the EXCHANGED case of the forward direction, which this file does
    not prove: `conjugate_of_signature_swap`, off `hermitianStar_neg` and the new
    `signature_neg`. Without that one theorem the `iff` is false as stated. The target also
    turned out to be `Sym2 ℕ` rather than a quotient by `RealScalarRel`: an unordered pair IS
    the quotient the exchange forces, and `Sym2.mk_eq_mk_iff` turns *equal or exchanged* into
    EQUALITY, so both sides of the classification became equalities without a quotient type
    being built at all.
  * **No eigenvalue is EVALUATED anywhere in this chain.** The completeness proof consumes
    eigenvalue SIGN COUNTS and never a value, so `StarStructureInequivalent.signature_diagTwist`
    remains the only non-definite signature this estate has computed.
  * ~~**Nothing is proved about how many ⋆-structures there are.** Completeness says the
    signature separates them; it does not count the achievable signatures, which would need a
    twist exhibited at every `(p, q)` with `p + q = n`. **None is exhibited beyond `±1` and
    `diag(1,-1)`.**~~ **COUNTED THE NEXT UNIT (75)**, and **this bullet named the missing piece
    correctly**: `HermitianSignatureClassification.setTwist` exhibits a `±1` twist at every
    signature, indexed by a `Finset` rather than by a threshold so that the count needs no
    counting argument, and `card_achievable` gives **`n/2 + 1` ⋆-structures on `Mₙ(ℂ)` up to
    conjugacy** — two on `M₂(ℂ)`, which makes unit 71's inequivalent pair the `n = 2` case of a
    count rather than an example.
  * **Nothing over `ℝ` or `ℍ`.** The spectral theorem used is the complex one, and the whole
    chain rests on `U` being unitary hence `ℂ`-linear — which is exactly why the real inertia
    law could not be run backwards (`RE-SWEEP #58`).
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). **A closed classification of ⋆-structures on
    `Mₙ(ℂ)` still prefers no factorisation of `M₁₆`** — it says what the objects are, not which
    one the cascade supplies.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import HermitianSignatureEigenvalues
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace HermitianSignatureComplete

open Matrix HermitianRealForm StarStructureInequivalent HermitianSignatureEigenvalues

noncomputable section

variable {n : ℕ}

/-- Two matrices are CONGRUENT when an invertible `S` carries one to the other as `Sᴴ · - · S`.
This is the relation the signature is an invariant of. -/
def Congruent (P Q : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ,
    P = (S : Matrix (Fin n) (Fin n) ℂ)ᴴ * Q * (S : Matrix (Fin n) (Fin n) ℂ)

theorem Congruent.refl (P : Matrix (Fin n) (Fin n) ℂ) : Congruent P P :=
  ⟨1, by simp⟩

theorem Congruent.symm {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Congruent P Q) : Congruent Q P := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S⁻¹, ?_⟩
  have h1 : ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      * (S : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul]
    simp
  have h2 : (S : Matrix (Fin n) (Fin n) ℂ)
      * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
  calc Q = 1 * Q * 1 := by simp
    _ = (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
          * (S : Matrix (Fin n) (Fin n) ℂ)ᴴ) * Q
        * ((S : Matrix (Fin n) (Fin n) ℂ)
          * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
          rw [h1, h2]
    _ = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
        * ((S : Matrix (Fin n) (Fin n) ℂ)ᴴ * Q * (S : Matrix (Fin n) (Fin n) ℂ))
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by noncomm_ring
    _ = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * P
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hS]

theorem Congruent.trans {P Q R : Matrix (Fin n) (Fin n) ℂ}
    (h₁ : Congruent P Q) (h₂ : Congruent Q R) : Congruent P R := by
  obtain ⟨S, hS⟩ := h₁
  obtain ⟨T, hT⟩ := h₂
  refine ⟨T * S, ?_⟩
  rw [hS, hT]
  simp only [Units.val_mul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- Congruent matrices have the same signature — this is `signature_congr` read through the
relation. -/
theorem signature_eq_of_congruent {P Q : Matrix (Fin n) (Fin n) ℂ} (h : Congruent P Q) :
    signature P = signature Q := by
  obtain ⟨S, hS⟩ := h
  rw [hS]
  exact signature_congr Q S

/-! ## Normalising a real diagonal to signs -/

/-- An invertible diagonal matrix, as a unit. -/
def diagUnit (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := Matrix.diagonal c
  inv := Matrix.diagonal (fun i => (c i)⁻¹)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [mul_inv_cancel₀ (hc i)]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [inv_mul_cancel₀ (hc i)]

@[simp] theorem diagUnit_val (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0) :
    ((diagUnit c hc : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal c := rfl

/-- The sign vector of a nowhere-zero real vector. -/
def signVec (d : Fin n → ℝ) : Fin n → ℝ := fun i => if 0 < d i then 1 else -1

theorem signVec_pos_iff (d : Fin n → ℝ) (i : Fin n) : 0 < signVec d i ↔ 0 < d i := by
  unfold signVec
  by_cases h : 0 < d i <;> simp [h]

theorem signVec_neg_iff (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (i : Fin n) :
    signVec d i < 0 ↔ d i < 0 := by
  unfold signVec
  by_cases h : 0 < d i
  · rw [if_pos h]
    constructor
    · intro hc; linarith
    · intro hc; linarith
  · rw [if_neg h]
    refine ⟨fun _ => lt_of_le_of_ne (not_lt.1 h) (hd i), fun _ => by norm_num⟩

/-- **Every nowhere-zero real diagonal is congruent to its sign pattern.** Rescale each
coordinate by `|d i|^(-1/2)`, which is a real diagonal congruence. -/
theorem congruent_diagonal_signVec (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    Congruent (Matrix.diagonal (fun i => ((signVec d i : ℝ) : ℂ)))
      (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) := by
  have habs : ∀ i, (0 : ℝ) < |d i| := fun i => abs_pos.2 (hd i)
  have hcne : ∀ i, (((Real.sqrt |d i|)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    intro i
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact Real.sqrt_ne_zero'.2 (habs i)
  refine ⟨diagUnit (fun i => (((Real.sqrt |d i|)⁻¹ : ℝ) : ℂ)) hcne, ?_⟩
  rw [diagUnit_val, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have hsq : (Real.sqrt |d i|)⁻¹ * (Real.sqrt |d i|)⁻¹ = (|d i|)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (le_of_lt (habs i))]
  have hkey : (Real.sqrt |d i|)⁻¹ * d i * (Real.sqrt |d i|)⁻¹ = signVec d i := by
    have : (Real.sqrt |d i|)⁻¹ * d i * (Real.sqrt |d i|)⁻¹
        = ((Real.sqrt |d i|)⁻¹ * (Real.sqrt |d i|)⁻¹) * d i := by ring
    rw [this, hsq]
    unfold signVec
    by_cases h : 0 < d i
    · rw [if_pos h, abs_of_pos h]
      exact inv_mul_cancel₀ (hd i)
    · have hneg : d i < 0 := lt_of_le_of_ne (not_lt.1 h) (hd i)
      rw [if_neg h, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ (hd i)]
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hkey]

/-! ## Permuting a diagonal is a congruence -/

/-- A permutation matrix, as a unit. -/
def permUnit (σ : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := Equiv.Perm.permMatrix ℂ σ
  inv := Equiv.Perm.permMatrix ℂ σ⁻¹
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

@[simp] theorem permUnit_val (σ : Equiv.Perm (Fin n)) :
    ((permUnit σ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Equiv.Perm.permMatrix ℂ σ := rfl

/-- **Reindexing a diagonal by a permutation is a congruence.** -/
theorem congruent_diagonal_comp (d : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    Congruent (Matrix.diagonal (d ∘ σ)) (Matrix.diagonal d) := by
  refine ⟨permUnit σ⁻¹, ?_⟩
  rw [permUnit_val, Matrix.conjTranspose_permMatrix, inv_inv]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rw [show ((σ⁻¹ : Equiv.Perm (Fin n)).symm) = σ from rfl]
  simp only [Function.comp_id, Function.id_comp]
  rw [Matrix.submatrix_diagonal_equiv]

/-! ## Matching two sign patterns of equal count -/

/-- **Two nowhere-zero real vectors with the same number of positive entries have the same sign
pattern up to a PERMUTATION.** Glued from a bijection of the positive index sets and one of their
complements, through `Equiv.sumCompl`. -/
theorem exists_perm_signVec_eq (d e : Fin n → ℝ)
    (hcard : (Finset.univ.filter fun i => 0 < d i).card
      = (Finset.univ.filter fun i => 0 < e i).card) :
    ∃ σ : Equiv.Perm (Fin n), signVec d ∘ σ = signVec e := by
  classical
  have h1 : Fintype.card {i : Fin n // 0 < e i} = Fintype.card {i : Fin n // 0 < d i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hcard.symm
  have h2 : Fintype.card {i : Fin n // ¬ 0 < e i} = Fintype.card {i : Fin n // ¬ 0 < d i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e₁ := Fintype.equivOfCardEq h1
  let e₂ := Fintype.equivOfCardEq h2
  refine ⟨(Equiv.sumCompl (fun i => 0 < e i)).symm.trans
    ((e₁.sumCongr e₂).trans (Equiv.sumCompl (fun i => 0 < d i))), ?_⟩
  funext i
  by_cases hi : 0 < e i
  · have hstep : ((Equiv.sumCompl (fun i => 0 < e i)).symm.trans
        ((e₁.sumCongr e₂).trans (Equiv.sumCompl (fun i => 0 < d i)))) i
        = ((e₁ ⟨i, hi⟩ : {i : Fin n // 0 < d i}) : Fin n) := by
      have hs : (Equiv.sumCompl (fun j => 0 < e j)).symm i = Sum.inl ⟨i, hi⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun j => 0 < e j) (a := i) hi
      rw [Equiv.trans_apply, Equiv.trans_apply, hs]
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    simp only [Function.comp_apply, hstep]
    unfold signVec
    rw [if_pos (e₁ ⟨i, hi⟩).2, if_pos hi]
  · have hstep : ((Equiv.sumCompl (fun i => 0 < e i)).symm.trans
        ((e₁.sumCongr e₂).trans (Equiv.sumCompl (fun i => 0 < d i)))) i
        = ((e₂ ⟨i, hi⟩ : {i : Fin n // ¬ 0 < d i}) : Fin n) := by
      have hs : (Equiv.sumCompl (fun j => 0 < e j)).symm i = Sum.inr ⟨i, hi⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun j => 0 < e j) (a := i) hi
      rw [Equiv.trans_apply, Equiv.trans_apply, hs]
      simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp only [Function.comp_apply, hstep]
    unfold signVec
    rw [if_neg (e₂ ⟨i, hi⟩).2, if_neg hi]

/-! ## Completeness -/

theorem congruent_diagonal_eigenvalues (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    Congruent (Matrix.diagonal (fun i => ((hP.eigenvalues i : ℝ) : ℂ))) P :=
  ⟨unitaryUnit hP.eigenvectorUnitary,
    (HermitianSignatureEigenvalues.conjTranspose_mul_mul_eq_diagonal P hP).symm⟩

/-- **Every INVERTIBLE Hermitian matrix is congruent to a `±1` diagonal.** -/
theorem congruent_signVec_of_unit (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ).IsHermitian) :
    Congruent (Matrix.diagonal (fun i => ((signVec hP.eigenvalues i : ℝ) : ℂ)))
      (P : Matrix (Fin n) (Fin n) ℂ) :=
  (congruent_diagonal_signVec hP.eigenvalues
      (HermitianSignatureEigenvalues.eigenvalues_ne_zero_of_unit P hP)).trans
    (congruent_diagonal_eigenvalues _ hP)

/-- **EQUAL SIGNATURE IMPLIES CONGRUENT.** The converse of `signature_eq_of_congruent`, and the
piece units 70, 71 and 73 all recorded as open. -/
theorem congruent_of_signature_eq (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ).IsHermitian)
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ).IsHermitian)
    (h : signature (P : Matrix (Fin n) (Fin n) ℂ) = signature (Q : Matrix (Fin n) (Fin n) ℂ)) :
    Congruent (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) := by
  have hcount : (Finset.univ.filter fun i => 0 < hP.eigenvalues i).card
      = (Finset.univ.filter fun i => 0 < hQ.eigenvalues i).card := by
    have hp := HermitianSignatureEigenvalues.signature_isHermitian
      (P : Matrix (Fin n) (Fin n) ℂ) hP
    have hq := HermitianSignatureEigenvalues.signature_isHermitian
      (Q : Matrix (Fin n) (Fin n) ℂ) hQ
    rw [hp, hq] at h
    have := (Prod.ext_iff.1 h).1
    omega
  obtain ⟨σ, hσ⟩ := exists_perm_signVec_eq hP.eigenvalues hQ.eigenvalues hcount
  have hperm : Congruent
      (Matrix.diagonal (fun i => ((signVec hQ.eigenvalues i : ℝ) : ℂ)))
      (Matrix.diagonal (fun i => ((signVec hP.eigenvalues i : ℝ) : ℂ))) := by
    have hcomp : (fun i => ((signVec hP.eigenvalues i : ℝ) : ℂ)) ∘ σ
        = (fun i => ((signVec hQ.eigenvalues i : ℝ) : ℂ)) := by
      funext i
      have := congrFun hσ i
      simp only [Function.comp_apply] at this ⊢
      rw [this]
    have := congruent_diagonal_comp (fun i => ((signVec hP.eigenvalues i : ℝ) : ℂ)) σ
    rwa [hcomp] at this
  exact ((congruent_signVec_of_unit P hP).symm.trans hperm.symm).trans
    (congruent_signVec_of_unit Q hQ)

/-- **AND SO THE SIGNATURE IS A COMPLETE INVARIANT.** Equal signature gives CONJUGATE
⋆-structures, which with `StarStructureInequivalent.signature_eq_or_swap_of_conjugate` closes the
classification up to the exchange that `hermitianStar_neg` shows is unavoidable. -/
theorem conjugate_of_signature_eq [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : signature (P : Matrix (Fin n) (Fin n) ℂ) = signature (Q : Matrix (Fin n) (Fin n) ℂ)) :
    Conjugate (StarStructureTwistFibre.hermitianStar Q hQ)
      (StarStructureTwistFibre.hermitianStar P hP) := by
  obtain ⟨S, hS⟩ := congruent_of_signature_eq P Q hP hQ h
  have hPQ : P = congrTwist Q S := Units.ext (by rw [hS, congrTwist_val])
  subst hPQ
  exact conjugate_hermitianStar_congrTwist Q S hQ

end

end HermitianSignatureComplete
