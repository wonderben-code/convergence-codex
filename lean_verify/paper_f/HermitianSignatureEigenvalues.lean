/-
  HermitianSignatureEigenvalues: the signature of ANY Hermitian twist, counted off its
  eigenvalues — and the form is non-degenerate exactly when the twist is invertible

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39104, item (1)'s residue, and `RE-SWEEP #58`'s
  measured target.

  WHERE THIS PICKS UP. Units 70 and 71 built the signature and used it, and both recorded the
  same limitation: **three values computed — at `1`, `-1` and `diag(1,-1)` — and no formula.**
  `RE-SWEEP #58` then found the route by grep rather than by reasoning, and wrote it down as a
  prediction: Mathlib's `Matrix.IsHermitian.spectral_theorem` conjugates any Hermitian matrix to
  a real diagonal one **by a UNITARY**, which is a congruence `HermitianRealForm.signature_congr`
  cannot see. **This file is that prediction carried out, and it held.**

  WHAT IS PROVED.
  * **`coordSupp`, `mem_coordSupp`, `finrank_coordSupp`** — the coordinate subspace machinery at
    full generality. For a `Finset S` of indices, the vectors supported on `S` form an
    `ℝ`-subspace of `Fin n → ℂ` of dimension **`2 · S.card`**. Unit 71 did this by hand for two
    singleton kernels in `Fin 2`; this is the general statement it was a special case of.
    ~~Proved by rank–nullity on `LinearMap.funLeft` restricted to the complement.~~
    **AMENDED 2026-09-16 (unit 77): that is no longer the proof, and the reason is a defect of
    this file's.** `RE-SWEEP #59` found that `coordSupp` was the estate's THIRD copy of one
    construction — `NullSpaceDimension.supportedOn` is the same thing over `ℝ` instead of `ℂ`,
    agreeing with it `mem_*` for `mem_*` and `finrank_*` for `finrank_*` — and
    `UNLOCK_WATCHLIST` L26329 is an item about the duplication, which this file did not check
    before adding to it. Both are now cases of `SupportedOn.finrank_supportedOn`, **one theorem
    at `#H · finrank W` with the codomain hypothesis removed**, and this file's proof is one
    `rw` where it was twenty-five lines. The statement is unchanged; `funLeft` is gone from the
    code and `Complex.finrank_real_complex` is where the `2` enters.
  * **`realQuad_diagonal_apply`** — for a REAL diagonal matrix the form is
    `x ↦ ∑ i, d i · ‖x i‖²`, which is where the whole computation lives.
  * **`posDef_realQuad_diagonal` and `nonpos_realQuad_diagonal`** — positive definite on the
    coordinates where `d` is positive, non-positive off them. No diagonalisation, no
    weighted-sum-of-squares presentation: the two inequalities are the argument.
  * **`sigPos_realQuad_diagonal` and `signature_diagonal`** — so
    `signature (diagonal d) = (2 · #{i | 0 < d i}, 2 · #{i | d i < 0})`, squeezed between
    `le_sigPos_of_posDef` and `QuadraticForm.sigPos_add_finrank_le_of_nonpos`. The negative half
    comes free by applying the positive half to `-d`.
  * **`signature_isHermitian`** — **THE FORMULA, for every Hermitian matrix**:

    > `signature P = (2 · #{i | 0 < λᵢ}, 2 · #{i | λᵢ < 0})` in the eigenvalues of `P`.

    `spectral_theorem` gives `P = U · diagonal λ · Uᴴ` with `U` unitary, so `Uᴴ P U = diagonal λ`,
    and `signature_congr` transports the count. **The doubling is the restriction of scalars and
    it is visible in the answer**, as it has been since unit 70.
  * **`signature_add_of_unit`** — and for an INVERTIBLE twist the two halves add to `2n`. The
    determinant is a unit, so no eigenvalue vanishes (`eigenvalues_ne_zero_of_unit`), so the
    positive and negative index sets partition `Fin n`. **`non-degenerate` was the watchlist's own
    word for the residue — *a non-degenerate Hermitian form up to scalars* — and it is now a
    theorem about every twist rather than a description of one.**

  WHAT IS **NOT** CLAIMED.
  * ~~**COMPLETENESS is still open, and it is now the only thing left of this residue.** Equal
    signature does not yet give conjugacy.~~ **CLOSED THE NEXT UNIT (74),**
    `HermitianSignatureComplete.conjugate_of_signature_eq`: **equal signature gives CONJUGATE
    ⋆-structures.** The two steps named below are `congruent_diagonal_signVec` and
    `congruent_diagonal_comp`, and **this bullet's route estimate was right, including which
    step carried the content** — the permutation did. One thing it got wrong in the cheap
    direction: the sign-matching needed NO nowhere-zero hypothesis, because `signVec` is total,
    and the linter reported the hypotheses unused before the proof was finished.
  * **No eigenvalue is computed.** The formula counts signs of `hP.eigenvalues`, which is
    Mathlib's noncomputable choice of an eigenvalue list; **nothing here evaluates it for a
    particular matrix**. Unit 71's `signature_diagTwist = (2,2)` is still the only non-definite
    value this estate has in hand, and it was obtained without the formula.
  * **Nothing over `ℝ` or `ℍ`**, and nothing about the cascade: `a·b·c = 16` keeps every
    alternative (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). A computable invariant of a ⋆-structure
    still prefers no factorisation of `M₁₆`.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import StarStructureInequivalent
import SupportedOn
import Mathlib.Analysis.Matrix.Spectrum

namespace HermitianSignatureEigenvalues

open Matrix HermitianRealForm

noncomputable section

variable {n : ℕ}

/-- The `ℝ`-subspace of `Fin n → ℂ` of vectors supported on a finite set of coordinates. -/
def coordSupp (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℂ) :=
  SupportedOn.supportedOn (R := ℝ) S

theorem mem_coordSupp {S : Finset (Fin n)} {x : Fin n → ℂ} :
    x ∈ coordSupp S ↔ ∀ i ∉ S, x i = 0 := Iff.rfl

/-- **AMENDED 2026-09-16 (unit 77).** This was proved here by rank–nullity on
`LinearMap.funLeft` over the complement. `RE-SWEEP #59` found that
`NullSpaceDimension.supportedOn` is the same construction over `ℝ` instead of `ℂ`, with
`mem_*` and `finrank_*` matching modulo the prefix, so both are now the `W = ℝ` and `W = ℂ`
cases of `SupportedOn.finrank_supportedOn` — **one theorem at `#H · finrank W`, with the
codomain hypothesis removed** (`PROOF_STRATEGY` §7 item 3). The statement is unchanged; the
`funLeft` argument is gone and `Complex.finrank_real_complex` is where the `2` now enters. -/
theorem finrank_coordSupp (S : Finset (Fin n)) :
    Module.finrank ℝ (coordSupp S) = 2 * S.card := by
  rw [coordSupp, SupportedOn.finrank_supportedOn, Complex.finrank_real_complex, mul_comm]

/-! ## The real form of a real diagonal matrix -/

theorem realQuad_diagonal_apply (d : Fin n → ℝ) (x : Fin n → ℂ) :
    realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) x
      = ∑ i, d i * Complex.normSq (x i) := by
  simp only [realQuad_apply, dotProduct, Pi.star_apply, RCLike.star_def,
    Matrix.mulVec_diagonal]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]
  ring

/-- On the coordinates where `d` is positive, the form is positive definite. -/
theorem posDef_realQuad_diagonal (d : Fin n → ℝ) :
    ((realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))).restrict
      (coordSupp (Finset.univ.filter fun i => 0 < d i))).PosDef := by
  intro x hx
  have hsupp : ∀ i ∉ Finset.univ.filter (fun i => 0 < d i), (x : Fin n → ℂ) i = 0 :=
    mem_coordSupp.1 x.2
  have hne : (x : Fin n → ℂ) ≠ 0 := by simpa [Submodule.coe_eq_zero] using hx
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hjS : j ∈ Finset.univ.filter (fun i => 0 < d i) := by
    by_contra hcon
    exact hj (hsupp j hcon)
  have hjd : 0 < d j := by simpa using hjS
  simp only [QuadraticMap.restrict_apply, realQuad_diagonal_apply]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · by_cases hi : i ∈ Finset.univ.filter (fun i => 0 < d i)
    · have : 0 < d i := by simpa using hi
      exact mul_nonneg this.le (Complex.normSq_nonneg _)
    · rw [hsupp i hi]
      simp
  · exact mul_pos hjd (Complex.normSq_pos.2 hj)

/-- Off those coordinates, the form is non-positive. -/
theorem nonpos_realQuad_diagonal (d : Fin n → ℝ) (x : Fin n → ℂ)
    (hx : x ∈ coordSupp (Finset.univ.filter fun i => 0 < d i)ᶜ) :
    realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))) x ≤ 0 := by
  have hsupp : ∀ i ∉ (Finset.univ.filter fun i => 0 < d i)ᶜ, x i = 0 := mem_coordSupp.1 hx
  rw [realQuad_diagonal_apply]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : i ∈ (Finset.univ.filter fun i => 0 < d i)ᶜ
  · have hd : d i ≤ 0 := by
      have : i ∉ Finset.univ.filter (fun i => 0 < d i) := Finset.mem_compl.1 hi
      simpa using this
    exact mul_nonpos_of_nonpos_of_nonneg hd (Complex.normSq_nonneg _)
  · rw [hsupp i hi]
    simp

/-! ## The signature of a real diagonal matrix, by counting signs -/

theorem sigPos_realQuad_diagonal (d : Fin n → ℝ) :
    _root_.sigPos (realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))))
      = 2 * (Finset.univ.filter fun i => 0 < d i).card := by
  have hcard : (Finset.univ.filter fun i => 0 < d i).card
      + (Finset.univ.filter fun i => 0 < d i)ᶜ.card = n := by
    rw [Finset.card_compl]
    have hle := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => 0 < d i)
    simp only [Finset.card_univ, Fintype.card_fin] at hle ⊢
    omega
  refine le_antisymm ?_ ?_
  · have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos
      (Q := realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))))
      (V := coordSupp (Finset.univ.filter fun i => 0 < d i)ᶜ)
      (nonpos_realQuad_diagonal d)
    rw [finrank_coordSupp, finrank_real_pi_complex] at h
    omega
  · have h := le_sigPos_of_posDef
      (Q := realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))))
      (posDef_realQuad_diagonal d)
    rwa [finrank_coordSupp] at h

/-- **The signature of a real diagonal matrix counts the signs of the diagonal**, doubled by the
restriction of scalars. -/
theorem signature_diagonal (d : Fin n → ℝ) :
    signature (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)))
      = (2 * (Finset.univ.filter fun i => 0 < d i).card,
         2 * (Finset.univ.filter fun i => d i < 0).card) := by
  refine Prod.ext (sigPos_realQuad_diagonal d) ?_
  change _root_.sigNeg _ = _
  rw [← sigPos_neg]
  have hneg : -(realQuad (Matrix.diagonal (fun i => ((d i : ℝ) : ℂ))))
      = realQuad (Matrix.diagonal (fun i => ((((-d) i) : ℝ) : ℂ))) := by
    rw [← realQuad_neg]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hfilter : (Finset.univ.filter fun i => 0 < (-d) i)
      = (Finset.univ.filter fun i => d i < 0) := by
    refine Finset.filter_congr fun i _ => ?_
    simp
  rw [hneg, sigPos_realQuad_diagonal, hfilter]

/-! ## The general formula, via the spectral theorem -/

/-- A unitary matrix as a unit of the matrix ring. -/
def unitaryUnit (U : Matrix.unitaryGroup (Fin n) ℂ) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := (U : Matrix (Fin n) (Fin n) ℂ)
  inv := (U : Matrix (Fin n) (Fin n) ℂ)ᴴ
  val_inv := by
    have h := U.2
    rw [Matrix.mem_unitaryGroup_iff] at h
    rwa [← Matrix.star_eq_conjTranspose]
  inv_val := by
    have h := U.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [← Matrix.star_eq_conjTranspose]

@[simp] theorem unitaryUnit_val (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ((unitaryUnit U : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = (U : Matrix (Fin n) (Fin n) ℂ) := rfl

/-- **The spectral theorem as a CONGRUENCE.** `Uᴴ P U` is the real diagonal of `P`'s
eigenvalues, for `U` the eigenvector unitary. **Exported rather than left inside
`signature_isHermitian`'s proof** so that unit 74 can consume it instead of re-deriving it —
`ERRATUM 348`'s rule, that logic nobody can call gets rewritten badly by the next person who
needs it. -/
theorem conjTranspose_mul_mul_eq_diagonal (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    ((unitaryUnit hP.eigenvectorUnitary : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)ᴴ * P
      * ((unitaryUnit hP.eigenvectorUnitary : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal (fun i => ((hP.eigenvalues i : ℝ) : ℂ)) := by
  have hmul : (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ
      * (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have h := hP.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [← Matrix.star_eq_conjTranspose]
  have hspec := hP.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstep := congrArg
    (fun A => (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ * A
      * (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) hspec
  simp only at hstep
  rw [unitaryUnit_val, hstep, ← Matrix.star_eq_conjTranspose]
  calc star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        * ((hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
          * Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
          * star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))
        * (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      = (star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
          * (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))
        * Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
        * (star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
          * (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by noncomm_ring
    _ = Matrix.diagonal (fun i => ((hP.eigenvalues i : ℝ) : ℂ)) := by
        rw [Matrix.star_eq_conjTranspose, hmul, Matrix.one_mul, Matrix.mul_one]
        rfl

/-- **THE SIGNATURE OF ANY HERMITIAN MATRIX COUNTS THE SIGNS OF ITS EIGENVALUES**, doubled.
The spectral theorem conjugates `P` to a real diagonal matrix by a UNITARY, which is a
congruence `HermitianRealForm.signature_congr` cannot see. -/
theorem signature_isHermitian (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    signature P
      = (2 * (Finset.univ.filter fun i => 0 < hP.eigenvalues i).card,
         2 * (Finset.univ.filter fun i => hP.eigenvalues i < 0).card) := by
  rw [← signature_congr P (unitaryUnit hP.eigenvectorUnitary),
    conjTranspose_mul_mul_eq_diagonal P hP, signature_diagonal]

/-! ## For an invertible twist the form is non-degenerate -/

theorem eigenvalues_ne_zero_of_unit (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ).IsHermitian) (i : Fin n) :
    hP.eigenvalues i ≠ 0 := by
  intro h
  have hdet : (P : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _ |>.1 P.isUnit).ne_zero
  rw [hP.det_eq_prod_eigenvalues] at hdet
  exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h]))

/-- **The signature of an INVERTIBLE Hermitian twist fills the whole dimension**: `sigPos` and
`sigNeg` add to `2n`, so the real form is non-degenerate. That is the word the watchlist used for
the residue — *a NON-DEGENERATE Hermitian form up to scalars* — now a theorem about every twist
rather than a description. -/
theorem signature_add_of_unit (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ).IsHermitian) :
    (signature (P : Matrix (Fin n) (Fin n) ℂ)).1
      + (signature (P : Matrix (Fin n) (Fin n) ℂ)).2 = 2 * n := by
  have hcount : (Finset.univ.filter fun i => 0 < hP.eigenvalues i).card
      + (Finset.univ.filter fun i => hP.eigenvalues i < 0).card = n := by
    have hdisj : Disjoint (Finset.univ.filter fun i => 0 < hP.eigenvalues i)
        (Finset.univ.filter fun i => hP.eigenvalues i < 0) := by
      refine Finset.disjoint_left.2 fun i hi hi' => ?_
      have h1 : 0 < hP.eigenvalues i := by simpa using hi
      have h2 : hP.eigenvalues i < 0 := by simpa using hi'
      linarith
    have hunion : (Finset.univ.filter fun i => 0 < hP.eigenvalues i)
        ∪ (Finset.univ.filter fun i => hP.eigenvalues i < 0) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun i => ?_
      rcases lt_trichotomy (hP.eigenvalues i) 0 with hlt | heq | hgt
      · exact Finset.mem_union_right _ (by simpa using hlt)
      · exact absurd heq (eigenvalues_ne_zero_of_unit P hP i)
      · exact Finset.mem_union_left _ (by simpa using hgt)
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion] at this
    simpa using this.symm
  rw [signature_isHermitian _ hP]
  simp only
  omega

end

end HermitianSignatureEigenvalues
