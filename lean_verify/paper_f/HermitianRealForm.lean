/-
  HermitianRealForm: the signature, constructed — and the ⋆-structure determines it up to
  exchanging its two halves

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39104, item (1)'s residue: *the signature of `P`*.

  WHERE THIS PICKS UP. `StarStructureTwistFibre` (the unit before this one) computed the fibre of
  `P ↦ s_P` and then listed, as the larger half of what it had not done: **the signature is still
  not computed, no invariant is constructed, and the separation of two ⋆-structures is as MAPS and
  not up to conjugation.** It also measured what the missing step needed — Mathlib has both halves
  of Sylvester's law of inertia and this estate already uses that API, but **0 estate declarations
  name both a quadratic form and `IsHermitian` or `conjTranspose`**, so the bridge was bespoke work
  rather than a citation.

  **The bridge is built here, the invariant is constructed, and it is computed in two cases.** The
  conjugation leg is still open; §"WHAT IS NOT CLAIMED" writes out its algebra rather than
  gesturing at it, because it is now the shortest remaining step.

  WHAT IS PROVED.
  * **`realBilin`, `realBilin_symm`, `realQuad`** — **THE BRIDGE THAT WAS MEASURED ABSENT.** A
    Hermitian form is sesquilinear, so it is not `QuadraticMap.restrictScalars` of anything; the
    passage is to the underlying REAL space. `realBilin P x y = re ⟪x, P y⟫` is an `ℝ`-bilinear
    form on `Fin n → ℂ`, **symmetric exactly where `P` is Hermitian** (`realBilin_symm`, the one
    place `Pᴴ = P` is spent in this file), and `LinearMap.BilinMap.toQuadraticMap` makes it a
    `QuadraticForm ℝ`. From that line onward Mathlib's `sigPos` and `sigNeg` apply unchanged.
  * **`equivalent_smul_of_pos`** — **the crux, and it is one idea.** For `r > 0` the form `r • Q`
    is ISOMETRIC to `Q`: rescale the vector by `√r`, because a quadratic form has degree two. So
    `sigPos` and `sigNeg` cannot see a positive rescaling (`sigPos_smul_of_pos`,
    `sigNeg_smul_of_pos`). **This is what makes a signature well defined on the `ℝˣ`-orbit the
    previous unit computed**, and it needs no diagonalisation — the two facts fit together with
    nothing in between.
  * **`signature`** — the invariant itself: `(sigPos, sigNeg)` of the real form of `P`.
  * **`signature_real_smul_pos` and `signature_real_smul_neg`** — a positive rescaling leaves it
    alone; a NEGATIVE one EXCHANGES the halves, off Mathlib's `sigPos_neg` and `sigNeg_neg`.
  * **`signature_eq_or_swap_of_star_eq`** — **the theorem this chain was for**: two Hermitian
    twists presenting the same ⋆-structure have the same signature, or the exchanged one. The
    previous unit's fibre supplies the real scalar; the trichotomy on its sign supplies the two
    cases and nothing else is needed.
  * **`signature_one` and `signature_neg_one`** — **two COMPUTED values**, `(2n, 0)` and `(0, 2n)`,
    off `sigPos_eq_finrank_of_posDef` and `sigPos_eq_zero_of_neg` (both proved here from Mathlib's
    `sigPos_isGreatest`) together with `finrank_real_pi_complex : finrank ℝ (Fin n → ℂ) = 2n`.
    **The doubling is the restriction of scalars and it is visible in the answer** — a Hermitian
    signature `(p, q)` appears here as `(2p, 2q)`, exactly as the previous unit predicted it would.
  * **`star_eq_but_signature_ne`** — **and the exchange is REALISED, not a hedge.** For `n ≥ 1` the
    identity twist and its negative present the SAME ⋆-structure — that is the previous unit's
    `hermitianStar_neg` — and have DIFFERENT signatures, each other's exchange. **So no
    ORDERED-pair invariant of a ⋆-structure on `Mₙ(ℂ)` exists**, and the theorem above is as sharp
    as a statement of its kind can be.
  * **`signature_congr`** — **CONGRUENCE INVARIANCE.** `Sᴴ P S` has the same signature as `P`, for
    every invertible `S`, via `mulVecEquivR` (multiplication by `S` as an `ℝ`-linear equivalence)
    and `realQuad_congr_apply`. **This is what makes the pair a signature rather than a coordinate
    artefact**, and it is the half of the inertia law this development actually consumes — as
    Mathlib's `QuadraticMap.Equivalent.sigPos_eq` applied to a change of basis.

  WHAT IS **NOT** CLAIMED.
  * **The invariant is not COMPLETE, and it is not.** Equal signature does not give equal
    ⋆-structure: two Hermitian forms of the same signature are CONGRUENT, not equal, and by the
    previous unit's fibre a congruent twist `Sᴴ P S` presents the same ⋆-structure only when it is
    a real multiple of `P`, which is false for generic `S`. **So `signature_eq_or_swap_of_star_eq`
    runs one way and the converse is not available at this strength.**
  * **NO TWO ⋆-STRUCTURES ARE SHOWN INEQUIVALENT.** This is the leg that is now shortest, so the
    algebra is written down rather than described. Conjugating by the inner automorphism
    `α X = S X S⁻¹` replaces the Hermitian twist by `Sᴴ P S`: from `s X = (P X P⁻¹)ᴴ` one computes
    `α⁻¹ (s (α X)) = S⁻¹ ((P S) X (P S)⁻¹)ᴴ S = (Q⁻¹)ᴴ Xᴴ Qᴴ` with `Q = Sᴴ P S`, using that `P`
    and `P⁻¹` are Hermitian. **`signature_congr` is exactly the invariance that statement needs**,
    and `SkolemNoether.skolemNoether` — this estate's own — says every automorphism of `Mₙ(ℂ)` is
    inner, so taking `α` inner costs no generality. ~~**What is missing is the bookkeeping, not
    the mathematics.** Until it is a theorem, *inequivalent* is not a word this estate has
    earned.~~ **WRITTEN THE NEXT UNIT (71), AND THE ESTIMATE HELD.**
    `StarStructureInequivalent.hermitianStar_congrTwist` is the identity above, proved by
    conjugate-transposing both twists and `noncomm_ring`; `conjugate_of_conjugateAlg` turns the
    *costs no generality* remark into a theorem off `SkolemNoether.skolemNoether`;
    `conjugateAlg_symm` makes the relation symmetric so the word means what it should; and
    `not_conjugateAlg_conjTransposeStar_diagTwist` exhibits **two ⋆-structures on `M₂(ℂ)` that no
    algebra automorphism relates**, at signatures `(4, 0)` and `(2, 2)`. The bullet below is the
    one that moved with it — `diagTwist`'s signature is now computed.
  * ~~**The signature is computed at `±1` and nowhere else.**~~ **AMENDED (unit 71):
    `diagTwist`'s signature IS computed, `(2, 2)`, and the route this bullet named is not the one
    that worked.** `sigPos_of_equiv_weightedSumSquares` wants a weighted-sum-of-squares
    presentation, and none was built: `StarStructureInequivalent.signature_diagTwist` squeezes
    `sigPos` between `le_sigPos_of_posDef` on one coordinate kernel and
    `QuadraticForm.sigPos_add_finrank_le_of_nonpos` on the other, both of dimension 2 by
    rank–nullity. ~~**Three values are computed in all as of 2026-09-16** — at `1`, `-1` and
    `diag(1,-1)` — and no formula for a general twist, which still needs a diagonalisation.~~
    **THE FORMULA LANDED IN UNIT 73**, `HermitianSignatureEigenvalues.signature_isHermitian`:
    for every Hermitian `P`, `signature P = (2 · #{i | 0 < λᵢ}, 2 · #{i | λᵢ < 0})` in its
    eigenvalues, off Mathlib's `spectral_theorem` and this file's `signature_congr`. **And the
    prediction in this bullet was wrong in the useful direction**: it said a diagonalisation was
    needed, and one is — but Mathlib supplies it, and `RE-SWEEP #58` found that by grep rather
    than by reasoning. `signature_add_of_unit` adds that an INVERTIBLE twist's two halves sum to
    `2n`, so the form is non-degenerate, which was the watchlist's own word for the residue.
  * **Nothing over `ℝ` or `ℍ`.** The real form is taken OF a complex matrix; no real or
    quaternionic ⋆-structure appears.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). An invariant that exists and is not yet known to
    separate anything prefers no factorisation.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import StarStructureTwistFibre
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace HermitianRealForm

open Matrix

noncomputable section

variable {n : ℕ}

/-- The real bilinear form of a complex matrix: `(x, y) ↦ re ⟪x, P y⟫`. -/
def realBilin (P : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (star x ⬝ᵥ (P *ᵥ y)).re)
    (by intro x x' y; simp [star_add, add_dotProduct])
    (by
      intro r x y
      simp only [star_smul, smul_dotProduct, RCLike.star_def]
      simp)
    (by intro x y y'; simp [Matrix.mulVec_add, dotProduct_add])
    (by
      intro r x y
      simp only [Matrix.mulVec_smul, dotProduct_smul]
      simp)

@[simp] theorem realBilin_apply (P : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    realBilin P x y = (star x ⬝ᵥ (P *ᵥ y)).re := rfl

/-- **The form of a HERMITIAN matrix is symmetric.** Without this the object above would be the
real part of an arbitrary sesquilinear form; with it, it is a real symmetric bilinear form, which
is what a signature is an invariant of. -/
theorem realBilin_symm (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : Pᴴ = P) (x y : Fin n → ℂ) :
    realBilin P y x = realBilin P x y := by
  have hconj : (star y ⬝ᵥ (P *ᵥ x)) = (starRingEnd ℂ) (star x ⬝ᵥ (P *ᵥ y)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
      Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : (starRingEnd ℂ) (P j i) = P i j := by
      have hij := congrFun (congrFun hP i) j
      simpa [Matrix.conjTranspose_apply, RCLike.star_def] using hij
    rw [← h]
    simp only [Complex.conj_conj]
    ring
  rw [realBilin_apply, realBilin_apply, hconj]
  simp

/-! ## Scaling by a positive real is an isometry -/

/-- **Scaling a real quadratic form by a POSITIVE scalar gives an EQUIVALENT form**: rescale the
vector by the square root. This is the crux — it is what makes the signature blind to a positive
rescaling of the twist. -/
theorem equivalent_smul_of_pos {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) {r : ℝ} (hr : 0 < r) :
    QuadraticMap.Equivalent (r • Q) Q := by
  have hs : Real.sqrt r ≠ 0 := by positivity
  refine ⟨{ toLinearEquiv := LinearEquiv.smulOfUnit (Units.mk0 (Real.sqrt r) hs)
            map_app' := ?_ }⟩
  intro m
  change Q (Real.sqrt r • m) = r • Q m
  rw [QuadraticMap.map_smul, Real.mul_self_sqrt hr.le]

theorem sigPos_smul_of_pos {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) {r : ℝ} (hr : 0 < r) :
    _root_.sigPos (r • Q) = _root_.sigPos Q :=
  (equivalent_smul_of_pos Q hr).sigPos_eq

theorem sigNeg_smul_of_pos {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) {r : ℝ} (hr : 0 < r) :
    _root_.sigNeg (r • Q) = _root_.sigNeg Q :=
  (equivalent_smul_of_pos Q hr).sigNeg_eq

/-! ## The real quadratic form of a Hermitian matrix -/

/-- **The real quadratic form of a complex matrix**: `x ↦ re ⟪x, P x⟫`. -/
def realQuad (P : Matrix (Fin n) (Fin n) ℂ) : QuadraticForm ℝ (Fin n → ℂ) :=
  LinearMap.BilinMap.toQuadraticMap (realBilin P)

@[simp] theorem realQuad_apply (P : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    realQuad P x = (star x ⬝ᵥ (P *ᵥ x)).re := rfl

/-- Rescaling the matrix by a REAL scalar rescales the form by the same scalar. -/
theorem realQuad_real_smul (P : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    realQuad ((r : ℂ) • P) = r • realQuad P := by
  refine QuadraticMap.ext fun x => ?_
  have h : (star x ⬝ᵥ (((r : ℂ) • P) *ᵥ x)) = (r : ℂ) * (star x ⬝ᵥ (P *ᵥ x)) := by
    rw [Matrix.smul_mulVec, _root_.dotProduct_smul, smul_eq_mul]
  simp only [realQuad_apply, QuadraticMap.smul_apply, h, smul_eq_mul]
  simp

theorem realQuad_neg (P : Matrix (Fin n) (Fin n) ℂ) :
    realQuad (-P) = - realQuad P := by
  have h := realQuad_real_smul P (-1)
  simpa using h

/-! ## The signature, and what the ⋆-structure determines -/

/-- **The signature of a Hermitian matrix**: the pair of maximal dimensions of a
positive-definite and a negative-definite real subspace for `x ↦ re ⟪x, P x⟫`. -/
def signature (P : Matrix (Fin n) (Fin n) ℂ) : ℕ × ℕ :=
  (_root_.sigPos (realQuad P), _root_.sigNeg (realQuad P))

/-- A POSITIVE real rescaling of the twist leaves the signature alone. -/
theorem signature_real_smul_pos (P : Matrix (Fin n) (Fin n) ℂ) {r : ℝ} (hr : 0 < r) :
    signature ((r : ℂ) • P) = signature P := by
  simp only [signature, realQuad_real_smul, sigPos_smul_of_pos _ hr, sigNeg_smul_of_pos _ hr]

/-- A NEGATIVE real rescaling exchanges the two halves. -/
theorem signature_real_smul_neg (P : Matrix (Fin n) (Fin n) ℂ) {r : ℝ} (hr : r < 0) :
    signature ((r : ℂ) • P) = (signature P).swap := by
  have hpos : 0 < -r := by linarith
  have hneg : (r : ℝ) • realQuad P = -((-r) • realQuad P) := by
    rw [neg_smul, neg_neg]
  simp only [signature, realQuad_real_smul, hneg, sigPos_neg, sigNeg_neg,
    sigPos_smul_of_pos _ hpos, sigNeg_smul_of_pos _ hpos, Prod.swap_prod_mk]

/-- **THE INVARIANT.** Two Hermitian twists presenting the same ⋆-structure have the same
signature, or the exchanged one — and nothing sharper is available, because
`StarStructureTwistFibre.hermitianStar_neg` exhibits the exchange. -/
theorem signature_eq_or_swap_of_star_eq [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : StarStructureTwistFibre.hermitianStar P hP
      = StarStructureTwistFibre.hermitianStar Q hQ) :
    signature (P : Matrix (Fin n) (Fin n) ℂ) = signature (Q : Matrix (Fin n) (Fin n) ℂ)
      ∨ signature (P : Matrix (Fin n) (Fin n) ℂ)
        = (signature (Q : Matrix (Fin n) (Fin n) ℂ)).swap := by
  obtain ⟨r, hr, hPQ⟩ := (StarStructureTwistFibre.hermitianStar_eq_iff P Q hP hQ).1 h
  rcases lt_trichotomy r 0 with hlt | heq | hgt
  · exact Or.inr (by rw [hPQ]; exact signature_real_smul_neg _ hlt)
  · exact absurd heq hr
  · exact Or.inl (by rw [hPQ]; exact signature_real_smul_pos _ hgt)

/-! ## Non-vacuity: two values, and the exchange realised -/

/-- A positive-definite real quadratic form has `sigPos` the full dimension. -/
theorem sigPos_eq_finrank_of_posDef {M : Type*} [AddCommGroup M] [Module ℝ M]
    [Module.Finite ℝ M] (Q : QuadraticForm ℝ M) (hQ : Q.PosDef) :
    _root_.sigPos Q = Module.finrank ℝ M := by
  refine le_antisymm (sigPos_le_finrank Q) ?_
  have h : (Q.restrict (⊤ : Submodule ℝ M)).PosDef := by
    intro x hx
    refine hQ (x : M) ?_
    simpa [Submodule.coe_eq_zero] using hx
  have hle := le_sigPos_of_posDef (Q := Q) h
  simpa using hle

/-- A negative-definite real quadratic form has `sigPos` zero. -/
theorem sigPos_eq_zero_of_neg {M : Type*} [AddCommGroup M] [Module ℝ M]
    [Module.Finite ℝ M] (Q : QuadraticForm ℝ M) (hQ : ∀ x : M, x ≠ 0 → Q x < 0) :
    _root_.sigPos Q = 0 := by
  by_contra hne
  obtain ⟨V, hV, hpd⟩ := exists_finrank_eq_sigPos_and_posDef (Q := Q)
  have hpos : 0 < Module.finrank ℝ V := by
    rw [hV]; exact Nat.pos_of_ne_zero hne
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h1 : 0 < Q (x : M) := by simpa using hpd x hx
  have h2 : Q (x : M) < 0 := hQ _ (by simpa [Submodule.coe_eq_zero] using hx)
  linarith

theorem realQuad_one_apply (x : Fin n → ℂ) :
    realQuad (1 : Matrix (Fin n) (Fin n) ℂ) x = ∑ i, Complex.normSq (x i) := by
  simp only [realQuad_apply, Matrix.one_mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]

theorem posDef_realQuad_one : (realQuad (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  intro x hx
  rw [realQuad_one_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact Complex.normSq_pos.2 (by simpa using hi)

theorem finrank_real_pi_complex : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype ℝ]
  simp [Complex.finrank_real_complex, mul_comm]

/-- **The identity twist has signature `(2n, 0)`.** -/
theorem signature_one : signature (1 : Matrix (Fin n) (Fin n) ℂ) = (2 * n, 0) := by
  have hpd := posDef_realQuad_one (n := n)
  refine Prod.ext ?_ ?_
  · simpa [signature, finrank_real_pi_complex] using
      sigPos_eq_finrank_of_posDef (realQuad (1 : Matrix (Fin n) (Fin n) ℂ)) hpd
  · refine sigPos_eq_zero_of_neg _ fun x hx => ?_
    have := hpd x hx
    simpa using this

/-- **The negated identity has the exchanged signature `(0, 2n)`.** -/
theorem signature_neg_one : signature (-1 : Matrix (Fin n) (Fin n) ℂ) = (0, 2 * n) := by
  have h : ((-1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = -1 := by simp
  have := signature_real_smul_neg (1 : Matrix (Fin n) (Fin n) ℂ) (r := -1) (by norm_num)
  rw [h] at this
  rw [this, signature_one]
  rfl

/-- **The exchange is realised, not a hedge.** For `n ≥ 1` the identity twist and its negative
present the SAME ⋆-structure — `StarStructureTwistFibre.hermitianStar_neg` — and have DIFFERENT
signatures, each other's exchange. **So there is no ORDERED-pair invariant of a ⋆-structure on
`Mₙ(ℂ)`**, and `signature_eq_or_swap_of_star_eq` is as sharp as a statement of its kind can be. -/
theorem star_eq_but_signature_ne [NeZero n] :
    StarStructureTwistFibre.hermitianStar (-(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ))
        (StarStructureTwistFibre.neg_hermitian 1 (by simp))
        = StarStructureTwistFibre.hermitianStar (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) (by simp)
      ∧ signature ((-(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        ≠ signature (((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
  refine ⟨StarStructureTwistFibre.hermitianStar_neg 1 (by simp) _, ?_⟩
  have h1 : ((-(1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      = -(1 : Matrix (Fin n) (Fin n) ℂ) := by simp
  have h2 : (((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      = (1 : Matrix (Fin n) (Fin n) ℂ) := by simp
  rw [h1, h2, signature_neg_one, signature_one]
  intro h
  have hn : (0 : ℕ) = 2 * n := (Prod.ext_iff.1 h).1
  have : n ≠ 0 := NeZero.ne n
  omega

/-! ## Congruence invariance: the signature survives a change of basis -/

/-- Multiplication by an invertible matrix, as an `ℝ`-linear equivalence of `Fin n → ℂ`. -/
def mulVecEquivR (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) where
  toFun x := (S : Matrix (Fin n) (Fin n) ℂ) *ᵥ x
  invFun x := ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x
  map_add' x y := Matrix.mulVec_add _ _ _
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [← Matrix.mulVec_smul]
  left_inv x := by
    simp only
    rw [Matrix.mulVec_mulVec]
    simp
  right_inv x := by
    simp only
    rw [Matrix.mulVec_mulVec]
    simp

@[simp] theorem mulVecEquivR_apply (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (x : Fin n → ℂ) :
    mulVecEquivR S x = (S : Matrix (Fin n) (Fin n) ℂ) *ᵥ x := rfl

/-- **The real form of a congruent matrix is the form composed with the change of basis.** -/
theorem realQuad_congr_apply (P : Matrix (Fin n) (Fin n) ℂ)
    (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (x : Fin n → ℂ) :
    realQuad ((S : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * (S : Matrix (Fin n) (Fin n) ℂ)) x
      = realQuad P ((S : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) := by
  have hvm : (S : Matrix (Fin n) (Fin n) ℂ)ᴴ.vecMul (star x)
      = star ((S : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) := by
    funext j
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, RCLike.star_def,
      Matrix.conjTranspose_apply, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [realQuad_apply, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hvm]

/-- **CONGRUENCE INVARIANCE.** `Sᴴ P S` has the same signature as `P` — the statement that makes
this a signature rather than a coordinate artefact. -/
theorem signature_congr (P : Matrix (Fin n) (Fin n) ℂ)
    (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    signature ((S : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * (S : Matrix (Fin n) (Fin n) ℂ))
      = signature P := by
  have hequiv : QuadraticMap.Equivalent
      (realQuad ((S : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * (S : Matrix (Fin n) (Fin n) ℂ)))
      (realQuad P) := by
    refine ⟨{ toLinearEquiv := mulVecEquivR S
              map_app' := ?_ }⟩
    intro m
    exact (realQuad_congr_apply P S m).symm
  simp only [signature, hequiv.sigPos_eq, hequiv.sigNeg_eq]

end

end HermitianRealForm
