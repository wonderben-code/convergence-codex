/-
  MinkowskiSignature: The Signature (1,3) as a Basis-Independent Invariant
  =======================================================================

  Discharges the first item on `MinkowskiHerm2.lean`'s own NOT-proven list
  (tree §6.2/§7.1, old gap #7; spine L9). That file proved the determinant on
  Herm₂(ℂ) equals t² − x² − y² − z² in an injective, surjective, linear Pauli
  parametrisation — an explicit diagonalisation with signs (+,−,−,−). What it
  explicitly did NOT prove, and said so, was that (1,3) is THE signature:
  invariant under change of basis, i.e. Sylvester's law of inertia.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `minkowskiForm` — the Minkowski form as a bundled Mathlib
     `QuadraticForm ℝ (Fin 4 → ℝ)`, namely `weightedSumSquares ℝ ![1,-1,-1,-1]`,
     with `minkowskiForm_apply` computing it as t² − x² − y² − z².
  2. `minkowskiForm_eq_det` — it IS the determinant on Herm₂(ℂ), pulled back
     along the Pauli parametrisation (using `MinkowskiHerm2.det_pauliHerm`).
  3. `sigPos_minkowskiForm = 1`, `sigNeg_minkowskiForm = 3` — the signature,
     computed through Mathlib's `sigPos`/`sigNeg`, which are defined
     INVARIANTLY as the maximal dimension of a subspace on which the form is
     positive- (resp. negative-) definite. This is the content of Sylvester's
     law: the numbers 1 and 3 are properties of the form, not of the Pauli
     coordinates that exhibit them.
  4. `signature_invariant` — spelled out: every quadratic form isometric to
     this one has sigPos = 1 and sigNeg = 3.
  5. `not_equivalent_euclidean` — the obstruction in the useful direction:
     the determinant form on Herm₂ is NOT isometric to the Euclidean form on
     ℝ⁴. Spacetime is not space, and the proof is the signature.
  6. `finrank_radical_eq_zero` — the form is nondegenerate (its radical is
     trivial), so 1 + 3 = 4 exhausts the space.
  7. `exists_null_vector` — the light cone is not trivial: there are nonzero
     null directions, which is exactly what a definite form cannot have.
  8. `pauliCoord` + `pauliHerm_pauliCoord` — the inverse parametrisation, so
     Pauli coordinates are a genuine bijection with Herm₂(ℂ); and
     `minkowskiForm_lorentzMap` — **the SL₂(ℂ) conjugation action, read in
     those coordinates, preserves the Minkowski form**. That is the map into
     the orthogonal group O(1,3) at the level of the form, which with
     `MinkowskiHerm2.kernel_of_conj_action` (kernel exactly {±1}) is most of
     old gap #7's homomorphism half.

  NOT proven here (the rest of gap #7, unchanged): SURJECTIVITY of
  SL₂(ℂ) → SO⁺(1,3) (the actual covering statement — needs polar
  decomposition/connectedness), and with it the identification of the IMAGE
  as the identity component rather than merely a subgroup of O(1,3);
  ℝ-linearity of `lorentzMap` as a bundled `LinearMap` (the isometry
  equation is proven, the bundled object is not built); the identification of
  SL₂(ℂ) with Mathlib's `spinGroup`; a bundled `MulAction` of SL₂(ℂ) on
  Herm₂; and the
  claim that this signature is FORCED by the cascade rather than exhibited
  by it — the tree's derivation of "why Herm₂" is a separate argument, and
  nothing here supplies it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import MinkowskiHerm2
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real

open QuadraticMap QuadraticForm Matrix MinkowskiHerm2

noncomputable section

namespace MinkowskiSignature

/-! ## 1. The form -/

/-- The Minkowski weights (+1, −1, −1, −1). -/
def mw : Fin 4 → ℝ := ![1, -1, -1, -1]

/-- **The Minkowski quadratic form** on ℝ⁴ as a bundled Mathlib
    `QuadraticForm`. -/
def minkowskiForm : QuadraticForm ℝ (Fin 4 → ℝ) := weightedSumSquares ℝ mw

theorem minkowskiForm_apply (v : Fin 4 → ℝ) :
    minkowskiForm v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  have h0 : mw 0 = 1 := rfl
  have h1 : mw 1 = -1 := rfl
  have h2 : mw 2 = -1 := rfl
  have h3 : mw 3 = -1 := rfl
  rw [minkowskiForm, weightedSumSquares_apply, Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [smul_eq_mul]
  ring

/-- **The determinant form on Herm₂(ℂ) is the Minkowski form**: in the Pauli
    coordinates of `MinkowskiHerm2`, det(t·1 + x·σ₁ + y·σ₂ + z·σ₃) is exactly
    this quadratic form. -/
theorem minkowskiForm_eq_det (v : Fin 4 → ℝ) :
    ((minkowskiForm v : ℝ) : ℂ)
      = Matrix.det (pauliHerm (v 0) (v 1) (v 2) (v 3)) := by
  rw [minkowskiForm_apply, det_pauliHerm]

/-! ## 2. The signature, computed invariantly -/

/-- **One positive direction**: `sigPos` is the maximal dimension of a
    subspace on which the form is positive definite, so this is a statement
    about the form and not about the coordinates. -/
theorem sigPos_minkowskiForm : sigPos minkowskiForm = 1 := by
  rw [minkowskiForm, sigPos_weightedSumSquares]
  have h : {i : Fin 4 | 0 < mw i} = ({0} : Set (Fin 4)) := by
    ext i
    fin_cases i <;> norm_num [mw]
  rw [h, Set.ncard_singleton]

/-- **Three negative directions.** -/
theorem sigNeg_minkowskiForm : sigNeg minkowskiForm = 3 := by
  rw [minkowskiForm, sigNeg_weightedSumSquares]
  have hc : {i : Fin 4 | mw i < 0} = ({0} : Set (Fin 4))ᶜ := by
    ext i
    fin_cases i <;> norm_num [mw]
  have hsum := Set.ncard_add_ncard_compl ({0} : Set (Fin 4))
  rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  rw [hc]
  omega

/-- **Sylvester's law of inertia, applied**: any quadratic form isometric to
    the determinant form on Herm₂ has signature (1,3). The signature is a
    property of the geometry, not of the Pauli basis that exhibits it. -/
theorem signature_invariant {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (h : Equivalent minkowskiForm Q) :
    sigPos Q = 1 ∧ sigNeg Q = 3 :=
  ⟨by rw [← h.sigPos_eq, sigPos_minkowskiForm],
    by rw [← h.sigNeg_eq, sigNeg_minkowskiForm]⟩

/-! ## 3. Consequences -/

/-- **Spacetime is not space**: the determinant form on Herm₂(ℂ) is not
    isometric to the Euclidean form on ℝ⁴. The proof is the signature — no
    change of basis can turn one plus and three minuses into four pluses. -/
theorem not_equivalent_euclidean :
    ¬ Equivalent minkowskiForm (weightedSumSquares ℝ (fun _ : Fin 4 => (1 : ℝ))) := by
  intro h
  have h1 := h.sigPos_eq
  rw [sigPos_minkowskiForm, sigPos_weightedSumSquares] at h1
  have h2 : {i : Fin 4 | (0 : ℝ) < (fun _ : Fin 4 => (1 : ℝ)) i} = (Set.univ : Set (Fin 4)) := by
    ext i
    norm_num
  rw [h2, Set.ncard_univ] at h1
  simp at h1

/-- **Nondegeneracy**: the radical is trivial, so the signature 1 + 3
    exhausts the four dimensions. -/
theorem finrank_radical_eq_zero :
    Module.finrank ℝ minkowskiForm.radical = 0 := by
  have h := sigPos_add_sigNeg_add_radical (Q := minkowskiForm)
  rw [sigPos_minkowskiForm, sigNeg_minkowskiForm, Module.finrank_fin_fun] at h
  omega

/-- **The light cone is not trivial**: a definite form has no nonzero null
    vectors, and this one does. -/
theorem exists_null_vector : ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ minkowskiForm v = 0 := by
  refine ⟨![1, 1, 0, 0], ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · rw [minkowskiForm_apply]
    change (1 : ℝ) ^ 2 - 1 ^ 2 - 0 ^ 2 - 0 ^ 2 = 0
    norm_num

/-! ## 4. The SL₂(ℂ) action is by isometries of the form

    `MinkowskiHerm2` proves det(A·H·Aᴴ) = det(H) for det A = 1, and that the
    action fixes Herm₂. Transported through the Pauli coordinates, that says
    exactly that A acts on ℝ⁴ preserving the Minkowski form — the map into
    the orthogonal group O(1,3) at the level of the form. -/

/-- The inverse of the Pauli parametrisation on Hermitian matrices:
    t = (Re H₀₀ + Re H₁₁)/2, x = Re H₀₁, y = −Im H₀₁, z = (Re H₀₀ − Re H₁₁)/2. -/
def pauliCoord (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![(H 0 0).re / 2 + (H 1 1).re / 2, (H 0 1).re, -(H 0 1).im,
    (H 0 0).re / 2 - (H 1 1).re / 2]

/-- **Round trip**: on Hermitian matrices the Pauli coordinates recover the
    matrix, so `pauliCoord` really is the inverse parametrisation. -/
theorem pauliHerm_pauliCoord (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : Hᴴ = H) :
    pauliHerm (pauliCoord H 0) (pauliCoord H 1) (pauliCoord H 2)
      (pauliCoord H 3) = H := by
  have e00 := congrFun (congrFun hH 0) 0
  have e11 := congrFun (congrFun hH 1) 1
  have e10 := congrFun (congrFun hH 1) 0
  simp only [Matrix.conjTranspose_apply] at e00 e11 e10
  have h00 : (H 0 0).im = 0 := by
    have : (starRingEnd ℂ) (H 0 0) = H 0 0 := e00
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (H 1 1).im = 0 := by
    have : (starRingEnd ℂ) (H 1 1) = H 1 1 := e11
    exact Complex.conj_eq_iff_im.mp this
  have h10 : H 1 0 = (starRingEnd ℂ) (H 0 1) := e10.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliHerm, pauliCoord, Complex.ext_iff, h10, h00, h11]

/-- The Lorentz map induced by A ∈ SL₂(ℂ) in Pauli coordinates. -/
def lorentzMap (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  pauliCoord (A * pauliHerm (v 0) (v 1) (v 2) (v 3) * Aᴴ)

/-- **The action preserves the Minkowski form**: for A ∈ SL₂(ℂ),
    Q(A·v) = Q(v). This is the statement that the conjugation action lands in
    the orthogonal group of the form — the form half of SL₂(ℂ) → SO⁺(1,3).
    (What is still missing for the full covering statement: that the image is
    the IDENTITY COMPONENT and that the map is onto it.) -/
theorem minkowskiForm_lorentzMap (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Matrix.det A = 1) (v : Fin 4 → ℝ) :
    minkowskiForm (lorentzMap A v) = minkowskiForm v := by
  have hherm : (A * pauliHerm (v 0) (v 1) (v 2) (v 3) * Aᴴ)ᴴ
      = A * pauliHerm (v 0) (v 1) (v 2) (v 3) * Aᴴ :=
    conj_action_hermitian A _ (pauliHerm_isHermitian _ _ _ _)
  have hround := pauliHerm_pauliCoord _ hherm
  have hcast : ((minkowskiForm (lorentzMap A v) : ℝ) : ℂ)
      = ((minkowskiForm v : ℝ) : ℂ) := by
    rw [minkowskiForm_eq_det, minkowskiForm_eq_det, lorentzMap, hround]
    exact det_conj_invariant A _ hA
  exact_mod_cast hcast

/-- The identity acts as the identity. -/
theorem lorentzMap_one (v : Fin 4 → ℝ) : lorentzMap 1 v = v := by
  have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) * pauliHerm (v 0) (v 1) (v 2) (v 3)
      * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      = pauliHerm (v 0) (v 1) (v 2) (v 3) := by
    rw [Matrix.conjTranspose_one, one_mul, mul_one]
  unfold lorentzMap
  rw [h]
  funext i
  fin_cases i <;>
    simp [pauliCoord, pauliHerm] <;> ring

end MinkowskiSignature
