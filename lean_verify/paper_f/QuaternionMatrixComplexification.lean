/-
  QuaternionMatrixComplexification: `ℂ ⊗[ℝ] Mₙ(ℍ) ≃ₐ[ℝ] M₂ₙ(ℂ)` at EVERY size, so L14's Caesar
  item 6 closes — and the same complexification is ALSO `ℂ ⊗[ℝ] M₂ₙ(ℝ)`, which is a theorem that
  the complexification does not choose the real form

  SPINE LINK L14, Caesar item 6. **This file exists because the two units before it were both
  wrong about what the estate already contains, and the correction is the first thing to say.**

  THE CORRECTION, AND IT IS THE SIXTH OF ITS KIND IN THIS ONE THREAD (`ERRATUM 584`).
  * `ERRATUM 582` refuted the task list's deferral reason (*"Mathlib has no quaternion
    complexification"*) and then recorded a REAL instance diamond on `ℂ`: `#synth Module ℝ ℂ`
    resolves through the inner-product hierarchy while `#synth Algebra ℝ ℂ` resolves through
    `RCLike`, so `Semiring (ℂ ⊗[ℝ] X)` does not synthesise. **That measurement is correct and I
    re-measured it today**: without a pin, `Semiring (ℂ ⊗[ℝ] Mₙ(ℍ))` fails.
  * What was FALSE is the inference: that the diamond leaves the tensor form unavailable.
    `UNLOCK_WATCHLIST` entry 267 recorded route (1) — pin `Module ℝ ℂ` locally — as *"not done
    deliberately"*, on the ground that *"the result would be a statement about a tensor product
    built from a locally supplied instance, not interchangeable with anything else in the
    estate — a theorem that looks usable and is not."*
  * **`paper_f/ComplexQuaternionTensor.lean` has done exactly that since Campaign 3.** It carries
    `equivM2C : ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₂(ℂ)`, it is rated GENUINE in `TRUE_LEDGER`, it measured the
    same diamond in the same three ways, and it fixes it with one `local instance` line. The
    prediction that such a theorem is not interchangeable is **refuted by this file**: `equivM2C`
    composed with four further estate and Mathlib equivalences into the chain below **first try,
    with no friction at all**, because the pinned instance is the one `Algebra.toModule` supplies,
    which is what every polymorphic Mathlib algebra lemma instantiates to anyway.
  * `QuaternionComplexification`, the unit immediately before this one, says in its own
    NOT-CLAIMED list that *"the diamond `ERRATUM 582` measured is real and unfixed"*. Real, yes.
    **Unfixed, no** — and that file's header is amended in place rather than deleted.
  * **The rule this leaves.** My prior-art probes grep `ERRATA.md` and the task list. They did not
    look at the estate's own file names. `ls paper_f | grep -i quat` returns
    `ComplexQuaternionTensor.lean` in one command: the name of the file is the name of the theorem
    I twice recorded as missing.

  WHAT IS PROVED.
  * **`quatMatrixEquiv`** — `ℂ ⊗[ℝ] Mₙ(ℍ) ≃ₐ[ℝ] M₍ₙ·₂₎(ℂ)` for **every** `n`, as a six-step
    composite: commute the factors, `CliffordPeriodicityEight.matrixTensorRight` to move the
    tensor inside the matrix, commute back, `ComplexQuaternionTensor.equivM2C` entrywise via
    `AlgEquiv.mapMatrix`, `Matrix.compAlgEquiv` to flatten `Mₙ(M₂(ℂ))`, and one reindex along
    `finProdFinEquiv`. Nothing is constructed by hand.
  * **`caesarSix`** — hence `ℂ ⊗[ℝ] M₂(ℍ) ≃ₐ[ℝ] M₄(ℂ)`, which is Caesar item 6 verbatim, at
    `n = 2`. **`Fin (2 * 2)` and `Fin 4` are definitionally equal, so the instantiation is the
    whole proof.**
  * **`realMatrixEquiv`** — `ℂ ⊗[ℝ] Mₙ(ℝ) ≃ₐ[ℝ] Mₙ(ℂ)` for every `n`, three steps, the same
    machinery with `Algebra.TensorProduct.lid` in place of `equivM2C`.
  * **`quatRealSameComplexification`** — so `ℂ ⊗[ℝ] Mₙ(ℍ) ≃ₐ[ℝ] ℂ ⊗[ℝ] M₍ₙ·₂₎(ℝ)`: two real
    algebras with the SAME complexification, at every `n`.
  * **`realForm_not_determined_four`, `realForm_not_determined_eight`** — and at `n = 2` and
    `n = 4` the two real algebras are **not** isomorphic, by this estate's own
    `IdempotentRankInvariant.matrix2H_not_ringEquiv_matrix4R` and `matrix4H_not_ringEquiv_matrix8R`
    (the orthogonal-idempotent count: `M₄(ℝ)` admits four and `M₂(ℍ)` two; `M₈(ℝ)` eight and
    `M₄(ℍ)` four). **So the complexification does not determine the real form, and that is now a
    theorem rather than a remark.** Each is stated as a conjunction so that neither half can be
    read without the other, and there are two sizes so the first is not an accident of `M₄(ℂ)`.
  * **`matrix1H_not_ringEquiv_matrix2R`, `realForm_not_determined_two`** — and the same at
    `n = 1`, which is **the pair this campaign leans on hardest**. `ASSUMPTIONS_LEDGER` 3 says in
    prose that *"over `ℝ` the uniqueness is FALSE: `ℍ` and `M₂(ℝ)` are non-isomorphic,
    non-commutative, semisimple, both 4-dimensional"*; the non-isomorphism is proved here (the
    `n = 1` member of `IdempotentRankInvariant`'s family, which that file does not state), and
    the two complexify alike. **So *"the minimal non-commutative seed is `M₂(ℂ)`"* cannot be
    recovered from the complexification either, and that assumption's base-field restriction is
    doing work no theorem takes over.**
  * **`quatComplexEquivC`** — `ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] M₂(ℂ)`, the estate's `equivM2C` upgraded from
    `ℝ`-linear to `ℂ`-linear at one factor, via `AlgHom.liftEquiv ℝ ℂ` out of
    `ComplexQuaternionTensor.rho`. **`liftC_eq_T` is the honest content**: the `ℂ`-linear map IS
    the estate's `ℝ`-linear one, function for function, so what the upgrade adds is the recorded
    scalar tower and not a new map. Bijectivity is therefore `T_injective` and `T_surjective`
    transported, not reproved.
  * **`finrank_real_matrix_complex`, `finrank_complexified_quatMatrix`** — `2n²` and `8n²`, the
    second computed THROUGH `quatMatrixEquiv`, so it is a consequence of the chain rather than an
    independent count, and the chain is non-vacuous.

  WHAT IS **NOT** CLAIMED.
  * ~~**`quatMatrixEquiv` is `ℝ`-linear, not `ℂ`-linear**, and the `ℂ`-linear form of the MATRIX
    case is not stated. … pushing the sum through the five-fold composite inside
    `matrixTensorRight` **times out instance synthesis at 20000 heartbeats**. **That is an
    elaboration cost, NOT a structural obstruction.**~~ **STATED THE SAME DAY, ONE UNIT LATER —
    `quatMatrixEquivC` and `caesarSixC` (`ERRATUM 587`).** The residue was labelled a tactic cost
    and that label was right: what it needed was a COMPUTATION LEMMA for the composite, not a
    bigger heartbeat budget. `CliffordPeriodicityEight.matrixTensorRight` had none — every use of
    it was opaque — so `matrixTensorRight_single` and `matrixTensorRight_tmul` were added beside
    the definition, and with `M ⊗ₜ b ↦ M.map (· ⊗ₜ b)` in hand the composite is never unfolded
    and the timeout never arises. **The `ℝ`-linear statements are kept**: `liftCMat_eq` proves the
    two maps are the same function, so what the upgrade records is the scalar tower.
  * **The pin is `local` and this file's statements are about the pinned tensor product.** That is
    the same footing as `ComplexQuaternionTensor`, and the composite above is the evidence that it
    is usable; it is not a claim that the pin is unnecessary. Without it the chain does not
    elaborate — measured today.
  * **Nothing here says which real form the cascade HAS.** The opposite: the two
    `realForm_not_determined` theorems say the complexification cannot answer that question, so
    `ASSUMPTIONS_LEDGER` 3 and 25 and `DECISIONS NEEDED 4` are **more** firmly the author's,
    not less. `a·b·c = 16` keeps every alternative (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35).
  * **No star structure anywhere.** Nothing says any of these maps carries quaternionic
    conjugation to the conjugate transpose, which is what a real-form statement in the
    `⋆`-sense needs. The theorems above are about `ℝ`-algebra and `ℂ`-algebra structure only.
  * **`M₄(ℂ)`'s remaining real forms are not enumerated.** Two are exhibited. `M₂(ℂ)` as a real
    algebra (whose complexification is a product, not a matrix algebra) is not treated, and no
    classification is claimed.

  0 sorry. 0 new axioms. **24 declarations**, all on `[propext, Classical.choice, Quot.sound]`
  — and the `local instance` pin below is a fourteenth declaration that the count does NOT include,
  because `check_ledger.py`'s declaration scan has no `local` in its modifier list. The pin's axioms
  were checked too and are the same three.
-/

import ComplexQuaternionTensor
import CliffordPeriodicityEight
import IdempotentRankInvariant

namespace QuaternionMatrixComplexification

open scoped TensorProduct Quaternion

noncomputable section

/-- **The pin the file exists around, and it is `ComplexQuaternionTensor`'s, repeated because
`local` does not export.** Without it `Semiring (ℂ ⊗[ℝ] Mₙ(ℍ))` fails to synthesise — measured,
not assumed. `local`, so nothing downstream inherits it. -/
local instance pinModuleRealComplex : Module ℝ ℂ := Algebra.toModule

/-! ## 1. The chain, at every size -/

/-- **`ℂ ⊗[ℝ] Mₙ(ℍ) ≃ₐ[ℝ] M₍ₙ·₂₎(ℂ)`.** Six steps, none of them constructed by hand: commute,
move the tensor inside the matrix, commute back, apply `equivM2C` entrywise, flatten, reindex. -/
def quatMatrixEquiv (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ :=
  (Algebra.TensorProduct.comm ℝ ℂ (Matrix (Fin n) (Fin n) ℍ[ℝ])).trans <|
  (CliffordPeriodicityEight.matrixTensorRight (Fin n) ℍ[ℝ] ℂ).trans <|
  ((Algebra.TensorProduct.comm ℝ ℍ[ℝ] ℂ).mapMatrix (m := Fin n)).trans <|
  (ComplexQuaternionTensor.equivM2C.mapMatrix (m := Fin n)).trans <|
  (Matrix.compAlgEquiv (Fin n) (Fin 2) ℂ ℝ).trans
  (Matrix.reindexAlgEquiv ℝ ℂ finProdFinEquiv)

/-- **Caesar item 6, verbatim: `ℂ ⊗[ℝ] M₂(ℍ) ≃ₐ[ℝ] M₄(ℂ)`.** `Fin (2 * 2)` and `Fin 4` are
definitionally equal, so instantiating the general chain is the entire proof. -/
def caesarSix : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ :=
  quatMatrixEquiv 2

/-! ## 2. The other real form -/

/-- **`ℂ ⊗[ℝ] Mₙ(ℝ) ≃ₐ[ℝ] Mₙ(ℂ)`.** The same machinery with `Algebra.TensorProduct.lid` where
the quaternion chain used `equivM2C`. -/
def realMatrixEquiv (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Algebra.TensorProduct.comm ℝ ℂ (Matrix (Fin n) (Fin n) ℝ)).trans <|
  (CliffordPeriodicityEight.matrixTensorRight (Fin n) ℝ ℂ).trans
  ((Algebra.TensorProduct.lid ℝ ℂ).mapMatrix (m := Fin n))

/-- **Two real algebras, one complexification**, at every size. -/
def quatRealSameComplexification (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ] ≃ₐ[ℝ]
      ℂ ⊗[ℝ] Matrix (Fin (n * 2)) (Fin (n * 2)) ℝ :=
  (quatMatrixEquiv n).trans (realMatrixEquiv (n * 2)).symm

/-! ## 3. So the complexification does not choose the real form -/

/-- **`M₂(ℍ)` and `M₄(ℝ)` have the same complexification and are not isomorphic.** The second
conjunct is this estate's orthogonal-idempotent count, not new here; the first is the chain
above. Stated as a conjunction so neither half can be read without the other. -/
theorem realForm_not_determined_four :
    Nonempty (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃ₐ[ℝ] ℂ ⊗[ℝ] Matrix (Fin 4) (Fin 4) ℝ)
      ∧ IsEmpty (Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃+* Matrix (Fin 4) (Fin 4) ℝ) :=
  ⟨⟨quatRealSameComplexification 2⟩,
    IdempotentRankInvariant.matrix2H_not_ringEquiv_matrix4R⟩

/-- **And again one size up**, so the first instance is not an accident of `M₄(ℂ)`: `M₄(ℍ)` and
`M₈(ℝ)` complexify alike and are not isomorphic. -/
theorem realForm_not_determined_eight :
    Nonempty (ℂ ⊗[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ] ≃ₐ[ℝ] ℂ ⊗[ℝ] Matrix (Fin 8) (Fin 8) ℝ)
      ∧ IsEmpty (Matrix (Fin 4) (Fin 4) ℍ[ℝ] ≃+* Matrix (Fin 8) (Fin 8) ℝ) :=
  ⟨⟨quatRealSameComplexification 4⟩,
    IdempotentRankInvariant.matrix4H_not_ringEquiv_matrix8R⟩

/-- **`M₁(ℍ) ≇ M₂(ℝ)`** — the `n = 1` member of `IdempotentRankInvariant`'s family, which that
file states at `n = 2` and `n = 4` but not here. Same proof: `M₂(ℝ)` admits two orthogonal
nonzero idempotents summing to `1`, `M₁(ℍ)` at most one, and a ring isomorphism would transport
the first count to the second. **This is the pair `ASSUMPTIONS_LEDGER` 3 names in prose** —
*"over `ℝ` the uniqueness is FALSE: `ℍ` and `M₂(ℝ)` are non-isomorphic, non-commutative,
semisimple, both 4-dimensional"* — so it is proved here rather than asserted. -/
theorem matrix1H_not_ringEquiv_matrix2R :
    IsEmpty (Matrix (Fin 1) (Fin 1) ℍ[ℝ] ≃+* Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨fun φ => ?_⟩
  have h2 : IdempotentRankInvariant.HasOrthIdem (Matrix (Fin 2) (Fin 2) ℝ) 2 := by
    have h : IdempotentRankInvariant.HasOrthIdem (Matrix (Fin 2) (Fin 2) ℝ)
        (Fintype.card (Fin 2)) := IdempotentRankInvariant.matrix_hasOrthIdem_card
    simpa using h
  have h1 : IdempotentRankInvariant.HasOrthIdem (Matrix (Fin 1) (Fin 1) ℍ[ℝ]) 2 :=
    IdempotentRankInvariant.HasOrthIdem.of_ringEquiv φ.symm h2
  have := IdempotentRankInvariant.matrixH_orthIdem_le_card h1
  simp at this

/-- **The seed-uniqueness pair, at `n = 1`, and this is the one the campaign leans on hardest.**
`ℍ` and `M₂(ℝ)` complexify alike and are not isomorphic — so *"the minimal non-commutative seed
is `M₂(ℂ)`"* cannot be recovered from the complexification either, and `ASSUMPTIONS_LEDGER` 3's
base-field restriction is doing work no theorem can take over. -/
theorem realForm_not_determined_two :
    Nonempty (ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) ℍ[ℝ] ≃ₐ[ℝ] ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      ∧ IsEmpty (Matrix (Fin 1) (Fin 1) ℍ[ℝ] ≃+* Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨⟨quatRealSameComplexification 1⟩, matrix1H_not_ringEquiv_matrix2R⟩

/-! ## 4. The `ℂ`-linear upgrade at one factor -/

/-- The `ℂ`-algebra map `ℂ ⊗[ℝ] ℍ → M₂(ℂ)` that `AlgHom.liftEquiv` produces from the estate's
`ℝ`-algebra map `rho`. The universal property is a BIJECTION, so nothing is built. -/
def liftC : ℂ ⊗[ℝ] ℍ[ℝ] →ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  AlgHom.liftEquiv ℝ ℂ ℍ[ℝ] (Matrix (Fin 2) (Fin 2) ℂ) ComplexQuaternionTensor.rho

@[simp] theorem liftC_tmul (z : ℂ) (q : ℍ[ℝ]) :
    liftC (z ⊗ₜ[ℝ] q) = z • ComplexQuaternionTensor.rho q := by
  simp [liftC]

/-- **The honest content of the upgrade**: the `ℂ`-linear map is the estate's `ℝ`-linear `T`,
function for function. Both agree on every `z ⊗ₜ q` — `liftC_tmul` against
`ComplexQuaternionTensor.T_tmul` — and `TensorProduct.induction_on` does the rest. So what the
upgrade records is the scalar tower, not a new map. -/
theorem liftC_eq_T (x : ℂ ⊗[ℝ] ℍ[ℝ]) : liftC x = ComplexQuaternionTensor.T x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z q => simp [ComplexQuaternionTensor.T_tmul]
  | add a b ha hb => simp [ha, hb]

/-- Hence bijective, by transport rather than by a second proof. -/
theorem liftC_bijective : Function.Bijective liftC := by
  have h : (liftC : ℂ ⊗[ℝ] ℍ[ℝ] → Matrix (Fin 2) (Fin 2) ℂ) = ComplexQuaternionTensor.T :=
    funext liftC_eq_T
  rw [h]
  exact ⟨ComplexQuaternionTensor.T_injective, ComplexQuaternionTensor.T_surjective⟩

/-- **`ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] M₂(ℂ)`** — the estate's `equivM2C` with `ℂ` as the base ring. -/
def quatComplexEquivC : ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  AlgEquiv.ofBijective liftC liftC_bijective

/-! ## 5. The `ℂ`-linear upgrade of the MATRIX chain -/

/-- `equivM2C (z ⊗ₜ 1) = z • 1`, the one value of the estate's equivalence this needs. -/
theorem equivM2C_tmul_one (z : ℂ) :
    ComplexQuaternionTensor.equivM2C (z ⊗ₜ[ℝ] (1 : ℍ[ℝ])) = z • 1 := by
  simp [ComplexQuaternionTensor.equivM2C, ComplexQuaternionTensor.T_tmul]

/-- **The step the previous unit recorded as unreachable, and it was a tactic residue.**
`quatMatrixEquiv n (z ⊗ₜ 1) = algebraMap ℂ _ z` — i.e. the `ℝ`-linear chain already sends the
`ℂ`-scalars to the `ℂ`-scalars, which is exactly what `AlgHom.liftEquiv` needs to promote it.
What unblocked it was giving `CliffordPeriodicityEight.matrixTensorRight` a computation lemma
(`matrixTensorRight_tmul`, added there this unit): with it the five-fold composite is never
unfolded, and what is left is `Fin (n * 2)` index arithmetic plus the injectivity of
`finProdFinEquiv.symm`. -/
theorem quatMatrixEquiv_tmul_one (n : ℕ) (z : ℂ) :
    quatMatrixEquiv n (z ⊗ₜ[ℝ] (1 : Matrix (Fin n) (Fin n) ℍ[ℝ]))
      = algebraMap ℂ (Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ) z := by
  have key : ∀ a b : Fin (n * 2), a.divNat = b.divNat → a.modNat = b.modNat → a = b := by
    intro a b h1 h2
    exact (finProdFinEquiv (m := n) (n := 2)).symm.injective
      (by simp [finProdFinEquiv_symm_apply, h1, h2])
  simp only [quatMatrixEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    CliffordPeriodicityEight.matrixTensorRight_tmul, AlgEquiv.mapMatrix_apply,
    Matrix.compAlgEquiv_apply, Matrix.reindexAlgEquiv_apply]
  ext p q
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finProdFinEquiv_symm_apply,
    Matrix.comp_apply, Matrix.map_apply, Matrix.one_apply, apply_ite,
    Algebra.TensorProduct.comm_tmul, equivM2C_tmul_one, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq]
    by_cases hd : p.divNat = q.divNat
    · rw [if_pos hd]
      have hm : p.modNat ≠ q.modNat := fun h => hpq (key p q hd h)
      simp [hm]
    · simp [hd]

/-- The `ℝ`-algebra map the universal property consumes: `M ↦ quatMatrixEquiv n (1 ⊗ₜ M)`. -/
def quatMatrixEmb (n : ℕ) :
    Matrix (Fin n) (Fin n) ℍ[ℝ] →ₐ[ℝ] Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ :=
  (quatMatrixEquiv n).toAlgHom.comp Algebra.TensorProduct.includeRight

/-- The `ℂ`-algebra map `AlgHom.liftEquiv` produces from it. As at one factor, the universal
property is a BIJECTION, so nothing is constructed. -/
def liftCMat (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ] →ₐ[ℂ] Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ :=
  AlgHom.liftEquiv ℝ ℂ (Matrix (Fin n) (Fin n) ℍ[ℝ])
    (Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ) (quatMatrixEmb n)

@[simp] theorem liftCMat_tmul (n : ℕ) (z : ℂ) (M : Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    liftCMat n (z ⊗ₜ[ℝ] M) = z • quatMatrixEmb n M := by
  simp [liftCMat]

/-- **The honest content, as at one factor**: the `ℂ`-linear map IS the `ℝ`-linear chain,
function for function. `z ⊗ₜ M` factors as `(z ⊗ₜ 1) * (1 ⊗ₜ M)`, both maps are multiplicative,
they agree on the right factor by construction, and `quatMatrixEquiv_tmul_one` is the left. -/
theorem liftCMat_eq (n : ℕ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ]) :
    liftCMat n x = quatMatrixEquiv n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z M =>
    have h : (z ⊗ₜ[ℝ] M : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ])
        = (z ⊗ₜ[ℝ] (1 : Matrix (Fin n) (Fin n) ℍ[ℝ])) * ((1 : ℂ) ⊗ₜ[ℝ] M) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, quatMatrixEquiv_tmul_one, liftCMat_tmul, liftCMat_tmul, map_one,
      one_smul, Algebra.algebraMap_eq_smul_one]
    simp [quatMatrixEmb]
  | add a b ha hb => simp [ha, hb]

/-- Hence bijective, by transport rather than by a second proof. -/
theorem liftCMat_bijective (n : ℕ) : Function.Bijective (liftCMat n) := by
  have h : (liftCMat n : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ] → _)
      = quatMatrixEquiv n := funext (liftCMat_eq n)
  rw [h]
  exact (quatMatrixEquiv n).bijective

/-- **`ℂ ⊗[ℝ] Mₙ(ℍ) ≃ₐ[ℂ] M₍ₙ·₂₎(ℂ)` at every `n`**, with `ℂ` as the base ring. -/
def quatMatrixEquivC (n : ℕ) :
    ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin (n * 2)) (Fin (n * 2)) ℂ :=
  AlgEquiv.ofBijective (liftCMat n) (liftCMat_bijective n)

/-- **Caesar item 6 in its `ℂ`-linear form: `ℂ ⊗[ℝ] M₂(ℍ) ≃ₐ[ℂ] M₄(ℂ)`.** -/
def caesarSixC : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  quatMatrixEquivC 2

/-! ## 6. Dimensions, computed through the chain -/

/-- `dim_ℝ Mₙ(ℂ) = 2n²`, the general form of `ComplexQuaternionTensor.finrank_m2c`. -/
theorem finrank_real_matrix_complex (n : ℕ) :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  have h : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hm := Module.finrank_mul_finrank ℝ ℂ (Matrix (Fin n) (Fin n) ℂ)
  rw [h, Module.finrank_matrix] at hm
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hm
  rw [← hm]; ring

/-- `dim_ℝ (ℂ ⊗[ℝ] Mₙ(ℍ)) = 8n²`, and it is computed THROUGH `quatMatrixEquiv`, so the chain is
exercised rather than merely stated. -/
theorem finrank_complexified_quatMatrix (n : ℕ) :
    Module.finrank ℝ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ]) = 8 * n ^ 2 := by
  rw [(quatMatrixEquiv n).toLinearEquiv.finrank_eq, finrank_real_matrix_complex]
  ring

end

end QuaternionMatrixComplexification
