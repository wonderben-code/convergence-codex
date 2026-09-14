/-
  OrderOneNontrivial: a spectral triple whose order-one condition is NOT vacuous, which is
  the witness the previous unit's own finding said was needed

  SPINE LINK L6 — WALL W9, RUNG 2, the stair §W9.2 named. `SpectralTripleBimodule` built the
  pair `(A, A°)` as one algebra and then proved two things about the order-one condition that
  between them make it look empty:
  * `orderOne_of_commute_D` — it holds for free whenever `D` is in the commutant of `π A`;
  * `orderOne_of_central_piOp` — it holds for EVERY `D` whatever, however far from central,
    as soon as `πOp`'s image is CENTRAL.
  and order-zero already forces `πOp A°` into the commutant of `π A`, so **if `π` is
  irreducible then `πOp` is central by Schur and order-one says nothing at all.** That file's
  only witness was the scalars on `ℂ²`, which falls into exactly that trap: its `π` is
  scalar, so no choice of `D` would have made its order-one say anything.

  **So the open question was not "is the axiom true here" but "is the axiom ever doing
  anything".** This file answers it with a witness, and the answer is yes — in the reducible
  case, which is where §W9.2 said the content would be.

  THE WITNESS, and every piece of it is a concrete matrix.
  `A = M₂(ℂ)`, `H = EuclideanSpace ℂ (Fin 2 × Fin 2)` — the regular bimodule in Kronecker
  coordinates — with
  * `piL a = a ⊗ 1` (left slot), `piR (op b) = 1 ⊗ bᵀ` (right slot). Order-zero is then the
    Kronecker factorisation `(a ⊗ 1)(1 ⊗ c) = a ⊗ c = (1 ⊗ c)(a ⊗ 1)`, not a coincidence:
    `Matrix.mul_kronecker_mul` with `mul_one` and `one_mul`. The transpose makes `op b ↦ bᵀ`
    a homomorphism out of the OPPOSITE algebra — `Matrix.transposeAlgEquiv`, which is the
    same device `CascadeEnd` uses for the Azumaya square.
  * `D = σ₁ ⊗ 1`, `J = 1 ⊗ σ₁`, `γ = 1 ⊗ σ₃`. The KO-6 signs `(1, 1, -1)` hold because `σ₁`
    and `σ₃` are anticommuting involutions, and `J D = D J` holds because `D` lives in the
    LEFT slot and `J` in the right one, so they commute for free.

  WHAT IS PROVED, and the third item is the one the unit exists for.
  * **`witnessTriple`** — a `SpectralTripleBimodule.Triple ℂ ℂ (M₂(ℂ)) H`. So the structure
    has a second instance, and this one is not a scalar action.
  * **`orderOne_has_content`** — `⁅D, piW σ₃⁆ ≠ 0`. The one-form is genuinely non-zero, so
    order-one is a real condition here and not an identity between zeroes. This is the
    theorem the unit exists for.
  * **`Dw_not_commute_piW`** and **`piOpW_not_central`** — the hypotheses of BOTH vacuity
    theorems fail: `D` is not in the commutant of `π A`, and `πOp`'s image is not central
    (`Jw` fails to commute with `piOpW (op σ₃)`, both living in the right slot where
    `σ₁σ₃ ≠ σ₃σ₁`). So the witness ESCAPES the traps rather than satisfying their conclusions
    by accident, and `witness_escapes_both_traps` states all four facts as one theorem.
  * **`orderOne_holds_structurally`** — and the reason order-one holds is worth naming,
    because it is not smallness of anything. The one-form `⁅D, piL a⁆` lives in the LEFT
    Kronecker slot and `piR`'s image lives in the RIGHT one, and different slots commute.
    **That is the content of the order-one axiom for a regular bimodule**: left
    multiplications and right multiplications commute, so every one-form built from a left
    action automatically commutes with the right action.

  WHAT IS **NOT** CLAIMED.
  * **Faithfulness of `bimodule` for this witness is NOT established**, and it was planned
    and dropped rather than quietly omitted. `SpectralTripleBimodule.doubled_isSemisimple`
    needs an injective `bimodule`, and the natural route —
    `Matrix.kroneckerTMulAlgEquiv` — lands in `Matrix (m × n) (m × n) (ℂ ⊗[ℂ] ℂ)`, whose
    entries are a tensor product rather than scalars, so it needs an entrywise
    `TensorProduct.lid` transport plus a match against the `⊗ₖ` formula. That is plumbing for
    a conclusion the estate already has by a shorter road (`CascadeEnd.azumayaEquiv`, off
    `IsAzumaya.matrix`), so **no semisimplicity statement is made here** and the unit claims
    only what it proves.
  * **Rung 2 is still not climbed**, and this does not climb it. No involution is classified
    and no factor list is cut. What the unit supplies is the object the next stair needs: a
    triple in which order-one is a live hypothesis, so that asking what it forces is not
    asking about a vacuous condition.
  * **This is not a REAL spectral triple.** `𝕂 = 𝕜 = ℂ` here and `J` is ℂ-linear, whereas a
    real structure is conjugate-linear — the weakening `SpectralTripleBimodule`'s header
    already declares, and the reason no conclusion there or here uses `J`. Over `ℝ` the
    honest `J` would be `x ↦ xᴴ`; **and the real case is genuinely different rather than
    merely harder**, because `ℂ ⊗[ℝ] ℂ` is not a field, so the regular bimodule of `M₂(ℂ)`
    over `ℝ` is NOT faithful as an `A ⊗[ℝ] Aᵐᵒᵖ`-module and `doubled_isSemisimple` would not
    apply to it. That contrast is recorded in `UNLOCK_WATCHLIST` 262 and not resolved here.
  * **This is not the cascade's triple and not the estate's KO-6 triple.** No theorem
    connects it to `CascadeHilbert`, `CascadeAlgebra` or the 96; `KOSixSpectralTriple.piRep`
    still cannot instantiate anything, being provably non-additive in the matrix
    (`ERRATUM 565`, `UNLOCK_WATCHLIST` 261).
  * **`γ` is not a physical grading here** — it is an anticommuting partner for `J`, chosen
    to satisfy the KO-6 relations, with no chirality interpretation and no `D`-anticommutation
    claimed.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import SpectralTripleBimodule
import SpectralCutoffFactorises

namespace OrderOneNontrivial

open Matrix SpectralTripleBimodule
open scoped Kronecker TensorProduct

noncomputable section

/-! ## 1. Matrices as endomorphisms of a Euclidean space, as an algebra map -/

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- `ContinuousLinearMap.toLinearMapRingHom` upgraded to an algebra map: the scalars go where
they should, so `commutes'` is `rfl`. -/
def clmToEnd : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →ₐ[ℂ]
    Module.End ℂ (EuclideanSpace ℂ ι) :=
  { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ => rfl }

/-- Matrices act on `EuclideanSpace ℂ ι` as an algebra, through Mathlib's
`Matrix.toEuclideanCLM`. -/
def matAlg : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ ι) :=
  (clmToEnd ι).comp (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toAlgHom

theorem matAlg_injective : Function.Injective (matAlg ι) := by
  intro X Y h
  have h' : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) X
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) Y :=
    ContinuousLinearMap.coe_injective (by
      simpa [matAlg, clmToEnd, ContinuousLinearMap.toLinearMapRingHom] using h)
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).injective h'

/-- The ⋆-condition for `matAlg`, from `toEuclideanCLM` being a `StarAlgEquiv` and the
`Star` on continuous linear maps being the adjoint. -/
theorem matAlg_star (X : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    inner ℂ (matAlg ι X u) v = inner ℂ u (matAlg ι (star X) v) := by
  have hs : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (star X)
      = star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) X) := map_star _ _
  simp only [matAlg, clmToEnd, AlgHom.coe_comp, Function.comp_apply,
    AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, StarAlgEquiv.coe_toAlgEquiv,
    ContinuousLinearMap.toLinearMapRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, AlgHom.coe_mk, hs]
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right _ u v).symm

/-! ## 2. The two Kronecker slots, as algebra maps -/

variable (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- `a ↦ a ⊗ 1`, the LEFT slot, as an algebra map. Built on
`SpectralCutoffFactorises.kroneckerRight`, which was the `RingHom` version and whose only
other consumer is that file's own exponential theorem. -/
def kronLeft : Matrix m m ℂ →ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' a b := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by simp
  map_add' a b := by simp [Matrix.add_kronecker]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]

@[simp]
theorem kronLeft_apply (a : Matrix m m ℂ) :
    kronLeft m n a = a ⊗ₖ (1 : Matrix n n ℂ) := rfl

/-- `kronLeft` is `SpectralCutoffFactorises.kroneckerRight` with the algebra structure added,
which is why the two agree on the nose. Recorded so that the `RingHom` version has a second
consumer rather than one. -/
theorem kronLeft_eq_kroneckerRight (a : Matrix m m ℂ) :
    kronLeft m n a = SpectralCutoffFactorises.kroneckerRight m n a := rfl

/-- `op b ↦ 1 ⊗ bᵀ`, the RIGHT slot, as an algebra map out of the OPPOSITE algebra. The
transpose is what turns an anti-homomorphism into a homomorphism, via
`Matrix.transposeAlgEquiv`. -/
def kronRight : (Matrix n n ℂ)ᵐᵒᵖ →ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun b := (1 : Matrix m m ℂ) ⊗ₖ (MulOpposite.unop b)ᵀ
  map_one' := by
    change (1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)ᵀ = 1
    rw [Matrix.transpose_one, Matrix.one_kronecker_one]
  map_mul' b c := by
    change (1 : Matrix m m ℂ) ⊗ₖ (MulOpposite.unop (b * c))ᵀ = _
    rw [MulOpposite.unop_mul, Matrix.transpose_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by simp
  map_add' b c := by simp [Matrix.kronecker_add]
  commutes' r := by
    change (1 : Matrix m m ℂ) ⊗ₖ (MulOpposite.unop (algebraMap ℂ _ r))ᵀ = algebraMap ℂ _ r
    rw [MulOpposite.algebraMap_apply, MulOpposite.unop_op, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]

@[simp]
theorem kronRight_apply (b : (Matrix n n ℂ)ᵐᵒᵖ) :
    kronRight m n b = (1 : Matrix m m ℂ) ⊗ₖ (MulOpposite.unop b)ᵀ := rfl

/-- **Order-zero, structurally.** Different Kronecker slots commute, and that is the whole
content: `(a ⊗ 1)(1 ⊗ c) = a ⊗ c = (1 ⊗ c)(a ⊗ 1)`. -/
theorem kron_slots_commute (a : Matrix m m ℂ) (b : (Matrix n n ℂ)ᵐᵒᵖ) :
    Commute (kronLeft m n a) (kronRight m n b) := by
  change (a ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ _)
      = ((1 : Matrix m m ℂ) ⊗ₖ _) * (a ⊗ₖ (1 : Matrix n n ℂ))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

/-! ## 3. The witness: `M₂(ℂ)` on the regular bimodule in Kronecker coordinates -/

/-- The index set: `Fin 2 × Fin 2`, so `H` is four-dimensional and splits as a Kronecker
product of two two-dimensional slots. -/
abbrev Slots : Type := Fin 2 × Fin 2

/-- The Hilbert space. -/
abbrev Hw : Type := EuclideanSpace ℂ Slots

/-! `σ₁` and `σ₃` are `SpectralTripleBimodule.pauli1` and `pauli3`, imported rather than
redeclared — as are their involution and anticommutation lemmas, `pauli1_sq`, `pauli3_sq` and
`pauli1_anticomm`. `dupbody_scan` caught a first draft that redeclared all five under shorter
names in a file that already imports them. -/

/-- `σ₁` and `σ₃` do not commute — the fact that makes the one-form below non-zero. Not in
`SpectralTripleBimodule`, which needed only the anticommutation. -/
theorem p1_p3_ne : pauli1 * pauli3 ≠ pauli3 * pauli1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h01
  simp only [pauli1, pauli3, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] at h01
  norm_num at h01

/-- Transpose and conjugate transpose commute. Stated because the ⋆-condition on the RIGHT
slot needs it: `star` on the opposite algebra gives `ᴴ` and the slot map gives `ᵀ`. -/
theorem conjT_transpose_comm {ι' : Type*} (M : Matrix ι' ι' ℂ) : (Mᵀ)ᴴ = (Mᴴ)ᵀ := rfl

/-! ### The two actions -/

/-- The left action, `a ↦ a ⊗ 1` on `H`. -/
def piW : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ Hw :=
  (matAlg Slots).comp (kronLeft (Fin 2) (Fin 2))

/-- The right action, `op b ↦ 1 ⊗ bᵀ` on `H`. -/
def piOpW : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ →ₐ[ℂ] Module.End ℂ Hw :=
  (matAlg Slots).comp (kronRight (Fin 2) (Fin 2))

/-- **Order-zero for the witness**, extracted because the order-ONE proof needs it too: the
one-form lives in the left slot, so it commutes with the right slot for the same reason `π`
does. -/
theorem piW_piOpW_commute (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) : Commute (piW a) (piOpW b) :=
  (kron_slots_commute (Fin 2) (Fin 2) a b).map (matAlg Slots)

/-! ### The operators, and the KO-6 relations as matrix identities -/

/-- The Dirac operator, in the LEFT slot so that it fails to commute with `piW`. -/
def Dw : Module.End ℂ Hw := piW pauli1

/-- The real structure, in the RIGHT slot so that it commutes with `Dw` for free. -/
def Jw : Module.End ℂ Hw := matAlg Slots ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)

/-- The grading, also in the right slot, anticommuting with `Jw`. -/
def gw : Module.End ℂ Hw := matAlg Slots ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3)

theorem kron_right_p1_sq :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)
      = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, pauli1_sq, Matrix.one_kronecker_one]

theorem kron_right_p3_sq :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3)
      = 1 := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, pauli3_sq, Matrix.one_kronecker_one]

/-- `1 ⊗ (-M) = -(1 ⊗ M)`. Proved entrywise: Mathlib has `add_kronecker` and
`kronecker_add` but **no Kronecker-negation lemma at all** — `grep 'kronecker.*neg\|neg.*kronecker'`
over the full environment dump returns nothing — so this is stated rather than cited. -/
theorem kron_neg_right {ι' κ : Type*} [DecidableEq ι'] (M : Matrix κ κ ℂ) :
    (1 : Matrix ι' ι' ℂ) ⊗ₖ (-M) = -((1 : Matrix ι' ι' ℂ) ⊗ₖ M) := by
  ext i j; simp [Matrix.kroneckerMap]

theorem kron_right_anticomm :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3)
      = -(((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3)
          * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    pauli1_anticomm, kron_neg_right]

/-- **The one-form, computed.** `⁅D, π a⁆` is the left action of the commutator `⁅σ₁, a⁆`,
because both `D` and `π a` live in the left Kronecker slot. This is the identity the
order-one proof runs on, and the identity `orderOne_has_content` shows is not zero. -/
theorem oneForm_eq (a : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅Dw, piW a⁆ = piW (pauli1 * a - a * pauli1) := by
  rw [Dw, Ring.lie_def, ← map_mul, ← map_mul, ← map_sub]

/-! ### The `Triple` -/

/-- **The witness.** A `Triple` whose `π` is not a scalar action — see
`orderOne_has_content` and `piOpW_not_central` for why that is the point. -/
def witnessTriple : Triple ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ) Hw where
  π := piW
  πOp := piOpW
  D := Dw
  J := Jw
  γ := gw
  star_π a u v := by
    have h := matAlg_star Slots (kronLeft (Fin 2) (Fin 2) a) u v
    rw [kronLeft_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one] at h
    simpa [piW, Matrix.star_eq_conjTranspose] using h
  star_πOp b u v := by
    have h := matAlg_star Slots (kronRight (Fin 2) (Fin 2) b) u v
    rw [kronRight_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, conjT_transpose_comm] at h
    simpa [piOpW, MulOpposite.unop_star, Matrix.star_eq_conjTranspose] using h
  order_zero a b := piW_piOpW_commute a b
  order_one a b := by
    rw [oneForm_eq]
    exact commute_iff_lie_eq.mp (piW_piOpW_commute _ b)
  J_sq := by rw [Jw, ← map_mul, kron_right_p1_sq, map_one]
  J_comm_D := by
    rw [Jw, Dw, piW, AlgHom.coe_comp, Function.comp_apply, kronLeft_apply,
      ← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
  J_anticomm_γ := by rw [Jw, gw, ← map_mul, ← map_mul, kron_right_anticomm, map_neg]
  γ_sq := by rw [gw, ← map_mul, kron_right_p3_sq, map_one]

theorem triple_inhabited_nonscalar :
    Nonempty (Triple ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ) Hw) := ⟨witnessTriple⟩

/-! ## 4. Order-one has CONTENT here, which is what the unit exists for -/

theorem kronLeft_injective : Function.Injective (kronLeft (Fin 2) (Fin 2)) := by
  intro a b h
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [Matrix.kroneckerMap, Matrix.one_apply] using this

/-- `1 ⊗ X = 1 ⊗ Y` forces `X = Y`: the right slot is recoverable entrywise. -/
theorem kron_right_injective {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (h : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ X = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Y) : X = Y := by
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [Matrix.kroneckerMap, Matrix.one_apply] using this

theorem piW_injective : Function.Injective piW := by
  intro a b h
  exact kronLeft_injective (matAlg_injective Slots (by simpa [piW] using h))

theorem pauli3_transpose : pauli3ᵀ = pauli3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3]

/-- **THE THEOREM THE UNIT EXISTS FOR.** The one-form `⁅D, π σ₃⁆` is **non-zero**, so
order-one is a genuine condition on this triple and not an identity between zeroes. Contrast
`SpectralTripleBimodule.scalarWitness`, whose `D` is `0` and whose one-forms all vanish. -/
theorem orderOne_has_content : ⁅Dw, piW pauli3⁆ ≠ 0 := by
  rw [oneForm_eq]
  intro h
  have h0 : pauli1 * pauli3 - pauli3 * pauli1 = 0 := piW_injective (by rw [h, map_zero])
  exact p1_p3_ne (sub_eq_zero.mp h0)

/-- The Dirac operator does NOT lie in the commutant of `π`, so
`SpectralTripleBimodule.orderOne_of_commute_D` does not apply to this witness. -/
theorem Dw_not_commute_piW : ¬ (∀ a : Matrix (Fin 2) (Fin 2) ℂ, Commute Dw (piW a)) := by
  intro h
  exact orderOne_has_content (commute_iff_lie_eq.mp (h pauli3))

/-- **And `πOp`'s image is NOT central**, so
`SpectralTripleBimodule.orderOne_of_central_piOp` does not apply either. Together with
`Dw_not_commute_piW` this is what makes the witness escape both vacuity theorems rather than
satisfy their conclusions by accident: `Jw` fails to commute with `piOpW (op σ₃)`, because
both live in the right Kronecker slot and `σ₁σ₃ ≠ σ₃σ₁`. -/
theorem piOpW_not_central :
    ¬ (∀ (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) (x : Module.End ℂ Hw), Commute (piOpW b) x) := by
  intro h
  have hc := h (MulOpposite.op pauli3) Jw
  have hc' : ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3ᵀ)
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)
      = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)
        * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3ᵀ) := by
    refine matAlg_injective Slots ?_
    rw [map_mul, map_mul]
    simpa [piOpW, Jw, kronRight_apply] using hc
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at hc'
  have hm := kron_right_injective hc'
  rw [pauli3_transpose] at hm
  exact p1_p3_ne hm.symm

/-- **Why order-one nevertheless holds, and it is not smallness of anything.** The one-form
lives in the LEFT Kronecker slot and `πOp`'s image lives in the RIGHT one, and different
slots commute. **That is the content of the order-one axiom for a regular bimodule**: every
one-form built from a left action automatically commutes with the right action. So the axiom
is satisfied here for a structural reason, with a non-zero one-form — which is exactly the
configuration `SpectralTripleBimodule`'s two vacuity theorems could not produce. -/
theorem orderOne_holds_structurally (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) :
    ⁅Dw, piW a⁆ = piW (pauli1 * a - a * pauli1)
      ∧ Commute (piW (pauli1 * a - a * pauli1)) (piOpW b) :=
  ⟨oneForm_eq a, piW_piOpW_commute _ b⟩

/-- The summary, as one statement: a triple in which order-one holds, its one-form is
non-zero, and neither vacuity hypothesis is satisfied. -/
theorem witness_escapes_both_traps :
    (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        ⁅⁅Dw, piW a⁆, piOpW b⁆ = 0)
      ∧ ⁅Dw, piW pauli3⁆ ≠ 0
      ∧ ¬ (∀ a, Commute Dw (piW a))
      ∧ ¬ (∀ (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) (x : Module.End ℂ Hw),
            Commute (piOpW b) x) :=
  ⟨witnessTriple.order_one, orderOne_has_content, Dw_not_commute_piW, piOpW_not_central⟩

end

end OrderOneNontrivial
