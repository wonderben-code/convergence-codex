/-
  RealSpectralWitness: the CCM-compatible quintuple `ERRATUM 573` said the estate did not have

  SPINE LINK L6 — WALL W9, §W9.5. `UNLOCK_WATCHLIST` 265's item (1), taken.

  WHAT THIS ANSWERS. One unit ago `OppositeFromRealStructure` proved that
  `SpectralTripleBimodule.Triple` is strictly weaker than CCM's real spectral triple — it
  carries `πOp` as an independent field where CCM manufactures it as `J π(·*) J⁻¹` — and that
  the estate's only non-scalar witness fails CCM's order-zero for the `J`-implemented action
  (`oppFromJ_order_zero_fails`). That left an obvious question, and leaving it open would have
  meant an erratum with no positive half: **is there a CCM-compatible quintuple on that same
  `H` at all, or is the four-dimensional regular bimodule simply the wrong place to look?**

  **There is, and this file builds it.** Same `H`, same `π`, same `πOp` — only `J`, `D` and `γ`
  change, and the three that change are exactly the three unit 18 chose for convenience.

  **Three objects change, and they are exactly the three unit 18 chose for convenience.**
  * `J`: was `1 ⊗ σ₁` acting linearly (and, after `ERRATUM 571`, `conjPerm slotSwap`, which
    swaps the right slot). **Now `Jprod`** — conjugate, then exchange the two Kronecker
    FACTORS.
  * `D`: was `σ₁ ⊗ 1`, one slot only. **Now `σ₁ ⊗ 1 + 1 ⊗ σ₁`**, the symmetric sum.
  * `γ`: was `1 ⊗ σ₃`. **Now `gammaMat`**, a four-entry monomial matrix.
  * And the consequence: `πOp b = J π(b*) J` **FAILED** for unit 18's witness, taking CCM's
    order-zero down with it; here it **HOLDS**, on the nose, for every `a`.

  WHAT IS PROVED.
  * **`Dsym`** — `σ₁ ⊗ 1 + 1 ⊗ σ₁`, and `Jprod_comm_Dccm`: it commutes with `Jprod`, because it
    is real and symmetric under exchanging the Kronecker factors. **That is the repair of the
    clash `Jprod_not_commute_Dw` recorded**: unit 18's `D` sat in one slot, so exchanging the
    factors moved it; this one is the symmetric sum of both slots and is fixed.
  * **`oneForm_Dccm`** — `⁅D, π a⁆ = π (σ₁a - aσ₁)`, and the second summand contributes nothing
    because `1 ⊗ σ₁` commutes with every `a ⊗ 1`. So the one-form lands back in the LEFT slot,
    which is what makes order-one hold (`orderOne_Dccm`) while remaining **non-zero**
    (`orderOne_Dccm_has_content`, at `a = σ₃`).
  * **`gammaMat`** — the grading, four non-zero entries: `i` at `(00),(11)`, `1` at
    `(01),(01)`, `-1` at `(10),(10)`, `-i` at `(11),(00)`. `gammaCcm_sq` gives `γ² = 1` and
    `Jprod_anticomm_gammaCcm` the KO-6 sign `ε″ = -1`.
  * **`ccm_conditions`** — all of it as one theorem, so that no reader has to assemble the
    list: order-zero, order-one, a non-zero one-form, `D` outside the commutant, `J² = 1`,
    `JD = DJ`, `Jγ = -γJ`, `γ² = 1`, **and `πOp b = J π(b*) J`**.

  HOW `gammaMat` WAS FOUND, because the method is the reusable part and guessing did not work.
  Writing `J = conjPerm prodSwap` as `S · conj(·) · S` with `S` the exchange matrix, the KO-6
  sign `ε″ = -1` reads `S γ̄ S = -γ`, which is **`ℝ`-LINEAR in `γ`** — so its solutions form a
  subspace, computed to be **16-dimensional over `ℝ`** inside `M₄(ℂ)`, and the only remaining
  condition, `γ² = 1`, is quadratic. Two searches inside that subspace, both finite and both
  reported here with their exact scope rather than as "none exist":
  * **monomial matrices** — one non-zero entry per row, entries in `{±1, ±i}`: **four
    solutions**, all the same up to sign. `gammaMat` is one of them.
  * **combinations of one, two or three `σ_μ ⊗ σ_ν`** with coefficients in
    `{±1, ±i, ±½, ±i/2}`: **none.** A four-term one does exist —
    `½(σ₁⊗1 - 1⊗σ₁ + σ₂⊗σ₃ + σ₃⊗σ₂)`, checked and not used, because its entries are
    `±(1±i)/2` and the monomial form is cheaper to verify in Lean.
  **Neither search is exhaustive over the subspace**, so nothing here says a simpler `γ` does
  not exist; what they explain is why the short hand-guesses failed and why the matrix below
  is written entrywise rather than as a Kronecker expression.

  WHAT IS **NOT** CLAIMED.
  * **`Triple` is NOT amended here, and this is NOT yet a `Triple`.** Adding the field
    `πOp_impl` and migrating both witnesses is the next unit; doing it in this one would mean
    changing a structure and building its replacement instance in the same breath, with no
    green build in between.
  * **Unit 18's witness is not deleted and nothing proved about it is withdrawn.** `Dw`, `Jw`,
    `gw` and every theorem about them stand — including `oppFromJ_order_zero_fails`, which is
    the reason this file exists and which would be meaningless if its subject vanished.
  * **No uniqueness.** Four monomial `γ`s were found and one was taken; nothing says the
    quintuple is unique, nor that `Dsym` is the only compatible `D`.
  * **No claim about the KO-DIMENSION.** The signs `(ε, ε′, ε″) = (1, 1, -1)` are what
    `Triple` asks for and what is proved; **`D` is not shown to anticommute with `γ`**, and
    without that the pair `(D, γ)` is not a graded Dirac operator. Unit 18's witness had the
    same gap and it is not closed here.
  * **Not the cascade's triple, not the estate's KO-6 triple**, no `K`-theory, no factor list
    is cut, rung 2 is not climbed.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import OppositeFromRealStructure

namespace RealSpectralWitness

open Matrix MulOpposite SpectralTripleBimodule OrderOneNontrivial ConjugatePermutation
open OppositeFromRealStructure
open scoped Kronecker ComplexConjugate

noncomputable section

/-! ## 1. A Dirac operator the textbook real structure accepts -/

/-- `σ₁ ⊗ 1 + 1 ⊗ σ₁`. **Symmetric under exchanging the Kronecker factors**, which is exactly
what `Jprod` requires — unit 18's `D = σ₁ ⊗ 1` sat in one slot, so the exchange moved it
(`Jprod_not_commute_Dw`). -/
def Dsym : Matrix Slots Slots ℂ :=
  pauli1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1

/-- The Dirac operator as an endomorphism. -/
def Dccm : Module.End ℂ Hw := matAlg Slots Dsym

theorem submatrix_prodSwap_Dsym :
    (Dsym.submatrix prodSwap prodSwap).map (starRingEnd ℂ) = Dsym := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Dsym, prodSwap, pauli1, Matrix.kroneckerMap, Matrix.one_apply]

/-- **KO-6 sign `ε′ = 1`**: `Jprod` commutes with this `D`. -/
theorem Jprod_comm_Dccm (v : Hw) : Jprod (Dccm (Jprod v)) = Dccm v := by
  rw [Dccm, matAlg_apply, matAlg_apply, Jprod, conjPerm_conj prodSwap prodSwap_involutive,
    submatrix_prodSwap_Dsym]

/-! ## 2. The one-form, and order-one -/

/-- The second summand of `D` contributes nothing to the one-form: `1 ⊗ σ₁` commutes with every
`a ⊗ 1`. So the one-form is back in the LEFT slot. -/
theorem oneForm_Dccm (a : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅Dccm, piW a⁆ = piW (pauli1 * a - a * pauli1) := by
  have hmat : Dsym * (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        - (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Dsym
      = (pauli1 * a - a * pauli1) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext p q
    obtain ⟨i, j⟩ := p
    obtain ⟨k, l⟩ := q
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Dsym, Matrix.kroneckerMap, Matrix.mul_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Matrix.one_apply, pauli1, Matrix.vecMul, dotProduct]
  have hlie : ⁅Dccm, piW a⁆
      = matAlg Slots (Dsym * (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
          - (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Dsym) := by
    rw [Ring.lie_def, map_sub, map_mul, map_mul]
    rfl
  rw [hlie, hmat]
  rfl

/-- **Order-one holds**, because the one-form lives in the left slot and `πOp`'s image in the
right one. -/
theorem orderOne_Dccm (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) : ⁅⁅Dccm, piW a⁆, piOpW b⁆ = 0 := by
  rw [oneForm_Dccm]
  exact commute_iff_lie_eq.mp (piW_piOpW_commute _ b)

/-- **And it is not vacuous**: the one-form at `σ₃` is non-zero. -/
theorem orderOne_Dccm_has_content : ⁅Dccm, piW pauli3⁆ ≠ 0 := by
  intro h
  rw [oneForm_Dccm] at h
  have h0 : pauli1 * pauli3 - pauli3 * pauli1 = 0 := piW_injective (by rw [h, map_zero])
  exact p1_p3_ne (sub_eq_zero.mp h0)

/-- `D` is outside the commutant of `π`, so `orderOne_of_commute_D` does not apply. -/
theorem Dccm_not_commute_piW :
    ¬ (∀ a : Matrix (Fin 2) (Fin 2) ℂ, Commute Dccm (piW a)) := by
  intro h
  exact orderOne_Dccm_has_content (commute_iff_lie_eq.mp (h pauli3))

/-! ## 3. The grading -/

/-- **The grading.** Four non-zero entries, found by solving the `ℝ`-linear condition
`S γ̄ S = -γ` and searching its 16-dimensional solution space for a monomial square root of
`1` — see the header for why two- and three-term `σ_μ ⊗ σ_ν` guesses cannot work. -/
def gammaMat : Matrix Slots Slots ℂ := Matrix.of fun p q =>
  if p = (0, 0) ∧ q = (1, 1) then Complex.I
  else if p = (0, 1) ∧ q = (0, 1) then 1
  else if p = (1, 0) ∧ q = (1, 0) then -1
  else if p = (1, 1) ∧ q = (0, 0) then -Complex.I
  else 0

/-- The grading as an endomorphism. -/
def gammaCcm : Module.End ℂ Hw := matAlg Slots gammaMat

theorem gammaMat_sq : gammaMat * gammaMat = 1 := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [gammaMat, Matrix.mul_apply]

theorem submatrix_prodSwap_gammaMat :
    (gammaMat.submatrix prodSwap prodSwap).map (starRingEnd ℂ) = -gammaMat := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [gammaMat, prodSwap]

/-- **The grading is an involution.** -/
theorem gammaCcm_sq : gammaCcm * gammaCcm = 1 := by
  rw [gammaCcm, ← map_mul, gammaMat_sq, map_one]

/-- **KO-6 sign `ε″ = -1`**: `J` and `γ` anticommute. -/
theorem Jprod_anticomm_gammaCcm (v : Hw) : Jprod (gammaCcm (Jprod v)) = -(gammaCcm v) := by
  rw [gammaCcm, matAlg_apply, matAlg_apply, Jprod, conjPerm_conj prodSwap prodSwap_involutive,
    submatrix_prodSwap_gammaMat, map_neg, ContinuousLinearMap.neg_apply]

/-! ## 4. All of it at once -/

/-- **THE THEOREM THE UNIT EXISTS FOR.** On the same `H`, with the same `π` and the same `πOp`
as unit 18's witness, the quintuple `(π, πOp, D, J, γ)` with `J = Jprod`, `D = Dccm`,
`γ = gammaCcm` satisfies **every** condition `SpectralTripleBimodule.Triple` asks for **and**
CCM's relation `πOp b = J π(b*) J`, which unit 18's witness provably fails
(`OppositeFromRealStructure.oppFromJ_order_zero_fails`). Order-one is live rather than vacuous,
and `D` is outside the commutant. -/
theorem ccm_conditions :
    (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        Commute (piW a) (piOpW b))
      ∧ (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
          ⁅⁅Dccm, piW a⁆, piOpW b⁆ = 0)
      ∧ ⁅Dccm, piW pauli3⁆ ≠ 0
      ∧ ¬ (∀ a : Matrix (Fin 2) (Fin 2) ℂ, Commute Dccm (piW a))
      ∧ (∀ v : Hw, Jprod (Jprod v) = v)
      ∧ (∀ v : Hw, Jprod (Dccm (Jprod v)) = Dccm v)
      ∧ (∀ v : Hw, Jprod (gammaCcm (Jprod v)) = -(gammaCcm v))
      ∧ gammaCcm * gammaCcm = 1
      ∧ (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (v : Hw),
          Jprod (piW (star a) (Jprod v)) = piOpW (op a) v) :=
  ⟨piW_piOpW_commute, orderOne_Dccm, orderOne_Dccm_has_content, Dccm_not_commute_piW,
    fun v => LinearMap.congr_fun (conjPerm_comp_self prodSwap prodSwap_involutive) v,
    Jprod_comm_Dccm, Jprod_anticomm_gammaCcm, gammaCcm_sq, piOpW_via_prodSwap⟩

end

end RealSpectralWitness
