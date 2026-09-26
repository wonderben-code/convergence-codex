/-
  OppositeFromRealStructure: in CCM the right action is NOT a datum, and the estate's
  `Triple` lets it be one

  SPINE LINK L6 — WALL W9, RUNG 2. The question `UNLOCK_WATCHLIST` 264 opened one unit ago.

  THE POINT, STATED FIRST BECAUSE IT IS A NEGATIVE ONE ABOUT THIS ESTATE'S OWN STRUCTURE.
  In Connes' definition of a real spectral triple the right action is **not given**: it is
  `b° = J π(b*) J⁻¹`, manufactured from the real structure. Order-zero `[π(a), b°] = 0` and
  order-one `[[D, π(a)], b°] = 0` are therefore conditions relating `π`, `D` and `J` — three
  objects, not four. **`SpectralTripleBimodule.Triple` carries `πOp` as an INDEPENDENT FIELD**,
  with nothing tying it to `J`. So the structure is strictly weaker than CCM's, and every
  theorem proved about it is a theorem about the weaker object.

  Until the previous unit that gap was invisible, because `J` was a `ℂ`-linear map and
  `J π(b*) J` was not the right kind of thing to compare `πOp` with. Now that `J` is genuinely
  conjugate-linear (`ERRATUM 571`), the comparison is available — and this file makes it.

  WHAT IS BUILT.
  * **`conjByJ`** and **`oppFromJ`** — CCM's construction, over a variable algebra. `conjByJ T a`
    is `J ∘ π(a) ∘ J`, which is `𝕜`-LINEAR because `J` is antilinear twice, and `oppFromJ T`
    is `b ↦ conjByJ T (star (unop b))` packaged as a `RingHom` out of `Aᵐᵒᵖ`. Its
    multiplicativity is exactly `J² = 1` cancelling in the middle, and `star` being an
    antihomomorphism is what makes the source the OPPOSITE algebra rather than `A`.
  * **`conjPerm_conj`** — the computational tool: for an involutive `σ`,
    `J ∘ M ∘ J = (M.submatrix σ σ).map conj` as matrices. Two applications of
    `ConjugatePermutation.conjPerm_toEuclideanCLM`, and it turns every statement below into a
    matrix identity.

  AND THE THREE FACTS ABOUT THE ESTATE'S OWN WITNESS, which is what the unit exists for.
  * **`oppFromJw_eq`** — for unit 18's data, `J π(a*) J = π(aᵀ)`. That `J` sends the left
    Kronecker slot to the left Kronecker slot; its `πOp` lives in the RIGHT slot. **So `πOp`
    is not `J`-implemented**, and `oppFromJw_ne_piOpW` proves the two maps differ.
  * **`oppFromJw_order_zero_fails`** — and they differ so far that CCM's order-zero FAILS for
    the `J`-implemented action: `π(σ₃)` and `J π(σ₁*) J = π(σ₁)` are both left-slot operators
    and `σ₁σ₃ ≠ σ₃σ₁`. **That data is not a CCM real spectral triple and cannot be made one
    by keeping this `J`.** (These three were stated about `witnessTriple` when this file was
    written. `ERRATUM 573`'s amendment deleted that `Triple` — it fails the new field — so
    they are now stated about the raw maps, through `oppFromJw`. The mathematics is
    unchanged; what is gone is the packaging.)
  * **`oppFromJ_eq_piOp`** — **the amendment's payoff, one line.** Once `Triple` carries
    `πOp_impl`, `oppFromJ` is not a rival to `πOp` but a description of it: they agree for
    every `Triple`. What this file measured as a GAP became a THEOREM the moment the axiom was
    added, which is the cleanest evidence that the axiom was the missing one.
  * **`piOpW_via_prodSwap`** — but the right action IS implementable on this `H`, by a
    different real structure: `Jprod`, conjugation followed by exchanging the two Kronecker
    factors, gives `Jprod π(a*) Jprod = πOp (op a)` **on the nose**. That is the transpose map
    `x ↦ x*` on `M₂(ℂ)` in Kronecker coordinates, which is the textbook `J` for a regular
    bimodule. So the defect is the CHOICE of `J` in unit 18, not the geometry of the witness.
  * **`Jprod_not_commute_Dw`** — and the correct `J` is incompatible with the witness's `D`:
    `Jprod D Jprod = π'(1 ⊗ σ₁) ≠ D = π'(σ₁ ⊗ 1)`, so `JD = DJ` fails. **Unit 18 chose `J` in
    the right slot precisely so that `JD = DJ` would hold for free**, and that choice is what
    made `πOp` un-implementable. The two KO-6 requirements pull in opposite directions here,
    which is a fact about the witness and is stated rather than resolved.

  WHAT IS **NOT** CLAIMED, and the wall does not fall.
  * **No claim that unit 18's data is worthless.** Everything proved about it is true of it,
    and none of it was deleted with the `Triple` wrapper: `Dw`, `Jw`, `gw`, `oneForm_eq`,
    `orderOne_has_content`, `Dw_not_commute_piW`, `piOpW_not_central` and
    `orderOne_holds_structurally` all stand. What is now known is which object those theorems
    are about.
  * **No claim that no CCM triple exists on this `H`.** `piOpW_via_prodSwap` shows the right
    action is implementable; what is not built is a `D` compatible with `Jprod` together with
    a grading, nor is it shown that one exists. `Jprod_not_commute_Dw` rules out ONE `D`, the
    one already there.
    ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): built 26 minutes after this file,
    in `RealSpectralWitness` (`007ffbc`): `Dccm` commutes with `Jprod` and `gammaCcm` is a grading
    with the KO-6 signs (`ccm_conditions`); `D` anticommuting with it followed in `bb8d637`
    (`Dccm_anticomm_gammaCcm`). Kept as written (`ERRATUM 94`).
  * ~~**`Triple` is NOT amended here.**~~ **AMENDED the same day**, in the unit after the one
    that built this file: `Triple` now carries `πOp_impl`, and `OrderOneNontrivial`'s witness
    was deleted because it fails that field, with `RealSpectralWitness.realWitness` as its
    replacement. Discovering the need for the axiom, exhibiting a witness that can satisfy it,
    and adding it were three units, deliberately, so that no commit changed a structure without
    a green instance of it.
  * **`oppFromJ` is a `RingHom`, not an `AlgHom`.** The `𝕂`-algebra structure needs
    `conj (algebraMap 𝕂 𝕜 r) = algebraMap 𝕂 𝕜 (star r)`, which is a compatibility between the
    star on `𝕂` and the star on `𝕜` that `Triple`'s binders do not carry. The same shape as
    `KOSixInnerProduct.piRepRing`, and none of the conclusions below need the algebra
    packaging.
  * **No `K`-theory, no rung 3–5, no cascade, no factor list is cut.**

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import OrderOneNontrivial

namespace OppositeFromRealStructure

open Matrix MulOpposite SpectralTripleBimodule OrderOneNontrivial ConjugatePermutation
open scoped Kronecker ComplexConjugate

noncomputable section

/-! ## 1. CCM's construction, over a variable algebra -/

variable {𝕂 𝕜 A H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕂 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]

/-- The KO-6 sign `ε = 1` in pointwise form. -/
theorem J_apply_J (T : Triple 𝕂 𝕜 A H) (v : H) : T.J (T.J v) = v :=
  LinearMap.congr_fun T.J_sq v

/-- `J ∘ π(a) ∘ J`. **It is `𝕜`-LINEAR**, because `J` is conjugate-linear twice and
`RingHomCompTriple (starRingEnd 𝕜) (starRingEnd 𝕜) (RingHom.id 𝕜)` composes the twists away —
which is why this construction was not expressible before `ERRATUM 571`. -/
def conjByJ (T : Triple 𝕂 𝕜 A H) (a : A) : Module.End 𝕜 H :=
  T.J.comp ((T.π a).comp T.J)

@[simp] theorem conjByJ_apply (T : Triple 𝕂 𝕜 A H) (a : A) (v : H) :
    conjByJ T a v = T.J (T.π a (T.J v)) := rfl

/-- **CCM's right action, manufactured from `J` rather than given**: `b ↦ J π(b*) J`. A
`RingHom` out of `Aᵐᵒᵖ` — `star` is an antihomomorphism, which is what makes the source the
opposite algebra, and `J² = 1` is what cancels in the middle of a product. -/
def oppFromJ (T : Triple 𝕂 𝕜 A H) : Aᵐᵒᵖ →+* Module.End 𝕜 H where
  toFun b := conjByJ T (star (unop b))
  map_one' := by ext v; simp [J_apply_J]
  map_mul' b c := by ext v; simp [J_apply_J]
  map_zero' := by ext v; simp
  map_add' b c := by ext v; simp

@[simp] theorem oppFromJ_apply (T : Triple 𝕂 𝕜 A H) (b : Aᵐᵒᵖ) (v : H) :
    oppFromJ T b v = T.J (T.π (star (unop b)) (T.J v)) := rfl

/-- **THE AMENDMENT'S PAYOFF, one line.** Once `Triple` carries `πOp_impl` (`ERRATUM 573`),
`oppFromJ` is not a rival to `πOp` but a description of it: they agree for every `Triple`. What
this file measured as a GAP became a THEOREM the moment the axiom was added, which is the
cleanest evidence that the axiom was the missing one. -/
theorem oppFromJ_eq_piOp (T : Triple 𝕂 𝕜 A H) (b : Aᵐᵒᵖ) : oppFromJ T b = T.πOp b := by
  ext v
  exact (T.πOp_impl b v).symm

/-! ## 2. The computational tool -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Conjugating a matrix by an involutive `conjPerm`** conjugates its entries and permutes
its indices: `J ∘ M ∘ J` is the action of `(M.submatrix σ σ).map conj`. Two applications of
`ConjugatePermutation.conjPerm_toEuclideanCLM`, the second absorbed by `σ` being an
involution. -/
theorem conjPerm_conj (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i) (M : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    conjPerm σ (Matrix.toEuclideanCLM (𝕜 := ℂ) M (conjPerm σ v))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) ((M.submatrix σ σ).map (starRingEnd ℂ)) v := by
  rw [conjPerm_toEuclideanCLM]
  congr 1
  exact LinearMap.congr_fun (conjPerm_comp_self σ hσ) v

/-! ## 3. The estate's own witness, tested against CCM's construction -/

/-- `σ₁` is symmetric. Needed because `oppFromJ` carries a `star` and `kronRight` a transpose,
and the two have to be reconciled at `σ₁`. `pauli3_transpose` is already in
`OrderOneNontrivial`; this is its missing partner. -/
theorem pauli1_transpose : pauli1ᵀ = pauli1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1]

/-- `piW` at a vector, as a bare `toEuclideanCLM`. `rfl`, because `matAlg_apply` and
`kronLeft_apply` both are. Stated so that no proof below has to unfold an `AlgHom` with
`rw`, which does not work through `AlgHom.comp`. -/
theorem piW_apply (a : Matrix (Fin 2) (Fin 2) ℂ) (v : Hw) :
    piW a v = Matrix.toEuclideanCLM (𝕜 := ℂ)
      (a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) v := rfl

/-- `piOpW` at a vector, likewise. -/
theorem piOpW_apply (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) (v : Hw) :
    piOpW b v = Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (unop b)ᵀ) v := rfl

/-- **The matrix identity behind `oppFromJ_witness`.** Conjugating `a* ⊗ 1` by the RIGHT-slot
swap returns `aᵀ ⊗ 1` — still in the LEFT slot, because the swap never touches it. -/
theorem submatrix_slotSwap_kronLeft (a : Matrix (Fin 2) (Fin 2) ℂ) :
    (((star a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix slotSwap slotSwap).map
        (starRingEnd ℂ) = aᵀ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp [slotSwap, Matrix.kroneckerMap, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

/-- The action CCM's recipe manufactures from unit 18's `J`. **Written out rather than as
`oppFromJ witnessTriple`**, because that `Triple` no longer exists: `ERRATUM 573` added the
field `πOp_impl` and this data fails it, which is what the three theorems below prove. The
`J`, `π` and the two maps are unchanged; only the packaging is gone. -/
def oppFromJw (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) : Module.End ℂ Hw :=
  Jw.comp ((piW (star (unop b))).comp Jw)

@[simp] theorem oppFromJw_apply (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) (v : Hw) :
    oppFromJw b v = Jw (piW (star (unop b)) (Jw v)) := rfl

/-- **The witness's `J` sends the left slot to the left slot.** `J π(a*) J = π(aᵀ)`, so the
action CCM would manufacture from this `J` is another LEFT action, not the right one. -/
theorem oppFromJw_eq (a : Matrix (Fin 2) (Fin 2) ℂ) :
    oppFromJw (op a) = piW aᵀ := by
  refine LinearMap.ext fun v => ?_
  change Jw (piW (star a) (Jw v)) = piW aᵀ v
  rw [piW_apply, piW_apply, Jw, conjPerm_conj slotSwap slotSwap_involutive,
    submatrix_slotSwap_kronLeft]

/-- **So `πOp` is NOT `J`-implemented for this witness**, witnessed at `σ₃`: the manufactured
action is `π(σ₃)`, a left-slot operator, and `πOp (op σ₃)` is a right-slot one. -/
theorem oppFromJw_ne_piOpW :
    oppFromJw (op pauli3) ≠ piOpW (op pauli3) := by
  rw [oppFromJw_eq, pauli3_transpose]
  intro h
  have hm : pauli3 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3ᵀ :=
    matAlg_injective Slots (LinearMap.ext fun v => by
      have := LinearMap.congr_fun h v
      rwa [piW_apply, piOpW_apply, unop_op] at this)
  have h01 : (1 : ℂ) = -1 := by
    simpa [Matrix.kroneckerMap, Matrix.one_apply, pauli3] using
      congrFun (congrFun hm (0, 1)) (0, 1)
  exact absurd h01 (by norm_num)

/-- **AND THE FAILURE IS NOT COSMETIC: CCM's ORDER-ZERO FAILS for the `J`-implemented action.**
`π(σ₃)` and `J π(σ₁*) J = π(σ₁)` are both left-slot operators and `σ₁σ₃ ≠ σ₃σ₁`. So
`witnessTriple` is **not** a CCM real spectral triple, and no choice of `πOp` can rescue it
while it keeps this `J` — the right action is not a free parameter in CCM. -/
theorem oppFromJw_order_zero_fails :
    ¬ ∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        Commute (piW a) (oppFromJw b) := by
  intro h
  have hc := h pauli3 (op pauli1)
  rw [oppFromJw_eq, pauli1_transpose] at hc
  have hm : pauli3 * pauli1 = pauli1 * pauli3 := by
    refine piW_injective ?_
    rw [map_mul, map_mul]
    exact hc
  exact p1_p3_ne hm.symm

/-! ## 4. The right action IS implementable here — by a different real structure -/

/-- Exchanging the two Kronecker factors. Under `H ≃ M₂(ℂ)` this is the transpose, so
`conjPerm prodSwap` is the map `x ↦ x*` — the textbook real structure of a regular bimodule. -/
def prodSwap : Equiv.Perm Slots := Equiv.prodComm (Fin 2) (Fin 2)

/-- The textbook real structure on the regular bimodule, conjugate-linear. -/
def Jprod : Hw →ₛₗ[starRingEnd ℂ] Hw := conjPerm prodSwap

theorem prodSwap_involutive (p : Slots) : prodSwap (prodSwap p) = p := by
  obtain ⟨i, j⟩ := p; rfl

/-- `J² = 1` for `Jprod`, pointwise. Stated because `Jprod` wraps `conjPerm`, so
`conjPerm_involutive` does not match syntactically through the definition. -/
theorem Jprod_involutive (v : Hw) : Jprod (Jprod v) = v :=
  ConjugatePermutation.conjPerm_involutive prodSwap prodSwap_involutive v

/-- The matrix identity behind `piOpW_via_prodSwap`: exchanging the factors moves `a* ⊗ 1` to
`1 ⊗ aᵀ`, which is exactly `kronRight`'s formula. -/
theorem submatrix_prodSwap_kronLeft (a : Matrix (Fin 2) (Fin 2) ℂ) :
    (((star a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix prodSwap prodSwap).map
        (starRingEnd ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ aᵀ := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp [prodSwap, Matrix.kroneckerMap, Matrix.one_apply, apply_ite (starRingEnd ℂ),
    mul_comm]

/-- **The witness's right action IS `J`-implemented — by `Jprod`, on the nose.**
`Jprod π(a*) Jprod = πOp (op a)` for every `a`. So the defect `oppFromJ_ne_piOpW` records is
the CHOICE of `J` made in unit 18, not the geometry of this bimodule. -/
theorem piOpW_via_prodSwap (a : Matrix (Fin 2) (Fin 2) ℂ) (v : Hw) :
    Jprod (piW (star a) (Jprod v)) = piOpW (op a) v := by
  rw [piW_apply, piOpW_apply, unop_op, Jprod,
    conjPerm_conj prodSwap prodSwap_involutive, submatrix_prodSwap_kronLeft]

/-- The matrix identity behind `Jprod_not_commute_Dw`: `Jprod` moves `D = σ₁ ⊗ 1` to
`1 ⊗ σ₁`, the other slot. -/
theorem submatrix_prodSwap_Dw :
    ((pauli1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix prodSwap prodSwap).map
        (starRingEnd ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1 := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [prodSwap, pauli1, Matrix.kroneckerMap, Matrix.one_apply]

/-- **And the correct `J` is incompatible with the witness's `D`.** `Jprod D Jprod = rightP1`,
not `D`, so `JD = DJ` fails. **Unit 18 put `J` in the right slot precisely so that `JD = DJ`
would hold for free** — and that is the choice which made `πOp` un-implementable. On this
witness the two KO-6 requirements pull in opposite directions; that is recorded, not
resolved. -/
theorem Jprod_not_commute_Dw : ¬ ∀ v : Hw, Jprod (Dw (Jprod v)) = Dw v := by
  intro h
  have hm : matAlg Slots ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli1)
      = matAlg Slots (pauli1 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    refine LinearMap.ext fun v => ?_
    have hv := h v
    rw [Dw, piW_apply, Jprod, conjPerm_conj prodSwap prodSwap_involutive,
      submatrix_prodSwap_Dw] at hv
    rw [matAlg_apply, matAlg_apply]
    exact hv
  have h01 := congrFun (congrFun (matAlg_injective Slots hm) (0, 1)) (1, 1)
  simp [Matrix.kroneckerMap, Matrix.one_apply, pauli1] at h01

end

end OppositeFromRealStructure
