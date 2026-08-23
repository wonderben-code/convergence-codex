/-
  CliffordSignatureModel.lean — a nondegenerate real form of EVERY signature, and the
  classification statement it completes.

  WHY. `CliffordHyperbolicStep` named two legs between the estate and the real Clifford
  classification; `CliffordHypTower` built the second and narrowed the first. What the first
  leg still holds up is the *universally quantified* sentence. `clifford_reduce_k` climbs: it
  takes a small form as GIVEN and identifies the large one with the tower over it. To say
  "**every** real Clifford algebra of a nondegenerate form reduces to a definite one" is to
  quantify over the small form, so something has to produce it — and the estate names its forms
  one at a time (`Q₁₁`, `Q₁₃`, `Q₃₁`, `Q₂₄`, `Q₄₂`, `Q₂₂`) with no family indexed by `(p,q)`.
  Grepped rather than recalled: the estate's only `ℕ`-indexed family of forms is
  `CliffordEvenLadder.Rf n`, the all-ones form over ℂ — the COMPLEX analogue, which is why the
  complex table fell to one ladder and this one did not. The real family is what was missing.

  THIS FILE PRODUCES THE FAMILY. `sigForm p q` is `x₁² + ⋯ + x_p² − y₁² − ⋯ − y_q²` on
  `(Fin p ⊕ Fin q) → ℝ`, built as one of Mathlib's `weightedSumSquares`, so that
  `sigPos_weightedSumSquares` and `sigNeg_weightedSumSquares` compute its two indices and
  `separatingLeft_of_sig` reads off nondegeneracy from them. The index set is a SUM rather than
  `Fin (p+q)` on purpose: "how many weights are positive" is then a fact about the type, and the
  count is `Set.ncard_image_of_injective` rather than an argument about inequalities on `Fin`.

  WHAT IS PROVED.

  * `sigPos_sigForm`, `sigNeg_sigForm`, `sep_sigForm` — the model has exactly the signature it
    advertises and is nondegenerate; `exists_sep_form_of_signature` is leg 1, and it is stated
    with the space NAMED rather than existentially quantified, which is the stronger sentence;
  * `posDef_sigForm_right_zero` and `negDef_sigForm_left_zero` — a pure signature really is a
    DEFINITE form, so "reduces to a pure signature" is not a statement about two numbers;
  * **`equivalent_sigForm`** — every nondegenerate real form IS the model of its signature.
    **Sylvester's law of inertia with a canonical representative, which neither library states**:
    Mathlib's normal form hands back some ±1 weight vector with the signs in no stated order, and
    the estate's converse compares two forms without naming a third. `clifford_model` is the same
    fact one step along;
  * **`clifford_reduce_model`** — for every nondegenerate `Q'` and every `k` below both indices,
    `Cl Q' ≃ₐ[ℝ] M_{2^k}(Cl (sigForm (p−k) (q−k)))`. No hypothesis about a smaller form existing:
    §1 supplies it;
  * **`clifford_reduce_posDef` / `clifford_reduce_negDef`** — at `k = min p q` one index dies and
    the base is definite. **That is the classification statement, universally quantified.**

  AND IT IS INSTANTIATED (`ERRATUM 201`). `clifford_sigForm_zero_two` identifies `Cl (sigForm 0 2)`
  with `ℍ` through Mathlib's `CliffordAlgebraQuaternion.equiv`, and `clifford_Q₂₄_model` runs the
  general theorem on the estate's own `Q₂₄` to land on `M₄(Cl (sigForm 0 2))` — which
  `CliffordRealSignatureStep.equivM4H` already proved to be `M₄(ℍ)` by a different route. The
  general machinery reproduces a result the estate got by hand.

  WHAT IS STILL NOT PROVED, AND IT IS NOT THIS LEG. The reduction lands on `Cl (sigForm m 0)` or
  `Cl (sigForm 0 n)` and does not say what those ARE for general `m`, `n` — that is the eight-fold
  table, which this estate has at specific small values (`ℝ`, `ℂ`, `ℍ`, `M₂(ℍ)`, `M₄(ℝ)`) and not
  as a function of `m mod 8`. **The reduction is complete; the table it reduces to is not.**

  A universe note: `CliffordHypTower.clifford_reduce_k` had its `W` in the same universe as the
  base `V`, which no step of its proof needs — `cliffordEquiv_of_sigPos_eq` is already
  universe-polymorphic. It is generalised here, because the model form lives in `Type` and the
  forms it must serve do not.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordHypTower
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

namespace CliffordSignatureModel

open CliffordPeriodicityHyperbolic CliffordRealQuantified CliffordRealSignatures
open CliffordHyperbolicStep CliffordHypTower CliffordRealSignatureStep
open QuadraticForm QuadraticMap
open scoped Quaternion

noncomputable section

universe v

/-! ## 1. The model form of an arbitrary signature -/

/-- The index set of the model of signature `(p, q)`: `p` positive directions and `q` negative
ones. Kept as a SUM rather than `Fin (p + q)` so that the sign of a weight is decided by which
side of the sum the index is on, not by an inequality. -/
abbrev sigIdx (p q : ℕ) : Type := Fin p ⊕ Fin q

/-- `+1` on the positive block, `−1` on the negative block. -/
def sigWeights (p q : ℕ) : sigIdx p q → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

@[simp] theorem sigWeights_inl (p q : ℕ) (a : Fin p) : sigWeights p q (Sum.inl a) = 1 := rfl

@[simp] theorem sigWeights_inr (p q : ℕ) (b : Fin q) : sigWeights p q (Sum.inr b) = -1 := rfl

/-- The model space `ℝ^(p+q)`. -/
abbrev sigSpace (p q : ℕ) : Type := sigIdx p q → ℝ

/-- **The model form of signature `(p, q)`**: `x₁² + ⋯ + x_p² − y₁² − ⋯ − y_q²`. -/
def sigForm (p q : ℕ) : QuadraticForm ℝ (sigSpace p q) := weightedSumSquares ℝ (sigWeights p q)

theorem sigForm_apply (p q : ℕ) (x : sigSpace p q) :
    sigForm p q x = ∑ i, sigWeights p q i * (x i * x i) := by
  simp [sigForm]

theorem finrank_sigSpace (p q : ℕ) : Module.finrank ℝ (sigSpace p q) = p + q := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-! ## 2. Its two indices, and hence its nondegeneracy -/

/-- The positive weights are exactly the left summands, so counting them is counting `Fin p`. -/
theorem setOf_sigWeights_pos (p q : ℕ) :
    {i : sigIdx p q | 0 < sigWeights p q i} = Set.range (Sum.inl : Fin p → sigIdx p q) := by
  ext i
  cases i <;> simp

theorem setOf_sigWeights_neg (p q : ℕ) :
    {i : sigIdx p q | sigWeights p q i < 0} = Set.range (Sum.inr : Fin q → sigIdx p q) := by
  ext i
  cases i <;> simp

theorem sigPos_sigForm (p q : ℕ) : sigPos (sigForm p q) = p := by
  rw [sigForm, sigPos_weightedSumSquares, setOf_sigWeights_pos, ← Set.image_univ,
    Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ]
  simp

theorem sigNeg_sigForm (p q : ℕ) : sigNeg (sigForm p q) = q := by
  rw [sigForm, sigNeg_weightedSumSquares, setOf_sigWeights_neg, ← Set.image_univ,
    Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ]
  simp

/-- The two indices already fill the dimension, so there is no room for a radical. -/
theorem sep_sigForm (p q : ℕ) :
    (QuadraticMap.associated (R := ℝ) (sigForm p q)).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_sigForm, sigNeg_sigForm, finrank_sigSpace])

/-- **LEG 1 OF THE CLASSIFICATION.** For every `(p, q)` a nondegenerate real quadratic form of
signature `(p, q)` exists. `CliffordHyperbolicStep` recorded this as missing and
`CliffordHypTower` narrowed what it was holding up; here it is.

The space is NAMED rather than existentially quantified — `∃ Q on ℝ^(p+q)` is stronger than
`∃ a space and a form on it`, and the descent argument that wanted this leg wanted the space too. -/
theorem exists_sep_form_of_signature (p q : ℕ) :
    ∃ Q : QuadraticForm ℝ (sigSpace p q),
      (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft ∧ sigPos Q = p ∧ sigNeg Q = q :=
  ⟨sigForm p q, sep_sigForm p q, sigPos_sigForm p q, sigNeg_sigForm p q⟩

/-! ## 3. A pure signature is a definite form

Stated because "reduces to a pure signature" would otherwise be a claim about two natural numbers
rather than about the form. -/

/-- A weighted sum of squares with every weight positive is positive definite. -/
theorem posDef_weightedSumSquares {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    (weightedSumSquares ℝ w).PosDef := by
  intro x hx
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [weightedSumSquares_apply]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · simpa using mul_nonneg (hw j).le (mul_self_nonneg (x j))
  · simpa using mul_pos (hw i) (mul_self_pos.mpr hi)

theorem neg_sigForm (p q : ℕ) :
    -(sigForm p q) = weightedSumSquares ℝ (fun i => -(sigWeights p q i)) := by
  ext x
  simp [sigForm, Finset.sum_neg_distrib]

/-- **`sigForm p 0` IS POSITIVE DEFINITE.** -/
theorem posDef_sigForm_right_zero (p : ℕ) : (sigForm p 0).PosDef := by
  rw [sigForm]
  refine posDef_weightedSumSquares fun i => ?_
  cases i with
  | inl a => norm_num
  | inr b => exact b.elim0

/-- **`sigForm 0 q` IS NEGATIVE DEFINITE**, in the form Mathlib's signature file uses. -/
theorem negDef_sigForm_left_zero (q : ℕ) : (-(sigForm 0 q)).PosDef := by
  rw [neg_sigForm]
  refine posDef_weightedSumSquares fun i => ?_
  cases i with
  | inl a => exact a.elim0
  | inr b => norm_num

/-! ## 4. The model is a complete set of representatives

Probed by shape (`ERRATUM 42`, `ERRATUM 233`), and NEITHER library has this. Mathlib's Sylvester
normal form `equivalent_one_neg_one_weighted_sum_squared` produces SOME ±1 weight vector on
`Fin (finrank M)`, with nothing said about how many of each sign or in what order; the estate's
`equivalent_of_sigPos_eq` compares two forms of equal invariants and names no representative.
Sorting the weights is exactly what turns "a normal form" into "the model of its signature". -/

/-- **SYLVESTER'S LAW OF INERTIA WITH A CANONICAL REPRESENTATIVE.** Every nondegenerate real
quadratic form is isometric to the model of its own signature. -/
theorem equivalent_sigForm {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q' : QuadraticForm ℝ W} (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft) :
    Q'.Equivalent (sigForm (sigPos Q') (sigNeg Q')) :=
  equivalent_of_sigPos_eq hQ' (sep_sigForm _ _)
    (by rw [finrank_sigSpace]; exact (sig_add_of_sep hQ').symm)
    (sigPos_sigForm _ _).symm

/-- And so its Clifford algebra is the model's. `clifford_reduce_model` below reaches this at
`k = 0` only up to a one-by-one matrix; here it is on the nose, and it needs no tower. -/
theorem clifford_model {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q' : QuadraticForm ℝ W} (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] CliffordAlgebra (sigForm (sigPos Q') (sigNeg Q'))) :=
  cliffordEquiv_of_sigPos_eq hQ' (sep_sigForm _ _)
    (by rw [finrank_sigSpace]; exact (sig_add_of_sep hQ').symm)
    (sigPos_sigForm _ _).symm

/-! ## 5. The reduction, with nothing left to assume -/

/-- **EVERY NONDEGENERATE REAL FORM REDUCES BY `k` STEPS ONTO THE MODEL.** `clifford_reduce_k`
needs a small form; §1 supplies it, so this statement has no hypothesis but nondegeneracy and
`k ≤ min (p, q)`. -/
theorem clifford_reduce_model {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q' : QuadraticForm ℝ W} (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (k : ℕ) (hkp : k ≤ sigPos Q') (hkq : k ≤ sigNeg Q') :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k))
      (CliffordAlgebra (sigForm (sigPos Q' - k) (sigNeg Q' - k)))) := by
  refine clifford_reduce_k (sep_sigForm _ _) hQ' k ?_ ?_
  · have h := sig_add_of_sep hQ'
    rw [finrank_sigSpace]
    omega
  · rw [sigPos_sigForm]
    omega

/-- **AND AT `k = sigNeg Q'` THE BASE IS POSITIVE DEFINITE.** This is the classification
statement for a form with at least as many positive directions as negative ones. -/
theorem clifford_reduce_posDef {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q' : QuadraticForm ℝ W} (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hle : sigNeg Q' ≤ sigPos Q') :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin (2 ^ sigNeg Q')) (Fin (2 ^ sigNeg Q'))
      (CliffordAlgebra (sigForm (sigPos Q' - sigNeg Q') 0))) := by
  have h := clifford_reduce_model hQ' (sigNeg Q') hle le_rfl
  rwa [Nat.sub_self] at h

/-- **AND THE OTHER WAY ROUND THE BASE IS NEGATIVE DEFINITE.** -/
theorem clifford_reduce_negDef {W : Type v} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q' : QuadraticForm ℝ W} (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hle : sigPos Q' ≤ sigNeg Q') :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin (2 ^ sigPos Q')) (Fin (2 ^ sigPos Q'))
      (CliffordAlgebra (sigForm 0 (sigNeg Q' - sigPos Q')))) := by
  have h := clifford_reduce_model hQ' (sigPos Q') le_rfl hle
  rwa [Nat.sub_self] at h

/-! ## 6. Instantiations (`ERRATUM 201`) -/

/-- `Cl(0,2;ℝ) ≃ ℍ` for the MODEL form, through Mathlib's own quaternion equivalence. The estate
had this algebra only as `CliffordAlgebraQuaternion.Q (-1) (-1)`, which is a form on `ℝ × ℝ` and
not a member of any family. -/
theorem clifford_sigForm_zero_two :
    Nonempty (CliffordAlgebra (sigForm 0 2) ≃ₐ[ℝ] ℍ[ℝ]) := by
  have hsep : (QuadraticMap.associated (R := ℝ)
      (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1))).SeparatingLeft := by
    refine separatingLeft_of_sig ?_
    rw [sigPos_quaternionQ, sigNeg_quaternionQ]
    norm_num
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq (sep_sigForm 0 2) hsep
    (by rw [finrank_sigSpace]; simp)
    (by rw [sigPos_sigForm, sigPos_quaternionQ]; norm_num)
  exact ⟨e.trans CliffordAlgebraQuaternion.equiv⟩

/-- The estate's `Q₂₄` run through the general theorem. `Q₂₄` has four negative directions to two
positive ones, so it is `clifford_reduce_negDef` that applies, and the answer is
`M₄(Cl (sigForm 0 2))` — which §6's first result identifies as `M₄(ℍ)`, exactly what
`CliffordRealSignatureStep.equivM4H` proved by hand from the Minkowski case. -/
theorem clifford_Q₂₄_model :
    Nonempty (CliffordAlgebra Q₂₄ ≃ₐ[ℝ]
      Matrix (Fin 4) (Fin 4) (CliffordAlgebra (sigForm 0 2))) := by
  have h := clifford_reduce_negDef (Q' := Q₂₄) sep_Q₂₄
    (by rw [sigPos_Q₂₄, sigNeg_Q₂₄]; norm_num)
  rw [sigPos_Q₂₄, sigNeg_Q₂₄] at h
  have e1 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have e2 : (4 : ℕ) - 2 = 2 := by norm_num
  rwa [e1, e2] at h

end

end CliffordSignatureModel
