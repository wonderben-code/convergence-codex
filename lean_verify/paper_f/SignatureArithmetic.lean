import CliffordRealQuantified

/-!
# How signatures behave under sums of forms

`CliffordRealQuantified` proves that the isomorphism class of a real Clifford algebra depends only
on dimension and signature, and closes by recording a debt: the theorem speaks of `sigPos`, and no
named form in this estate has its `sigPos` computed, so the concrete isomorphisms are not yet
instances of their own generalisation. Paying that debt needs two facts, and this file proves the
general one.

> **`sigPos_prod`** — `sigPos (Q.prod Q') = sigPos Q + sigPos Q'`, and `sigNeg_prod` likewise.

This is not in Mathlib. `QuadraticMap.prod` has its `Equivalent.prod` congruence and the `Signature`
file computes `sigPos` of a `weightedSumSquares`, but nothing joins the two — so the additivity of
the signature over an orthogonal sum, which is the fact that makes the word *signature* useful, is
unproved there.

The proof is the obvious one and its only step with content is bookkeeping: an orthogonal sum of two
weighted sums of squares **is** a weighted sum of squares, on the sum of the index types
(`wssProdIsometry`), and the positive weights of `Sum.elim w v` split as those of `w` plus those of
`v` (`ncard_pos_sumElim`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SignatureArithmetic

open QuadraticForm QuadraticMap

noncomputable section

/-! ## An orthogonal sum of weighted sums of squares is a weighted sum of squares -/

/-- `wss w ⊥ wss v` is `wss (Sum.elim w v)` on the sum of the index types. -/
def wssProdIsometry {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → ℝ) (v : κ → ℝ) :
    ((weightedSumSquares ℝ w).prod (weightedSumSquares ℝ v)).IsometryEquiv
      (weightedSumSquares ℝ (Sum.elim w v)) where
  __ := (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ).symm
  map_app' := by
    rintro ⟨f, g⟩
    simp [weightedSumSquares_apply, QuadraticMap.prod_apply, Fintype.sum_sum_type,
      LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- The positive entries of `Sum.elim w v` are those of `w` together with those of `v`.

Stated with `Finite` rather than `Fintype` because the conclusion mentions neither: `Set.ncard` is
defined without a decidability or enumeration hypothesis, so carrying `Fintype` here would be a
hypothesis that appears in the proof and not in the statement. -/
theorem ncard_pos_sumElim {ι κ : Type*} [Finite ι] [Finite κ] (w : ι → ℝ) (v : κ → ℝ) :
    {s | 0 < Sum.elim w v s}.ncard = {i | 0 < w i}.ncard + {j | 0 < v j}.ncard := by
  have _ := Fintype.ofFinite ι
  have _ := Fintype.ofFinite κ
  rw [CliffordRealQuantified.ncard_eq_card_pos', CliffordRealQuantified.ncard_eq_card_pos',
    CliffordRealQuantified.ncard_eq_card_pos',
    Fintype.card_congr (Equiv.subtypeSum (p := fun s : ι ⊕ κ => 0 < Sum.elim w v s)),
    Fintype.card_sum]
  rfl

/-! ## Additivity of the signature -/

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- **The signature is additive over orthogonal sums.** Not in Mathlib: `Equivalent.prod` gives the
congruence and `sigPos_weightedSumSquares` gives the computation, but nothing joins them. -/
theorem sigPos_prod (Q : QuadraticForm ℝ V) (Q' : QuadraticForm ℝ W) :
    sigPos (Q.prod Q') = sigPos Q + sigPos Q' := by
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
  obtain ⟨v, hv⟩ := Q'.equivalent_weightedSumSquares
  have hprod : (Q.prod Q').Equivalent (weightedSumSquares ℝ (Sum.elim w v)) :=
    (QuadraticMap.Equivalent.prod hw hv).trans ⟨wssProdIsometry w v⟩
  rw [sigPos_of_equiv_weightedSumSquares hprod, sigPos_of_equiv_weightedSumSquares hw,
    sigPos_of_equiv_weightedSumSquares hv, ncard_pos_sumElim]

/-- The `sigNeg` half, from `sigPos` on the negated form. -/
theorem sigNeg_prod (Q : QuadraticForm ℝ V) (Q' : QuadraticForm ℝ W) :
    sigNeg (Q.prod Q') = sigNeg Q + sigNeg Q' := by
  have hneg : -(Q.prod Q') = (-Q).prod (-Q') := by
    ext x
    simp only [QuadraticMap.neg_apply, QuadraticMap.prod_apply]
    ring
  simp only [sigNeg, hneg]
  exact sigPos_prod (-Q) (-Q')

/-! ## The line, and the hyperbolic plane

Mathlib builds `CliffordAlgebraQuaternion.Q c₁ c₂` as `(c₁ • sq).prod (c₂ • sq)` — it is already an
orthogonal sum of two lines — so once the signature of a scaled square is known, `sigPos_prod` gives
the plane for free. `CliffordPeriodicityHyperbolic.Qhyp` is that form at `c₁ = 1`, `c₂ = -1`. -/

/-- A scaled square on the line is a one-entry weighted sum of squares. -/
def smulSqIsometry (c : ℝ) :
    (c • (QuadraticMap.sq : QuadraticForm ℝ ℝ)).IsometryEquiv
      (weightedSumSquares ℝ (fun _ : Fin 1 => c)) where
  __ := (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  map_app' x := by simp [weightedSumSquares_apply, QuadraticMap.sq]

/-- The signature of `c • x²` on the line. -/
@[simp] theorem sigPos_smul_sq (c : ℝ) :
    sigPos (c • (QuadraticMap.sq : QuadraticForm ℝ ℝ)) = if 0 < c then 1 else 0 := by
  rw [sigPos_of_equiv_weightedSumSquares ⟨smulSqIsometry c⟩]
  by_cases hc : 0 < c <;> simp [hc, Set.ncard_eq_toFinset_card']

/-- The negative half, from `sigNeg Q = sigPos (-Q)`. -/
@[simp] theorem sigNeg_smul_sq (c : ℝ) :
    sigNeg (c • (QuadraticMap.sq : QuadraticForm ℝ ℝ)) = if c < 0 then 1 else 0 := by
  have hneg : -(c • (QuadraticMap.sq : QuadraticForm ℝ ℝ)) = (-c) • QuadraticMap.sq := by
    ext x; simp [QuadraticMap.sq]
  simp only [sigNeg, hneg, sigPos_smul_sq, neg_pos]

/-- **The hyperbolic plane has signature `(1,1)`.** -/
theorem sigPos_Qhyp : sigPos (CliffordPeriodicityHyperbolic.Qhyp (K := ℝ)) = 1 := by
  simp only [CliffordPeriodicityHyperbolic.Qhyp, CliffordAlgebraQuaternion.Q, sigPos_prod,
    sigPos_smul_sq]
  norm_num

theorem sigNeg_Qhyp : sigNeg (CliffordPeriodicityHyperbolic.Qhyp (K := ℝ)) = 1 := by
  simp only [CliffordPeriodicityHyperbolic.Qhyp, CliffordAlgebraQuaternion.Q, sigNeg_prod,
    sigNeg_smul_sq]
  norm_num

/-- **Adjoining a hyperbolic plane adds `(1,1)` to the signature.** This is the arithmetic counter-
part of `periodicityEquivHyp`, and it is why that step walks a diagonal: it raises `sigPos` and
`sigNeg` together, so it never changes `p − q`. -/
theorem sigPos_QextHyp (Q : QuadraticForm ℝ V) :
    sigPos (CliffordPeriodicityHyperbolic.QextHyp Q) = sigPos Q + 1 := by
  rw [sigPos_prod, sigPos_Qhyp]

theorem sigNeg_QextHyp (Q : QuadraticForm ℝ V) :
    sigNeg (CliffordPeriodicityHyperbolic.QextHyp Q) = sigNeg Q + 1 := by
  rw [sigNeg_prod, sigNeg_Qhyp]

/-- **The hyperbolic step never changes `p − q`.**

`WALLS §W7.2` states this in prose and rests its whole account of the real wall on it: the step
`Cl_{p,q} → Cl_{p+1,q+1}` walks one diagonal of the eight-fold classification and provably cannot
leave it, so base cases on four of the eight residue classes are missing and the step cannot supply
them. That sentence is now a theorem rather than an observation.

Stated as `p' + q = q' + p` rather than as a difference because `sigPos` and `sigNeg` are natural
numbers and truncated subtraction would make the statement weaker than it is. -/
theorem sigPos_sub_sigNeg_QextHyp (Q : QuadraticForm ℝ V) :
    sigPos (CliffordPeriodicityHyperbolic.QextHyp Q) + sigNeg Q
      = sigNeg (CliffordPeriodicityHyperbolic.QextHyp Q) + sigPos Q := by
  rw [sigPos_QextHyp, sigNeg_QextHyp]
  omega

end

end SignatureArithmetic
