/-
  CliffordHyperbolicStep.lean — the hyperbolic step, quantified over forms.

  WHY. `UNLOCK_WATCHLIST` carries an item for the statement *"for every real
  quadratic space of signature `(p,q)`, `Cl(p,q;ℝ)` is the eight-fold table"*,
  and its own diagnosis is **"the gap is assembly, not ingredients"**. The
  assembly is an induction on `min(p,q)` whose step it names:
  `CliffordPeriodicityHyperbolic.periodicityEquivHyp`, which adjoins a hyperbolic
  plane and produces `M₂`.

  AND THAT STEP IS NOT IN THE FORM AN INDUCTION CAN USE. `periodicityEquivHyp` is
  about the LITERAL form `QextHyp Q` on the literal space `V × (ℝ × ℝ)`. An
  induction meets an arbitrary form `Q'` whose signature happens to be one more in
  each index, and has no reason to be that particular one.

  **Every neighbouring step in this estate has already been quantified and this
  one has not**: `clifford_periodicity_eight` (`+8` on `sigPos`),
  `clifford_step_pos` (`+2, 0`) and `clifford_step_neg` (`0, +2`) all take an
  arbitrary `Q'` with the right dimension and signature. The `(+1,+1)` step —
  **the one the classification item's induction actually runs on** — was left in
  its literal form. Grepped, not recalled: no statement in `paper_f` carries the
  hypothesis `sigPos Q' = sigPos Q + 1`.

  WHAT IS PROVED. `clifford_step_hyp`: for nondegenerate real `Q` on `V` and `Q'`
  on `W` with `finrank W = finrank V + 2` and `sigPos Q' = sigPos Q + 1`,
  `Cl Q' ≃ₐ[ℝ] M₂(Cl Q)`. The `sigNeg` half is a CONSEQUENCE and not a hypothesis
  (`sigNeg_of_step`), because nondegeneracy plus the dimension already forces it —
  stating it would have been a redundant assumption.

  WHAT IS NOT PROVED, AND IT IS THE REST OF THE ASSEMBLY. Two things, both named
  in the watchlist item rather than sketched here: that for every `(p,q)` with
  `p, q ≥ 1` a nondegenerate form of signature `(p−1, q−1)` EXISTS — this file
  takes both forms as given, which is what "quantified" means and is not the same
  as "constructed" — and the induction itself, which also needs
  `M₂(M_{2^k}(A)) ≃ M_{2^(k+1)}(A)` to flatten. **This is one rung of that
  ladder and it is not the ladder.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordPeriodicityQuantified
import CliffordRealSignatures

namespace CliffordHyperbolicStep

open CliffordPeriodicityHyperbolic CliffordRealQuantified CliffordRealSignatures
open QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-! ## 1. A nondegenerate form's two indices add to the dimension

The converse of `CliffordRealSignatures.separatingLeft_of_sig`, which the estate has in one
direction only. Both directions are one line from
`sigPos_add_sigNeg_add_radical`. -/

theorem sig_add_of_sep {Q : QuadraticForm ℝ V}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    sigPos Q + sigNeg Q = Module.finrank ℝ V := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hz : Module.finrank ℝ Q.radical = 0 := finrank_radical_eq_zero hQ
  omega

/-! ## 2. The hyperbolic extension is nondegenerate, from its signature alone -/

theorem sep_QextHyp {Q : QuadraticForm ℝ V}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (QextHyp Q)).SeparatingLeft := by
  refine separatingLeft_of_sig ?_
  rw [SignatureArithmetic.sigPos_QextHyp, SignatureArithmetic.sigNeg_QextHyp,
    finrank_extHyp (K := ℝ) (V := V)]
  have := sig_add_of_sep hQ
  omega

/-! ## 3. The step, quantified -/

/-- **THE HYPERBOLIC STEP, FOR EVERY FORM OF THE RIGHT SIGNATURE.** Adjoining a hyperbolic plane
raises both indices by one and produces `M₂`; this says the conclusion holds for any form whose
signature is one more in each index, not only for the literal extension.

This is the shape `clifford_periodicity_eight`, `clifford_step_pos` and `clifford_step_neg` are
already in, and the shape an induction on `min (sigPos, sigNeg)` needs. -/
theorem clifford_step_hyp {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2)
    (hsig : sigPos Q' = sigPos Q + 1) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ' (sep_QextHyp hQ)
    (by rw [hdim, finrank_extHyp (K := ℝ) (V := V)])
    (by rw [hsig, SignatureArithmetic.sigPos_QextHyp])
  exact ⟨e.trans (periodicityEquivHyp Q)⟩

/-- **AND THE `sigNeg` HALF IS A CONSEQUENCE, NOT A HYPOTHESIS.** Nondegeneracy and the dimension
force it, so the step really is `(+1, +1)` — which is why it walks a diagonal and is the move the
classification induction is built on. Assuming it would have been redundant. -/
theorem sigNeg_of_step {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2)
    (hsig : sigPos Q' = sigPos Q + 1) :
    sigNeg Q' = sigNeg Q + 1 := by
  have h := sig_add_of_sep hQ
  have h' := sig_add_of_sep hQ'
  omega

/-! ## 4. The instance, so the quantified form is visibly a generalisation

`ERRATUM 201`. The literal extension satisfies the hypotheses, so `periodicityEquivHyp` is a case
of the theorem above rather than a parallel statement. -/

theorem clifford_step_hyp_literal {Q : QuadraticForm ℝ V}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra (QextHyp Q) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) :=
  clifford_step_hyp hQ (sep_QextHyp hQ) (finrank_extHyp (K := ℝ) (V := V))
    (SignatureArithmetic.sigPos_QextHyp Q)

end

end CliffordHyperbolicStep
