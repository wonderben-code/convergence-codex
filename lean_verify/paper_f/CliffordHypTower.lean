/-
  CliffordHypTower.lean — the hyperbolic step iterated `k` times, and the
  reduction it performs.

  WHY. `CliffordHyperbolicStep` quantified the `(+1,+1)` step and closed by naming
  the two legs still between the estate and the real classification. This is the
  second of them: **the induction, and the matrix flattening it needs.**

  The watchlist item's plan is to lower `min (sigPos, sigNeg)` by one at a time
  until the signature is pure. The obstacle it names is that the conclusion of `k`
  steps is `M₂(M₂(⋯(Cl Q)))` and what one wants is `M_{2^k}(Cl Q)`; the estate had
  `equivEight`, which flattens exactly four steps, and nothing general.

  WHAT IS BUILT.

  * `hypSpace V k` and `hypForm Q k` — the space and form obtained by adjoining
    `k` hyperbolic planes, by recursion, with the three instances the recursion
    needs. `finrank_hypSpace`, `sigPos_hypForm` and `sigNeg_hypForm`: the tower
    adds `2k` to the dimension and `k` to **each** index, so it walks the diagonal
    `p − q` all the way up;
  * `matrixFinOneAlgEquiv` and `matrixTwoPowFlatten` — `M₁(A) ≃ A` and
    `M₂(M_{2^k}(A)) ≃ M_{2^(k+1)}(A)`. **Neither is in Mathlib and neither is in
    this estate**, probed by shape (`ERRATUM 42`, `ERRATUM 233`): `exact?` fails on
    both, `Matrix.scalarAlgEquiv` does not exist, and the estate's only flattening
    is `equivEight`'s fixed four steps;
  * **`cliffordEquivHypTower`** — `Cl (hypForm Q k) ≃ₐ[ℝ] M_{2^k}(Cl Q)`, by
    induction;
  * **`clifford_reduce_k`** — the same for ANY nondegenerate form of the right
    dimension and signature, which is the form an argument can use.

  AND THIS MAKES THE FIRST LEG UNNECESSARY FOR THE REDUCTION ITSELF. That leg asks
  for a form of signature `(p−1,q−1)` to exist. `clifford_reduce_k` does not need
  one: it takes the SMALLER form as given and climbs, rather than taking the
  larger one and descending. What still needs the first leg is the sentence *"every
  real Clifford algebra reduces to a pure signature"* — that quantifies over the
  small form and so must produce it. **The reduction is here; the existence
  statement is not.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordHyperbolicStep

namespace CliffordHypTower

open CliffordPeriodicityHyperbolic CliffordRealQuantified CliffordRealSignatures
open CliffordHyperbolicStep QuadraticMap

noncomputable section

universe u

/-! ## 1. The tower of spaces -/

/-- `V` with `k` hyperbolic planes adjoined. -/
def hypSpace (V : Type u) : ℕ → Type u
  | 0 => V
  | (k + 1) => hypSpace V k × (ℝ × ℝ)

instance instACG (V : Type u) [AddCommGroup V] : ∀ k, AddCommGroup (hypSpace V k)
  | 0 => ‹AddCommGroup V›
  | (k + 1) => letI := instACG V k; inferInstanceAs (AddCommGroup (hypSpace V k × (ℝ × ℝ)))

instance instMod (V : Type u) [AddCommGroup V] [Module ℝ V] : ∀ k, Module ℝ (hypSpace V k)
  | 0 => ‹Module ℝ V›
  | (k + 1) => letI := instMod V k; inferInstanceAs (Module ℝ (hypSpace V k × (ℝ × ℝ)))

instance instFD (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    ∀ k, FiniteDimensional ℝ (hypSpace V k)
  | 0 => ‹FiniteDimensional ℝ V›
  | (k + 1) =>
      letI := instFD V k; inferInstanceAs (FiniteDimensional ℝ (hypSpace V k × (ℝ × ℝ)))

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem finrank_hypSpace (k : ℕ) :
    Module.finrank ℝ (hypSpace V k) = Module.finrank ℝ V + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change Module.finrank ℝ (hypSpace V k × (ℝ × ℝ)) = _
      rw [Module.finrank_prod, ih]
      simp [Module.finrank_prod]
      ring

/-! ## 2. The tower of forms -/

/-- `Q` with `k` hyperbolic planes adjoined. -/
def hypForm (Q : QuadraticForm ℝ V) : ∀ k, QuadraticForm ℝ (hypSpace V k)
  | 0 => Q
  | (k + 1) => QextHyp (hypForm Q k)

/-- **THE TOWER ADDS `k` TO THE POSITIVE INDEX.** -/
theorem sigPos_hypForm (Q : QuadraticForm ℝ V) (k : ℕ) :
    sigPos (hypForm Q k) = sigPos Q + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change sigPos (QextHyp (hypForm Q k)) = _
      rw [SignatureArithmetic.sigPos_QextHyp, ih]
      omega

/-- **AND `k` TO THE NEGATIVE INDEX**, so it walks the diagonal `p − q` the whole way. -/
theorem sigNeg_hypForm (Q : QuadraticForm ℝ V) (k : ℕ) :
    sigNeg (hypForm Q k) = sigNeg Q + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change sigNeg (QextHyp (hypForm Q k)) = _
      rw [SignatureArithmetic.sigNeg_QextHyp, ih]
      omega

theorem sep_hypForm {Q : QuadraticForm ℝ V}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) (k : ℕ) :
    (QuadraticMap.associated (R := ℝ) (hypForm Q k)).SeparatingLeft := by
  induction k with
  | zero => exact hQ
  | succ k ih => exact sep_QextHyp ih

/-! ## 3. Two matrix equivalences the libraries do not have

Probed by shape and not by name (`ERRATUM 42`, `ERRATUM 233`): `exact?` closes neither goal,
`Matrix.scalarAlgEquiv` is not a constant, and this estate's only flattening is `equivEight`'s
fixed four steps. -/

/-- **A ONE-BY-ONE MATRIX ALGEBRA IS ITS ENTRY.** The base case of §4's induction. -/
def matrixFinOneAlgEquiv (A : Type*) [Semiring A] [Algebra ℝ A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[ℝ] A where
  toFun M := M 0 0
  invFun a := Matrix.of fun _ _ => a
  left_inv M := by ext i j; fin_cases i; fin_cases j; rfl
  right_inv _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

/-- **AND TWO-BY-TWO OF `2^k`-BY-`2^k` IS `2^(k+1)`-BY-`2^(k+1)`.** The step of §4's induction,
and the general form of what `equivEight` does at four steps. -/
def matrixTwoPowFlatten (A : Type*) [Semiring A] [Algebra ℝ A] (k : ℕ) :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) A)
      ≃ₐ[ℝ] Matrix (Fin (2 ^ (k + 1))) (Fin (2 ^ (k + 1))) A :=
  (Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ k)) A ℝ).trans
    (Matrix.reindexAlgEquiv ℝ A (finProdFinEquiv.trans (finCongr (by ring))))

/-! ## 4. The tower's Clifford algebra -/

/-- **`k` HYPERBOLIC PLANES GIVE `2^k`-BY-`2^k` MATRICES.** One application of
`periodicityEquivHyp` per step, with §3 assembling the sizes. -/
def cliffordEquivHypTower (Q : QuadraticForm ℝ V) : ∀ k,
    CliffordAlgebra (hypForm Q k) ≃ₐ[ℝ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) (CliffordAlgebra Q)
  | 0 => (matrixFinOneAlgEquiv (CliffordAlgebra Q)).symm
  | (k + 1) =>
      ((periodicityEquivHyp (hypForm Q k)).trans
        (cliffordEquivHypTower Q k).mapMatrix).trans
        (matrixTwoPowFlatten (CliffordAlgebra Q) k)

/-! ## 5. The reduction, quantified over forms -/

/-- **THE `k`-FOLD STEP, FOR EVERY FORM OF THE RIGHT DIMENSION AND SIGNATURE.**
`CliffordHyperbolicStep.clifford_step_hyp` is the case `k = 1`.

**What this is.** A form whose indices are both `k` larger than `Q`'s has Clifford algebra
`M_{2^k}(Cl Q)` — so the whole diagonal `p − q` collapses onto its smallest point, and the
classification of a diagonal reduces to the classification of one form on it. -/
theorem clifford_reduce_k {W : Type u} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft) (k : ℕ)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2 * k)
    (hsig : sigPos Q' = sigPos Q + k) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) (CliffordAlgebra Q)) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ' (sep_hypForm hQ k)
    (by rw [hdim, finrank_hypSpace (V := V) k])
    (by rw [hsig, sigPos_hypForm])
  exact ⟨e.trans (cliffordEquivHypTower Q k)⟩

/-- **AND THE NEGATIVE INDEX FOLLOWS**, as at one step: nondegeneracy and the dimension force it,
so the `k`-fold move is `(+k, +k)` and diagonal-preserving. -/
theorem sigNeg_of_reduce {W : Type u} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft) (k : ℕ)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2 * k)
    (hsig : sigPos Q' = sigPos Q + k) :
    sigNeg Q' = sigNeg Q + k := by
  have h := sig_add_of_sep hQ
  have h' := sig_add_of_sep hQ'
  omega

/-! ## 6. The instance, so `k = 1` is visibly a case and not a parallel statement -/

/-- `CliffordHyperbolicStep.clifford_step_hyp` recovered at `k = 1` (`ERRATUM 201`), up to the
`2 ^ 1 = 2` the statement there writes as `2`. -/
theorem clifford_reduce_one {W : Type u} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2)
    (hsig : sigPos Q' = sigPos Q + 1) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) (CliffordAlgebra Q)) :=
  clifford_reduce_k hQ hQ' 1 (by rw [hdim]) hsig

end

end CliffordHypTower
