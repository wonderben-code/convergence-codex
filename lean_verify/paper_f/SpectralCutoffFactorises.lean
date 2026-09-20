/-
  SpectralCutoffFactorises: the semigroup law the spectral action assumes, PROVED

  SPINE LINK L19 ("Spectral action -> exponential forced").

  WHAT THE SPINE SAID IN JULY, and what the 14 September recompute found. The July
  headline reads "spectral action -> exponential forced". The RIGHT-HAND half is real:
  `F4_1h_CauchyFunctionalEquation.semigroup_exponential_form` proves that a positive,
  monotone, multiplicative `g : ℝ → ℝ` is `exp (log (g 1) * x)`, with standard axioms
  and no `sorry`. The LEFT-hand half -- the arrow -- was not proved anywhere. Every
  theorem in `F4_1h` takes the semigroup law `g (x + y) = g x * g y` as a HYPOTHESIS,
  and `ASSUMPTIONS_LEDGER` 12 records that the claim that the cascade's tensor
  structure SUPPLIES that law is assumed and discharged nowhere. `F4_1h` had **zero
  consumers**: no file in the estate had ever applied it to anything.

  THIS FILE PROVES THE ARROW, IN BOTH THE SENSES IT CAN BE PROVED.

  (1) AT THE MATRIX LEVEL. The cascade's step is a tensor product, so a Dirac operator
      built from two levels is a Kronecker SUM `D₁ ⊗ₖ 1 + 1 ⊗ₖ D₂`. For the
      exponential cutoff the spectral action of that sum FACTORISES:
        `trace (exp (D₁ ⊗ₖ 1 + 1 ⊗ₖ D₂)) = trace (exp D₁) * trace (exp D₂)`
      (`trace_exp_kroneckerSum`). This is a theorem, not a hypothesis: the two Kronecker
      embeddings commute (`commute_kroneckerEmbeddings`), `exp` carries each of them
      (`exp_kroneckerRight`, `exp_kroneckerLeft`), and `Matrix.trace_kronecker` closes it.
      ⚠ (hardening unit 172, `OrderOneCutoffFactorises`): *built from two levels is a
      Kronecker SUM* is the PREMISE `UNLOCK_WATCHLIST` `L40433` records as assumed for the
      cascade's `D` — the estate has no `cascadeDirac`. On the regular bimodule of `Mₙ(ℂ)`
      the same shape is FORCED by CCM's order-one condition
      (`OrderOneRegularBimodule.orderOne_iff_kron`, unit 168), and
      `OrderOneCutoffFactorises.trace_exp_of_orderOne` composes that with this file's
      `trace_exp_smul_kroneckerSum`; at the witness the trace is `(eᵗ + e⁻ᵗ)²`.

  (2) AT THE SPECTRUM LEVEL, which is where the physics lives. Eigenvalues of a tensor
      sum ADD, so "the action factorises over tensor sums" says, for a cutoff `f`,
        `∑ i ∑ j, f (aᵢ + bⱼ) = (∑ i, f aᵢ) * (∑ j, f bⱼ)`  for all finite spectra.
      `semigroup_of_factorises` proves that this forces `f (x + y) = f x * f y` -- the
      exact hypothesis `F4_1h` needs -- by instantiating at one-point spectra. Composing
      gives `cutoff_exponential_of_factorises`: **the first consumer `F4_1h` has ever
      had**, with `ASSUMPTIONS_LEDGER` 12's silent assumption as a NAMED and DISCHARGED
      hypothesis rather than a sentence in a comment.
      ⚠ (hardening unit 174, `DecayingCutoff`, `ERRATUM 678`): *monotone* here is Mathlib's
      `Monotone f` — NON-DECREASING. Under it the exponent `log (f 1)` is provably `≥ 0`
      (`DecayingCutoff.log_nonneg_of_monotone`, `one_le_of_monotone`), so this class contains
      NO decaying cutoff, `e^{−v}` included — the case the physics uses. The decaying case is
      `DecayingCutoff.cutoff_exponential_of_antitone_factorises`, by reflection `x ↦ f (−x)`,
      with exponent `−log (f (−1))` and `log (f (−1)) ≥ 0`; `decaying_inhabited` is its witness.

  THE HYPOTHESIS CLASS IS SHOWN INHABITED, and that is deliberate. `ERRATUM 557` was
  filed this same day against a theorem of mine whose hypothesis no rational could
  satisfy: it was true, machine-checked, and said nothing. The rule recorded there is
  that a bridge stated as a hypothesis carries its witness. So `exp_factorises` proves
  `Real.exp` satisfies `Factorises`, and `cutoff_factorisation_inhabited` exhibits it
  together with positivity and monotonicity. `two_not_factorises` is the negative
  control: the constant cutoff `2` does NOT factorise, so `Factorises` is not vacuous
  in the other direction either -- it is a real constraint that the exponential meets
  and other functions fail.

  WHAT IS **NOT** PROVED HERE, stated plainly.
  * That the cascade's OWN Dirac operator is a Kronecker sum of two level operators.
    That identification is `ASSUMPTIONS_LEDGER` 12 and it is untouched: this file proves
    what follows FROM the tensor-sum shape, not that the estate's `D` has it.
  * Nothing about the spectral action as an integral or an asymptotic expansion. There
    is no heat-kernel coefficient anywhere in this estate or in pinned Mathlib
    (re-verified 14 Sep), which is `WALLS` §W5 and spine link L22.
  * The physical normalisations. `log (f 1)` is a real number the theorem returns; that
    it is negative, or that it is `-1` after absorbing the cutoff Λ, is a boundary
    condition nothing here supplies. L19's tail -- "zero free parameters" -- is claimed
    by six `F3_10a` declarations whose statements are `exp 0 = 1` and `12 * 2 * 16 = 384`,
    and this file does not improve them.
  * Monotonicity of the cutoff is a HYPOTHESIS of `cutoff_exponential_of_factorises`,
    inherited from `F4_1h`. Factorisation alone does not force the exponential: the
    Cauchy equation has non-measurable solutions.

  MATHLIB USED. `Matrix.exp_add_of_commute`, `Matrix.trace_kronecker`,
  `Matrix.mul_kronecker_mul`, `NormedSpace.map_exp` -- the matrix exponential had
  **never been imported by this estate** before this file (`grep -rl 'Matrix.exp'`
  returned nothing), which is why the arrow looked harder than it is.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import F4_1h_CauchyFunctionalEquation

open Matrix NormedSpace
open scoped Kronecker
open scoped Matrix.Norms.Operator

namespace SpectralCutoffFactorises

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-! ## 1. The two Kronecker embeddings, as ring homomorphisms

`A ↦ A ⊗ₖ 1` and `B ↦ 1 ⊗ₖ B` are the two ways a level of the cascade sits inside the
tensor product of two levels. Both are ring homomorphisms -- the multiplicativity is
`Matrix.mul_kronecker_mul` with `1 * 1 = 1` -- and both are continuous, because each
entry of the image is an entry of the source times a constant. Bundling them is what
lets `NormedSpace.map_exp` carry the exponential across. -/

/-- `A ↦ A ⊗ₖ 1`: the left level embedded in the tensor product. -/
def kroneckerRight (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.add_kronecker]

/-- `B ↦ 1 ⊗ₖ B`: the right level embedded in the tensor product. -/
def kroneckerLeft (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun B := (1 : Matrix m m ℂ) ⊗ₖ B
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.kronecker_add]

theorem continuous_kroneckerRight : Continuous (kroneckerRight m n) := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

theorem continuous_kroneckerLeft : Continuous (kroneckerLeft m n) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

/-! ## 2. The exponential carries both embeddings

A continuous ring homomorphism commutes with `NormedSpace.exp` (`map_exp`). The
`CompleteSpace` instance has to be pinned with `inferInstanceAs`: the uniformity coming
from `Matrix.linftyOpNormedRing` and the one coming from the product topology are
definitionally equal but not syntactically equal, so instance search does not bridge
them on its own. -/

theorem exp_kroneckerRight (A : Matrix m m ℂ) :
    exp (A ⊗ₖ (1 : Matrix n n ℂ)) = exp A ⊗ₖ (1 : Matrix n n ℂ) :=
  (@map_exp (Matrix m m ℂ) (Matrix (m × n) (m × n) ℂ) _ _
    (inferInstanceAs (CompleteSpace (Matrix m m ℂ))) _ _ _ _ _
    (kroneckerRight m n) continuous_kroneckerRight A).symm

theorem exp_kroneckerLeft (B : Matrix n n ℂ) :
    exp ((1 : Matrix m m ℂ) ⊗ₖ B) = (1 : Matrix m m ℂ) ⊗ₖ exp B :=
  (@map_exp (Matrix n n ℂ) (Matrix (m × n) (m × n) ℂ) _ _
    (inferInstanceAs (CompleteSpace (Matrix n n ℂ))) _ _ _ _ _
    (kroneckerLeft m n) continuous_kroneckerLeft B).symm

/-! ## 3. The Kronecker sum, and the factorisation at the matrix level -/

/-- The Kronecker (tensor) sum: the Dirac operator of a composite of two cascade
levels. Its eigenvalues are the sums of the eigenvalues of the two summands, which is
the reason the spectral action of an exponential cutoff factorises. -/
def kroneckerSum (D₁ : Matrix m m ℂ) (D₂ : Matrix n n ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  D₁ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ D₂

/-- The two embedded levels commute. This is `Matrix.mul_kronecker_mul` twice: both
products are `D₁ ⊗ₖ D₂`. -/
theorem commute_kroneckerEmbeddings (D₁ : Matrix m m ℂ) (D₂ : Matrix n n ℂ) :
    Commute (D₁ ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix m m ℂ) ⊗ₖ D₂) := by
  unfold Commute SemiconjBy
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- **The exponential of a Kronecker sum is the Kronecker product of the
exponentials.** No hypothesis: this holds for every pair of complex matrices. -/
theorem exp_kroneckerSum (D₁ : Matrix m m ℂ) (D₂ : Matrix n n ℂ) :
    exp (kroneckerSum D₁ D₂) = exp D₁ ⊗ₖ exp D₂ := by
  rw [kroneckerSum, Matrix.exp_add_of_commute _ _ (commute_kroneckerEmbeddings D₁ D₂),
    exp_kroneckerRight, exp_kroneckerLeft, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- **THE ARROW, AT THE MATRIX LEVEL.** The spectral action with an exponential cutoff
factorises across the cascade's tensor sum. This is the statement
`ASSUMPTIONS_LEDGER` 12 records as assumed; here it is a theorem with no hypothesis
at all. -/
theorem trace_exp_kroneckerSum (D₁ : Matrix m m ℂ) (D₂ : Matrix n n ℂ) :
    (exp (kroneckerSum D₁ D₂)).trace = (exp D₁).trace * (exp D₂).trace := by
  rw [exp_kroneckerSum, Matrix.trace_kronecker]

/-- With a cutoff scale: rescaling the operator rescales each summand, so the
factorisation survives the cutoff. `t` is `-1/Λ²` in the physics. -/
theorem trace_exp_smul_kroneckerSum (t : ℂ) (D₁ : Matrix m m ℂ) (D₂ : Matrix n n ℂ) :
    (exp (t • kroneckerSum D₁ D₂)).trace = (exp (t • D₁)).trace * (exp (t • D₂)).trace := by
  have h : t • kroneckerSum D₁ D₂ = kroneckerSum (t • D₁) (t • D₂) := by
    simp only [kroneckerSum, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [h, trace_exp_kroneckerSum]

/-! ## 4. The factorisation at the level of spectra

Eigenvalues of a tensor sum add. So for a cutoff `f` the statement "the action of a
composite is the product of the actions" is a statement about finite multisets of
reals, and it is this form that connects to `F4_1h`. -/

/-- A cutoff `f` **factorises** when, for every pair of finite spectra, the action of
the tensor sum is the product of the actions. -/
def Factorises (f : ℝ → ℝ) : Prop :=
  ∀ (p q : ℕ) (a : Fin p → ℝ) (b : Fin q → ℝ),
    (∑ i, ∑ j, f (a i + b j)) = (∑ i, f (a i)) * (∑ j, f (b j))

/-- **Factorisation forces the semigroup law.** One-point spectra already do it: the
`p = q = 1` instance of `Factorises` IS `f (x + y) = f x * f y`. This is the hypothesis
every theorem in `F4_1h` takes and that nothing in the estate discharged. -/
theorem semigroup_of_factorises (f : ℝ → ℝ) (hf : Factorises f) (x y : ℝ) :
    f (x + y) = f x * f y := by
  have h := hf 1 1 (fun _ => x) (fun _ => y)
  simpa using h

/-- **The witness: the exponential factorises.** `ERRATUM 557`'s rule -- a bridge
stated as a hypothesis carries its witness -- applied before the fact rather than
after it. -/
theorem exp_factorises : Factorises Real.exp := by
  intro p q a b
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.exp_add]

/-- The negative control, so that `Factorises` is known to have content in both
directions: the constant cutoff `2` does not factorise, because `2 ≠ 2 * 2`. -/
theorem two_not_factorises : ¬ Factorises (fun _ => (2 : ℝ)) := by
  intro h
  have := h 1 1 (fun _ => 0) (fun _ => 0)
  simp at this

/-- The hypothesis class of `cutoff_exponential_of_factorises` is inhabited. -/
theorem cutoff_factorisation_inhabited :
    ∃ f : ℝ → ℝ, (∀ x, 0 < f x) ∧ Monotone f ∧ Factorises f :=
  ⟨Real.exp, fun x => Real.exp_pos x, Real.exp_monotone, exp_factorises⟩

/-! ## 5. `F4_1h` gets its first consumer -/

/-- **L19's ARROW, COMPOSED WITH ITS CONVERSE.** A positive, monotone cutoff whose
spectral action factorises over tensor sums is an exponential. The factorisation
hypothesis is the one `trace_exp_kroneckerSum` shows the cascade's tensor structure
satisfies for `exp`, and `cutoff_factorisation_inhabited` shows it is not empty.

This is the **first** declaration in the estate to apply
`F4_1h_CauchyFunctionalEquation.semigroup_exponential_form` to anything. -/
theorem cutoff_exponential_of_factorises (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hmon : Monotone f) (hfact : Factorises f) (x : ℝ) :
    f x = Real.exp (Real.log (f 1) * x) :=
  semigroup_exponential_form f hpos (semigroup_of_factorises f hfact) hmon x

/-- The same conclusion with the boundary condition `f 1 = Real.exp c` read off, so the
exponent is visible as a single real constant: the cutoff has one parameter, and
`f 1` fixes it. What no theorem here supplies is that the constant is negative.
⚠ `ERRATUM 678` (unit 174): under `Monotone f` the constant is `≥ 0`
(`DecayingCutoff.log_nonneg_of_monotone`); the decaying case, `∃ κ ≥ 0, f x = exp (−(κ x))`,
is `DecayingCutoff.cutoff_one_parameter_antitone`. -/
theorem cutoff_one_parameter (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hmon : Monotone f) (hfact : Factorises f) :
    ∃ c : ℝ, ∀ x, f x = Real.exp (c * x) :=
  ⟨Real.log (f 1), fun x => cutoff_exponential_of_factorises f hpos hmon hfact x⟩

end SpectralCutoffFactorises
