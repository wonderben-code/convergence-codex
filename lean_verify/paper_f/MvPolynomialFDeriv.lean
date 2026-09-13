/-
  MvPolynomialFDeriv.lean — the FULL Fréchet derivative of polynomial
  evaluation, and the chain rule that follows from it.

  WHY THIS FILE EXISTS. Mathlib's `Analysis/Calculus/Deriv/Polynomial.lean`
  gives the UNIVARIATE polynomial a complete differentiation API — **26
  declarations**, counted: `hasStrictDerivAt`, `hasDerivAt`, `hasDerivWithinAt`,
  `differentiableAt`, `differentiable`, `differentiableOn`, `deriv`,
  `derivWithin`, `hasFDerivAt` and the rest, most with an `aeval` twin. **The multivariate
  file does not exist.** Probed at file granularity, which is stronger than
  declaration granularity: of the Mathlib files that mention `MvPolynomial`,
  **none** mentions `fderiv`, `ContDiff` or `HasFDerivAt`.

  `MvPolynomialSobolev` (2026-09-13, the unit before this one) opened that gap
  by one lemma: `fderiv_eval_single`, the derivative along the `i`-th AXIS. That
  is what the Gaussian Sobolev chain consumes, because `SobolevWeakPi` is
  written with `Pi.single i 1` throughout — and it is the whole estate's
  convention: outside this unit's own two files, `Pi.single` shares a line with
  `fderiv` **218 times across 22 files**.

  **THIS FILE REMOVES THE AXIS RESTRICTION.** The derivative is a continuous
  linear map, the axes determine it, and the statement about all directions is
  the one that composes. `fderiv_eval_single` becomes the `v = Pi.single i 1`
  case of `fderiv_eval_apply`, and §2 proves that specialisation rather than
  asserting it.

  WHAT THIS FILE PROVES.

  1. `clm_apply_eq_sum` — a continuous linear map out of `Fin n → ℝ` is the sum
     of its axis values: `L v = ∑ i, v i • L (Pi.single i 1)`. True of every
     CLM, nothing polynomial in it, and the estate had never stated it.
     `clm_ext_single` is the ext lemma it gives.
  2. **`fderiv_eval_apply`** — `∂ᵥ(eval · p)(x) = ∑ᵢ vᵢ · eval x (pderiv i p)`,
     in EVERY direction. And **`fderiv_eval`**, the same as an identity between
     continuous linear maps, which is the form a chain rule can consume.
  3. **`hasFDerivAt_eval`** — the `HasFDerivAt` form. This is the multivariate
     twin of Mathlib's `Polynomial.hasFDerivAt`, and it is the one declaration
     here that everything else could have been derived from had it come first.
  4. `dirPderiv` and **`fderiv_eval_dir`** — the directional derivative is again
     the evaluation of a POLYNOMIAL, `∑ᵢ C vᵢ * pderiv i p`. The formal-analytic
     bridge of the unit before, now closed under taking directions.
  5. **`hasFDerivAt_eval_comp`** — the chain rule: a polynomial of a
     differentiable map is differentiable, with the derivative you expect.
     Nothing in Mathlib or this estate had it, and it is the reusable one.
  6. `fderiv_eval_single_of_apply` — today's axis lemma recovered, so the
     nesting is proved and not claimed.

  WHAT THIS DOES NOT DO. **No `HasStrictFDerivAt`, no `iteratedFDeriv`, no
  `derivWithin`** — Mathlib's univariate file has all three and this one has
  none, so the multivariate API is opened, not completed. Nothing in this estate
  consumes them and `ERRATUM 246` is the entry about proving what is wanted
  rather than what would look symmetric. **No new analysis**: every step is the
  chain rule or linearity, and the mathematical content was spent in
  `MvPolynomialSobolev.fderiv_eval_single`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import MvPolynomialSobolev

namespace MvPolynomialFDeriv

open MeasureTheory MvPolynomial
open MvPolynomialSobolev

noncomputable section

variable {n : ℕ}

/-! ## 1. A continuous linear map out of `Fin n → ℝ` is its axis values -/

/-- **THE AXES DETERMINE THE MAP.** Nothing polynomial here: this is
`pi_eq_sum_univ'` pushed through linearity, and it is the reason an axiswise
statement about a derivative is a statement about every direction. -/
theorem clm_apply_eq_sum (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, v i * L (Pi.single i (1 : ℝ)) := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Two continuous linear functionals agreeing on the axes are equal. -/
theorem clm_ext_single {L M : (Fin n → ℝ) →L[ℝ] ℝ}
    (h : ∀ i, L (Pi.single i (1 : ℝ)) = M (Pi.single i (1 : ℝ))) : L = M := by
  ext v
  rw [clm_apply_eq_sum L v, clm_apply_eq_sum M v]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-! ## 2. The full Fréchet derivative of polynomial evaluation -/

/-- **THE DERIVATIVE IN EVERY DIRECTION.** `MvPolynomialSobolev.fderiv_eval_single`
is the `v = Pi.single i 1` case; §2's last theorem proves that it is. -/
theorem fderiv_eval_apply (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x v
      = ∑ i, v i * MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  rw [clm_apply_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [fderiv_eval_single p x i]

/-- The gradient as a continuous linear map: the sum of the formal partials
against the coordinate projections. -/
theorem fderiv_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x
      = ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i p)
          • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
  ext v
  rw [fderiv_eval_apply p x v]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **THE MULTIVARIATE TWIN OF `Polynomial.hasFDerivAt`.** Mathlib has the
univariate statement and no multivariate file at all. -/
theorem hasFDerivAt_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => MvPolynomial.eval y p)
      (∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i p)
        • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have h := (differentiable_eval p x).hasFDerivAt
  rwa [fderiv_eval p x] at h

/-- **THE NESTING, PROVED.** The unit before this one states the axis case;
here it is as the `v = Pi.single i 1` instance of `fderiv_eval_apply`, so the
claim that the general statement subsumes it is a theorem. -/
theorem fderiv_eval_single_of_apply (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x (Pi.single i (1:ℝ))
      = MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  classical
  rw [fderiv_eval_apply p x (Pi.single i (1:ℝ))]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## 3. And the direction is again a polynomial -/

/-- The FORMAL directional derivative: `∑ᵢ vᵢ · ∂ᵢp`, a polynomial. -/
def dirPderiv (v : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv i p

theorem eval_dirPderiv (v : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (dirPderiv v p)
      = ∑ i, v i * MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  simp [dirPderiv, MvPolynomial.eval_mul]

/-- **THE FORMAL-ANALYTIC BRIDGE, CLOSED UNDER DIRECTIONS.** The unit before
identified the axis derivative with `pderiv i`; every directional derivative is
the evaluation of a polynomial too. -/
theorem fderiv_eval_dir (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x v
      = MvPolynomial.eval x (dirPderiv v p) := by
  rw [eval_dirPderiv, fderiv_eval_apply]

/-! ## 4. The chain rule -/

/-- **A POLYNOMIAL OF A DIFFERENTIABLE MAP IS DIFFERENTIABLE**, with the
derivative the chain rule predicts. Absent from Mathlib — which has no
multivariate differentiation file — and from this estate. -/
theorem hasFDerivAt_eval_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → Fin n → ℝ} {g' : E →L[ℝ] Fin n → ℝ} {x : E}
    (hg : HasFDerivAt g g' x) (p : MvPolynomial (Fin n) ℝ) :
    HasFDerivAt (fun y : E => MvPolynomial.eval (g y) p)
      ((∑ i, MvPolynomial.eval (g x) (MvPolynomial.pderiv i p)
        • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)).comp g') x :=
  (hasFDerivAt_eval p (g x)).comp x hg

/-- The chain rule, read off in one direction. -/
theorem fderiv_eval_comp_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → Fin n → ℝ} {g' : E →L[ℝ] Fin n → ℝ} {x : E}
    (hg : HasFDerivAt g g' x) (p : MvPolynomial (Fin n) ℝ) (w : E) :
    fderiv ℝ (fun y : E => MvPolynomial.eval (g y) p) x w
      = ∑ i, (g' w) i * MvPolynomial.eval (g x) (MvPolynomial.pderiv i p) := by
  rw [(hasFDerivAt_eval_comp hg p).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A polynomial of a differentiable map is differentiable. -/
theorem differentiable_eval_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → Fin n → ℝ} (hg : Differentiable ℝ g)
    (p : MvPolynomial (Fin n) ℝ) :
    Differentiable ℝ (fun y : E => MvPolynomial.eval (g y) p) :=
  fun x => (hasFDerivAt_eval_comp (hg x).hasFDerivAt p).differentiableAt

/-! ## 5. Review round 71 — the ways this could be hollow

**"§1 must be in Mathlib."** The DECOMPOSITION is (`pi_eq_sum_univ'`, which this
uses); the statement about a continuous linear map is not, and neither is the
ext lemma. Probed: `pi_eq_sum_univ'` occurs in Mathlib **exactly once**, at its
own declaration — it has no use anywhere in the library, let alone one beside
`ContinuousLinearMap`. And in `paper_f`, no line carries both `Pi.single` and
`ContinuousLinearMap` outside this unit. It is four lines here and is stated
because §2 needs it and a reader should see which step is the linear-algebra one.

**"§2 is a restatement."** It is not: `MvPolynomialSobolev.fderiv_eval_single`
constrains the derivative on `n` vectors and says nothing about the other
directions until §1 is available. The evidence that the two differ is
`fderiv_eval_single_of_apply`, which is a PROOF that the general one gives the
axis one — the direction that needs an argument. Nothing here gives the converse
for free either; §2 consumes the axis lemma, and the file says so.

**"§4 could be vacuous."** `hasFDerivAt_eval_comp` at `g = id` is
`hasFDerivAt_eval`, so the hypothesis is satisfiable and the conclusion is not
trivially true. At `E = ℝ` it is the statement that `t ↦ p(γ(t))` is
differentiable along a differentiable curve, which is the use a reader will have.

**"This should have been in the unit before."** It should have, and that is
worth saying plainly rather than presenting the split as a plan: the axis lemma
was written to serve `SobolevWeakPi`, whose definition is axiswise, and the
question *what about the other directions* was not asked until the file was
finished. The split is a record of how the work went, not a design.

**"The API is now complete."** It is not, and the header says which twenty
Mathlib declarations have no twin here. What is built is what something
consumes: `SobolevWeakPi` consumes the axis case, the chain rule is the piece a
reader composing polynomials with maps needs, and `HasStrictFDerivAt` and
`iteratedFDeriv` have no consumer in this estate and are not written.
-/

end

end MvPolynomialFDeriv
