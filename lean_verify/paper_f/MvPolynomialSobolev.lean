/-
  MvPolynomialSobolev.lean — polynomials are members of the textbook Gaussian
  Sobolev space, and therefore the sharpness theorem this chain proved is the
  WEAKER of the two, not the stronger.

  WHY THIS FILE EXISTS, AND IT IS A CORRECTION OF A CORRECTION. `ERRATUM 547`
  found `TextbookSobolevPiSharp`'s *"In n dimensions the estate does not have it
  in any class"* false — the estate has **five** n-dimensional no-better-constant
  theorems on the polynomial class, counted rather than recalled:
  `GaussianPoincareProduct.no_better_constant_MV` and `_R16`,
  `GaussianProductMeasure.no_better_constant_measure` and
  `_R16_lambda_measure`, and `SpectralGaussianGap.no_better_constant_R16_lambda`
  (`ERRATUM 549` — `ERRATUM 547`'s own query record said three). **The
  annotation then said, of the two classes, that "this file's statement is the
  stronger". That is backwards** (`ERRATUM 548`).

  Both theorems have the shape *if `c` serves every member of the class, then
  `1 ≤ c`*. Polynomials sit INSIDE the textbook class, so quantifying over the
  textbook class is the STRONGER hypothesis, and a theorem with a stronger
  hypothesis is the WEAKER theorem. **`no_better_constant_sobolevWeakPi` is a
  corollary of `no_better_constant_MV`**, and this file proves the derivation
  rather than asserting the direction a second time.

  WHAT THIS FILE PROVES.

  1. `contDiff_eval` — polynomial evaluation on `Fin n → ℝ` is `C^∞`. Mathlib's
     `AnalyticOnNhd.eval_mvPolynomial`, then `AnalyticAt.contDiffAt` pointwise
     through `contDiff_iff_contDiffAt`. **Not in Mathlib as a `ContDiff`
     statement** — probed: no Mathlib FILE contains both `MvPolynomial` and any
     of `fderiv`, `ContDiff`, `HasFDerivAt`, so no declaration can, and
     `Topology/Algebra/MvPolynomial.lean` holds exactly one theorem,
     `continuous_eval`.
  2. **`fderiv_eval_single`** — `∂ᵢ(eval · p) = eval · (pderiv i p)`, the bridge
     between the analytic derivative and the FORMAL one. This is the file's
     content and the piece nothing anywhere had: an induction over
     `MvPolynomial.induction_on`, where the `p * X j` step is the product rule
     against `pderiv i (p * X j) = pderiv i p * X j + p * δᵢⱼ`.
  3. `memLp_eval` — and it is `L²(γⁿ)`, from
     `GaussianProductMeasure.integrable_eval` applied to `p * p`.
  4. **`sobolevWeakPi_eval`** — so a polynomial with its formal gradient IS a
     member of the textbook class. The nesting `ERRATUM 547` named and did not
     prove.
  5. **`no_better_constant_sobolevWeakPi_of_MV`** — and therefore the Sobolev
     sharpness statement follows from the polynomial one. Stated in the
     direction that is true.

  WHAT THIS DOES NOT DO. It does not withdraw `no_better_constant_sobolevWeakPi`.
  A corollary stated on the class a reader of the Sobolev chain has in hand is
  worth having, and that file proves it independently, by a witness rather than
  by this derivation. **What was wrong was one word about which of two theorems
  implies the other**, and the repair is this derivation plus a dated
  annotation. **No converse**: `no_better_constant_MV` does not follow from the
  Sobolev version here, and whether it does is not asked (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import TextbookSobolevPiSharp
import SteinGeneralPi
import GaussianPoincareProduct
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

namespace MvPolynomialSobolev

open MeasureTheory MvPolynomial
open GaussianProductMeasure TextbookSobolevPi

noncomputable section

variable {n : ℕ}

/-! ## 1. Polynomial evaluation is smooth -/

/-- Polynomial evaluation on `Fin n → ℝ` is `C^∞`. Mathlib has
`MvPolynomial.continuous_eval` and the analytic statement, and **no `ContDiff`
one** — `MvPolynomial` does not co-occur with `fderiv` or `ContDiff` in any
Mathlib declaration. -/
theorem contDiff_eval (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => MvPolynomial.eval x p) := by
  have h : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => MvPolynomial.eval x p) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial p
  exact contDiff_iff_contDiffAt.2 fun x => (h x (Set.mem_univ x)).contDiffAt

theorem differentiable_eval (p : MvPolynomial (Fin n) ℝ) :
    Differentiable ℝ (fun x : Fin n → ℝ => MvPolynomial.eval x p) :=
  (contDiff_eval p).differentiable (by simp)

/-! ## 2. And its derivative is the formal one -/

/-- **THE BRIDGE.** The analytic partial derivative of `eval · p` along the `i`-th
axis is the evaluation of the FORMAL partial derivative `pderiv i p`. Nothing in
Mathlib or this estate had it; the induction's only real step is `p * X j`, where
the product rule meets `pderiv i (p * X j) = pderiv i p * X j + p * δᵢⱼ`. -/
theorem fderiv_eval_single (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x (Pi.single i (1:ℝ))
      = MvPolynomial.eval x (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      have hd : ∀ z : Fin n → ℝ,
          HasFDerivAt (fun y : Fin n → ℝ => MvPolynomial.eval y p)
            (fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) z) z :=
        fun z => (differentiable_eval p z).hasFDerivAt
      have hd' : ∀ z : Fin n → ℝ,
          HasFDerivAt (fun y : Fin n → ℝ => MvPolynomial.eval y q)
            (fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y q) z) z :=
        fun z => (differentiable_eval q z).hasFDerivAt
      have : fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y (p + q)) x
          = fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x
            + fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y q) x := by
        have := ((hd x).add (hd' x)).fderiv
        simpa [MvPolynomial.eval_add] using this
      rw [this]
      simp only [ContinuousLinearMap.add_apply, hp, hq, map_add]
  | mul_X p j hp =>
      have hdp : HasFDerivAt (fun y : Fin n → ℝ => MvPolynomial.eval y p)
          (fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x) x :=
        (differentiable_eval p x).hasFDerivAt
      have hdx : HasFDerivAt (fun y : Fin n → ℝ => y j)
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) x :=
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
      have hmul : HasFDerivAt (fun y : Fin n → ℝ => MvPolynomial.eval y (p * MvPolynomial.X j))
          ((MvPolynomial.eval x p) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)
            + (x j) • fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x) x := by
        have := hdp.mul hdx
        simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X, mul_comm, add_comm] using this
      rw [hmul.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, hp]
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_X, mul_one]
        ring
      · rw [Pi.single_eq_of_ne (Ne.symm hij)]
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X, Ne.symm hij, mul_comm]

/-! ## 3. And it is `L²(γⁿ)` -/

/-- Polynomial evaluation is `L²(γⁿ)`. **The name is taken three times over in
this estate** — `GraphLaplacian.memLp_eval`, `LatticeField.memLp_eval` and
`OS2MeasureLevel.memLp_eval` are all *"the coordinate `ω ↦ ω p` of a Gaussian
FIELD is `L²`"*, a different statement about a different `eval`. None of the
three is in this file's import closure, so there is no ambiguity in Lean; the
collision is a reader's and is named here rather than renamed away, because the
file's other four names (`contDiff_eval`, `differentiable_eval`,
`fderiv_eval_single`, `sobolevWeakPi_eval`) all use `eval` for this one. -/
theorem memLp_eval (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x : Fin n → ℝ => MvPolynomial.eval x p) 2 (gaussPi n) := by
  refine (memLp_two_iff_integrable_sq ?_).mpr ?_
  · exact ((MvPolynomial.continuous_eval p).aestronglyMeasurable)
  · have h := integrable_eval n (p * p)
    simpa [MvPolynomial.eval_mul, sq] using h

/-! ## 4. So a polynomial is a member of the textbook class -/

/-- **THE NESTING.** A polynomial, with its FORMAL gradient, belongs to the
textbook Gaussian Sobolev space in `n` dimensions. `ERRATUM 547` named this and
did not prove it, and said it needed `MvPolynomial` evaluation to be `ContDiff`
and `MemLp` — which is exactly what §1 and §3 are. -/
theorem sobolevWeakPi_eval (p : MvPolynomial (Fin n) ℝ) :
    SobolevWeakPi n (fun x => MvPolynomial.eval x p)
      (fun i x => MvPolynomial.eval x (MvPolynomial.pderiv i p)) := by
  have h := SteinGeneralPi.sobolevWeakPi_of_contDiff (n := n)
    (f := fun x : Fin n → ℝ => MvPolynomial.eval x p)
    ((contDiff_eval p).of_le (by exact_mod_cast le_top))
    (memLp_eval p)
    (fun i => by
      have : (fun x : Fin n → ℝ =>
            fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x (Pi.single i (1:ℝ)))
          = fun x => MvPolynomial.eval x (MvPolynomial.pderiv i p) :=
        funext fun x => fderiv_eval_single p x i
      rw [this]
      exact memLp_eval _)
  have heq : (fun (i : Fin n) (x : Fin n → ℝ) =>
        fderiv ℝ (fun y : Fin n → ℝ => MvPolynomial.eval y p) x (Pi.single i (1:ℝ)))
      = fun (i : Fin n) (x : Fin n → ℝ) => MvPolynomial.eval x (MvPolynomial.pderiv i p) :=
    funext fun i => funext fun x => fderiv_eval_single p x i
  rwa [heq] at h

/-! ## 5. So the Sobolev sharpness statement is a COROLLARY -/

/-- **THE DIRECTION `ERRATUM 547` GOT BACKWARDS.** Both statements read *if `c`
serves every member of the class then `1 ≤ c`*; polynomials sit inside the
textbook class, so the textbook hypothesis is the STRONGER one and the textbook
theorem is therefore the WEAKER. Here it is, derived from
`GaussianPoincareProduct.no_better_constant_MV`.

`TextbookSobolevPiSharp.no_better_constant_sobolevWeakPi` is **not withdrawn** —
it proves the same conclusion independently, by a witness rather than by this
derivation, and it is stated on the class a reader of the Sobolev chain holds. -/
theorem no_better_constant_sobolevWeakPi_of_MV (n : ℕ) (c : ℝ)
    (h : ∀ (f : (Fin (n + 1) → ℝ) → ℝ) (g : Fin (n + 1) → ((Fin (n + 1) → ℝ) → ℝ)),
      SobolevWeakPi (n + 1) f g →
        (∫ x, f x * f x ∂gaussPi (n + 1)) - (∫ x, f x ∂gaussPi (n + 1)) ^ 2
          ≤ c * ∑ j : Fin (n + 1), ∫ x, g j x * g j x ∂gaussPi (n + 1)) :
    1 ≤ c := by
  refine GaussianPoincareProduct.no_better_constant_MV n c fun p => ?_
  have hp := h _ _ (sobolevWeakPi_eval p)
  rw [GaussianProductMeasure.EN_eq_integral, GaussianProductMeasure.EN_eq_integral]
  have hnum : (∫ x, MvPolynomial.eval x (p * p) ∂gaussPi (n + 1))
      = ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x p ∂gaussPi (n + 1) := by
    simp [MvPolynomial.eval_mul]
  have hden : ∀ j : Fin (n + 1),
      GaussianPoincareProduct.EN (n + 1) (MvPolynomial.pderiv j p * MvPolynomial.pderiv j p)
        = ∫ x, MvPolynomial.eval x (MvPolynomial.pderiv j p)
            * MvPolynomial.eval x (MvPolynomial.pderiv j p) ∂gaussPi (n + 1) := by
    intro j
    rw [GaussianProductMeasure.EN_eq_integral]
    simp [MvPolynomial.eval_mul]
  rw [hnum]
  simp_rw [hden]
  exact hp

/-! ## 6. Review round 70 — the ways this could be hollow

**"§2 could be in Mathlib."** Probed before writing and again after, at file
granularity, which is the stronger check: of the Mathlib files that mention
`MvPolynomial`, **none** mentions `fderiv`, `ContDiff` or `HasFDerivAt`, so no
Mathlib declaration can state this. `Topology/Algebra/MvPolynomial.lean` holds
exactly one theorem, `continuous_eval`. The analytic side
(`Analysis/Analytic/Polynomial.lean`) gives smoothness and says nothing about
which function the derivative is.

**"§5 could be circular."** It cites `GaussianPoincareProduct.no_better_constant_MV`,
whose proof is a witness at `MvPolynomial.X 0`. Checked at the import graph, not
by memory: that file's imports are `GaussianPoincare` and three Mathlib
`MvPolynomial` files, and no Sobolev-chain file is among them.

**"This makes the earlier theorem redundant."** It makes it a corollary, which is
not the same thing, and the header says so. `TextbookSobolevPiSharp` proves it
from `coord_sobolevWeakPi` and the estate's own attainment, with no polynomial
anywhere; two routes to one conclusion is not a defect, and the one on the
reader's own class is the one a reader of that chain wants.

**"The correction might be wrong again."** The check is mechanical and worth
writing out, since this is the second attempt at it. Both statements are
`(∀ x ∈ 𝒞, P x) → 1 ≤ c`. If `𝒜 ⊆ ℬ` then `(∀ x ∈ ℬ, P x) → (∀ x ∈ 𝒜, P x)`, so the
`ℬ`-hypothesis is the stronger and `(∀ x ∈ ℬ, P) → C` is the weaker theorem. Here
`𝒜` is the polynomials, `ℬ` the textbook class, and §4 is `𝒜 ⊆ ℬ`. **The direction
that type-checks is the direction that is true**, and §5 is that derivation
compiling.
-/

end

end MvPolynomialSobolev
