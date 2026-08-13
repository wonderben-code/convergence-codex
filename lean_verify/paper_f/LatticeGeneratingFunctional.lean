import FieldAutInvariance

/-!
# The generating functional of the lattice field, in closed form

The `UNLOCK_WATCHLIST` item for the OS axioms says of the three that are not OS2:

> **STILL OPEN: OS0** (regularity/growth of the generating functional), **OS1** (Euclidean
> covariance …), **OS4** (clustering). **None attempted, none made easier.**

This attempts the first one's finite-volume content, and the header is careful about what that
means — the same care `FieldAutInvariance` took when it delivered the finite-volume shadow of OS3
and said in capitals that it was **not** OS3.

## What is delivered

`generatingFunctional`: for every `f`,

    ∫ exp ⟪f, ω⟫ d(gaussianField G m) ω = exp (½ · f ⬝ᵥ green G m *ᵥ f)

on every finite graph, at every nonzero mass. Two things come with it:

* **The exponential moments of `gaussianField` are finite** (`integrable_exp_inner`). Scoped to
  this field deliberately: `GaussPiExp.integrable_exp_sumAbs` already has real exponential moments
  for the **OU-product** field `gaussPi`, built by hand out of a one-dimensional bound and a
  product argument. Nothing had them for the **lattice** field, where everything about
  exponentials went through `charFun` — modulus one, integrability free, and no information about
  the real exponential. Here they come out of the Gaussian structure rather than an estimate.
* **The growth is order two, with the constant named.** `generatingFunctional_smul` gives the
  whole ray `t ↦ exp(t²·c/2)` with `c = f ⬝ᵥ green G m *ᵥ f`, so the growth rate is not estimated
  but computed.

§4 records the two-point function as the special case `cov[ω p, ω q] = green G m p q`. Checked by
grep before being claimed: no statement in `paper_f` equates this field's covariance to the Green
function — the only other occurrence of the word is a scalar `def` in `BakryEmeryGap`.

## What this is NOT, and the precedent for saying so

**It is not OS0.** OS0 is a growth condition on the Schwinger functions of a *continuum* theory,
phrased with Schwartz seminorms and a factorial bound, and it constrains a whole sequence of
distributions. This is one finite-dimensional Gaussian integral. What is true is that the object
OS0 talks about — the generating functional — now **exists in closed form here**, with its
integrability and its growth order, where before the estate had it only through its characteristic
function. **No theorem in this file should be recorded as OS0**, and the watchlist item keeps
`OS0` open.

The reason for the capitals is the precedent, not an incident: the watchlist item recording the
OS3 shadow carries **"THIS IS NOT OS3 AND MUST NOT BE RECORDED AS OS3"** — written by its own
author as a **preventive** warning. An earlier draft of this paragraph said that shadow *"was
misread once already"*; `ERRATA.md` was searched for `OS3` and contains no such incident, so the
sentence was unsupported and is withdrawn. This file inherits the standard rather than a story
about it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeGeneratingFunctional

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The field paired against a test function is a real Gaussian

Everything below is this one fact plus Mathlib's real-Gaussian moment generating function. The
mean is zero because the field's is, and the variance is the Green quadratic form because that is
what `covarianceBilin` of a multivariate Gaussian is.
-/

/-- The pairing `ω ↦ ⟪f, ω⟫`, as a continuous linear functional. -/
noncomputable def pair (f : EuclideanSpace ℝ V) : EuclideanSpace ℝ V →L[ℝ] ℝ := innerSL ℝ f

omit [DecidableEq V] in
@[simp] theorem pair_apply (f ω : EuclideanSpace ℝ V) : pair f ω = ⟪f, ω⟫ := rfl

/-- **THE MEAN IS ZERO**, because the field's mean is. **No hypothesis on the mass** — the linter
found `m ≠ 0` unused here and it is: centring is a property of `multivariateGaussian 0 _`, whatever
the covariance turns out to be. -/
theorem integral_pair (f : EuclideanSpace ℝ V) :
    (gaussianField G m)[pair f] = 0 := by
  rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id (pair f),
    gaussianField, integral_id_multivariateGaussian]
  simp

/-- **THE VARIANCE IS THE GREEN QUADRATIC FORM.** -/
theorem variance_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Var[pair f; gaussianField G m] = f ⬝ᵥ green G m *ᵥ f := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  rw [← covariance_self (by fun_prop),
    show (⇑(pair f)) = (fun ω => ⟪f, ω⟫) from rfl,
    ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, gaussianField,
    covarianceBilin_multivariateGaussian hps]

/-- **SO THE PAIRING IS A CENTRED REAL GAUSSIAN**, with the Green form as its variance. -/
theorem map_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    (gaussianField G m).map (pair f)
      = gaussianReal 0 (f ⬝ᵥ green G m *ᵥ f).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal (pair f), integral_pair (G := G) f, variance_pair hm f]

/-! ## 2. The generating functional -/

/-- **THE GENERATING FUNCTIONAL, ALONG A RAY.** Order two, with the constant computed rather than
estimated. -/
theorem generatingFunctional_smul (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (t : ℝ) :
    ∫ ω, Real.exp (t * ⟪f, ω⟫) ∂(gaussianField G m)
      = Real.exp ((f ⬝ᵥ green G m *ᵥ f) * t ^ 2 / 2) := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  have hnn : (0 : ℝ) ≤ f ⬝ᵥ green G m *ᵥ f := by
    simpa using hps.dotProduct_mulVec_nonneg (WithLp.ofLp f)
  have h := mgf_gaussianReal (X := pair f) (p := gaussianField G m) (map_pair hm f) t
  rw [mgf] at h
  simpa [pair_apply, hnn, mul_comm] using h

/-- **THE GENERATING FUNCTIONAL.** The `t = 1` case, which is the statement OS0 is about. -/
theorem generatingFunctional (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m)
      = Real.exp ((f ⬝ᵥ green G m *ᵥ f) / 2) := by
  have h := generatingFunctional_smul (G := G) hm f 1
  simpa using h

/-! ## 3. The exponential moments exist

Everything the estate proved about exponentials went through `charFun`, whose integrand has
modulus one — integrability there is free and says nothing. This is the real exponential, and its
integrability is a fact about the Gaussian tail.
-/

/-- **THE FIELD HAS EXPONENTIAL MOMENTS**, at every test function and every nonzero mass. -/
theorem integrable_exp_inner (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Integrable (fun ω => Real.exp ⟪f, ω⟫) (gaussianField G m) := by
  have hmeas : AEMeasurable (pair f) (gaussianField G m) :=
    (pair f).continuous.measurable.aemeasurable
  have hstr : AEStronglyMeasurable (fun x : ℝ => Real.exp (1 * x))
      ((gaussianField G m).map (pair f)) := by fun_prop
  have h1 : Integrable (fun x : ℝ => Real.exp (1 * x))
      ((gaussianField G m).map (pair f)) := by
    rw [map_pair hm f]; exact integrable_exp_mul_gaussianReal 1
  have h2 := (integrable_map_measure hstr hmeas).mp h1
  simpa using h2

/-! ## 4. The two-point function is the Green function

Used informally since the field was defined, written down nowhere.
-/

/-- **THE COVARIANCE OF TWO SITES IS THE PROPAGATOR BETWEEN THEM.** -/
theorem covariance_eval (hm : m ≠ 0) (p q : V) :
    cov[fun ω => ω p, fun ω => ω q; gaussianField G m] = green G m p q := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  rw [gaussianField, covariance_eval_multivariateGaussian hps]

/-- **AND THE VARIANCE AT A SITE IS THE DIAGONAL ENTRY.** -/
theorem variance_eval (hm : m ≠ 0) (p : V) :
    Var[fun ω => ω p; gaussianField G m] = green G m p p := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  rw [gaussianField, variance_eval_multivariateGaussian hps]

end LatticeGeneratingFunctional
