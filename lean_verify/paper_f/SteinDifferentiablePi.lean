import SteinGeneralPi
import DifferentiableNotC1

/-!
# The n-dimensional criterion, with `C¹` weakened to differentiable

`SteinGeneralPi` proved that a `ContDiff ℝ 1` function whose value and gradient are
square-integrable belongs to the Gaussian Sobolev class, hence to the Stein class, hence satisfies
the Poincaré inequality. **Its one-dimensional twin never asked for `C¹`.**
`PoincareBeyondPolynomials.stein_general` takes `hderiv : ∀ x, HasDerivAt f (f' x) x` and polynomial
growth, and nothing else; so does `PoincareSteinScaled.poincare_scaled_beyond_original`, and so
does `LatticePoincare.poincare_smeared`, which is built on it. The n-dimensional chain has been
the weaker of the two since it was written.

`UNLOCK_WATCHLIST`'s item says so in its own title — *"n-dimensional `stein_general` — a
**differentiable** function of polynomial growth IS a Stein pair with its gradient"* — and the
closure recorded under it delivers `SteinGeneralPi.steinPairPi_of_contDiff`, a `C¹` function. The
item was closed by something adjacent to it.

**Why this could not be settled by rewording until now.** `Differentiable` and `ContDiff ℝ 1` are
different hypotheses, but until `DifferentiableNotC1` the estate had no object separating them, so
"weaken `C¹` to differentiable" was a statement about hypothesis lists with no demonstrated content.
§4 supplies the content: a member of the class reached by this file's criterion and **not** by
`SteinGeneralPi`'s.

## Where the `C¹` was actually being used, which is one place

`sobolevWeakPi_of_contDiff` is `⟨hmem, hgrad, integral_mul_partial⟩`, and the first two components
are `MemLp` hypotheses that never mention smoothness. Inside `integral_mul_partial`, Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` asks only for `DifferentiableAt` — **the
`ContDiff` is spent entirely on producing the three integrability side conditions from continuity.**

Two of those three survive unchanged: they involve `f` itself, and a differentiable function is
continuous. Only the third, `Integrable (∂ᵢf · ψ)`, genuinely loses its argument, because `∂ᵢf` of a
merely differentiable `f` need not be continuous. `measurable_partial` supplies measurability
(`measurable_fderiv_apply_const`), and a growth bound supplies domination against a continuous
compactly supported majorant — which is exactly the polynomial-growth hypothesis the 1-d twin
already carries.

## What is proved

* **`integral_mul_partial_of_differentiable`** — the integration-by-parts clause for a merely
  differentiable `f` whose `i`-th partial obeys a polynomial bound;
* **`sobolevWeakPi_of_differentiable`**, **`steinPairPi_of_differentiable`** — the membership
  criteria, with hypotheses `(hf, hb, hb')` matching the 1-d twin's shape;
* **`poincare_differentiable`** — and so the n-dimensional Gaussian Poincaré inequality for an
  arbitrary differentiable function of polynomial growth, with no continuity of the gradient;
* **`wigCoord`** — `x ↦ wig xᵢ`, differentiable, of polynomial growth, and **not `ContDiff ℝ 1`**;
  `poincare_wigCoord` runs the inequality on it, and `criterion_strictly_weaker_hypotheses` records
  that `SteinGeneralPi`'s criterion cannot.

## What this is NOT

**It does not remove polynomial growth.** `SteinGeneralPi`'s criterion takes bare `MemLp` conditions
and no growth bound at all; this one takes a growth bound, because the domination argument needs a
majorant. So the two criteria are **not nested** — this reaches non-`C¹` functions, that one
reaches `C¹` functions of super-polynomial growth that happen to stay `L²`.
`criterion_strictly_weaker_hypotheses` claims only the direction it proves. *The same
incomparability `LatticeSmearedFromGeneral` found between the estate's two Poincaré lines reappears
here, for the same reason: a growth hypothesis and a smoothness hypothesis are traded against each
other, not ordered.*

**It does not prove that a differentiable function with no growth bound is a Stein pair**, and that
is not a gap in the write-up but a genuine obstruction: a derivative of an everywhere-differentiable
function need not be locally integrable, so `Integrable (∂ᵢf · ψ)` can fail outright. The bound is
load-bearing.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SteinDifferentiablePi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open GaussPiDensity HermitePiStein HermitePiPoincare TextbookSobolevPi
open W6ConversePi GaussPiExp SteinGeneralPi

variable {n : ℕ}

/-! ## 1. The partial derivative of a merely differentiable function is measurable -/

/-- `x ↦ ∂ᵢf x` is measurable for **any** `f`, differentiable or not: Mathlib's
`measurable_fderiv_apply_const` sends non-differentiability points to `0`. This is the only thing
that replaces `SteinGeneralPi.continuous_gradient`, and it needs no hypothesis at all. -/
theorem measurable_partial (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    Measurable fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) :=
  measurable_fderiv_apply_const ℝ f (Pi.single i (1 : ℝ))

/-- A coordinate is bounded by the norm, squared. Used to push a one-variable growth bound up to
`Fin n → ℝ`. -/
theorem sq_apply_le (x : Fin n → ℝ) (i : Fin n) : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h : |x i| ≤ ‖x‖ := by
    have := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at this
  nlinarith [abs_nonneg (x i), sq_abs (x i), norm_nonneg x]

/-! ## 2. The integration-by-parts clause, without continuity of the gradient -/

/-- **`∫ f·∂ᵢψ = −∫ (∂ᵢf)·ψ` for a merely DIFFERENTIABLE `f`.**

Compare `SteinGeneralPi.integral_mul_partial`, which asks for `ContDiff ℝ 1 f` and no growth bound.
The `ContDiff` there is spent on three integrability facts; two of them only need `f` continuous,
which differentiability gives. The third, `Integrable (∂ᵢf · ψ)`, is what a polynomial bound on
`∂ᵢf` buys instead — `∂ᵢf` is measurable for free, and `C·(1+‖x‖²)^k·|ψ|` is a continuous
compactly supported majorant. -/
theorem integral_mul_partial_of_differentiable {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) {C : ℝ} {k : ℕ}
    (hb' : ∀ x, |fderiv ℝ f x (Pi.single i (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, f x * fderiv ℝ ψ x (Pi.single i (1 : ℝ)))
      = -∫ x, fderiv ℝ f x (Pi.single i (1 : ℝ)) * ψ x := by
  have hfc : Continuous f := hf.continuous
  have hmaj : Continuous fun x : Fin n → ℝ => C * (1 + ‖x‖ ^ 2) ^ k * |ψ x| := by
    fun_prop
  have hmajc : HasCompactSupport fun x : Fin n → ℝ => C * (1 + ‖x‖ ^ 2) ^ k * |ψ x| :=
    (hcψ.abs).mul_left
  have hmajint : Integrable
      (fun x : Fin n → ℝ => C * (1 + ‖x‖ ^ 2) ^ k * |ψ x|) volume :=
    hmaj.integrable_of_hasCompactSupport hmajc
  have h1 : Integrable
      (fun x : Fin n → ℝ => fderiv ℝ f x (Pi.single i (1 : ℝ)) * ψ x) volume := by
    refine hmajint.mono' (((measurable_partial f i).aestronglyMeasurable).mul
      hψ.continuous.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb' x) (abs_nonneg _)
  have h2 : Integrable
      (fun x : Fin n → ℝ => f x * fderiv ℝ ψ x (Pi.single i (1 : ℝ))) volume :=
    (hfc.mul (continuous_partial n hψ i)).integrable_of_hasCompactSupport
      (hasCompactSupport_partial n hcψ i).mul_left
  have h3 : Integrable (fun x : Fin n → ℝ => f x * ψ x) volume :=
    (hfc.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Fin n → ℝ))) (v := Pi.single i (1 : ℝ)) h1 h2 h3
    (fun x _ => hf.differentiableAt)
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)

/-! ## 3. The criteria, and the inequality they deliver -/

/-- **THE MEMBERSHIP CRITERION, WITHOUT `C¹`.** A differentiable function of polynomial growth,
whose partial derivatives obey the same bound, belongs to the textbook Gaussian Sobolev space with
its actual gradient as the weak one.

The hypothesis list is the 1-d twin's, transcribed: `PoincareBeyondPolynomials.stein_general` takes
`hderiv`, `hb`, `hb'` with a common `C` and `k`, and so does this. -/
theorem sobolevWeakPi_of_differentiable {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (i : Fin n) (x), |fderiv ℝ f x (Pi.single i (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    SobolevWeakPi n f (fun i x => fderiv ℝ f x (Pi.single i (1 : ℝ))) :=
  ⟨memLp_of_polyGrowth hf.continuous.aestronglyMeasurable hb,
    fun i => memLp_of_polyGrowth (measurable_partial f i).aestronglyMeasurable (hb' i),
    fun i _ψ hψ hcψ => integral_mul_partial_of_differentiable hf i (hb' i) hψ hcψ⟩

/-- The same, on the Hermite-tested class. -/
theorem steinPairPi_of_differentiable {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (i : Fin n) (x), |fderiv ℝ f x (Pi.single i (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    SteinPairPi n f (fun i x => fderiv ℝ f x (Pi.single i (1 : ℝ))) :=
  steinPairPi_of_sobolevWeakPi n (sobolevWeakPi_of_differentiable hf hb hb')

/-- **THE n-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY FOR A DIFFERENTIABLE FUNCTION.**
`Var_γⁿ(f) ≤ ∑ᵢ ∫ (∂ᵢf)² dγⁿ`, with **no continuity of the gradient anywhere in the hypotheses** —
the n-dimensional statement the 1-d chain has had since `PoincareBeyondPolynomials`. -/
theorem poincare_differentiable {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (i : Fin n) (x), |fderiv ℝ f x (Pi.single i (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      ≤ ∑ i : Fin n, ∫ x, fderiv ℝ f x (Pi.single i (1 : ℝ))
          * fderiv ℝ f x (Pi.single i (1 : ℝ)) ∂gaussPi n :=
  poincare_steinPi n (steinPairPi_of_differentiable hf hb hb')

/-! ## 4. A member the criterion reaches and `SteinGeneralPi`'s does not

`ERRATUM 48`: when a unit's contribution is "this makes X possible", the check is to attempt X.
Here X is a member of the class that the `C¹` criterion cannot deliver, and `DifferentiableNotC1`
was built for exactly this. -/

/-- `x ↦ wig xᵢ` — the `x²sin(1/x)` witness read off one coordinate. -/
noncomputable def wigCoord (i : Fin n) : (Fin n → ℝ) → ℝ := fun x => DifferentiableNotC1.wig (x i)

theorem hasFDerivAt_wigCoord (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (wigCoord i)
      (DifferentiableNotC1.wig' (x i) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have hproj : HasFDerivAt (fun y : Fin n → ℝ => y i)
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact (DifferentiableNotC1.hasDerivAt_wig (x i)).comp_hasFDerivAt x hproj

theorem differentiable_wigCoord (i : Fin n) : Differentiable ℝ (wigCoord i) :=
  fun x => (hasFDerivAt_wigCoord i x).differentiableAt

theorem fderiv_wigCoord (i j : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (wigCoord i) x (Pi.single j (1 : ℝ))
      = DifferentiableNotC1.wig' (x i) * ((Pi.single j (1 : ℝ) : Fin n → ℝ) i) := by
  rw [(hasFDerivAt_wigCoord i x).fderiv]
  simp

theorem wigCoord_bound (i : Fin n) (x : Fin n → ℝ) :
    |wigCoord i x| ≤ 2 * (1 + ‖x‖ ^ 2) ^ 1 := by
  have h1 := DifferentiableNotC1.wig_bound (x i)
  have h2 := sq_apply_le x i
  simp only [pow_one] at h1 ⊢
  simp only [wigCoord]
  nlinarith [sq_nonneg (x i), norm_nonneg x]

theorem fderiv_wigCoord_bound (i j : Fin n) (x : Fin n → ℝ) :
    |fderiv ℝ (wigCoord i) x (Pi.single j (1 : ℝ))| ≤ 2 * (1 + ‖x‖ ^ 2) ^ 1 := by
  have h2 := sq_apply_le x i
  have hw := DifferentiableNotC1.wig'_bound (x i)
  simp only [pow_one] at hw ⊢
  rw [fderiv_wigCoord, abs_mul]
  have hs : |(Pi.single j (1 : ℝ) : Fin n → ℝ) i| ≤ 1 := by
    rw [Pi.single_apply]
    split <;> simp
  nlinarith [abs_nonneg (DifferentiableNotC1.wig' (x i)),
    abs_nonneg ((Pi.single j (1 : ℝ) : Fin n → ℝ) i), sq_nonneg (x i), norm_nonneg x]

/-- **AND IT IS NOT `ContDiff ℝ 1`**, so `SteinGeneralPi`'s criterion does not apply to it.
Restricting to the `i`-th axis returns `wig` itself. -/
theorem not_contDiff_wigCoord (i : Fin n) : ¬ ContDiff ℝ 1 (wigCoord i) := by
  intro h
  have hline : ContDiff ℝ 1 (fun t : ℝ => (Pi.single i t : Fin n → ℝ)) := by
    have := (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i).contDiff (n := 1)
    exact this
  have hcomp := h.comp hline
  have heq : (fun t : ℝ => wigCoord i (Pi.single i t)) = DifferentiableNotC1.wig := by
    funext t
    simp [wigCoord]
  rw [Function.comp_def, heq] at hcomp
  exact DifferentiableNotC1.not_contDiff_wig hcomp

/-- **THE INEQUALITY, ON A FUNCTION THE `C¹` CRITERION CANNOT REACH.** -/
theorem poincare_wigCoord (i : Fin n) :
    (∫ x, wigCoord i x * wigCoord i x ∂gaussPi n) - (∫ x, wigCoord i x ∂gaussPi n) ^ 2
      ≤ ∑ j : Fin n, ∫ x, fderiv ℝ (wigCoord i) x (Pi.single j (1 : ℝ))
          * fderiv ℝ (wigCoord i) x (Pi.single j (1 : ℝ)) ∂gaussPi n :=
  poincare_differentiable (differentiable_wigCoord i) (wigCoord_bound i)
    (fun j x => fderiv_wigCoord_bound i j x)

/-- **THE SEPARATION, STATED IN THE ONE DIRECTION IT IS PROVED.**

There is a function in the Stein class, reached by this file's criterion, which is differentiable
of polynomial growth and **not** `ContDiff ℝ 1` — so no `C¹` hypothesis can deliver it.

This does **not** say the two criteria are ordered. `SteinGeneralPi`'s takes bare `MemLp` clauses
and no growth bound, so it reaches `C¹` functions of super-polynomial growth that stay `L²`, which
this one excludes outright. The claim is one containment failing, not a comparison. -/
theorem criterion_strictly_weaker_hypotheses (i : Fin n) :
    Differentiable ℝ (wigCoord i)
      ∧ (∀ x, |wigCoord i x| ≤ 2 * (1 + ‖x‖ ^ 2) ^ 1)
      ∧ SteinPairPi n (wigCoord i)
          (fun j x => fderiv ℝ (wigCoord i) x (Pi.single j (1 : ℝ)))
      ∧ ¬ ContDiff ℝ 1 (wigCoord i) :=
  ⟨differentiable_wigCoord i, wigCoord_bound i,
    steinPairPi_of_differentiable (differentiable_wigCoord i) (wigCoord_bound i)
      (fun j x => fderiv_wigCoord_bound i j x),
    not_contDiff_wigCoord i⟩

end SteinDifferentiablePi
