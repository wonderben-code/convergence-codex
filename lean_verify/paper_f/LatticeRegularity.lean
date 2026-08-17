import LatticeGeneratingFunctional
import LatticeUniformPoincare

/-!
# The generating functional's bound, uniform in the graph

`UNLOCK_WATCHLIST`'s item *"the OS axioms other than OS2, for the lattice field"* records that the
estate has reflection positivity at three levels and **"nothing whatever about OS0, OS1, OS3 or
OS4 for `gaussianField`"**. One entry has been made against it since: `FieldAutInvariance` supplied
the finite-volume shadow of OS3, under a heading insisting in capitals that it **is not OS3 and must
not be recorded as OS3**, because OS3 is invariance under the Euclidean group and a finite graph has
an automorphism group instead.

This file makes the corresponding entry for OS0, under the same discipline.

## What OS0 is about, and what is here

`LatticeGeneratingFunctional.generatingFunctional` computes

```
Z(f) := ∫ exp⟪f,ω⟫ dμ  =  exp(½ · f ⬝ᵥ G *ᵥ f)
```

and its docstring says this is "the statement OS0 is about". **An equality is not a bound**, and OS0
in its usual form is a *growth estimate* on `Z` in the test function. Turning the equality into an
estimate is one step, and the step is worth taking because of **which** estimate comes out:

`LatticeUniformPoincare.quadForm_green_le` bounds `f ⬝ᵥ G *ᵥ f` by `m⁻²·∑ⱼfⱼ²` with a constant that
**names no graph**. So

```
Z(f)  ≤  exp( ‖f‖² / (2m²) )
```

holds at every finite vertex type, every graph and every side length, with a constant depending on
the mass alone. That is the shape a family of finite volumes needs, and it is the reason this is a
statement and not a remark.

## What is proved

* **`generatingFunctional_le`** — the displayed bound, constant `1/(2m²)`, no graph;
* **`one_le_generatingFunctional`** — and `Z(f) ≥ 1`, because the quadratic form is positive
  semidefinite. The functional is pinned between an absolute constant and a graph-free one;
* **`log_generatingFunctional_le`** — the same in the additive form the cluster expansion uses;
* **`generatingFunctional_ray_eq`**, **`contDiff_generatingFunctional_ray`** — along a ray the
  functional is literally `t ↦ exp(c·t²/2)`, hence `C^∞` in `t`, with `c` computed rather than
  estimated.

## What this is NOT — and the OS3 precedent is the reason this section exists

**THIS IS NOT OS0 AND MUST NOT BE RECORDED AS OS0.** OS0 is a statement about a continuum field
theory: the generating functional on **Schwartz test functions**, bounded in a norm built from
`‖f‖_{L¹}` and `‖f‖_{L^p}`, with the bound part of a package that yields a distribution-valued
measure. Every word of that is a continuum word. What is here is a finite-dimensional Gaussian
integral over a finite graph, bounded in the Euclidean norm of a finite vector.

**The uniformity is the constant's, and does not by itself give a limit.** `1/(2m²)` does not grow
with the box — and a bound whose constant does not blow up is an **ingredient** of a tightness
argument, not one. **`OS4` does not move**: no sequence of measures, no limit and no compactness
appears here, and `UNLOCK_WATCHLIST`'s infinite-volume item is untouched — in particular its clause
(i), that the torus covariances are not compatible, which no bound repairs.

**Nothing here is a new estimate.** Both halves existed: the equality since
`LatticeGeneratingFunctional`, the quadratic-form bound since `LatticeUniformPoincare`. This is the
composition, and it earns a name only because the watchlist item says the estate has nothing about
OS0 and that sentence should stop being true in a way that is precisely labelled.

**No spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeRegularity

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeGeneratingFunctional LatticeUniformPoincare
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The quadratic form in the norm -/

omit [DecidableEq V] in
/-- `∑ⱼ fⱼ² = ‖f‖²` on `EuclideanSpace`, which is what lets `quadForm_green_le`'s coordinate sum be
read as a norm and the bound stated basis-free. -/
theorem sum_sq_eq_norm_sq (f : EuclideanSpace ℝ V) :
    ∑ j, (WithLp.ofLp f) j ^ 2 = ‖f‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- **THE QUADRATIC FORM, BOUNDED WITH NO GRAPH IN THE CONSTANT.** -/
theorem quadForm_green_le_norm (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    f ⬝ᵥ green G m *ᵥ f ≤ (m ^ 2)⁻¹ * ‖f‖ ^ 2 := by
  have h := quadForm_green_le (K := G) hm (WithLp.ofLp f)
  rwa [sum_sq_eq_norm_sq] at h

/-! ## 2. The bound on the generating functional -/

/-- **THE GENERATING FUNCTIONAL IS BOUNDED, UNIFORMLY IN THE GRAPH.**

```
∫ exp⟪f,ω⟫ dμ  ≤  exp( ‖f‖² / (2m²) )
```

at every finite vertex type, every graph and every side length. The constant is `1/(2m²)` and
**mentions no graph**; only the mass appears. -/
theorem generatingFunctional_le (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ≤ Real.exp (‖f‖ ^ 2 / (2 * m ^ 2)) := by
  rw [generatingFunctional hm f]
  refine Real.exp_le_exp.mpr ?_
  have h := quadForm_green_le_norm (G := G) hm f
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hrw : (m ^ 2)⁻¹ * ‖f‖ ^ 2 / 2 = ‖f‖ ^ 2 / (2 * m ^ 2) := by
    field_simp
  calc (f ⬝ᵥ green G m *ᵥ f) / 2 ≤ ((m ^ 2)⁻¹ * ‖f‖ ^ 2) / 2 := by linarith
    _ = ‖f‖ ^ 2 / (2 * m ^ 2) := hrw

/-- **AND IT IS AT LEAST `1`.** The quadratic form is positive semidefinite, so the exponent is
nonnegative. Together with `generatingFunctional_le` the functional is pinned between an absolute
constant and a graph-free one. -/
theorem one_le_generatingFunctional (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    1 ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) := by
  rw [generatingFunctional hm f]
  refine Real.one_le_exp ?_
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  have hnn : (0 : ℝ) ≤ f ⬝ᵥ green G m *ᵥ f := by
    simpa using hps.dotProduct_mulVec_nonneg (WithLp.ofLp f)
  positivity

/-- **THE ADDITIVE FORM.** `log Z(f) ≤ ‖f‖²/(2m²)`, which is the shape the cluster expansion in
`GreenClustering` states its results in. -/
theorem log_generatingFunctional_le (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Real.log (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m)) ≤ ‖f‖ ^ 2 / (2 * m ^ 2) := by
  rw [generatingFunctional hm f, Real.log_exp]
  have h := quadForm_green_le_norm (G := G) hm f
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hrw : (m ^ 2)⁻¹ * ‖f‖ ^ 2 / 2 = ‖f‖ ^ 2 / (2 * m ^ 2) := by
    field_simp
  calc (f ⬝ᵥ green G m *ᵥ f) / 2 ≤ ((m ^ 2)⁻¹ * ‖f‖ ^ 2) / 2 := by linarith
    _ = ‖f‖ ^ 2 / (2 * m ^ 2) := hrw

/-! ## 3. Along a ray the functional is an explicit Gaussian in `t` -/

/-- Along a ray the functional **is** `t ↦ exp(c·t²/2)`, with `c = f ⬝ᵥ G *ᵥ f` computed rather than
estimated — a restatement of `generatingFunctional_smul` as an equality of functions, which is what
a smoothness statement needs. -/
theorem generatingFunctional_ray_eq (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    (fun t : ℝ => ∫ ω, Real.exp (t * ⟪f, ω⟫) ∂(gaussianField G m))
      = fun t : ℝ => Real.exp ((f ⬝ᵥ green G m *ᵥ f) * t ^ 2 / 2) :=
  funext fun t => generatingFunctional_smul hm f t

/-- **AND SO IT IS `C^∞` IN THE RAY PARAMETER.** No differentiation under the integral sign is
needed anywhere: the integral has been evaluated, and what is left is a polynomial inside `exp`. -/
theorem contDiff_generatingFunctional_ray (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => ∫ ω, Real.exp (t * ⟪f, ω⟫) ∂(gaussianField G m) := by
  rw [generatingFunctional_ray_eq hm f]
  exact Real.contDiff_exp.comp (by fun_prop)

end LatticeRegularity
