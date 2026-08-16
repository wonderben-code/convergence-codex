import LatticeIsserlisFour
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Gaussian integration by parts for the lattice field

`LatticeMomentsGeneral`'s addendum re-pointed the `UNLOCK_WATCHLIST` sub-trigger from *"build a
pairings type"* to this:

> *"someone wants Gaussian integration by parts for `gaussianField G m`. … The estate has Stein/IBP
> machinery only for the product Gaussian (`SteinCoefficients`, `HermitePiStein`,
> `SteinGeneralPi`), and `gaussianField G m` is not a product measure."*

**This is that identity, for the exponential observable:**

    ∫ ⟪a,ω⟫ · exp ⟪f,ω⟫ dμ  =  ⟨a, G f⟩ · exp (½ ⟨f, G f⟩)

— the covariance pulls the linear factor out, which is the whole content of Stein's lemma. The
correlated case, not a product measure, and not previously in the estate.

## Why it comes out, and what does the work

`LatticeGeneratingFunctional.generatingFunctional` already gives `∫ exp⟪g,ω⟫ = exp(v(g)/2)` for
**every** test function `g`. Put `g = f + s·a` and differentiate in `s` at `0`: the right-hand side
is an explicit smooth function of `s` and its derivative is immediate, and the left-hand side —
**if** differentiation may pass under the integral — is exactly `∫ ⟪a,ω⟫ exp⟪f,ω⟫`.

So the whole unit is the "if". Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` wants a
single integrable function dominating `∂/∂s` on a neighbourhood of `0`, and

    |y·exp(x + s·y)| ≤ exp(x + 2y) + 2·exp x + exp(x − 2y)   for |s| ≤ 1

does it, using `|y| ≤ eʸ + e⁻ʸ` twice. **Each of those three terms is `exp⟪g,ω⟫` for a test
function `g`** — `f + 2a`, `f`, `f − 2a` — and
`LatticeGeneratingFunctional.integrable_exp_inner` is stated for **every** test function, so all
three are integrable with nothing further to prove. That the estate's integrability lemma was
proved in that generality, rather than for one `f`, is what makes this a short file.

## What is proved

* `abs_le_exp_add_exp_neg`, `deriv_bound` — the pointwise domination;
* `dotG_smul_right`, `dotG_smul_left`, `linVar_smul`, `linVar_add_smul` — the variance along the
  ray `f + s·a`, which is the quadratic `v(f) + 2s⟨a,Gf⟩ + s²v(a)`;
* `integrable_deriv_bound` — the dominating function is integrable;
* `hasDerivAt_gf_ray` — the right-hand side's derivative at `0`;
* `hasDerivAt_integral_ray` — and the left-hand side's, by the parametric-integral lemma;
* **`stein_identity`** — hence the two are equal.
* `stein_identity_self` — at `a = f`, `∫ ⟪f,ω⟫exp⟪f,ω⟫ = v(f)·exp(v(f)/2)`;
* `stein_identity_zero` — and at `f = 0` it degenerates to `∫ ⟪a,ω⟫ = 0`, which
  `LatticeMoments.moment_one` already had. That agreement is the check.

## What this is NOT

**It is the exponential observable, not the polynomial one.** The Wick recursion
`E[X₁⋯X_{2n}] = ∑_j ⟨X₁,X_j⟩·E[∏_{i≠1,j}X_i]` needs `∫ ⟪a,ω⟫·F(ω)` for `F` a **product of smeared
fields**, and getting there from the exponential case means differentiating again — once per factor.
That is not done here, so **the sub-trigger does not close**; what changes is that its first leg
exists and the remaining step is a second differentiation rather than a missing identity.

**And OS4 does not move.** Finite volume throughout. **No published tag moves.**
-/

namespace LatticeSteinIdentity

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The pointwise domination -/

/-- `|y| ≤ eʸ + e⁻ʸ`. Used twice: once on the linear factor, once inside the exponent. -/
theorem abs_le_exp_add_exp_neg (y : ℝ) : |y| ≤ Real.exp y + Real.exp (-y) := by
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have h1 : y ≤ Real.exp y := (Real.add_one_le_exp y).trans' (by linarith)
    have h2 : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
    linarith
  · rw [h]
    have h1 : -y ≤ Real.exp (-y) := (Real.add_one_le_exp (-y)).trans' (by linarith)
    have h2 : (0 : ℝ) < Real.exp y := Real.exp_pos _
    linarith

/-- **THE DOMINATING BOUND.** `|y·exp(x + s·y)| ≤ exp(x+2y) + 2·exp x + exp(x−2y)` whenever
`|s| ≤ 1`, and the right-hand side does not mention `s`. -/
theorem deriv_bound (x y s : ℝ) (hs : |s| ≤ 1) :
    ‖y * Real.exp (x + s * y)‖
      ≤ Real.exp (x + 2 * y) + 2 * Real.exp x + Real.exp (x - 2 * y) := by
  have hsy : s * y ≤ |y| := by
    calc s * y ≤ |s * y| := le_abs_self _
      _ = |s| * |y| := abs_mul s y
      _ ≤ 1 * |y| := by nlinarith [abs_nonneg y, abs_nonneg s]
      _ = |y| := one_mul _
  have hmono : Real.exp (x + s * y) ≤ Real.exp (x + |y|) := Real.exp_le_exp.mpr (by linarith)
  have hy : |y| ≤ Real.exp y + Real.exp (-y) := abs_le_exp_add_exp_neg y
  have habs : ‖y * Real.exp (x + s * y)‖ = |y| * Real.exp (x + s * y) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [habs]
  have hexp : Real.exp (x + |y|) ≤ Real.exp x * (Real.exp y + Real.exp (-y)) := by
    rw [Real.exp_add]
    have hin : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
      rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        [linarith [Real.exp_pos (-y)]; linarith [Real.exp_pos y]]
    nlinarith [Real.exp_pos x, Real.exp_pos y, Real.exp_pos (-y)]
  have hchain : |y| * Real.exp (x + s * y)
      ≤ (Real.exp y + Real.exp (-y)) * (Real.exp x * (Real.exp y + Real.exp (-y))) := by
    apply mul_le_mul hy (hmono.trans hexp) (Real.exp_pos _).le
    linarith [Real.exp_pos y, Real.exp_pos (-y)]
  refine hchain.trans (le_of_eq ?_)
  have e1 : Real.exp (x + 2 * y) = Real.exp x * (Real.exp y * Real.exp y) := by
    rw [show x + 2 * y = x + y + y by ring, Real.exp_add, Real.exp_add]; ring
  have e2 : Real.exp (x - 2 * y) = Real.exp x * ((Real.exp y)⁻¹ * (Real.exp y)⁻¹) := by
    rw [show x - 2 * y = x + -y + -y by ring, Real.exp_add, Real.exp_add, Real.exp_neg]; ring
  have hpos : Real.exp y ≠ 0 := ne_of_gt (Real.exp_pos y)
  rw [e1, e2, Real.exp_neg]
  field_simp
  ring

/-! ## 2. The variance along the ray `f + s·a` -/

theorem dotG_smul_right (f a : EuclideanSpace ℝ V) (s : ℝ) :
    dotG G m f (s • a) = s * dotG G m f a := by
  simp [dotG, Matrix.mulVec_smul, dotProduct_smul]

theorem dotG_smul_left (f a : EuclideanSpace ℝ V) (s : ℝ) :
    dotG G m (s • a) f = s * dotG G m a f := by
  simp [dotG, smul_dotProduct]

theorem linVar_smul (a : EuclideanSpace ℝ V) (s : ℝ) :
    linVar G m (s • a) = s ^ 2 * linVar G m a := by
  rw [linVar_eq_dotG, dotG_smul_left, dotG_smul_right, linVar_eq_dotG]
  ring

/-- **THE VARIANCE ALONG THE RAY IS A QUADRATIC IN `s`**, with the linear coefficient `2⟨a,Gf⟩` —
which is the number Stein's identity produces. -/
theorem linVar_add_smul (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (s : ℝ) :
    linVar G m (f + s • a)
      = linVar G m f + 2 * s * dotG G m f a + s ^ 2 * linVar G m a := by
  rw [linVar_add hm f (s • a), dotG_smul_right, linVar_smul]
  ring

/-! ## 3. Integrability of the dominating function -/

omit [DecidableEq V] in
theorem inner_add_smul (f a : EuclideanSpace ℝ V) (s : ℝ) (ω : EuclideanSpace ℝ V) :
    (inner ℝ (f + s • a) ω : ℝ) = (inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ) := by
  rw [inner_add_left, real_inner_smul_left]

/-- The three terms of the bound are `exp⟪g,ω⟫` at `g = f + 2a`, `f`, `f − 2a`, and
`integrable_exp_inner` is stated for **every** test function. -/
theorem integrable_deriv_bound (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    Integrable
      (fun ω => Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ a ω : ℝ))
        + 2 * Real.exp (inner ℝ f ω : ℝ)
        + Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ a ω : ℝ))) (gaussianField G m) := by
  have hp : Integrable
      (fun ω => Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ a ω : ℝ))) (gaussianField G m) := by
    refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm (f + (2 : ℝ) • a)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp [inner_add_left, real_inner_smul_left]
  have hm0 : Integrable (fun ω => Real.exp (inner ℝ f ω : ℝ)) (gaussianField G m) :=
    LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm f
  have hn : Integrable
      (fun ω => Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ a ω : ℝ))) (gaussianField G m) := by
    refine (LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm (f + (-2 : ℝ) • a)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [inner_add_left, real_inner_smul_left]
    ring_nf
  exact (hp.add (hm0.const_mul 2)).add hn

/-! ## 4. The two derivatives -/

/-- The right-hand side is `exp` of a quadratic; its derivative at `0` is `⟨a,Gf⟩·exp(v(f)/2)`. -/
theorem hasDerivAt_gf_ray (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => Real.exp (linVar G m (f + s • a) / 2))
      (dotG G m f a * Real.exp (linVar G m f / 2)) 0 := by
  have hfun : (fun s : ℝ => Real.exp (linVar G m (f + s • a) / 2))
      = fun s : ℝ => Real.exp ((linVar G m f + 2 * s * dotG G m f a
          + s ^ 2 * linVar G m a) / 2) := by
    funext s
    rw [linVar_add_smul hm]
  rw [hfun]
  have hq : HasDerivAt
      (fun s : ℝ => (linVar G m f + 2 * s * dotG G m f a + s ^ 2 * linVar G m a) / 2)
      (dotG G m f a) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => linVar G m f + 2 * s * dotG G m f a
        + s ^ 2 * linVar G m a) (2 * dotG G m f a) 0 := by
      have ha : HasDerivAt (fun s : ℝ => 2 * s * dotG G m f a) (2 * dotG G m f a) 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (dotG G m f a))
      have hb : HasDerivAt (fun s : ℝ => s ^ 2 * linVar G m a) 0 0 := by
        simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (linVar G m a))
      simpa using (ha.const_add (linVar G m f)).add hb
    simpa using h1.div_const 2
  have hres := hq.exp
  convert hres using 1
  norm_num
  ring

/-- **AND THE LEFT-HAND SIDE'S**, by the parametric-integral lemma with the bound of §1. -/
theorem hasDerivAt_integral_ray (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ))
        ∂(gaussianField G m))
      (∫ ω, (inner ℝ a ω : ℝ) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (inner ℝ a ω : ℝ) * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) with hF'
  have hcont : ∀ s : ℝ, Continuous (F s) := by
    intro s
    exact Real.continuous_exp.comp
      ((continuous_pair f).add (continuous_const.mul (continuous_pair a)))
  have hcont' : ∀ s : ℝ, Continuous (F' s) := by
    intro s
    exact (continuous_pair a).mul (hcont s)
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (s : ℝ), HasDerivAt (F · ω) (F' s ω) s := by
    intro ω s
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ a ω : ℝ)) (inner ℝ a ω : ℝ) s := by
      simpa using ((hasDerivAt_id s).mul_const (inner ℝ a ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    simpa [hF, hF', mul_comm] using hlin.exp
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω =>
      Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ a ω : ℝ))
        + 2 * Real.exp (inner ℝ f ω : ℝ)
        + Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ a ω : ℝ)))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (by simpa [hF] using LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm f)
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω s hsm => by
      have : |s| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hsm)
      simpa [hF'] using deriv_bound (inner ℝ f ω : ℝ) (inner ℝ a ω : ℝ) s this)
    (integrable_deriv_bound hm f a)
    (Filter.Eventually.of_forall fun ω s _ => hderiv ω s)
  simpa [hF, hF'] using hres.2

/-! ## 5. The identity -/

/-- **GAUSSIAN INTEGRATION BY PARTS FOR THE LATTICE FIELD.**

`∫ ⟪a,ω⟫·exp⟪f,ω⟫ dμ = ⟨a,Gf⟩·exp(½⟨f,Gf⟩)` — the covariance pulls the linear factor out.

This is Stein's lemma for a **correlated** Gaussian; the estate's existing Stein machinery
(`SteinCoefficients`, `HermitePiStein`, `SteinGeneralPi`) is for **product** measures and does not
apply to `gaussianField G m`. -/
theorem stein_identity (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = dotG G m f a * Real.exp (linVar G m f / 2) := by
  have hL := hasDerivAt_integral_ray (G := G) hm f a
  have hR := hasDerivAt_gf_ray (G := G) hm f a
  have hsame : (fun s : ℝ => ∫ ω, Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ))
      ∂(gaussianField G m)) = fun s : ℝ => Real.exp (linVar G m (f + s • a) / 2) := by
    funext s
    have h := LatticeGeneratingFunctional.generatingFunctional (G := G) hm (f + s • a)
    rw [show linVar G m (f + s • a)
        = (f + s • a).ofLp ⬝ᵥ green G m *ᵥ (f + s • a).ofLp from rfl, ← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [inner_add_smul])
  rw [hsame] at hL
  exact hL.unique hR

/-- At `a = f`: `∫ ⟪f,ω⟫·exp⟪f,ω⟫ = v(f)·exp(v(f)/2)`. -/
theorem stein_identity_self (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = linVar G m f * Real.exp (linVar G m f / 2) := by
  rw [stein_identity hm f f, linVar_eq_dotG]

/-- **AND AT `f = 0` IT DEGENERATES TO `∫ ⟪a,ω⟫ = 0`**, which `LatticeMoments.moment_one` already
proved by a different route. A new identity that disagreed with an old one at a shared point would
be worth knowing about; this one agrees. -/
theorem stein_identity_zero (hm : m ≠ 0) (a : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) ∂(gaussianField G m) = 0 := by
  have h := stein_identity (G := G) hm 0 a
  have hd : dotG G m (0 : EuclideanSpace ℝ V) a = 0 := by simp [dotG]
  rw [hd, zero_mul] at h
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) h
  simp

end LatticeSteinIdentity
