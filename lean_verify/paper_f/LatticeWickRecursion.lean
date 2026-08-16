import LatticeMomentsGeneral
import LatticeSteinIdentity

/-!
# Wick's recursion for the lattice field: the polynomial observable

`LatticeSteinIdentity` proved Gaussian integration by parts against the **exponential** observable,

```
∫ ⟪a,ω⟫·exp⟪f,ω⟫ dμ = ⟨a,Gf⟩·exp(½⟨f,Gf⟩)
```

and said so in its own summary, which the `UNLOCK_WATCHLIST` sub-trigger quotes:

> *"**It is the exponential observable, not the polynomial one.** … getting there from the
> exponential case means differentiating again — once per factor. That is not done here, so **the
> sub-trigger does not close**; what changes is that its first leg exists and the remaining step is
> a second differentiation rather than a missing identity."*

**This is that second differentiation**, and it is done in one step rather than `n` of them,
because the differentiation is taken in the *test function* rather than in a scalar multiplying it.

## The route, derived rather than estimated (`ERRATUM 181`)

Differentiating the exponential identity `n` times in a scalar `t` at `f ↦ tf` would need the
`iteratedDeriv` machinery again, once per factor. It is not necessary. Set

```
ψ(ε) = ∫ ⟪f + ε·a, ω⟫^(n+2) dμ
```

and read it two ways:

* **as an integral**, `ψ'(0) = (n+2)·∫ ⟪a,ω⟫·⟪f,ω⟫^(n+1) dμ`, by differentiating under the
  integral sign — the *only* analytic step in the file, and the same lemma
  `LatticeSteinIdentity` used;
* **as a closed form**, because `LatticeMomentsGeneral` already knows every moment of a single
  smeared field: `ψ(ε) = c_{n+2}·q(ε)^{(n+2)/2}` with `q(ε) = ⟨f,Gf⟩ + 2ε⟨f,Ga⟩ + ε²⟨a,Ga⟩` the
  variance along the ray (`LatticeSteinIdentity.linVar_add_smul`), so `ψ'(0)` is the chain rule on
  a *polynomial*.

Equating the two and cancelling `n+2` is the theorem. **The whole of the `n`-fold differentiation
is absorbed by the fact that the moments of `⟪g,·⟫` are already known at every order** — which is
what `LatticeMomentsGeneral` bought and what its own summary did not notice it had bought.

## What is proved

* `abs_pow_le_one_add_even`, `abs_mul_pow_le`, `add_abs_pow_le` — the domination
  `|y·(x+sy)^n| ≤ 2^n·(2 + x^{2n+2} + y^{2n+2})` for `|s| ≤ 1`, whose two halves are `add_pow_le`
  and `|x|^k ≤ 1 + x^{2k}`. **Polynomial rather than exponential**, so `integrable_pow_pair`
  suffices where `LatticeSteinIdentity` needed `integrable_exp_inner`;
* `wickCoeff`, `wickCoeff_even`, `wickCoeff_odd`, **`moment_eq_wickCoeff`** — the two branches of
  `LatticeMomentsGeneral` (`moment_odd`, `moment_even`) merged into **one unconditional formula**
  `∫ ⟪f,ω⟫^k = c_k·(fᵀGf)^{k/2}`, valid at every `k` because `c_k = 0` on the odds. This is what
  removes the parity case split from everything downstream;
* `doubleFactorial_step`, `wickCoeff_step` — `c_{k+2}·((k+2)/2)·2 = (k+2)(k+1)·c_k`, the one
  arithmetic fact the cancellation needs;
* `hasDerivAt_moment_ray`, `hasDerivAt_moment_closed` — the two readings of `ψ'(0)`;
* **`wick_recursion`** — `∫ ⟪a,ω⟫·⟪f,ω⟫^(n+1) = (n+1)·⟨f,Ga⟩·∫ ⟪f,ω⟫^n`, and
  **`wick_recursion_closed`**, the same with the right-hand integral evaluated;
* `wick_recursion_zero` — the case `n = 0`, which is `LatticeIsserlisSmeared.smeared_twoPoint`
  recovered from the recursion, and `wick_recursion_two`, `∫ ⟪a,ω⟫⟪f,ω⟫³ = 3⟨f,Ga⟩⟨f,Gf⟩`;
* `moment_four_of_recursion` — **the cross-check**: at `a = f` and `n = 2` the recursion says
  `∫⟪f,ω⟫⁴ = 3(fᵀGf)²`. This is a **deliberate same-statement duplicate** — the shape
  `LatticeIsserlisSmeared.isserlis_sq_sq_of_smeared` already uses — and it is the **third** copy of
  that statement in `paper_f` (`LatticeMoments.moment_four`,
  `LatticeMomentsGeneral.moment_four_of_general`), which is declared here rather than left for a
  later `grep`. It is **not** an independent derivation: all three routes go through
  `iteratedDeriv_expQuad_even`. What it tests is this file's own two new ingredients, the
  differentiation under the integral and the double-factorial step, against a number already
  known.

## What this is NOT

**It is one linear factor against a power of ONE test function**, `∫ ⟪a,ω⟫·⟪f,ω⟫^n`, not
`∫ ⟪a,ω⟫·⟪f₁,ω⟫⋯⟪f_n,ω⟫`. The general product is reachable from this by polarising the power in
the `fᵢ`, exactly as `LatticeIsserlisFour` polarised at order four — and that polarisation is
**not carried out here** and, per `ERRATUM 181`, **is not costed here either**.

**And the full Wick expansion is still not the closed sum over pairings**, which needs the index
type `LatticeMomentsGeneral`'s summary records that Mathlib does not have. What this supplies is
the recursion's inductive step at a single test function. **No published tag moves.**
-/

namespace LatticeWickRecursion

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeMomentsGeneral LatticeSteinIdentity

/-! ## 1. The domination, which is polynomial rather than exponential -/

/-- `|x|^k ≤ 1 + x^{2k}`: below one the left side is at most one, above one it is at most the
even power. The `1` is what makes the bound work at `|x| ≤ 1` without a case in the caller. -/
theorem abs_pow_le_one_add_even (x : ℝ) (k : ℕ) : |x| ^ k ≤ 1 + x ^ (2 * k) := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    nlinarith [even_two_mul k |>.pow_nonneg x]
  · have h1 : |x| ^ k ≤ |x| ^ (2 * k) := pow_le_pow_right₀ h.le (by omega)
    have h2 : |x| ^ (2 * k) = x ^ (2 * k) := by
      rw [← abs_pow, abs_of_nonneg (even_two_mul k |>.pow_nonneg x)]
    linarith [h1, h2.le, h2.ge]

/-- The pointwise derivative bound, before integrability: for `|s| ≤ 1` the factor `s` cannot
enlarge `|y|`, so the whole product sits under `(|x|+|y|)^{n+1}`. -/
theorem abs_mul_pow_le (x y s : ℝ) (hs : |s| ≤ 1) (n : ℕ) :
    |y * (x + s * y) ^ n| ≤ (|x| + |y|) ^ (n + 1) := by
  rw [abs_mul, abs_pow]
  have hxy : |x + s * y| ≤ |x| + |y| := by
    refine (abs_add_le _ _).trans ?_
    have hsy : |s * y| ≤ |y| := by
      rw [abs_mul]
      nlinarith [abs_nonneg y, abs_nonneg s]
    linarith
  calc |y| * |x + s * y| ^ n ≤ (|x| + |y|) * (|x| + |y|) ^ n := by
        refine mul_le_mul (by linarith [abs_nonneg x]) ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (abs_nonneg _) hxy n
    _ = (|x| + |y|) ^ (n + 1) := by ring

/-- **AND THE INTEGRABLE MAJORANT.** `add_pow_le` splits the binomial, `abs_pow_le_one_add_even`
turns each odd-looking power into an even one, and every even power of a smeared field is
integrable by `LatticeIsserlis.integrable_pow_pair`. -/
theorem add_abs_pow_le (x y : ℝ) (n : ℕ) :
    (|x| + |y|) ^ (n + 1)
      ≤ 2 ^ n * (2 + x ^ (2 * (n + 1)) + y ^ (2 * (n + 1))) := by
  have hsplit : (|x| + |y|) ^ (n + 1)
      ≤ 2 ^ (n + 1 - 1) * (|x| ^ (n + 1) + |y| ^ (n + 1)) :=
    add_pow_le (abs_nonneg x) (abs_nonneg y) (n + 1)
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hsplit
  have hx := abs_pow_le_one_add_even x (n + 1)
  have hy := abs_pow_le_one_add_even y (n + 1)
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  nlinarith [hsplit, hx, hy, h2]

/-! ## 2. Integrability of the majorant -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- Three integrable pieces: a constant, and two even powers of smeared fields. -/
theorem integrable_wick_bound (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (n : ℕ) :
    Integrable (fun ω => ((n : ℝ) + 2)
        * (2 ^ (n + 1) * (2 + (inner ℝ f ω : ℝ) ^ (2 * (n + 2))
          + (inner ℝ a ω : ℝ) ^ (2 * (n + 2))))) (gaussianField G m) := by
  have hf : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) ^ (2 * (n + 2)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm f _
  have ha : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ a ω : ℝ) ^ (2 * (n + 2)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm a _
  have hc : Integrable (fun _ : EuclideanSpace ℝ V => (2 : ℝ)) (gaussianField G m) :=
    integrable_const 2
  exact (((hc.add hf).add ha).const_mul _).const_mul _

/-! ## 3. The moments merged into one formula

`moment_odd` and `moment_even` are two theorems with two shapes; every use downstream then has to
carry a parity case. **One coefficient that vanishes on the odds removes the case entirely**, and
the natural-number division `k/2` is exactly the right exponent in both branches. -/

/-- `(k−1)‼` on the evens and `0` on the odds. -/
def wickCoeff (k : ℕ) : ℝ := if k % 2 = 0 then ((k - 1)‼ : ℝ) else 0

@[simp] theorem wickCoeff_even (j : ℕ) : wickCoeff (2 * j) = ((2 * j - 1)‼ : ℝ) := by
  have h : 2 * j % 2 = 0 := by omega
  simp [wickCoeff, h]

@[simp] theorem wickCoeff_odd (j : ℕ) : wickCoeff (2 * j + 1) = 0 := by
  simp [wickCoeff]

/-- **EVERY MOMENT, WITH NO PARITY HYPOTHESIS.** `moment_even` and `moment_odd` are the two
branches; `wickCoeff` is what lets them be written as one equation. -/
theorem moment_eq_wickCoeff (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)
      = wickCoeff k * (linVar G m f) ^ (k / 2) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have h2 : j + j = 2 * j := by omega
    have hd : 2 * j / 2 = j := by omega
    rw [h2, moment_even hm f j, wickCoeff_even, hd]
  · subst hj
    rw [moment_odd hm f j, wickCoeff_odd]
    ring

/-- The double-factorial recursion in the index shape the cancellation produces. -/
theorem doubleFactorial_step (j : ℕ) : (2 * j + 1)‼ = (2 * j + 1) * (2 * j - 1)‼ := by
  match j with
  | 0 => decide
  | (i + 1) =>
      have h1 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
      have h3 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
      rw [h1, h3, Nat.doubleFactorial_add_two]

/-- **THE ONE ARITHMETIC FACT.** `c_{k+2}·((k+2)/2)·2 = (k+2)(k+1)·c_k`, which on the evens is the
double-factorial recursion and on the odds is `0 = 0`. Stated at an abstract `q` so that the
exponents `(k+2)/2 − 1` and `k/2` have to be shown equal, which is where truncated division earns
its keep. -/
theorem wickCoeff_step (k : ℕ) (q : ℝ) :
    wickCoeff (k + 2) * (((k + 2) / 2 : ℕ) : ℝ) * q ^ ((k + 2) / 2 - 1) * 2
      = ((k : ℝ) + 2) * ((k : ℝ) + 1) * (wickCoeff k * q ^ (k / 2)) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have hjj : j + j = 2 * j := by omega
    rw [hjj]
    have hidx : 2 * j + 2 = 2 * (j + 1) := by ring
    have hd1 : 2 * (j + 1) / 2 = j + 1 := by omega
    have hd2 : 2 * j / 2 = j := by omega
    have hsub : j + 1 - 1 = j := by omega
    rw [hidx, wickCoeff_even, wickCoeff_even, hd1, hd2, hsub]
    have hstep : (2 * (j + 1) - 1)‼ = (2 * j + 1) * (2 * j - 1)‼ := by
      have h : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [h, doubleFactorial_step]
    rw [hstep]
    push_cast
    ring
  · subst hj
    have hidx : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    rw [hidx, wickCoeff_odd, wickCoeff_odd]
    ring

/-! ## 4. The two readings of `ψ'(0)` -/

/-- **THE INTEGRAL READING**, by differentiation under the integral sign with the majorant of §1.
This is the only analytic step in the file. -/
theorem hasDerivAt_moment_ray (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (n : ℕ) :
    HasDerivAt (fun s : ℝ => ∫ ω, ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ (n + 2)
        ∂(gaussianField G m))
      (((n : ℝ) + 2)
        * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ (n + 2) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => ((n : ℝ) + 2) * ((inner ℝ a ω : ℝ)
      * ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ (n + 1)) with hF'
  have hcont : ∀ s : ℝ, Continuous (F s) := by
    intro s
    exact ((continuous_pair f).add (continuous_const.mul (continuous_pair a))).pow _
  have hcont' : ∀ s : ℝ, Continuous (F' s) := by
    intro s
    exact continuous_const.mul ((continuous_pair a).mul
      (((continuous_pair f).add (continuous_const.mul (continuous_pair a))).pow _))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (s : ℝ), HasDerivAt (F · ω) (F' s ω) s := by
    intro ω s
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ a ω : ℝ)) (inner ℝ a ω : ℝ) s := by
      simpa using ((hasDerivAt_id s).mul_const (inner ℝ a ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := hlin.pow (n + 2)
    simp only [hF, hF']
    convert hp using 1
    push_cast
    ring
  have hint0 : Integrable (F 0) μ := by
    refine (integrable_pow_pair (G := G) hm f (n + 2)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp [hF]
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω => ((n : ℝ) + 2)
      * (2 ^ (n + 1) * (2 + (inner ℝ f ω : ℝ) ^ (2 * (n + 2))
        + (inner ℝ a ω : ℝ) ^ (2 * (n + 2)))))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    hint0
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω s hsm => by
      have hs : |s| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hsm)
      have h1 := abs_mul_pow_le (inner ℝ f ω : ℝ) (inner ℝ a ω : ℝ) s hs (n + 1)
      have h2 := add_abs_pow_le (inner ℝ f ω : ℝ) (inner ℝ a ω : ℝ) (n + 1)
      have hn2 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
      have hidx : 2 * (n + 1 + 1) = 2 * (n + 2) := by ring
      rw [hidx] at h2
      calc ‖F' s ω‖ = ((n : ℝ) + 2) * |(inner ℝ a ω : ℝ)
              * ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ (n + 1)| := by
            simp only [hF', Real.norm_eq_abs]
            rw [abs_mul, abs_of_nonneg hn2]
        _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) hn2)
    (integrable_wick_bound hm f a n)
    (Filter.Eventually.of_forall fun ω s _ => hderiv ω s)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ((n : ℝ) + 2) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂μ := by
    simp only [hF']
    rw [integral_const_mul]
    simp
  rw [← hval]
  simpa [hF] using hres.2

/-- **THE CLOSED-FORM READING.** `ψ(ε) = c_{n+2}·q(ε)^{(n+2)/2}` with `q` the quadratic
`linVar_add_smul` computes, so the derivative is the chain rule on a polynomial — no analysis. -/
theorem hasDerivAt_moment_closed (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (k : ℕ) :
    HasDerivAt (fun s : ℝ => ∫ ω, ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ k
        ∂(gaussianField G m))
      (wickCoeff k * ((k / 2 : ℕ) : ℝ) * (linVar G m f) ^ (k / 2 - 1)
        * (2 * dotG G m f a)) 0 := by
  have hfun : (fun s : ℝ => ∫ ω, ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ)) ^ k
      ∂(gaussianField G m))
      = fun s : ℝ => wickCoeff k
          * (linVar G m f + 2 * s * dotG G m f a + s ^ 2 * linVar G m a) ^ (k / 2) := by
    funext s
    have h1 : ∀ ω : EuclideanSpace ℝ V, ((inner ℝ f ω : ℝ) + s * (inner ℝ a ω : ℝ))
        = (inner ℝ (f + s • a) ω : ℝ) := fun ω => (inner_add_smul f a s ω).symm
    simp only [h1]
    rw [moment_eq_wickCoeff hm (f + s • a) k, linVar_add_smul hm]
  rw [hfun]
  have hq : HasDerivAt
      (fun s : ℝ => linVar G m f + 2 * s * dotG G m f a + s ^ 2 * linVar G m a)
      (2 * dotG G m f a) 0 := by
    have ha : HasDerivAt (fun s : ℝ => 2 * s * dotG G m f a) (2 * dotG G m f a) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (dotG G m f a))
    have hb : HasDerivAt (fun s : ℝ => s ^ 2 * linVar G m a) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (linVar G m a))
    simpa using (ha.const_add (linVar G m f)).add hb
  have hres := (hq.pow (k / 2)).const_mul (wickCoeff k)
  convert hres using 1
  norm_num
  ring

/-! ## 5. The recursion -/

/-- **WICK'S RECURSION AT ONE TEST FUNCTION.**

`∫ ⟪a,ω⟫·⟪f,ω⟫^(n+1) dμ = (n+1)·⟨f,Ga⟩·∫ ⟪f,ω⟫^n dμ`.

Each of the `n+1` copies of `⟪f,ω⟫` gets contracted with `⟪a,ω⟫` in turn, and every contraction
contributes the same propagator `⟨f,Ga⟩` — which is why the combinatorial factor is a plain
`n+1` rather than a sum. -/
theorem wick_recursion (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (n : ℕ) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m)
      = ((n : ℝ) + 1) * dotG G m f a
        * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
  have h1 := hasDerivAt_moment_ray (G := G) hm f a n
  have h2 := hasDerivAt_moment_closed (G := G) hm f a (n + 2)
  have heq := h1.unique h2
  have hstep := wickCoeff_step n (linVar G m f)
  rw [moment_eq_wickCoeff hm f n]
  have hkey : ((n : ℝ) + 2)
      * (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m))
      = ((n : ℝ) + 2) * (((n : ℝ) + 1) * dotG G m f a
          * (wickCoeff n * (linVar G m f) ^ (n / 2))) := by
    rw [heq]
    calc wickCoeff (n + 2) * (((n + 2) / 2 : ℕ) : ℝ) * (linVar G m f) ^ ((n + 2) / 2 - 1)
            * (2 * dotG G m f a)
        = (wickCoeff (n + 2) * (((n + 2) / 2 : ℕ) : ℝ) * (linVar G m f) ^ ((n + 2) / 2 - 1) * 2)
            * dotG G m f a := by ring
      _ = (((n : ℝ) + 2) * ((n : ℝ) + 1) * (wickCoeff n * (linVar G m f) ^ (n / 2)))
            * dotG G m f a := by rw [hstep]
      _ = _ := by ring
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  exact mul_left_cancel₀ hn2 hkey

/-- The same with the surviving integral evaluated: everything on the right is an algebraic
expression in the Green function. -/
theorem wick_recursion_closed (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) (n : ℕ) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m)
      = ((n : ℝ) + 1) * dotG G m f a * (wickCoeff n * (linVar G m f) ^ (n / 2)) := by
  rw [wick_recursion hm f a n, moment_eq_wickCoeff hm f n]

/-! ## 6. The first cases, and the check that two routes give the same number -/

@[simp] theorem wickCoeff_zero : wickCoeff 0 = 1 := by
  simp [wickCoeff, Nat.doubleFactorial]

@[simp] theorem wickCoeff_one : wickCoeff 1 = 0 := by
  simp [wickCoeff]

@[simp] theorem wickCoeff_two : wickCoeff 2 = 1 := by
  simp [wickCoeff, Nat.doubleFactorial]

/-- `n = 0` gives back `LatticeIsserlisSmeared.smeared_twoPoint` — the same statement modulo
`dotG_comm`, so this too is a **declared duplicate** rather than new content. A recursion whose
base case is not the theorem it was built on top of is a different recursion, and
`wick_recursion_zero_eq_smeared` below is the identification written out. -/
theorem wick_recursion_zero (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ∂(gaussianField G m) = dotG G m f a := by
  have h := wick_recursion_closed (G := G) hm f a 0
  simpa using h

/-- And it agrees with `smeared_twoPoint` on the nose, `dotG` being symmetric. -/
theorem wick_recursion_zero_eq_smeared (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = ∫ ω, (inner ℝ f ω : ℝ) * (inner ℝ a ω : ℝ) ∂(gaussianField G m) := by
  rw [wick_recursion_zero hm f a, smeared_twoPoint hm f a]

/-- `∫ ⟪a,ω⟫⟪f,ω⟫³ = 3·⟨f,Ga⟩·(fᵀGf)` — the first case the estate did not already have. -/
theorem wick_recursion_two (hm : m ≠ 0) (f a : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ 3 ∂(gaussianField G m)
      = 3 * dotG G m f a * linVar G m f := by
  have h := wick_recursion (G := G) hm f a 2
  rw [moment_two_of_general hm f] at h
  norm_num at h
  simpa using h

/-- **THE CROSS-CHECK**, and a **declared duplicate statement**: `LatticeMoments.moment_four` and
`LatticeMomentsGeneral.moment_four_of_general` already carry this exact statement, so this is the
**third** declaration of it in `paper_f`. That is deliberate and is recorded here rather than left
for a later `grep` (`ERRATUM 176`).

**What the check does and does not buy.** It is *not* an independent derivation: this file's route
runs through `moment_eq_wickCoeff → moment_even → iteratedDeriv_expQuad_even`, which is the very
machinery the other two use. What it exercises that they do not is the file's **two new
ingredients** — differentiation under the integral sign (`hasDerivAt_moment_ray`) and the
double-factorial arithmetic (`wickCoeff_step`). An error in either would move this number, and
the number is known. That is the whole of the claim. -/
theorem moment_four_of_recursion (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 4 ∂(gaussianField G m) = 3 * (linVar G m f) ^ 2 := by
  have h := wick_recursion_two (G := G) hm f f
  have hff : dotG G m f f = linVar G m f := (linVar_eq_dotG f).symm
  rw [hff] at h
  have hpow : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ f ω : ℝ) * (inner ℝ f ω : ℝ) ^ 3 = (inner ℝ f ω : ℝ) ^ 4 := by
    intro ω; ring
  simp only [hpow] at h
  rw [h]
  ring

end LatticeWickRecursion
