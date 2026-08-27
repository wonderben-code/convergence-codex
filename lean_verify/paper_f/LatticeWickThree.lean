import LatticeWickTwo

/-!
# Three linear factors against a power: order six at **four** distinct test functions

`LatticeWickTwo` pulled **two** smeared fields out of a Gaussian average against a power of a
third, and reached order six in the pattern `(a, b, f, f, f, f)` — two distinct test functions.
Its closing paragraph named the residue precisely:

> *"The obstruction is no longer 'order six' but **the number of DISTINCT test functions**"*,

and the watchlist clause above it instructs the next person to **derive** the cost of a further
factor rather than read one, `ERRATUM 181` having been a cost written five times without once
being re-derived.

**The cost, derived, and it is the same two readings of one derivative.** Put

```
F(ε) = ∫ ⟪a,ω⟫·⟪b,ω⟫·⟪f + ε·c, ω⟫^(k+1) dμ.
```

*Integral reading:* `F'(0) = (k+1)·∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪f,ω⟫^k`, by the same parametric-integral
lemma the last two units used. *Closed reading:* `wick_two_raw` evaluates `F(ε)` **outright**,
because `dotG` is bilinear and `linVar_add_smul` turns `linVar (f + ε·c)` into a quadratic in `ε`;
so `F(ε)` is an explicit polynomial expression in `ε` and `F'(0)` is one product rule — over three
`ε`-dependent factors this time rather than two. **The previous unit's theorem is what makes this
differentiation cheap**, exactly as it said it would be.

**The one genuinely new ingredient is the majorant, and it is a fourth factor rather than a new
idea.** `LatticeWickTwo` needed `|z|·u ≤ (z²+u²)/2`. Here the integrand carries
`|⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫|·|X|^k` — one absolute value more — so the same AM–GM is applied twice, giving
`|x|·|y|·u ≤ (x⁴ + y⁴ + 2u²)/4`. Every term is an **even** power of a smeared field, hence
integrable, and `abs_add_pow_even_le` absorbs the `ε` inside `X` exactly as it already does.

## What is proved

* `wickCoeff_mul_half` — `c_{k+2}·((k+2)/2)·2 = (k+2)(k+1)·c_k`, **with no `q` power attached.**
  `LatticeWickRecursion.wickCoeff_step` is this identity multiplied by `q^{k/2}`; stripping the
  power off is what lets it be **applied twice**, which is what a second contraction needs and
  what the bundled form cannot do (an equation between two things each carrying `q^{J}` does not
  give an equation between the coefficients);
* `sq_mul_le_sq_add`, `abs_three_mul_le` — AM–GM once and then twice, the second stated with the
  `0 ≤ u` it genuinely needs (unlike `abs_mul_le_sq_add`, where the hypothesis was idle);
* `hasDerivAt_three_ray`, `hasDerivAt_three_closed` — the two readings of `F'(0)`;
* `wick_three_raw` — what comes out before the double factorials are tidied;
* **`wick_three`** — and after, with both integrals restored and no truncated subtraction:

  ```
  ∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪f,ω⟫^(n+3)
    = (n+3)·(⟨b,Ga⟩⟨f,Gc⟩ + ⟨c,Ga⟩⟨f,Gb⟩ + ⟨c,Gb⟩⟨f,Ga⟩)·∫⟪f,ω⟫^(n+2)
      + (n+3)(n+2)(n+1)·⟨f,Ga⟩⟨f,Gb⟩⟨f,Gc⟩·∫⟪f,ω⟫^n
  ```

  Read combinatorially: either two of `a, b, c` contract with each other and the third with one of
  the `n+3` copies of `f`, or all three contract with distinct copies, in `(n+3)(n+2)(n+1)` ways.
  Both counts are visible in the statement;
* **`wick_three_order_six`** — the case `n = 0`:
  `∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪f,ω⟫³ = 3(⟨b,Ga⟩⟨f,Gc⟩+⟨c,Ga⟩⟨f,Gb⟩+⟨c,Gb⟩⟨f,Ga⟩)(fᵀGf) +
  6⟨f,Ga⟩⟨f,Gb⟩⟨f,Gc⟩`. **The estate's first order-six correlation at four distinct test
  functions.** Its `3·3 + 6 = 15 = 5‼` is the pairing count of six objects, and it is the one
  visible check that the coefficients are right;
* **`wick_three_eq_isserlis_four`** — and at the *other* end, `k = 1` collapses the cubic term
  (`k(k−1)(k−2) = 0`) and reproduces `LatticeIsserlisFour.isserlis_four` exactly. That check is
  not a restatement: `isserlis_four` was proved by polarising a fourth moment twice and shares no
  derivative with anything here, so it is an independent test of the whole chain.

## What this is NOT

**It is three arbitrary test functions and a power of a fourth**, not six arbitrary ones. The
watchlist's count moves from three distinct factors to four, and **the wall stays exactly where
that clause puts it**: what is still not derived is where this route stops being writable without
a pairings carrier, since at `k` distinct factors the right-hand side *is* the pairing sum. A
fourth factor does not answer that question and no number is claimed for it here (`ERRATUM 194`).

**And OS4 does not move.** Finite volume throughout. **No published tag moves.**
-/

namespace LatticeWickThree

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeMomentsGeneral LatticeSteinIdentity LatticeWickRecursion LatticeWickTwo

/-! ## 1. The coefficient identity with the power stripped off

`wickCoeff_step` is `wickCoeff_mul_half` multiplied through by `q^{k/2}`. For **one** contraction
that is the convenient form. For **two** it is the wrong one: the second contraction needs the
coefficient identity at a *different* index, and an equation whose two sides each carry `q^{J}`
says nothing about the coefficients alone. -/

/-- **THE ARITHMETIC FACT, WITHOUT THE POWER.** `c_{k+2}·((k+2)/2)·2 = (k+2)(k+1)·c_k`: on the
evens this is the double-factorial recursion, and on the odds it is `0 = 0`. -/
theorem wickCoeff_mul_half (k : ℕ) :
    wickCoeff (k + 2) * (((k + 2) / 2 : ℕ) : ℝ) * 2
      = ((k : ℝ) + 2) * ((k : ℝ) + 1) * wickCoeff k := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have hjj : j + j = 2 * j := by omega
    rw [hjj]
    have hidx : 2 * j + 2 = 2 * (j + 1) := by ring
    have hd1 : 2 * (j + 1) / 2 = j + 1 := by omega
    rw [hidx, wickCoeff_even, wickCoeff_even, hd1]
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

/-- The two truncated divisions that appear once a second contraction is taken:
`(k+4)/2 − 1 = (k+2)/2` and `(k+2)/2 − 1 = k/2`, both by `omega` after a parity split. -/
theorem half_sub_one (k : ℕ) : (k + 2) / 2 - 1 = k / 2 := by omega

/-! ## 2. The majorant: one more factor, hence AM–GM twice -/

/-- AM–GM in the shape the fourth factor forces. No sign hypothesis: `(z²−u)² ≥ 0` is the whole
proof and it is unconditional. -/
theorem sq_mul_le_sq_add (z u : ℝ) : z ^ 2 * u ≤ (z ^ 4 + u ^ 2) / 2 := by
  nlinarith [sq_nonneg (z ^ 2 - u)]

/-- **THE NEW INGREDIENT.** `LatticeWickTwo.abs_mul_le_sq_add` split one absolute value off a
nonnegative quantity; a third linear factor means splitting two, and the result is a sum of
**fourth** powers and a square. Here `0 ≤ u` is genuinely needed — it is what lets the first
bound be multiplied through by `u`. -/
theorem abs_three_mul_le (x y u : ℝ) (hu : 0 ≤ u) :
    |x| * |y| * u ≤ (x ^ 4 + y ^ 4 + 2 * u ^ 2) / 4 := by
  have h1 : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    have := abs_mul_le_sq_add x |y|
    rwa [sq_abs y] at this
  have h2 : |x| * |y| * u ≤ (x ^ 2 + y ^ 2) / 2 * u := mul_le_mul_of_nonneg_right h1 hu
  have h3 := sq_mul_le_sq_add x u
  have h4 := sq_mul_le_sq_add y u
  nlinarith [h2, h3, h4]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- Four even powers of smeared fields, so `integrable_pow_pair` four times. -/
theorem integrable_wick_three_bound (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) (k : ℕ) :
    Integrable (fun ω => ((k : ℝ) + 1)
        * (((inner ℝ a ω : ℝ) ^ 4 + (inner ℝ b ω : ℝ) ^ 4
            + 2 * (2 ^ (2 * k + 1)
              * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
                + (inner ℝ c ω : ℝ) ^ (2 * (k + 1))))) / 4)) (gaussianField G m) := by
  have ha : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ a ω : ℝ) ^ 4)
      (gaussianField G m) := integrable_pow_pair (G := G) hm a _
  have hb : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ b ω : ℝ) ^ 4)
      (gaussianField G m) := integrable_pow_pair (G := G) hm b _
  have hf : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) ^ (2 * (k + 1)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm f _
  have hc : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ c ω : ℝ) ^ (2 * (k + 1)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm c _
  exact (((ha.add hb).add (((hf.add hc).const_mul _).const_mul _)).div_const 4).const_mul _

/-! ## 3. The two readings of `F'(0)` -/

/-- **THE INTEGRAL READING.** The same parametric-integral lemma as the previous two units; the
only change is the majorant, and the only change in the majorant is `abs_three_mul_le`. -/
theorem hasDerivAt_three_ray (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) (k : ℕ) :
    HasDerivAt (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      (((k : ℝ) + 1) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun ε ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
      * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ (k + 1) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun ε ω => ((k : ℝ) + 1) * ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
      * ((inner ℝ c ω : ℝ) * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ k)) with hF'
  have hbase : ∀ ε : ℝ, Continuous
      (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) := fun ε =>
    (continuous_pair f).add (continuous_const.mul (continuous_pair c))
  have hcont : ∀ ε : ℝ, Continuous (F ε) := fun ε =>
    ((continuous_pair a).mul (continuous_pair b)).mul ((hbase ε).pow _)
  have hcont' : ∀ ε : ℝ, Continuous (F' ε) := fun ε =>
    continuous_const.mul (((continuous_pair a).mul (continuous_pair b)).mul
      ((continuous_pair c).mul ((hbase ε).pow _)))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (ε : ℝ), HasDerivAt (F · ω) (F' ε ω) ε := by
    intro ω ε
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ c ω : ℝ)) (inner ℝ c ω : ℝ) ε := by
      simpa using ((hasDerivAt_id ε).mul_const (inner ℝ c ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := (hlin.pow (k + 1)).const_mul ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ))
    simp only [hF, hF']
    convert hp using 1
    push_cast
    ring
  have hint0 : Integrable (F 0) μ := by
    have hfsq : Integrable
        (fun ω : EuclideanSpace ℝ V => ((inner ℝ f ω : ℝ) ^ (k + 1)) ^ 2) μ := by
      simpa [← pow_mul] using integrable_pow_pair (G := G) hm f ((k + 1) * 2)
    have hprod : Integrable (fun ω : EuclideanSpace ℝ V =>
        ((inner ℝ a ω : ℝ) ^ 4 + (inner ℝ b ω : ℝ) ^ 4
          + 2 * ((inner ℝ f ω : ℝ) ^ (k + 1)) ^ 2) / 4) μ :=
      (((integrable_pow_pair (G := G) hm a 4).add
        (integrable_pow_pair (G := G) hm b 4)).add (hfsq.const_mul 2)).div_const 4
    refine Integrable.mono' hprod ((hcont 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := abs_three_mul_le (inner ℝ a ω : ℝ) (inner ℝ b ω : ℝ)
      (|(inner ℝ f ω : ℝ)| ^ (k + 1)) (by positivity)
    rw [← abs_pow, sq_abs] at h
    calc ‖F 0 ω‖
        = |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * |(inner ℝ f ω : ℝ) ^ (k + 1)| := by
          simp only [hF, Real.norm_eq_abs]
          rw [abs_mul, abs_mul]
          norm_num
      _ ≤ _ := h
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω => ((k : ℝ) + 1)
      * (((inner ℝ a ω : ℝ) ^ 4 + (inner ℝ b ω : ℝ) ^ 4
          + 2 * (2 ^ (2 * k + 1)
            * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
              + (inner ℝ c ω : ℝ) ^ (2 * (k + 1))))) / 4))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun ε => (hcont ε).aestronglyMeasurable)
    hint0
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ε hεm => by
      have hε : |ε| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hεm)
      have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      have h1 := abs_mul_pow_le (inner ℝ f ω : ℝ) (inner ℝ c ω : ℝ) ε hε k
      have h2 := abs_three_mul_le (inner ℝ a ω : ℝ) (inner ℝ b ω : ℝ)
        ((|(inner ℝ f ω : ℝ)| + |(inner ℝ c ω : ℝ)|) ^ (k + 1)) (by positivity)
      have h3 := abs_add_pow_even_le (inner ℝ f ω : ℝ) (inner ℝ c ω : ℝ) k
      have hpow : ((|(inner ℝ f ω : ℝ)| + |(inner ℝ c ω : ℝ)|) ^ (k + 1)) ^ 2
          = (|(inner ℝ f ω : ℝ)| + |(inner ℝ c ω : ℝ)|) ^ (2 * (k + 1)) := by
        rw [← pow_mul, mul_comm]
      rw [hpow] at h2
      have hstep : |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * |(inner ℝ c ω : ℝ)
          * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ k|
          ≤ ((inner ℝ a ω : ℝ) ^ 4 + (inner ℝ b ω : ℝ) ^ 4
            + 2 * (2 ^ (2 * k + 1)
              * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
                + (inner ℝ c ω : ℝ) ^ (2 * (k + 1))))) / 4 := by
        have hmono : |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * |(inner ℝ c ω : ℝ)
            * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ k|
            ≤ |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)|
              * (|(inner ℝ f ω : ℝ)| + |(inner ℝ c ω : ℝ)|) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        linarith [hmono, h2, h3]
      calc ‖F' ε ω‖
          = ((k : ℝ) + 1) * (|(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)| * |(inner ℝ c ω : ℝ)
              * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ k|) := by
            simp only [hF', Real.norm_eq_abs]
            rw [abs_mul, abs_of_nonneg hk1, abs_mul, abs_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hstep hk1)
    (integrable_wick_three_bound hm a b c f k)
    (Filter.Eventually.of_forall fun ω ε _ => hderiv ω ε)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ((k : ℝ) + 1) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
          * (inner ℝ f ω : ℝ) ^ k ∂μ := by
    simp only [hF']
    rw [integral_const_mul]
    simp [mul_assoc]
  rw [← hval]
  simpa [hF] using hres.2

/-- **THE CLOSED-FORM READING**, and this is where the previous unit is spent: `F(ε)` is not an
integral to be estimated but an explicit expression in `ε`, because `wick_two_raw` evaluated it.
One product rule, over three `ε`-dependent factors rather than two. -/
theorem hasDerivAt_three_closed (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) (k : ℕ) :
    HasDerivAt (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      (dotG G m b a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ ((k + 1) / 2 - 1) * (2 * dotG G m f c)))
        + (dotG G m c a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ ((k + 1) / 2 - 1) * (2 * dotG G m f b)))
          + dotG G m f a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
              * ((((k + 1) / 2 - 1 : ℕ) : ℝ) * (linVar G m f) ^ ((k + 1) / 2 - 1 - 1)
                  * (2 * dotG G m f c))
              * (2 * dotG G m f b)
            + (((k + 1) / 2 : ℕ) : ℝ) * (linVar G m f) ^ ((k + 1) / 2 - 1)
              * (2 * dotG G m c b))))) 0 := by
  have hfun : (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
      * ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      = fun ε : ℝ => dotG G m b a * (wickCoeff (k + 1)
            * (linVar G m f + 2 * ε * dotG G m f c + ε ^ 2 * linVar G m c) ^ ((k + 1) / 2))
          + (dotG G m f a + ε * dotG G m c a) * (wickCoeff (k + 1)
            * ((((k + 1) / 2 : ℕ) : ℝ)
              * (linVar G m f + 2 * ε * dotG G m f c + ε ^ 2 * linVar G m c) ^ ((k + 1) / 2 - 1)
              * (2 * (dotG G m f b + ε * dotG G m c b)))) := by
    funext ε
    have h1 : ∀ ω : EuclideanSpace ℝ V, ((inner ℝ f ω : ℝ) + ε * (inner ℝ c ω : ℝ))
        = (inner ℝ (f + ε • c) ω : ℝ) := fun ω => (inner_add_smul f c ε ω).symm
    simp only [h1]
    rw [wick_two_raw hm a b (f + ε • c) (k + 1), linVar_add_smul hm,
      dotG_add_left, dotG_add_left, dotG_smul_left, dotG_smul_left]
  rw [hfun]
  have hq : HasDerivAt
      (fun ε : ℝ => linVar G m f + 2 * ε * dotG G m f c + ε ^ 2 * linVar G m c)
      (2 * dotG G m f c) 0 := by
    have hα : HasDerivAt (fun ε : ℝ => 2 * ε * dotG G m f c) (2 * dotG G m f c) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (dotG G m f c))
    have hβ : HasDerivAt (fun ε : ℝ => ε ^ 2 * linVar G m c) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (linVar G m c))
    simpa using (hα.const_add (linVar G m f)).add hβ
  have hu : HasDerivAt (fun ε : ℝ => dotG G m f a + ε * dotG G m c a) (dotG G m c a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m c a)).const_add (dotG G m f a)
  have hw : HasDerivAt (fun ε : ℝ => 2 * (dotG G m f b + ε * dotG G m c b))
      (2 * dotG G m c b) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m c b)).const_add (dotG G m f b)
    simpa using this.const_mul (2 : ℝ)
  -- the first summand: a constant times a power of `Q`
  have hfst := ((hq.pow ((k + 1) / 2)).const_mul (wickCoeff (k + 1))).const_mul (dotG G m b a)
  -- the second summand: `u · (c · ((J:ℝ) · Q^(J−1) · w))`
  have hpow' := hq.pow ((k + 1) / 2 - 1)
  have hinner := (hpow'.const_mul ((((k + 1) / 2 : ℕ) : ℝ))).mul hw
  have hsnd := hu.mul (hinner.const_mul (wickCoeff (k + 1)))
  have hres := hfst.add hsnd
  convert hres using 1
  norm_num

/-! ## 4. Three linear factors -/

/-- What comes out of `HasDerivAt.unique`, before the double factorials are tidied. -/
theorem wick_three_raw (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) (k : ℕ) :
    ((k : ℝ) + 1) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)
      = dotG G m b a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ ((k + 1) / 2 - 1) * (2 * dotG G m f c)))
        + (dotG G m c a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ ((k + 1) / 2 - 1) * (2 * dotG G m f b)))
          + dotG G m f a * (wickCoeff (k + 1) * ((((k + 1) / 2 : ℕ) : ℝ)
              * ((((k + 1) / 2 - 1 : ℕ) : ℝ) * (linVar G m f) ^ ((k + 1) / 2 - 1 - 1)
                  * (2 * dotG G m f c))
              * (2 * dotG G m f b)
            + (((k + 1) / 2 : ℕ) : ℝ) * (linVar G m f) ^ ((k + 1) / 2 - 1)
              * (2 * dotG G m c b)))) :=
  (hasDerivAt_three_ray (G := G) hm a b c f k).unique (hasDerivAt_three_closed hm a b c f k)

/-- **WICK'S RECURSION WITH THREE LINEAR FACTORS.**

`∫⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪f,ω⟫^(n+3) = (n+3)(⟨b,Ga⟩⟨f,Gc⟩+⟨c,Ga⟩⟨f,Gb⟩+⟨c,Gb⟩⟨f,Ga⟩)·∫⟪f,ω⟫^(n+2) +
(n+3)(n+2)(n+1)·⟨f,Ga⟩⟨f,Gb⟩⟨f,Gc⟩·∫⟪f,ω⟫^n`.

Read combinatorially: of `⟪a,·⟫, ⟪b,·⟫, ⟪c,·⟫`, either exactly two contract with each other and
the third with one of the `n+3` copies of `⟪f,·⟫` — three ways to choose the pair, `n+3` ways to
choose the copy, and the remaining `n+2` copies contract among themselves — or all three contract
with distinct copies, in `(n+3)(n+2)(n+1)` ordered ways, leaving `n`. Every count is visible in
the statement. -/
theorem wick_three (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) (n : ℕ) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ (n + 3) ∂(gaussianField G m)
      = ((n : ℝ) + 3)
          * (dotG G m b a * dotG G m f c + dotG G m c a * dotG G m f b
              + dotG G m c b * dotG G m f a)
          * ∫ ω, (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m)
        + ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1)
            * (dotG G m f a * dotG G m f b * dotG G m f c)
            * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
  have hraw := wick_three_raw (G := G) hm a b c f (n + 3)
  rw [moment_eq_wickCoeff hm f (n + 2), moment_eq_wickCoeff hm f n]
  -- the index identities, so that every power is `q ^ ((n+2)/2)` or `q ^ (n/2)`
  have hi0 : n + 3 + 1 = n + 4 := by omega
  have hi2 : (n + 4) / 2 - 1 = (n + 2) / 2 := by omega
  have hi3 : (n + 2) / 2 - 1 = n / 2 := half_sub_one n
  rw [hi0, hi2, hi3] at hraw
  push_cast at hraw
  -- the coefficient identity at `n+2`, which is `wickCoeff_mul_half` re-indexed
  have hc1 : wickCoeff (n + 4) * (((n + 4) / 2 : ℕ) : ℝ) * 2
      = ((n : ℝ) + 4) * ((n : ℝ) + 3) * wickCoeff (n + 2) := by
    have h := wickCoeff_mul_half (n + 2)
    have hidx : n + 2 + 2 = n + 4 := by omega
    rw [hidx] at h
    push_cast at h
    linear_combination h
  have hc2 : wickCoeff (n + 2) * (((n + 2) / 2 : ℕ) : ℝ) * 2
      = ((n : ℝ) + 2) * ((n : ℝ) + 1) * wickCoeff n := wickCoeff_mul_half n
  -- **AND THE SAME IDENTITY APPLIED TWICE**, which is what the bundled `wickCoeff_step`
  -- cannot deliver: two contractions need the coefficient at two consecutive indices.
  have hc3 : wickCoeff (n + 4) * (((n + 4) / 2 : ℕ) : ℝ) * (((n + 2) / 2 : ℕ) : ℝ) * 4
      = ((n : ℝ) + 4) * ((n : ℝ) + 3) * ((n : ℝ) + 2) * ((n : ℝ) + 1) * wickCoeff n := by
    linear_combination ((((n + 2) / 2 : ℕ) : ℝ) * 2) * hc1
      + (((n : ℝ) + 4) * ((n : ℝ) + 3)) * hc2
  have hk1 : ((n : ℝ) + 4) ≠ 0 := by positivity
  refine mul_left_cancel₀ hk1 ?_
  linear_combination hraw
    + ((dotG G m b a * dotG G m f c + dotG G m c a * dotG G m f b
          + dotG G m f a * dotG G m c b) * linVar G m f ^ ((n + 2) / 2)) * hc1
    + (dotG G m f a * dotG G m f b * dotG G m f c * linVar G m f ^ (n / 2)) * hc3

/-! ## 5. Two checks, at the two ends of the range -/

/-- `n = 0`: **the estate's first order-six correlation at four distinct test functions.**
`3·3 + 6 = 15 = 5‼`, the number of pairings of six objects. -/
theorem wick_three_order_six (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ 3 ∂(gaussianField G m)
      = 3 * (dotG G m b a * dotG G m f c + dotG G m c a * dotG G m f b
              + dotG G m c b * dotG G m f a) * linVar G m f
        + 6 * (dotG G m f a * dotG G m f b * dotG G m f c) := by
  have h := wick_three (G := G) hm a b c f 0
  rw [moment_two_of_general hm f, moment_eq_wickCoeff hm f 0] at h
  norm_num [wickCoeff] at h
  linear_combination h

/-! ### And at the other end of the range, an independent route to the same number -/

/-- `k = 1`: the cubic term's coefficient `k(k−1)(k−2)` vanishes and only the three
pair-and-contract terms survive.

**THIS STATEMENT IS `LatticeIsserlisFour.isserlis_four` AGAIN, AND THE DUPLICATION IS THE POINT**
(`ERRATUM 176` asks for declared duplicates to be declared). It is the same integral and the same
number, reached here by **three** differentiations under the integral sign — `wick_recursion`,
`wick_two_raw`, `wick_three_raw` — where `isserlis_four` reached it by polarising a fourth moment
twice, with no derivative anywhere. Nothing in either proof is shared.
`wick_three_order_four_eq_isserlis` below is what makes the agreement a theorem rather than
an observation. -/
theorem wick_three_order_four (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = dotG G m b a * dotG G m f c + dotG G m c a * dotG G m f b
        + dotG G m c b * dotG G m f a := by
  have h := wick_three_raw (G := G) hm a b c f 1
  norm_num [wickCoeff] at h
  linear_combination h / 2

/-- **THE CHECK, AND IT IS NOT A RESTATEMENT.** `LatticeIsserlisFour.isserlis_four` is the same
number by a completely different route — two polarisations of a fourth moment, with no derivative
anywhere in it — and it was proved before any of this machinery existed. Since `wick_three_raw`
comes out of `wick_two_raw`, which comes out of `wick_recursion_closed`, an agreement here tests
the whole chain of three differentiations at once, including both new coefficient identities. -/
theorem wick_three_order_four_eq_isserlis (hm : m ≠ 0) (a b c f : EuclideanSpace ℝ V) :
    dotG G m b a * dotG G m f c + dotG G m c a * dotG G m f b
        + dotG G m c b * dotG G m f a
      = dotG G m a b * dotG G m c f + dotG G m a c * dotG G m b f
        + dotG G m a f * dotG G m b c := by
  have h1 := wick_three_order_four (G := G) hm a b c f
  have h2 := isserlis_four (G := G) hm a b c f
  rw [h1] at h2
  exact h2

end LatticeWickThree
