import LatticeWickRecursion

/-!
# Two linear factors against a power: the estate's first correlation of order six

`LatticeWickRecursion` pulled **one** smeared field out of a Gaussian average against a power of
another. This pulls out **two**, and the point of doing so is that it reaches order six, which the
`UNLOCK_WATCHLIST` has an open and deliberately uncosted sub-trigger for:

> *"someone wants Isserlis at order six or general order. Whether that is an induction on the
> pairing count or another two-line trick **is not estimated here**, and the next person to touch
> it should derive the cost rather than read one."*

**The cost, derived.** It is one more differentiation of exactly the kind the previous unit did,
and the only thing that is genuinely new is the domination. Put

```
F(ε) = ∫ ⟪a,ω⟫·⟪f + ε·b, ω⟫^(k+1) dμ
```

and read it twice, as before. As an integral, `F'(0) = (k+1)·∫ ⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫^k`. As a formula,
`wick_recursion_closed` evaluates `F(ε)` outright — `(k+1)·⟨f+εb, Ga⟩·c_k·q(ε)^{k/2}`, a product of
two explicit polynomials in `ε` — so `F'(0)` is one product rule. **The previous unit's theorem is
what makes the second differentiation cheap**, exactly as the general moment formula made the first
one cheap.

**What is new is the majorant.** `LatticeWickRecursion` bounded `|y·(x+sy)^n|` by a polynomial in
`x` and `y`. Here there is a third field in the way, and `|z|·u` is not a polynomial in a single
variable; the split is `|z|·u ≤ (z² + u²)/2`, which turns the product into a sum of two even powers
and costs one `nlinarith`. That is the whole of the difference.

## What is proved

* `abs_mul_le_sq_add`, `abs_add_pow_even_le` — the two halves of the majorant: AM–GM to break the
  product, then `add_pow_le` to break the binomial at an **even** exponent, where `|x|^{2j} =
  x^{2j}` makes the result integrable by `LatticeIsserlis.integrable_pow_pair`. The first is
  stated **without** the `0 ≤ u` it was written with: at `u < 0` the left side is `≤ 0` and the
  right is `≥ 0`, so the hypothesis was never doing any work;
* `hasDerivAt_two_ray`, `hasDerivAt_two_closed` — the two readings of `F'(0)`;
* `wick_two_raw` — what comes out before the double factorials are tidied:
  `∫ ⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫^k = ⟨b,Ga⟩·c_k·q^{k/2} + 2⟨f,Ga⟩⟨f,Gb⟩·c_k·(k/2)·q^{k/2−1}`;
* **`wick_two`** — and after, with both integrals restored and no truncated subtraction:

  ```
  ∫ ⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫^(n+2) = ⟨b,Ga⟩·∫⟪f,ω⟫^(n+2) + (n+2)(n+1)·⟨f,Ga⟩⟨f,Gb⟩·∫⟪f,ω⟫^n
  ```

  which is Wick's recursion with `X₁ = ⟪a,·⟫` contracted against `⟪b,·⟫` once and against the
  `n+2` copies of `⟪f,·⟫` in `(n+2)` ways, each of which costs a further contraction of `⟪b,·⟫`
  into the remaining `n+1`. The two combinatorial factors are visible in the statement;
* **`wick_two_order_four`** — the case `n = 0`, `∫⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫² = ⟨b,Ga⟩⟨f,Gf⟩ +
  2⟨f,Ga⟩⟨f,Gb⟩`, **checked against `LatticeIsserlisFour.isserlis_four`** in
  `wick_two_order_four_eq_isserlis`. That check is *not* a restatement: `isserlis_four` was proved
  by polarising a fourth moment twice and knows nothing about differentiation;
* **`wick_two_order_six`** — `∫⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫⁴ = 3⟨b,Ga⟩(fᵀGf)² + 12⟨f,Ga⟩⟨f,Gb⟩(fᵀGf)`. **The
  first correlation of order six anywhere in the estate.** Its `15 = 3 + 12` is the count of
  pairings of six objects, and it is the one visible check that the two coefficients are right.

## What this is NOT

**It is two arbitrary test functions and a power of a third**, not six arbitrary ones. Isserlis at
order six in full is `∫⟪f₁,ω⟫⋯⟪f₆,ω⟫` with all six distinct, a sum over `15` pairings; the pattern
here is `(a,b,f,f,f,f)`, which is one of the shapes that sum specialises to. **The sub-trigger for
general order does not close**, and what the watchlist records after this file is a narrower thing
than what it recorded before: it is now `k` distinct factors rather than any at all.

**And OS4 does not move.** Finite volume throughout. **No published tag moves.**
-/

namespace LatticeWickTwo

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeMomentsGeneral LatticeSteinIdentity LatticeWickRecursion

/-! ## 1. The majorant, whose only new ingredient is a product split -/

/-- AM–GM in the form the third field forces: a product of an absolute value and a nonnegative
quantity is bounded by a sum of squares, each of which is separately integrable. -/
theorem abs_mul_le_sq_add (z u : ℝ) : |z| * u ≤ (z ^ 2 + u ^ 2) / 2 := by
  nlinarith [sq_nonneg (|z| - u), sq_abs z, abs_nonneg z]

/-- `add_pow_le` at an **even** exponent, where the absolute values can be dropped. -/
theorem abs_add_pow_even_le (x y : ℝ) (k : ℕ) :
    (|x| + |y|) ^ (2 * (k + 1)) ≤ 2 ^ (2 * k + 1) * (x ^ (2 * (k + 1)) + y ^ (2 * (k + 1))) := by
  have hsplit : (|x| + |y|) ^ (2 * (k + 1))
      ≤ 2 ^ (2 * (k + 1) - 1) * (|x| ^ (2 * (k + 1)) + |y| ^ (2 * (k + 1))) :=
    add_pow_le (abs_nonneg x) (abs_nonneg y) (2 * (k + 1))
  have hidx : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have hx : |x| ^ (2 * (k + 1)) = x ^ (2 * (k + 1)) := by
    rw [← abs_pow, abs_of_nonneg (even_two_mul (k + 1) |>.pow_nonneg x)]
  have hy : |y| ^ (2 * (k + 1)) = y ^ (2 * (k + 1)) := by
    rw [← abs_pow, abs_of_nonneg (even_two_mul (k + 1) |>.pow_nonneg y)]
  rw [hidx, hx, hy] at hsplit
  exact hsplit

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- Three even powers of smeared fields, so `integrable_pow_pair` three times. -/
theorem integrable_wick_two_bound (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (k : ℕ) :
    Integrable (fun ω => ((k : ℝ) + 1)
        * (((inner ℝ a ω : ℝ) ^ 2 + 2 ^ (2 * k + 1)
            * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
              + (inner ℝ b ω : ℝ) ^ (2 * (k + 1)))) / 2)) (gaussianField G m) := by
  have ha : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ a ω : ℝ) ^ 2)
      (gaussianField G m) := integrable_pow_pair (G := G) hm a _
  have hf : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) ^ (2 * (k + 1)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm f _
  have hb : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ b ω : ℝ) ^ (2 * (k + 1)))
      (gaussianField G m) := integrable_pow_pair (G := G) hm b _
  exact (((ha.add ((hf.add hb).const_mul _)).div_const 2).const_mul _)

/-! ## 2. The two readings of `F'(0)` -/

/-- **THE INTEGRAL READING.** Same parametric-integral lemma as the previous two units; the only
change is the majorant, and the only change in the majorant is `abs_mul_le_sq_add`. -/
theorem hasDerivAt_two_ray (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (k : ℕ) :
    HasDerivAt (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
        * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      (((k : ℝ) + 1) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun ε ω => (inner ℝ a ω : ℝ)
      * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ (k + 1) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun ε ω => ((k : ℝ) + 1) * ((inner ℝ a ω : ℝ) * ((inner ℝ b ω : ℝ)
      * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ k)) with hF'
  have hbase : ∀ ε : ℝ, Continuous
      (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) := fun ε =>
    (continuous_pair f).add (continuous_const.mul (continuous_pair b))
  have hcont : ∀ ε : ℝ, Continuous (F ε) := fun ε =>
    (continuous_pair a).mul ((hbase ε).pow _)
  have hcont' : ∀ ε : ℝ, Continuous (F' ε) := fun ε =>
    continuous_const.mul ((continuous_pair a).mul ((continuous_pair b).mul ((hbase ε).pow _)))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (ε : ℝ), HasDerivAt (F · ω) (F' ε ω) ε := by
    intro ω ε
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ b ω : ℝ)) (inner ℝ b ω : ℝ) ε := by
      simpa using ((hasDerivAt_id ε).mul_const (inner ℝ b ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := (hlin.pow (k + 1)).const_mul (inner ℝ a ω : ℝ)
    simp only [hF, hF']
    convert hp using 1
    push_cast
    ring
  have hint0 : Integrable (F 0) μ := by
    have hprod : Integrable (fun ω : EuclideanSpace ℝ V =>
        ((inner ℝ a ω : ℝ) ^ 2 + ((inner ℝ f ω : ℝ) ^ (k + 1)) ^ 2) / 2) μ :=
      ((integrable_pow_pair (G := G) hm a 2).add
        (by simpa [← pow_mul] using
          integrable_pow_pair (G := G) hm f ((k + 1) * 2))).div_const 2
    refine Integrable.mono' hprod ((hcont 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := abs_mul_le_sq_add (inner ℝ a ω : ℝ) (|(inner ℝ f ω : ℝ)| ^ (k + 1))
    rw [← abs_pow, sq_abs] at h
    calc ‖F 0 ω‖ = |(inner ℝ a ω : ℝ)| * |(inner ℝ f ω : ℝ) ^ (k + 1)| := by
          simp only [hF, Real.norm_eq_abs]
          rw [abs_mul]
          norm_num
      _ ≤ _ := h
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ)) (bound := fun ω => ((k : ℝ) + 1)
      * (((inner ℝ a ω : ℝ) ^ 2 + 2 ^ (2 * k + 1)
          * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
            + (inner ℝ b ω : ℝ) ^ (2 * (k + 1)))) / 2))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun ε => (hcont ε).aestronglyMeasurable)
    hint0
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ε hεm => by
      have hε : |ε| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hεm)
      have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
      have h1 := abs_mul_pow_le (inner ℝ f ω : ℝ) (inner ℝ b ω : ℝ) ε hε k
      have h2 := abs_mul_le_sq_add (inner ℝ a ω : ℝ)
        ((|(inner ℝ f ω : ℝ)| + |(inner ℝ b ω : ℝ)|) ^ (k + 1))
      have h3 := abs_add_pow_even_le (inner ℝ f ω : ℝ) (inner ℝ b ω : ℝ) k
      have hpow : ((|(inner ℝ f ω : ℝ)| + |(inner ℝ b ω : ℝ)|) ^ (k + 1)) ^ 2
          = (|(inner ℝ f ω : ℝ)| + |(inner ℝ b ω : ℝ)|) ^ (2 * (k + 1)) := by
        rw [← pow_mul, mul_comm]
      rw [hpow] at h2
      have hstep : |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)
          * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ k|
          ≤ ((inner ℝ a ω : ℝ) ^ 2 + 2 ^ (2 * k + 1)
            * ((inner ℝ f ω : ℝ) ^ (2 * (k + 1))
              + (inner ℝ b ω : ℝ) ^ (2 * (k + 1)))) / 2 := by
        have hmono : |(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)
            * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ k|
            ≤ |(inner ℝ a ω : ℝ)| * (|(inner ℝ f ω : ℝ)| + |(inner ℝ b ω : ℝ)|) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        linarith [hmono, h2, h3]
      calc ‖F' ε ω‖ = ((k : ℝ) + 1) * (|(inner ℝ a ω : ℝ)| * |(inner ℝ b ω : ℝ)
              * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ k|) := by
            simp only [hF', Real.norm_eq_abs]
            rw [abs_mul, abs_of_nonneg hk1, abs_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hstep hk1)
    (integrable_wick_two_bound hm a b f k)
    (Filter.Eventually.of_forall fun ω ε _ => hderiv ω ε)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ((k : ℝ) + 1) * ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
          * (inner ℝ f ω : ℝ) ^ k ∂μ := by
    simp only [hF']
    rw [integral_const_mul]
    simp [mul_assoc]
  rw [← hval]
  simpa [hF] using hres.2

/-- **THE CLOSED-FORM READING**, and this is where the previous unit is spent: `F(ε)` is not an
integral to be estimated but a product of two explicit polynomials in `ε`, because
`wick_recursion_closed` evaluated it. One product rule. -/
theorem hasDerivAt_two_closed (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (k : ℕ) :
    HasDerivAt (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
        * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      (((k : ℝ) + 1) * (dotG G m b a * (wickCoeff k * (linVar G m f) ^ (k / 2))
        + dotG G m f a * (wickCoeff k * (((k / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ (k / 2 - 1) * (2 * dotG G m f b))))) 0 := by
  have hfun : (fun ε : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
      * ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ)) ^ (k + 1) ∂(gaussianField G m))
      = fun ε : ℝ => ((k : ℝ) + 1) * ((dotG G m f a + ε * dotG G m b a)
          * (wickCoeff k * (linVar G m f + 2 * ε * dotG G m f b
              + ε ^ 2 * linVar G m b) ^ (k / 2))) := by
    funext ε
    have h1 : ∀ ω : EuclideanSpace ℝ V, ((inner ℝ f ω : ℝ) + ε * (inner ℝ b ω : ℝ))
        = (inner ℝ (f + ε • b) ω : ℝ) := fun ω => (inner_add_smul f b ε ω).symm
    simp only [h1]
    rw [wick_recursion_closed hm (f + ε • b) a k, linVar_add_smul hm,
      dotG_add_left, dotG_smul_left]
    ring
  rw [hfun]
  have hu : HasDerivAt (fun ε : ℝ => dotG G m f a + ε * dotG G m b a) (dotG G m b a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m b a)).const_add (dotG G m f a)
  have hq : HasDerivAt
      (fun ε : ℝ => linVar G m f + 2 * ε * dotG G m f b + ε ^ 2 * linVar G m b)
      (2 * dotG G m f b) 0 := by
    have hα : HasDerivAt (fun ε : ℝ => 2 * ε * dotG G m f b) (2 * dotG G m f b) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (dotG G m f b))
    have hβ : HasDerivAt (fun ε : ℝ => ε ^ 2 * linVar G m b) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (linVar G m b))
    simpa using (hα.const_add (linVar G m f)).add hβ
  have hv := (hq.pow (k / 2)).const_mul (wickCoeff k)
  have hres := ((hu.mul hv).const_mul ((k : ℝ) + 1))
  convert hres using 1
  norm_num

/-! ## 3. Two linear factors -/

/-- What comes out of `HasDerivAt.unique`, before the double factorials are tidied. -/
theorem wick_two_raw (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)
      = dotG G m b a * (wickCoeff k * (linVar G m f) ^ (k / 2))
        + dotG G m f a * (wickCoeff k * (((k / 2 : ℕ) : ℝ)
            * (linVar G m f) ^ (k / 2 - 1) * (2 * dotG G m f b))) := by
  have heq := (hasDerivAt_two_ray (G := G) hm a b f k).unique (hasDerivAt_two_closed hm a b f k)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hk1 heq

/-- **WICK'S RECURSION WITH TWO LINEAR FACTORS.**

`∫ ⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫^(n+2) = ⟨b,Ga⟩·∫⟪f,ω⟫^(n+2) + (n+2)(n+1)·⟨f,Ga⟩⟨f,Gb⟩·∫⟪f,ω⟫^n`.

Read combinatorially: `⟪a,·⟫` contracts either with `⟪b,·⟫`, leaving all `n+2` copies of `⟪f,·⟫`
behind, or with one of those `n+2` copies, after which `⟪b,·⟫` must contract with one of the
remaining `n+1`. Both counts are visible in the statement. -/
theorem wick_two (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (n : ℕ) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m)
      = dotG G m b a * ∫ ω, (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m)
        + ((n : ℝ) + 2) * ((n : ℝ) + 1) * (dotG G m f a * dotG G m f b)
            * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
  rw [wick_two_raw hm a b f (n + 2), moment_eq_wickCoeff hm f (n + 2),
    moment_eq_wickCoeff hm f n]
  have hstep := wickCoeff_step n (linVar G m f)
  linear_combination (dotG G m f a * dotG G m f b) * hstep

/-! ## 4. Order four, checked, and then order six -/

/-- `n = 0`: `∫⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫² = ⟨b,Ga⟩(fᵀGf) + 2⟨f,Ga⟩⟨f,Gb⟩`. -/
theorem wick_two_order_four (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m)
      = dotG G m b a * linVar G m f + 2 * (dotG G m f a * dotG G m f b) := by
  have h := wick_two (G := G) hm a b f 0
  rw [moment_two_of_general hm f] at h
  simpa using h

/-- **THE CHECK.** `LatticeIsserlisFour.isserlis_four` is the same number by a completely different
route — two polarisations of a fourth moment, with no derivative anywhere in it. It is the one
place in this file where the coefficients are confirmed against something that did not come from
`wick_recursion`, and the proof cites both sides rather than re-deriving either.

**Where the `2` comes from is visible here.** Isserlis' three pairings of `(a,b,c,d)` are
`⟨ab⟩⟨cd⟩ + ⟨ac⟩⟨bd⟩ + ⟨ad⟩⟨bc⟩`; at `c = d = f` the last two become the *same* term, and the
right-hand side below is written with that repetition left in rather than collapsed, so the
coincidence can be read off. -/
theorem wick_two_order_four_eq_isserlis (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) :
    dotG G m b a * linVar G m f + 2 * (dotG G m f a * dotG G m f b)
      = dotG G m a b * dotG G m f f + dotG G m a f * dotG G m b f
        + dotG G m a f * dotG G m b f := by
  have h1 := wick_two_order_four (G := G) hm a b f
  have h2 := isserlis_four (G := G) hm a b f f
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ f ω : ℝ) * (inner ℝ f ω : ℝ)
        = (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ f ω : ℝ) ^ 2 := by
    intro ω; ring
  simp only [hpt] at h2
  rw [h1] at h2
  exact h2

/-- **ORDER SIX, AND IT IS THE FIRST IN THE ESTATE.**

`∫⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫⁴ = 3⟨b,Ga⟩(fᵀGf)² + 12⟨f,Ga⟩⟨f,Gb⟩(fᵀGf)`.

`3 + 12 = 15 = 5‼`, the number of pairings of six objects, which is the one check available on the
coefficients without another route to the same number. -/
theorem wick_two_order_six (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ 4 ∂(gaussianField G m)
      = 3 * (dotG G m b a * (linVar G m f) ^ 2)
        + 12 * (dotG G m f a * dotG G m f b * linVar G m f) := by
  have h := wick_two (G := G) hm a b f 2
  rw [moment_four_of_recursion hm f, moment_two_of_general hm f] at h
  norm_num at h
  rw [h]
  ring

/-- Diagonal check: at `a = b = f` order six collapses to `15(fᵀGf)³`, which is `moment_even` at
`k = 3` — the `15` being `5‼`, and the only place the two summands' coefficients are tested
against a number the estate computed by the `iteratedDeriv` route. -/
theorem moment_six_of_wick_two (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 6 ∂(gaussianField G m) = 15 * (linVar G m f) ^ 3 := by
  have h := wick_two_order_six (G := G) hm f f f
  have hff : dotG G m f f = linVar G m f := (linVar_eq_dotG f).symm
  rw [hff] at h
  have hpow : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ f ω : ℝ) * (inner ℝ f ω : ℝ) * (inner ℝ f ω : ℝ) ^ 4
        = (inner ℝ f ω : ℝ) ^ 6 := by
    intro ω; ring
  simp only [hpow] at h
  rw [h]
  ring

end LatticeWickTwo
