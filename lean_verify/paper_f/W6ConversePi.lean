/-
  W6ConversePi.lean — the n-dimensional converse, and the Gaussian Poincaré
  inequality restated on the textbook Sobolev space.

  WHY. The n-dimensional staircase built two classes and never connected
  them in the direction that matters. `HermitePiStein.SteinPairPi` is the
  class the coefficient recursion consumes and the class
  `HermitePiPoincare.poincare_steinPi` proves the inequality FOR; it is
  defined by testing against the Hermite products `Hpi n m`.
  `TextbookSobolevPi.SmoothSteinPairPi` is the class a reader of a textbook
  would recognise — tested against `Cc^∞(ℝⁿ)` — and stair N5 proved it
  equal to `SobolevWeakPi`, the honest Lebesgue-weak-derivative definition.
  Nothing said a member of the textbook class is a member of the Hermite
  class. The two had exactly one thing in common, and only because it had
  been put into each SEPARATELY — the constants
  (`TextbookSobolevPi.const_mem_stein`, `HermitePiStein.one_mem`), on which
  Poincaré reads `0 ≤ 0`. This file supplies the arrow.

  WHAT THIS FILE PROVES:
  1. **`steinPairPi_of_smoothSteinPairPi`** — the containment. Every
     `Cc^∞`-tested pair is a Hermite-tested pair. This is the
     n-dimensional twin of `W6Converse.steinPair_of_smoothSteinPair` and it
     runs on the same idea: cut `Hpi n m` down to `Hpi n m · χ_k`, which IS
     a legal `Cc^∞` test function, and let `k → ∞`.
  2. **`poincare_sobolevWeakPi`** — the payoff, and the reason the arrow
     was worth building. **The n-dimensional Gaussian Poincaré inequality,
     stated for a function whose gradient is its LEBESGUE weak derivative**:
     no Hermite coefficient, no Stein pairing, no polynomial in the
     hypothesis. `Var_γⁿ(f) ≤ Σᵢ ∫ (∂ᵢf)² dγⁿ`.
  3. **`coord_sobolevWeakPi`** — and that is not a theorem about constants.
     The coordinate function `x ↦ xᵢ` is in the textbook class with the
     weak gradient `eᵢ`, proved from the Lebesgue definition directly, and
     `poincare_coord_textbook` runs (2) on it: both sides are `1`.

  WHAT THIS DOES NOT DO, flagged rather than absorbed. **The reverse
  containment is not proved and is not a corollary of anything here.** In
  one dimension `SteinPair → SmoothSteinPair` was
  `SteinSmoothTest.smoothSteinPair_of_steinPair`, and its proof went
  through the coefficient identity `PoincareBeyondPolynomials.stein_general`
  — which has no n-dimensional counterpart in the estate (that gap is its
  own watchlist item, opened by ERRATUM 51). So what is proved here is ONE
  containment,
  `SmoothSteinPairPi ⊆ SteinPairPi`, and the two n-dimensional classes are
  NOT known to be equal. `W6Converse.stein_iff_smooth` has no twin below
  and none is claimed.

  A SECOND THING NOT PROVED, so that (2) is read at its true strength:
  the estate has no n-dimensional properness witness — no `f ∈ L²(γⁿ)`
  shown to lie outside `SteinPairPi`. In one dimension that was
  `HermiteHilbertBasis.exists_memLp_not_steinPair`, and it needed the
  coefficient CHARACTERISATION, which n dimensions also lack. So (2) is a
  theorem about a class known to be inhabited by non-constants (§5) and
  not known to be proper.

  ONE OF THE NAMED PIECES BELOW IS GENERIC AND DOES NOT BELONG IN THIS
  FILE: `hasCompactSupport_coordProd` — a product of one-variable compactly
  supported functions of the coordinates has compact support. It says
  nothing about Gaussians, Hermite polynomials or cutoffs. Its natural home
  is beside `GaussPiDensity.fderiv_coordProd`, whose shape it copies; it is
  here only because this is its first consumer, and it should move when a
  second appears. Everything else named below is specific to this argument
  and is named rather than inlined for the usual reason.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import W6Converse
import TextbookSobolevPi
import HermitePiPoincare
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace W6ConversePi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open GaussPiDensity HermitePiStein HermitePiPoincare TextbookSobolevPi

noncomputable section

/-! ## 0. A product of one-variable compactly supported functions

The twin of `GaussPiDensity.fderiv_coordProd`, for support rather than for
the derivative. The support of `x ↦ ∏ⱼ uⱼ(xⱼ)` sits inside the box
`∏ⱼ tsupport uⱼ`, which is compact because a product of compacts is: one
coordinate leaving its factor's support kills the whole product.
-/

theorem hasCompactSupport_coordProd (n : ℕ) (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, HasCompactSupport (u j)) :
    HasCompactSupport fun x : Fin n → ℝ => ∏ j, u j (x j) := by
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => tsupport (u j))
    (isCompact_univ_pi fun j => hu j) ?_
  intro x hx
  simp only [Set.mem_univ_pi, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) (image_eq_zero_of_notMem_tsupport hj)

/-! ## 1. The n-dimensional cutoff

It is the one-dimensional cutoff, one coordinate at a time. `ContDiffBump`
wants a smooth norm and `Fin n → ℝ` carries the sup norm, so a single
n-dimensional bump is not directly available from Mathlib; the product
sidesteps that entirely and — more usefully — makes every fact below a
one-line consequence of the corresponding fact in `W6Converse`.
-/

/-- `χ_k` in n variables: the product of the one-dimensional `W6Converse.cut`
    over the coordinates. -/
def cutPi (n k : ℕ) (x : Fin n → ℝ) : ℝ := ∏ l, W6Converse.cut k (x l)

theorem cutPi_smooth (n k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutPi n k) :=
  contDiff_prod fun l _ => (W6Converse.cut_smooth k).comp (contDiff_apply ℝ ℝ l)

theorem cutPi_continuous (n k : ℕ) : Continuous (cutPi n k) :=
  (cutPi_smooth n k).continuous

theorem cutPi_differentiableAt (n k : ℕ) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (cutPi n k) x :=
  ((cutPi_smooth n k).differentiable (by simp)).differentiableAt

theorem cutPi_support (n k : ℕ) : HasCompactSupport (cutPi n k) :=
  hasCompactSupport_coordProd n (fun _ => W6Converse.cut k)
    fun _ => W6Converse.cut_support k

/-- `|∏ χ| ≤ 1` over ANY index set — stated for a general `Finset` because
    the derivative bound below needs it over `univ.erase i`. -/
theorem prod_cut_abs_le_one (n k : ℕ) (s : Finset (Fin n)) (x : Fin n → ℝ) :
    |∏ j ∈ s, W6Converse.cut k (x j)| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun j _ => abs_nonneg _)
    fun j _ => W6Converse.cut_abs_le_one k (x j)

theorem cutPi_abs_le_one (n k : ℕ) (x : Fin n → ℝ) : |cutPi n k x| ≤ 1 :=
  prod_cut_abs_le_one n k Finset.univ x

/-- At a FIXED point every coordinate's cutoff is eventually `1`, and there
    are finitely many coordinates — which is the only place the finiteness
    of the dimension is used in this section. -/
theorem cutPi_eventually_one (n : ℕ) (x : Fin n → ℝ) :
    ∀ᶠ k : ℕ in atTop, cutPi n k x = 1 := by
  have h : ∀ᶠ k : ℕ in atTop, ∀ l : Fin n, W6Converse.cut k (x l) = 1 :=
    eventually_all.mpr fun l => W6Converse.cut_eventually_one (x l)
  filter_upwards [h] with k hk
  exact Finset.prod_eq_one fun l _ => hk l

theorem cutPi_tendsto (n : ℕ) (x : Fin n → ℝ) :
    Tendsto (fun k : ℕ => cutPi n k x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [cutPi_eventually_one n x] with k hk
  exact hk.symm

/-- The partial derivative of the cutoff, by `fderiv_coordProd`: one factor
    is differentiated and the rest are carried along. -/
theorem fderiv_cutPi (n k : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ))
      = deriv (W6Converse.cut k) (x i)
        * ∏ j ∈ Finset.univ.erase i, W6Converse.cut k (x j) := by
  have hprod : cutPi n k = fun y : Fin n → ℝ => ∏ j, W6Converse.cut k (y j) := rfl
  rw [hprod, fderiv_coordProd n (fun _ => W6Converse.cut k)
    (fun _ => (W6Converse.cut_smooth k).differentiable (by simp)) i x]

theorem continuous_fderiv_cutPi (n k : ℕ) (i : Fin n) :
    Continuous fun x : Fin n → ℝ => fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)) := by
  have heq : (fun x : Fin n → ℝ => fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)))
      = fun x : Fin n → ℝ => deriv (W6Converse.cut k) (x i)
          * ∏ j ∈ Finset.univ.erase i, W6Converse.cut k (x j) :=
    funext fun x => fderiv_cutPi n k i x
  rw [heq]
  exact (((W6Converse.cut_smooth k).continuous_deriv (by exact_mod_cast le_top)).comp
      (continuous_apply i)).mul
    (continuous_finset_prod _ fun j _ =>
      (W6Converse.cut_smooth k).continuous.comp (continuous_apply j))

/-- **The quantitative heart, carried up a dimension.** The extra factors
    are bounded by `1`, so the `O(1/k)` decay of the one-dimensional
    derivative survives untouched. -/
theorem fderiv_cutPi_abs_le {D : ℝ} (hD : ∀ y, |deriv W6Converse.chiF y| ≤ D)
    (n k : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    |fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ))| ≤ D / ((k : ℝ) + 1) := by
  rw [fderiv_cutPi, abs_mul]
  have h1 := W6Converse.deriv_cut_abs_le hD k (x i)
  have h2 := prod_cut_abs_le_one n k (Finset.univ.erase i) x
  have hD0 : (0:ℝ) ≤ D / ((k : ℝ) + 1) := le_trans (abs_nonneg _) h1
  simpa using mul_le_mul h1 h2 (abs_nonneg _) hD0

theorem tendsto_fderiv_cutPi (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    Tendsto (fun k : ℕ => fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ))) atTop (𝓝 0) := by
  obtain ⟨D, _, hD⟩ := W6Converse.exists_deriv_bound
  refine squeeze_zero_norm (a := fun k : ℕ => D / ((k : ℝ) + 1)) (fun k => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact fderiv_cutPi_abs_le hD n k i x
  · exact tendsto_const_nhds.div_atTop W6Converse.tendsto_nat_add_one_atTop

/-! ## 2. The Hermite products are smooth

`HermitePi` proved `Hpi_continuous` and `Hpi_memLp`; the test functions
below need one degree more, and it is the same product argument.
-/

theorem contDiff_Hpi (n : ℕ) (m : Fin n → ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Hpi n m) :=
  contDiff_prod fun j _ =>
    (W6Converse.polynomial_contDiff (H (m j))).comp (contDiff_apply ℝ ℝ j)

theorem differentiableAt_Hpi (n : ℕ) (m : Fin n → ℕ) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (Hpi n m) x :=
  ((contDiff_Hpi n m).differentiable (by simp)).differentiableAt

/-! ## 3. The test functions `Hpi n m · χ_k`, and integrability uniform in `k`

The n-dimensional twin of `W6Converse.integrable_bdd`: a bounded continuous
factor cannot break the integrability of `f·Hpi n m`, which is Cauchy–Schwarz
between two `L²(γⁿ)` functions.
-/

theorem testfPi_smooth (n : ℕ) (m : Fin n → ℕ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => Hpi n m x * cutPi n k x :=
  (contDiff_Hpi n m).mul (cutPi_smooth n k)

theorem testfPi_support (n : ℕ) (m : Fin n → ℕ) (k : ℕ) :
    HasCompactSupport fun x => Hpi n m x * cutPi n k x :=
  (cutPi_support n k).mul_left

theorem integrable_bddPi (n : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (gaussPi n))
    (m : Fin n → ℕ) {u : (Fin n → ℝ) → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : ∀ x, |u x| ≤ M) :
    Integrable (fun x => f x * (Hpi n m x * u x)) (gaussPi n) := by
  have hfH : Integrable (fun x => f x * Hpi n m x) (gaussPi n) :=
    MemLp.integrable_mul hf (Hpi_memLp n m)
  refine Integrable.mono' (hfH.abs.const_mul M) ?_ ?_
  · exact hf.aestronglyMeasurable.mul
      (((Hpi_continuous n m).mul hu).aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have h2 : (0:ℝ) ≤ |f x| * |Hpi n m x| := by positivity
    calc |f x| * (|Hpi n m x| * |u x|) = (|f x| * |Hpi n m x|) * |u x| := by ring
      _ ≤ (|f x| * |Hpi n m x|) * M := mul_le_mul_of_nonneg_left (hM x) h2
      _ = M * (|f x| * |Hpi n m x|) := by ring

/-- What the cutoff does to the Stein integrand: the recursion `Hpi_succ`
    survives, and the whole error is `Hpi n m · ∂ᵢχ_k`. -/
theorem stein_integrand_cut (n : ℕ) (m : Fin n → ℕ) (k : ℕ) (i : Fin n)
    (x : Fin n → ℝ) :
    x i * (Hpi n m x * cutPi n k x)
        - fderiv ℝ (fun y => Hpi n m y * cutPi n k y) x (Pi.single i (1:ℝ))
      = Hpi n (succAt m i) x * cutPi n k x
        - Hpi n m x * fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)) := by
  rw [fderiv_fun_mul (differentiableAt_Hpi n m x) (cutPi_differentiableAt n k x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← Hpi_succ n m i x]
  ring

/-! ## 4. The three limits, and the containment -/

/-- **THE CONVERSE, IN n DIMENSIONS.** Testing against `Cc^∞(ℝⁿ)` forces
    the pairing at every Hermite product. -/
theorem steinPairPi_of_smoothSteinPairPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPi n f g) :
    SteinPairPi n f g := by
  obtain ⟨hf, hg, hpair⟩ := h
  obtain ⟨D, hD0, hD⟩ := W6Converse.exists_deriv_bound
  refine ⟨hf, hg, fun i m => ?_⟩
  -- the goal, with the recursion applied on the left
  have hgoal : (∫ x, f x * (x i * Hpi n m x
        - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))) ∂gaussPi n)
      = ∫ x, f x * Hpi n (succAt m i) x ∂gaussPi n :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [Hpi_succ])
  rw [hgoal]
  -- the three sequences of integrals
  have hIa : ∀ k : ℕ,
      Integrable (fun x => f x * (Hpi n (succAt m i) x * cutPi n k x)) (gaussPi n) :=
    fun k => integrable_bddPi n hf (succAt m i) (cutPi_continuous n k) (cutPi_abs_le_one n k)
  have hIb : ∀ k : ℕ, Integrable
      (fun x => f x * (Hpi n m x * fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ))))
      (gaussPi n) :=
    fun k => integrable_bddPi n hf m (continuous_fderiv_cutPi n k i)
      (fderiv_cutPi_abs_le hD n k i)
  -- the identity supplied by the hypothesis, rearranged
  have hkey : ∀ k : ℕ,
      (∫ x, f x * (Hpi n (succAt m i) x * cutPi n k x) ∂gaussPi n)
        - ∫ x, f x * (Hpi n m x * fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)))
            ∂gaussPi n
      = ∫ x, g i x * (Hpi n m x * cutPi n k x) ∂gaussPi n := by
    intro k
    have hp := hpair i (fun y => Hpi n m y * cutPi n k y) (testfPi_smooth n m k)
      (testfPi_support n m k)
    have hLHS : (∫ x, f x * (x i * (Hpi n m x * cutPi n k x)
          - fderiv ℝ (fun y => Hpi n m y * cutPi n k y) x (Pi.single i (1:ℝ)))
            ∂gaussPi n)
        = (∫ x, f x * (Hpi n (succAt m i) x * cutPi n k x) ∂gaussPi n)
          - ∫ x, f x * (Hpi n m x * fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)))
              ∂gaussPi n := by
      rw [← integral_sub (hIa k) (hIb k)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [stein_integrand_cut n m k i x]
      ring
    rw [← hLHS]
    exact hp
  -- limit A: the cutoff disappears from the raised-index pairing
  have hlimA : Tendsto
      (fun k : ℕ => ∫ x, f x * (Hpi n (succAt m i) x * cutPi n k x) ∂gaussPi n)
      atTop (𝓝 (∫ x, f x * Hpi n (succAt m i) x ∂gaussPi n)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |f x * Hpi n (succAt m i) x|)
      (fun k => (hIa k).aestronglyMeasurable)
      (MemLp.integrable_mul hf (Hpi_memLp n (succAt m i))).abs (fun k => ?_) ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [cutPi_abs_le_one n k x, abs_nonneg (f x),
        abs_nonneg (Hpi n (succAt m i) x),
        mul_nonneg (abs_nonneg (f x)) (abs_nonneg (Hpi n (succAt m i) x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := f x * Hpi n (succAt m i) x)).mul
        (cutPi_tendsto n x)
      simpa [mul_assoc] using this
  -- limit B: the error term dies, at rate `1/k`
  have hlimB : Tendsto
      (fun k : ℕ => ∫ x, f x * (Hpi n m x * fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ)))
        ∂gaussPi n) atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _x : Fin n → ℝ, (0 : ℝ) ∂gaussPi n := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence
      (fun x => D * |f x * Hpi n m x|)
      (fun k => (hIb k).aestronglyMeasurable)
      ((MemLp.integrable_mul hf (Hpi_memLp n m)).abs.const_mul D) (fun k => ?_) ?_
    · filter_upwards with x
      have hb : |fderiv ℝ (cutPi n k) x (Pi.single i (1:ℝ))| ≤ D := by
        refine (fderiv_cutPi_abs_le hD n k i x).trans ?_
        rw [div_le_iff₀ (W6Converse.npos k)]
        nlinarith [hD0, W6Converse.npos k]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [hb, abs_nonneg (f x), abs_nonneg (Hpi n m x),
        mul_nonneg (abs_nonneg (f x)) (abs_nonneg (Hpi n m x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := f x * Hpi n m x)).mul
        (tendsto_fderiv_cutPi n i x)
      simpa [mul_assoc] using this
  -- limit C: the cutoff disappears from the gradient pairing
  have hlimC : Tendsto
      (fun k : ℕ => ∫ x, g i x * (Hpi n m x * cutPi n k x) ∂gaussPi n) atTop
      (𝓝 (∫ x, g i x * Hpi n m x ∂gaussPi n)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g i x * Hpi n m x|)
      (fun k => (integrable_bddPi n (hg i) m (cutPi_continuous n k)
        (cutPi_abs_le_one n k)).aestronglyMeasurable)
      (MemLp.integrable_mul (hg i) (Hpi_memLp n m)).abs (fun k => ?_) ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [cutPi_abs_le_one n k x, abs_nonneg (g i x), abs_nonneg (Hpi n m x),
        mul_nonneg (abs_nonneg (g i x)) (abs_nonneg (Hpi n m x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := g i x * Hpi n m x)).mul (cutPi_tendsto n x)
      simpa [mul_assoc] using this
  -- pass to the limit
  have hlimLHS := hlimA.sub hlimB
  rw [sub_zero] at hlimLHS
  exact tendsto_nhds_unique (by simpa only [hkey] using hlimLHS) hlimC

/-- Composed with stair N5: the Lebesgue-weak-derivative class injects into
    the Hermite-tested class. -/
theorem steinPairPi_of_sobolevWeakPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SobolevWeakPi n f g) :
    SteinPairPi n f g :=
  steinPairPi_of_smoothSteinPairPi n
    ((smoothSteinPairPi_iff_sobolevWeakPi n f g).mpr h)

/-! ## 5. The payoff: Poincaré on the textbook space -/

/-- **THE n-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY, ON THE TEXTBOOK
    SOBOLEV SPACE.** The hypothesis is the Lebesgue weak-derivative
    definition — `∫ f·∂ᵢψ dx = −∫ gᵢ·ψ dx` for every `ψ ∈ Cc^∞(ℝⁿ)`, both
    `f` and each `gᵢ` in `L²(γⁿ)` — and nothing else. No Hermite
    coefficient and no polynomial appears in the statement. -/
theorem poincare_sobolevWeakPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SobolevWeakPi n f g) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      ≤ ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPi n :=
  poincare_steinPi n (steinPairPi_of_sobolevWeakPi n h)

/-- The same, phrased on the `Cc^∞`-tested class. -/
theorem poincare_smoothSteinPairPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPi n f g) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      ≤ ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPi n :=
  poincare_steinPi n (steinPairPi_of_smoothSteinPairPi n h)

/-! ## 6. Review round 58 — the ways this could be hollow

**"§5 could be a theorem about constants."** `TextbookSobolevPi.const_mem`
is the only member of `SobolevWeakPi` the estate had, and on a constant both
sides of Poincaré are `0`. That is a real objection and the rest of this
section answers it by producing a non-constant member — from the LEBESGUE
definition, not by importing one through §4, which points the wrong way.

**"The cutoff family could be degenerate."** Inherited from
`W6Converse.chiF_eq_one`: `χ = 1` on `[-1,1]`, so `cutPi_eventually_one`
is not vacuous, and limit A consumes it. A degenerate `χ` would break the
proof rather than cheapen it.

**"The containment could be vacuous — nothing might be a
`SmoothSteinPairPi`."** `TextbookSobolevPi.const_mem_stein` and the
coordinate witness below are both members, so §4 has something to act on.

**"The coordinate witness might be reached by going round through §4."**
It is not, and that would be circular for this purpose: §4 points from the
textbook class INTO the Hermite class, so it cannot put anything into the
textbook class. `coord_sobolevWeakPi` is proved from the Lebesgue
definition, out of `TextbookSobolevPi.integral_partial_eq_zero` and the
product rule, with no Gaussian measure in the pairing at all. The estate's
`HermitePiPoincare.coord_mem` — the same function, on the Hermite side —
is not used and could not have been.
-/

/-- The coordinate function is `L²(γⁿ)` — it is the Hermite product at the
    multi-index `eᵢ`, by `HermitePiPoincare.Hpi_single_eq_coord`. -/
theorem memLp_coord (n : ℕ) (i : Fin n) :
    MemLp (fun x : Fin n → ℝ => x i) 2 (gaussPi n) := by
  have heq : (fun x : Fin n → ℝ => x i) = Hpi n (Pi.single i 1) :=
    funext fun x => (Hpi_single_eq_coord n i x).symm
  rw [heq]
  exact Hpi_memLp n (Pi.single i 1)

/-- `∂ⱼ(xᵢ) = δᵢⱼ`, as a directional derivative against `Pi.single j 1`. -/
theorem fderiv_coord (n : ℕ) (i j : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => y i) x (Pi.single j (1:ℝ))
      = if i = j then (1:ℝ) else 0 := by
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y i) x
      = (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.fderiv
  rw [hproj]
  simp [Pi.single_apply]

/-- **A NON-CONSTANT MEMBER OF THE TEXTBOOK CLASS.** The coordinate function
    `x ↦ xᵢ` has weak gradient `eᵢ`. Proved from the Lebesgue definition
    directly: apply `∫ ∂ⱼΨ dx = 0` to `Ψ = xᵢ·ψ` and read off the product
    rule. No Gaussian measure enters the pairing. -/
theorem coord_sobolevWeakPi (n : ℕ) (i : Fin n) :
    SobolevWeakPi n (fun x => x i) (fun j _ => if j = i then (1:ℝ) else 0) := by
  refine ⟨memLp_coord n i, fun j => memLp_const _, fun j ψ hψ hcψ => ?_⟩
  -- the auxiliary test function `xᵢ·ψ`
  have hΨs : ContDiff ℝ (⊤ : ℕ∞) fun y : Fin n → ℝ => y i * ψ y :=
    (contDiff_apply ℝ ℝ i).mul hψ
  have hΨc : HasCompactSupport fun y : Fin n → ℝ => y i * ψ y := hcψ.mul_left
  have hkey := integral_partial_eq_zero n hΨs hΨc j
  -- the product rule, pointwise
  have hpt : ∀ x : Fin n → ℝ,
      fderiv ℝ (fun y : Fin n → ℝ => y i * ψ y) x (Pi.single j (1:ℝ))
        = (if j = i then (1:ℝ) else 0) * ψ x
          + x i * fderiv ℝ ψ x (Pi.single j (1:ℝ)) := by
    intro x
    have hcd : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).differentiableAt
    rw [fderiv_fun_mul hcd ((hψ.differentiable (by simp)).differentiableAt)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_coord n i j x]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij.symm]; ring
    · rw [if_neg hij, if_neg (Ne.symm hij)]; ring
  -- split the integral: both summands are continuous with compact support
  have hi1 : Integrable
      (fun x : Fin n → ℝ => (if j = i then (1:ℝ) else 0) * ψ x) volume :=
    (continuous_const.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hi2 : Integrable
      (fun x : Fin n → ℝ => x i * fderiv ℝ ψ x (Pi.single j (1:ℝ))) volume :=
    (((continuous_apply i).mul (continuous_partial n hψ j)).integrable_of_hasCompactSupport
      (hasCompactSupport_partial n hcψ j).mul_left)
  have hsplit : (∫ x : Fin n → ℝ,
        fderiv ℝ (fun y : Fin n → ℝ => y i * ψ y) x (Pi.single j (1:ℝ)))
      = (∫ x : Fin n → ℝ, (if j = i then (1:ℝ) else 0) * ψ x)
        + ∫ x : Fin n → ℝ, x i * fderiv ℝ ψ x (Pi.single j (1:ℝ)) := by
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hsplit] at hkey
  linarith [hkey]

/-- **AND POINCARÉ RUNS ON IT, WITH BOTH SIDES EQUAL TO `1`.** The variance
    of a coordinate under `γⁿ` is `1`; its weak gradient is a unit vector,
    so the right-hand side is `1` too. The inequality of §5 is therefore
    sharp, and attained at a non-constant function reached entirely through
    the Lebesgue definition. -/
theorem poincare_coord_textbook (n : ℕ) (i : Fin n) :
    (∫ x, x i * x i ∂gaussPi n) - (∫ x : Fin n → ℝ, x i ∂gaussPi n) ^ 2 = 1
      ∧ (∑ j : Fin n, ∫ _x : Fin n → ℝ,
            (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0)
              ∂gaussPi n) = 1
      ∧ (∫ x, x i * x i ∂gaussPi n) - (∫ x : Fin n → ℝ, x i ∂gaussPi n) ^ 2
          ≤ ∑ j : Fin n, ∫ _x : Fin n → ℝ,
              (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0)
                ∂gaussPi n := by
  classical
  have hvar : (∫ x, x i * x i ∂gaussPi n) - (∫ x : Fin n → ℝ, x i ∂gaussPi n) ^ 2 = 1 := by
    have heq : (fun x : Fin n → ℝ => x i) = Hpi n (Pi.single i 1) :=
      funext fun x => (Hpi_single_eq_coord n i x).symm
    have h1 : (∫ x, x i * x i ∂gaussPi n)
        = ∫ x, Hpi n (Pi.single i 1) x * Hpi n (Pi.single i 1) x ∂gaussPi n := by
      simp only [← Hpi_single_eq_coord n i]
    have h2 : (∫ x : Fin n → ℝ, x i ∂gaussPi n)
        = ∫ x, Hpi n (Pi.single i 1) x ∂gaussPi n := by
      simp only [← Hpi_single_eq_coord n i]
    rw [h1, h2]
    exact coord_var n i
  have hgrad : (∑ j : Fin n, ∫ _x : Fin n → ℝ,
      (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0) ∂gaussPi n) = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      simp
    · intro j _ hj
      rw [if_neg hj]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact ⟨hvar, hgrad, by
    have := poincare_sobolevWeakPi n (coord_sobolevWeakPi n i)
    simpa using this⟩

end

end W6ConversePi
