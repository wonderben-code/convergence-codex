/-
  AbsSteinWitness: (|x|, sgn) is a Stein Pair — Strictness at the L²-Class Level
  ==============================================================================

  The fJump witness (`PoincareSteinClass.stein_strict`) certified that the
  Stein class's HYPOTHESES reach strictly further than any pointwise-
  derivative hypothesis — but fJump is a.e. equal to the identity, so as
  an L² element it is nothing new. Round 6's reviewer sketched the
  stronger witness and the watchlist mapped it; this file delivers it:
  (|x|, sgn) is a Stein pair, and NO everywhere-differentiable function
  is even a.e.-equal to |x| — so the Stein class strictly exceeds the
  embedded everywhere-differentiable class AT THE LEVEL OF L² CLASSES,
  one level up from fJump.

  The route is the classical smoothing argument, done honestly:
  f_ε(x) = √(x² + ε²) is everywhere differentiable with |f_ε′| ≤ 1, so
  `stein_general` gives the Gaussian IBP pairing for every ε ≠ 0; both
  sides converge as ε = 1/(n+1) → 0 by dominated convergence (the
  dominating functions are polynomials times constants, integrable
  against the Gaussian), and the limits are the (|x|, sgn) pairing.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `sgn` — the sign function as an explicit piecewise definition (−1,
     0, +1), measurable, bounded by 1. The value at 0 is irrelevant to
     every integral statement (a null point).
  2. `smooth_hasDerivAt`, `smooth_le`, `smooth_deriv_le` — the smoothing
     family: √(x²+ε²) is differentiable with derivative x/√(x²+ε²),
     value ≤ (1+|ε|)(1+x²), derivative bounded by 1.
  3. `tendsto_smooth`, `tendsto_smooth_deriv` — pointwise limits: values
     → |x| everywhere; derivatives → sgn x for x ≠ 0 (hence γ-a.e.).
  4. **`steinPair_abs`** — (|x|, sgn) IS a Stein pair: membership by
     polynomial growth, the pairing by dominated convergence through
     the smoothing family.
  5. **`abs_not_ae_differentiable`** — no everywhere-differentiable
     g : ℝ → ℝ is a.e.-equal to |x|: the Gaussian has full support, so
     a.e.-equality of continuous functions is equality, and |x| is not
     differentiable at 0 (`not_differentiableAt_abs_zero`). This is the
     L²-CLASS-level unreachability fJump could not give.
  6. **`stein_strict_classes`** — the certificate: membership,
     class-level unreachability, and the Poincaré conclusion
     Var(|x|) ≤ ∫ sgn² dγ in one statement.

  NOT proven here: the comparison with the Cc^∞-defined W^{1,2}(γ)
  stays OPEN exactly as before — |x| lies in that Sobolev space too, so
  this witness says nothing about the containment question, and none is
  claimed. One dimension, variance one (the σ-transport of this witness
  is routine via `PoincareSteinScaled` and not needed by any claim).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import PoincareSteinClass
import Mathlib.Analysis.Calculus.Deriv.Abs

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AbsSteinWitness

open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
  PoincareBeyondPolynomials PoincareSteinClass

/-! ## 1. The sign function and polynomial integrability -/

/-- The sign function, explicit and self-contained. -/
def sgn (x : ℝ) : ℝ := if x < 0 then -1 else if 0 < x then 1 else 0

theorem abs_sgn_le (x : ℝ) : |sgn x| ≤ 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem measurable_sgn : Measurable sgn := by
  unfold sgn
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

theorem div_abs_eq_sgn {x : ℝ} (hx : x ≠ 0) : x / |x| = sgn x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h]
    unfold sgn
    rw [if_pos h]
    field_simp
  · rw [abs_of_pos h]
    unfold sgn
    rw [if_neg (not_lt.mpr h.le), if_pos h]
    field_simp

/-- Polynomial evaluations have polynomial growth (with the sum of
    absolute coefficients as the constant). -/
theorem abs_eval_le_polyGrowth (q : ℝ[X]) (x : ℝ) :
    |q.eval x| ≤ (∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i|)
      * (1 + x ^ 2) ^ q.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc |∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1),
          |q.coeff i| * (1 + x ^ 2) ^ q.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_pow]
        calc |x| ^ i ≤ (1 + x ^ 2) ^ i :=
              pow_le_pow_left₀ (abs_nonneg x)
                (by nlinarith [sq_nonneg (|x| - 1), sq_abs x]) i
          _ ≤ (1 + x ^ 2) ^ q.natDegree :=
              pow_le_pow_right₀ (by nlinarith [sq_nonneg x])
                (Finset.mem_range_succ_iff.mp hi)
    _ = _ := by rw [← Finset.sum_mul]

/-- Polynomial growth gives Gaussian integrability (via L² membership;
    the Gaussian is a probability measure). -/
theorem integrable_polyGrowth {f : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable f gauss)
    {C : ℝ} {m : ℕ} (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m) :
    Integrable f gauss :=
  (memLp_of_polyGrowth hmeas hb).integrable one_le_two

/-! ## 2. The smoothing family -/

theorem smooth_hasDerivAt {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (y ^ 2 + ε ^ 2))
      (x / Real.sqrt (x ^ 2 + ε ^ 2)) x := by
  have hpos : 0 < x ^ 2 + ε ^ 2 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (ε ^ 2)
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp x hinner
  convert hs using 1
  have hsq : Real.sqrt (x ^ 2 + ε ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  field_simp

theorem smooth_le (ε x : ℝ) :
    Real.sqrt (x ^ 2 + ε ^ 2) ≤ (1 + |ε|) * (1 + x ^ 2) := by
  have h1 : Real.sqrt (x ^ 2 + ε ^ 2) ≤ |x| + |ε| := by
    have hle : x ^ 2 + ε ^ 2 ≤ (|x| + |ε|) ^ 2 := by
      nlinarith [abs_nonneg x, abs_nonneg ε, sq_abs x, sq_abs ε,
        mul_nonneg (abs_nonneg x) (abs_nonneg ε)]
    calc Real.sqrt (x ^ 2 + ε ^ 2) ≤ Real.sqrt ((|x| + |ε|) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = |x| + |ε| := Real.sqrt_sq (by positivity)
  have h2 : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  nlinarith [abs_nonneg ε, sq_nonneg x]

theorem smooth_deriv_le (ε x : ℝ) : |x / Real.sqrt (x ^ 2 + ε ^ 2)| ≤ 1 := by
  rcases eq_or_ne (x ^ 2 + ε ^ 2) 0 with h0 | h0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg ε]
    simp [hx]
  · have hpos : 0 < x ^ 2 + ε ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
      div_le_one (Real.sqrt_pos.mpr hpos)]
    calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
      _ ≤ Real.sqrt (x ^ 2 + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

/-! ## 3. The pointwise limits along ε = 1/(n+1) -/

theorem tendsto_eps :
    Tendsto (fun n : ℕ => (1 / (n + 1) : ℝ)) atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_smooth (x : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2))
      atTop (nhds |x|) := by
  have h1 : Tendsto (fun n : ℕ => x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)
      atTop (nhds (x ^ 2)) := by
    have hsq : Tendsto (fun n : ℕ => (1 / (n + 1) : ℝ) ^ 2)
        atTop (nhds 0) := by
      have := tendsto_eps.pow 2
      simpa using this
    simpa using tendsto_const_nhds.add hsq
  have h2 := (Real.continuous_sqrt.tendsto (x ^ 2)).comp h1
  simpa [Function.comp, Real.sqrt_sq_eq_abs] using h2

theorem tendsto_smooth_deriv {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2))
      atTop (nhds (sgn x)) := by
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hconst : Tendsto (fun _ : ℕ => x) atTop (nhds x) := tendsto_const_nhds
  have h2 := hconst.div (tendsto_smooth x) habs
  rwa [div_abs_eq_sgn hx] at h2

/-! ## 4. The pairing, by dominated convergence -/

/-- **(|x|, sgn) is a Stein pair.** Membership by polynomial growth;
    the pairing as the ε → 0 limit of `stein_general` applied to the
    smoothing family, both sides controlled by dominated convergence. -/
theorem steinPair_abs : SteinPair (fun x => |x|) sgn := by
  have habs_meas : AEStronglyMeasurable (fun x : ℝ => |x|) gauss :=
    continuous_abs.aestronglyMeasurable
  have habs_b : ∀ x : ℝ, |(fun y : ℝ => |y|) x| ≤ 1 * (1 + x ^ 2) ^ 1 := by
    intro x
    simp only [abs_abs, one_mul, pow_one]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hsgn_b : ∀ x : ℝ, |sgn x| ≤ 1 * (1 + x ^ 2) ^ 0 := by
    intro x
    simpa using abs_sgn_le x
  refine ⟨memLp_of_polyGrowth habs_meas habs_b,
    memLp_of_polyGrowth measurable_sgn.aestronglyMeasurable hsgn_b,
    fun q => ?_⟩
  set r : ℝ[X] := X * q - derivative q with hrdef
  -- the smoothed pairings
  have hpair : ∀ n : ℕ,
      ∫ x, (x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)) * q.eval x ∂gauss
        = ∫ x, Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2) * r.eval x ∂gauss := by
    intro n
    have hεpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hderiv := smooth_hasDerivAt (ε := 1 / (n + 1)) hεpos.ne'
    have hb : ∀ x : ℝ, |Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)|
        ≤ (1 + |(1 / (n + 1) : ℝ)|) * (1 + x ^ 2) ^ 1 := by
      intro x
      rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_one]
      exact smooth_le _ x
    have hb' : ∀ x : ℝ, |x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)|
        ≤ (1 + |(1 / (n + 1) : ℝ)|) * (1 + x ^ 2) ^ 1 := by
      intro x
      calc |x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)| ≤ 1 :=
            smooth_deriv_le _ x
        _ ≤ (1 + |(1 / (n + 1) : ℝ)|) * (1 + x ^ 2) ^ 1 := by
            have h1 : (0 : ℝ) ≤ |(1 / (n + 1) : ℝ)| := abs_nonneg _
            nlinarith [sq_nonneg x]
    exact stein_general hderiv hb hb' q
  -- limit of the derivative side
  have hL : Tendsto (fun n : ℕ =>
      ∫ x, (x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)) * q.eval x ∂gauss)
      atTop (nhds (∫ x, sgn x * q.eval x ∂gauss)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |q.eval x|) ?_ ?_ ?_ ?_
    · intro n
      exact ((continuous_id.div
        (Real.continuous_sqrt.comp (by continuity))
        (fun x => (Real.sqrt_pos.mpr (by positivity)).ne')).mul
        q.continuous).aestronglyMeasurable
    · exact (integrable_polyGrowth
        (Polynomial.continuous q).aestronglyMeasurable
        (fun x => abs_eval_le_polyGrowth q x)).abs
    · intro n
      refine Eventually.of_forall fun x => ?_
      simp only []
      rw [Real.norm_eq_abs, abs_mul]
      calc |x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)| * |q.eval x|
          ≤ 1 * |q.eval x| :=
            mul_le_mul_of_nonneg_right (smooth_deriv_le _ x) (abs_nonneg _)
        _ = |q.eval x| := one_mul _
    · have hna : NoAtoms (gauss : Measure ℝ) := noAtoms_gaussianReal one_ne_zero
      have h0 : (gauss : Measure ℝ) {0} = 0 := measure_singleton 0
      have hmem : {(0 : ℝ)}ᶜ ∈ ae gauss := by
        rw [mem_ae_iff, compl_compl]
        exact h0
      filter_upwards [hmem] with x hx
      exact (tendsto_smooth_deriv
        (Set.mem_compl_singleton_iff.mp hx)).mul tendsto_const_nhds
  -- limit of the function side
  have hR : Tendsto (fun n : ℕ =>
      ∫ x, Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2) * r.eval x ∂gauss)
      atTop (nhds (∫ x, |x| * r.eval x ∂gauss)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * (1 + x ^ 2) * |r.eval x|) ?_ ?_ ?_ ?_
    · intro n
      exact ((Real.continuous_sqrt.comp (by continuity)).mul
        r.continuous).aestronglyMeasurable
    · have hmeas : AEStronglyMeasurable
          (fun x : ℝ => 2 * (1 + x ^ 2) * |r.eval x|) gauss := by
        exact ((continuous_const.mul (by continuity)).mul
          (continuous_abs.comp r.continuous)).aestronglyMeasurable
      refine integrable_polyGrowth hmeas
        (C := 2 * (∑ i ∈ Finset.range (r.natDegree + 1), |r.coeff i|))
        (m := r.natDegree + 1) fun x => ?_
      have hq := abs_eval_le_polyGrowth r x
      have hnn : (0 : ℝ) ≤ 2 * (1 + x ^ 2) * |r.eval x| := by positivity
      rw [abs_of_nonneg hnn]
      calc 2 * (1 + x ^ 2) * |r.eval x|
          ≤ 2 * (1 + x ^ 2) *
              ((∑ i ∈ Finset.range (r.natDegree + 1), |r.coeff i|)
                * (1 + x ^ 2) ^ r.natDegree) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = 2 * (∑ i ∈ Finset.range (r.natDegree + 1), |r.coeff i|)
              * (1 + x ^ 2) ^ (r.natDegree + 1) := by
            ring
    · intro n
      refine Eventually.of_forall fun x => ?_
      simp only []
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hε1 : |(1 / (n + 1) : ℝ)| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2) * |r.eval x|
          ≤ (1 + |(1 / (n + 1) : ℝ)|) * (1 + x ^ 2) * |r.eval x| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            simpa [pow_one] using smooth_le (1 / (n + 1) : ℝ) x
        _ ≤ 2 * (1 + x ^ 2) * |r.eval x| := by
            have h1 : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
            nlinarith [abs_nonneg (r.eval x),
              mul_nonneg h1 (abs_nonneg (r.eval x))]
    · refine Eventually.of_forall fun x => ?_
      exact (tendsto_smooth x).mul tendsto_const_nhds
  -- the two limits agree
  have hR' : Tendsto (fun n : ℕ =>
      ∫ x, (x / Real.sqrt (x ^ 2 + (1 / (n + 1) : ℝ) ^ 2)) * q.eval x ∂gauss)
      atTop (nhds (∫ x, |x| * r.eval x ∂gauss)) := by
    refine hR.congr fun n => (hpair n).symm
  exact tendsto_nhds_unique hL hR'

/-! ## 5. Class-level unreachability -/

/-- The Gaussian charges every nonempty open set: full support. -/
instance : (gauss : Measure ℝ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have hv : (volume : Measure ℝ) U = 0 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  exact (hU.measure_pos volume hne).ne' hv

/-- **No everywhere-differentiable function is a.e.-equal to |x|**: by
    full support, a.e.-equality of continuous functions is equality —
    and |x| is not differentiable at 0. Unreachability at the level of
    L² CLASSES, one level beyond the fJump witness. -/
theorem abs_not_ae_differentiable (g : ℝ → ℝ)
    (hdiff : ∀ x, DifferentiableAt ℝ g x) :
    ¬ (g =ᵐ[gauss] fun x => |x|) := by
  intro hae
  have hgc : Continuous g := by
    have : Differentiable ℝ g := fun x => hdiff x
    exact this.continuous
  have heq : g = fun x => |x| :=
    (Continuous.ae_eq_iff_eq gauss hgc continuous_abs).mp hae
  have h0 := hdiff 0
  rw [heq] at h0
  exact not_differentiableAt_abs_zero h0

/-- **The class-level strictness certificate**: (|x|, sgn) is in the
    Stein class, no everywhere-differentiable function represents its
    L² class, and the Poincaré conclusion holds for it. -/
theorem stein_strict_classes :
    SteinPair (fun x => |x|) sgn
      ∧ (∀ g : ℝ → ℝ, (∀ x, DifferentiableAt ℝ g x)
          → ¬ (g =ᵐ[gauss] fun x => |x|))
      ∧ ((∫ x, |x| ^ 2 ∂gauss) - (∫ x, |x| ∂gauss) ^ 2
          ≤ ∫ x, sgn x ^ 2 ∂gauss) :=
  ⟨steinPair_abs, abs_not_ae_differentiable, poincare_stein steinPair_abs⟩

end AbsSteinWitness
