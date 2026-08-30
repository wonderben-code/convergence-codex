/-
  W6Converse.lean — the other containment, and with it WALLS W6.

  WHY. `SteinSmoothTest` proved the Stein class contained in the
  Cc^∞-tested class and named the missing direction as `W6Converse`, with
  its route written out: cut a polynomial `q` down to `q·χ(·/R)`, which IS
  a legal Cc^∞ test function, and let `R → ∞`. Three limits, one of which
  is the error term `∫ f·q·χ_R′ dγ`, bounded by `‖χ′‖_∞/R · ‖f·q‖_{L¹(γ)}`
  and therefore zero in the limit.

  WHAT THIS FILE PROVES:
  1. **`steinPair_of_smoothSteinPair`** — the converse. Testing against
     `Cc^∞` forces the pairing at every polynomial.
  2. **`stein_iff_smooth`** — and therefore **the two classes are equal.**
     `W6Converse` is discharged; `SteinSmoothTest.w6_of_converse` becomes
     unconditional.
  3. **`w6_answered`** — stated as the answer to the question WALLS W6
     asks, in the form the wall asks it: the Stein class does not merely
     sit inside the Cc^∞-tested Gaussian Sobolev class, it IS that class.

  WHAT THIS DOES NOT DO, and it is the same caveat as before, still
  flagged rather than absorbed: what is proved equal to the Stein class is
  the **Cc^∞-tested GAUSSIAN pairing**. That this coincides with the
  textbook LEBESGUE-weak-derivative Sobolev space is the substitution
  `ψ = φ·ρ`, written out in `SteinSmoothTest`'s header, recorded there as
  `TextbookBridge`, and **still not machine-checked**. W6 as the estate
  phrased it is answered; W6 as a reader of a textbook would phrase it
  needs that one further bridge, and this file does not build it.

  ⚠ **«STILL NOT MACHINE-CHECKED» IS FALSE AND THE PARAGRAPH IS KEPT PER
  `ERRATUM 94`.** `TextbookSobolev.textbookBridge : SteinSmoothTest
  .TextbookBridge` proves it, and that file's own header opens by saying
  so. **The last sentence stands as written of THIS file** — it does not
  build the bridge — and what is false is the claim about the estate.
  `ERRATUM 230`'s fifteenth instance, found by reading `WALLS` §W6's one
  unread status claim, which carries the same stale sentence.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SteinSmoothTest
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

namespace W6Converse

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass SteinCoefficients HermiteHilbertBasis SteinSmoothTest

noncomputable section

/-! ## 0. Polynomials are smooth

Needed because the test functions below are `q·χ_R` and the definition of
`SmoothSteinPair` asks for `Cc^∞`. Mathlib has `Polynomial.continuous` and
`Polynomial.hasDerivAt` but no `ContDiff` statement; this is the induction.

**⚠ THAT LAST CLAUSE IS FALSE AND WAS FALSE WHEN WRITTEN. Kept per `ERRATUM 94`; `ERRATUM 354`
records it.** `Polynomial.contDiff_aeval` is in the **pinned** Mathlib —
`Mathlib/Analysis/Calculus/ContDiff/Polynomial.lean:22`, `ContDiff 𝕜 n (fun x ↦ f.aeval x)` at every
`WithTop ℕ∞` order — and the manifest pinning it is dated **2026-05-07**, three months before this
file. Over `ℝ` it IS this statement, `aeval` and `eval` agreeing by
`Polynomial.coe_aeval_eq_eval`. **The induction below was a re-proof**, by the same
`Polynomial.induction_on'` with the same two cases as Mathlib's.
**REPAIRED BY DELETING THE PROOF, NOT THE THEOREM**: the name has a consumer (`testf_smooth`), so
it stays and is now one line off Mathlib. `ERRATUM 336`'s class, found by auditing this estate's
`Mathlib has no …` claims against the pinned tree.
**AND THE COST OF THE DUPLICATE WAS ONE `import` LINE, WHICH IS WORTH STATING EXACTLY.** The lemma
was not in this file's import closure, so `exact?` and `simp` could not have found it; it is in the
pinned tree and reachable by importing `Mathlib.Analysis.Calculus.ContDiff.Polynomial`, which this
file now does. **That makes the claim false about Mathlib and true about what was in scope** — a
distinction the sentence did not draw, and the reason `ERRATUM 42`'s rule is to grep the tree
rather than to trust a failed tactic.
-/

theorem polynomial_contDiff (q : ℝ[X]) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : ℝ => q.eval x := by
  simpa [Polynomial.coe_aeval_eq_eval] using Polynomial.contDiff_aeval (𝕜 := ℝ) q n

/-- The original hand induction, kept as a `private` witness that the two statements really are the
same one, since the repair above is otherwise unfalsifiable prose. -/
private theorem polynomial_contDiff_by_induction (q : ℝ[X]) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : ℝ => q.eval x := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [Polynomial.eval_add]
      exact hp.add hr
  | monomial k a =>
      simp only [Polynomial.eval_monomial]
      exact contDiff_const.mul (contDiff_id.pow k)

/-! ## 1. The cutoff family

A single bump, rescaled. `χ = 1` on `[-1,1]` and vanishes outside
`[-2,2]`; `χ_n(x) = χ(x/(n+1))`. The only quantitative fact needed is that
`χ_n′` is uniformly `O(1/n)`, which is where the error term dies.
-/

/-- The fixed bump. -/
def chi : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- Its underlying function. -/
def chiF : ℝ → ℝ := chi

theorem chiF_smooth : ContDiff ℝ (⊤ : ℕ∞) chiF := ContDiffBump.contDiff _

theorem chiF_support : HasCompactSupport chiF := ContDiffBump.hasCompactSupport _

theorem chiF_nonneg (x : ℝ) : 0 ≤ chiF x := ContDiffBump.nonneg _

theorem chiF_le_one (x : ℝ) : chiF x ≤ 1 := ContDiffBump.le_one _

theorem chiF_abs_le_one (x : ℝ) : |chiF x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [chiF_nonneg x], chiF_le_one x⟩

theorem chiF_eq_one {x : ℝ} (hx : |x| ≤ 1) : chiF x = 1 := by
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hx

theorem chiF_differentiable : Differentiable ℝ chiF :=
  chiF_smooth.differentiable (by simp)

/-- `χ′` is bounded, being continuous with compact support. This constant
    is the whole quantitative content of the argument. -/
theorem exists_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv chiF x| ≤ D := by
  obtain ⟨D, hD⟩ := chiF_support.deriv.exists_bound_of_continuous
    (chiF_smooth.continuous_deriv (by exact_mod_cast le_top))
  refine ⟨D, ?_, fun x => ?_⟩
  · exact le_trans (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hD 0)
  · simpa [Real.norm_eq_abs] using hD x

/-- The rescaled cutoff. -/
def cut (n : ℕ) (x : ℝ) : ℝ := chiF (x / ((n : ℝ) + 1))

theorem npos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

theorem cut_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cut n) :=
  chiF_smooth.comp (contDiff_id.div_const _)

theorem cut_support (n : ℕ) : HasCompactSupport (cut n) := by
  have hc : (((n : ℝ) + 1)⁻¹) ≠ 0 := inv_ne_zero (ne_of_gt (npos n))
  have h := chiF_support.comp_smul hc
  have heq : (fun x : ℝ => chiF ((((n : ℝ) + 1)⁻¹) • x)) = cut n := by
    funext x
    simp [cut, smul_eq_mul, div_eq_inv_mul]
  rwa [heq] at h

theorem cut_abs_le_one (n : ℕ) (x : ℝ) : |cut n x| ≤ 1 := chiF_abs_le_one _

theorem cut_eventually_one (x : ℝ) : ∀ᶠ n : ℕ in atTop, cut n x = 1 := by
  have hev : ∀ᶠ n : ℕ in atTop, |x| ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
    have hcast : ((⌈|x|⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [Nat.le_ceil |x|]
  filter_upwards [hev] with n hn
  refine chiF_eq_one ?_
  rw [abs_div, abs_of_pos (npos n), div_le_one (npos n)]
  exact hn

theorem cut_tendsto (x : ℝ) : Tendsto (fun n : ℕ => cut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [cut_eventually_one x] with n hn
  exact hn.symm

theorem hasDerivAt_cut (n : ℕ) (x : ℝ) :
    HasDerivAt (cut n) (deriv chiF (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
    (hasDerivAt_id x).div_const _
  have houter : HasDerivAt chiF (deriv chiF (x / ((n : ℝ) + 1))) (x / ((n : ℝ) + 1)) :=
    (chiF_differentiable _).hasDerivAt
  have hcomp := houter.comp x hinner
  have heq : chiF ∘ (fun y : ℝ => y / ((n : ℝ) + 1)) = cut n := rfl
  rw [heq] at hcomp
  simpa [div_eq_mul_inv] using hcomp

theorem deriv_cut (n : ℕ) (x : ℝ) :
    deriv (cut n) x = deriv chiF (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) :=
  (hasDerivAt_cut n x).deriv

/-- **The quantitative heart**: the cutoff's derivative is `O(1/n)`,
    uniformly in `x`. -/
theorem deriv_cut_abs_le {D : ℝ} (hD : ∀ y, |deriv chiF y| ≤ D) (n : ℕ) (x : ℝ) :
    |deriv (cut n) x| ≤ D / ((n : ℝ) + 1) := by
  rw [deriv_cut, abs_div, abs_of_pos (npos n)]
  gcongr
  exact hD _

theorem tendsto_nat_add_one_atTop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem tendsto_deriv_cut (x : ℝ) :
    Tendsto (fun n : ℕ => deriv (cut n) x) atTop (𝓝 0) := by
  obtain ⟨D, _, hD⟩ := exists_deriv_bound
  refine squeeze_zero_norm (a := fun n : ℕ => D / ((n : ℝ) + 1)) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs]
    exact deriv_cut_abs_le hD n x
  · exact tendsto_const_nhds.div_atTop tendsto_nat_add_one_atTop

/-! ## 2. The test functions `q·χ_n` -/

def testf (q : ℝ[X]) (n : ℕ) (x : ℝ) : ℝ := q.eval x * cut n x

theorem testf_smooth (q : ℝ[X]) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (testf q n) :=
  (polynomial_contDiff q).mul (cut_smooth n)

theorem testf_support (q : ℝ[X]) (n : ℕ) : HasCompactSupport (testf q n) :=
  (cut_support n).mul_left

theorem hasDerivAt_testf (q : ℝ[X]) (n : ℕ) (x : ℝ) :
    HasDerivAt (testf q n)
      ((derivative q).eval x * cut n x + q.eval x * deriv (cut n) x) x := by
  have h := (q.hasDerivAt x).mul (hasDerivAt_cut n x)
  rw [deriv_cut n x]
  exact h

theorem deriv_testf (q : ℝ[X]) (n : ℕ) (x : ℝ) :
    deriv (testf q n) x
      = (derivative q).eval x * cut n x + q.eval x * deriv (cut n) x :=
  (hasDerivAt_testf q n x).deriv

/-! ## 3. Integrability, uniformly in the cutoff -/

theorem integrable_bdd {f : ℝ → ℝ} (hf : MemLp f 2 gauss) (P : ℝ[X]) {u : ℝ → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : ∀ x, |u x| ≤ M) :
    Integrable (fun x => f x * (P.eval x * u x)) gauss := by
  have hfP : Integrable (fun x => f x * P.eval x) gauss :=
    MemLp.integrable_mul hf (GaussianPoincare.memLp_polynomial_gaussianReal P 0 1)
  refine Integrable.mono' (hfP.abs.const_mul M) ?_ ?_
  · exact hf.aestronglyMeasurable.mul
      (((Polynomial.continuous P).mul hu).aestronglyMeasurable)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have h2 : (0 : ℝ) ≤ |f x| * |P.eval x| := by positivity
    calc |f x| * (|P.eval x| * |u x|) = (|f x| * |P.eval x|) * |u x| := by ring
      _ ≤ (|f x| * |P.eval x|) * M := mul_le_mul_of_nonneg_left (hM x) h2
      _ = M * (|f x| * |P.eval x|) := by ring

/-! ## 4. The three limits, and the converse -/

/-- **THE CONVERSE.** Testing against `Cc^∞` forces the pairing at every
    polynomial: the Cc^∞-tested class is contained in the Stein class. -/
theorem steinPair_of_smoothSteinPair {f g : ℝ → ℝ} (h : SmoothSteinPair f g) :
    SteinPair f g := by
  obtain ⟨hf, hg, hpair⟩ := h
  obtain ⟨D, hD0, hD⟩ := exists_deriv_bound
  refine ⟨hf, hg, fun q => ?_⟩
  set P : ℝ[X] := X * q - derivative q with hP
  -- the three sequences of integrals
  have hIa : ∀ n : ℕ, Integrable (fun x => f x * (P.eval x * cut n x)) gauss :=
    fun n => integrable_bdd hf P (cut_smooth n).continuous (cut_abs_le_one n)
  have hIb : ∀ n : ℕ, Integrable (fun x => f x * (q.eval x * deriv (cut n) x)) gauss :=
    fun n => integrable_bdd hf q
      ((cut_smooth n).continuous_deriv (by exact_mod_cast le_top))
      (deriv_cut_abs_le hD n)
  -- the identity supplied by the hypothesis, rearranged
  have hkey : ∀ n : ℕ,
      (∫ x, f x * (P.eval x * cut n x) ∂gauss)
        - ∫ x, f x * (q.eval x * deriv (cut n) x) ∂gauss
      = ∫ x, g x * (q.eval x * cut n x) ∂gauss := by
    intro n
    have hp := hpair (testf q n) (testf_smooth q n) (testf_support q n)
    have hLHS : ∫ x, f x * (x * testf q n x - deriv (testf q n) x) ∂gauss
        = (∫ x, f x * (P.eval x * cut n x) ∂gauss)
          - ∫ x, f x * (q.eval x * deriv (cut n) x) ∂gauss := by
      rw [← integral_sub (hIa n) (hIb n)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_testf, hP]
      simp only [testf, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
      ring
    have hRHS : ∫ x, g x * testf q n x ∂gauss
        = ∫ x, g x * (q.eval x * cut n x) ∂gauss := rfl
    rw [← hLHS, ← hRHS]
    exact hp
  -- limit A
  have hlimA : Tendsto (fun n : ℕ => ∫ x, f x * (P.eval x * cut n x) ∂gauss) atTop
      (𝓝 (∫ x, f x * P.eval x ∂gauss)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |f x * P.eval x|) (fun n => (hIa n).aestronglyMeasurable)
      (MemLp.integrable_mul hf
        (GaussianPoincare.memLp_polynomial_gaussianReal P 0 1)).abs
      (fun n => ?_) ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [cut_abs_le_one n x, abs_nonneg (f x), abs_nonneg (P.eval x),
        mul_nonneg (abs_nonneg (f x)) (abs_nonneg (P.eval x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := f x * P.eval x)).mul (cut_tendsto x)
      simpa [mul_assoc] using this
  -- limit B: the error term dies
  have hlimB : Tendsto (fun n : ℕ => ∫ x, f x * (q.eval x * deriv (cut n) x) ∂gauss)
      atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) ∂gauss := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence
      (fun x => D * |f x * q.eval x|) (fun n => (hIb n).aestronglyMeasurable)
      ((MemLp.integrable_mul hf
        (GaussianPoincare.memLp_polynomial_gaussianReal q 0 1)).abs.const_mul D)
      (fun n => ?_) ?_
    · filter_upwards with x
      have hb : |deriv (cut n) x| ≤ D := by
        refine (deriv_cut_abs_le hD n x).trans ?_
        rw [div_le_iff₀ (npos n)]
        nlinarith [hD0, npos n]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [hb, abs_nonneg (f x), abs_nonneg (q.eval x),
        mul_nonneg (abs_nonneg (f x)) (abs_nonneg (q.eval x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := f x * q.eval x)).mul (tendsto_deriv_cut x)
      simpa [mul_assoc] using this
  -- limit C
  have hlimC : Tendsto (fun n : ℕ => ∫ x, g x * (q.eval x * cut n x) ∂gauss) atTop
      (𝓝 (∫ x, g x * q.eval x ∂gauss)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x * q.eval x|)
      (fun n => (integrable_bdd hg q (cut_smooth n).continuous
        (cut_abs_le_one n)).aestronglyMeasurable)
      (MemLp.integrable_mul hg
        (GaussianPoincare.memLp_polynomial_gaussianReal q 0 1)).abs
      (fun n => ?_) ?_
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [cut_abs_le_one n x, abs_nonneg (g x), abs_nonneg (q.eval x),
        mul_nonneg (abs_nonneg (g x)) (abs_nonneg (q.eval x))]
    · filter_upwards with x
      have := (tendsto_const_nhds (x := g x * q.eval x)).mul (cut_tendsto x)
      simpa [mul_assoc] using this
  -- pass to the limit in hkey
  have hlimLHS := hlimA.sub hlimB
  rw [sub_zero] at hlimLHS
  have hfinal : (∫ x, f x * P.eval x ∂gauss) = ∫ x, g x * q.eval x ∂gauss :=
    tendsto_nhds_unique (by simpa only [hkey] using hlimLHS) hlimC
  exact hfinal.symm

/-! ## 5. WALLS W6, as the estate phrased it -/

/-- **THE TWO CLASSES COINCIDE.** -/
theorem stein_iff_smooth (f g : ℝ → ℝ) : SteinPair f g ↔ SmoothSteinPair f g :=
  ⟨smoothSteinPair_of_steinPair, steinPair_of_smoothSteinPair⟩

/-- `SteinSmoothTest.W6Converse`, discharged. -/
theorem w6Converse_holds : SteinSmoothTest.W6Converse :=
  fun _ _ h => steinPair_of_smoothSteinPair h

/-- **The answer, in the shape WALLS W6 asks the question.** Testing the
    Gaussian integration-by-parts pairing against polynomials and testing
    it against smooth compactly supported functions define the SAME class
    — even though the two test families are incomparable (no nonzero
    polynomial has compact support, no nonzero `Cc^∞` function is a
    polynomial; ERRATA 35). Neither containment is formal; both are
    theorems. -/
theorem w6_answered :
    (∀ f g : ℝ → ℝ, SteinPair f g ↔ SmoothSteinPair f g)
      ∧ SteinSmoothTest.W6Converse :=
  ⟨stein_iff_smooth, w6Converse_holds⟩

/-! ## 6. Review round 40 — the ways this could be hollow

**"The cutoff family could be degenerate."** If `χ` were identically zero
the test functions would all be zero and every limit would be `0 = 0`.
`chiF_eq_one` computes `χ = 1` on `[-1,1]`, and `cut_eventually_one` shows
each `χ_n` is eventually `1` at every fixed point — which is exactly what
limit A consumes, so a degenerate `χ` would break the proof rather than
cheapen it.

**"The equality could hold only for `q = 0`."** It holds for every
polynomial by construction, and §5's biconditional is inhabited: the sharp
witness `(X, 1)` and the non-differentiable witness `(|x|, sgn)` are both
Stein pairs, hence both Cc^∞ pairs, hence both sides are nonempty.

**"The converse might be vacuous because nothing is a `SmoothSteinPair`."**
`SteinSmoothTest.smoothSteinPair_id_one` and `abs_smoothSteinPair` are
witnesses, and now — with this file — every Stein pair is one and
conversely, so the class is exactly as large as the Stein class, which
`HermiteHilbertBasis.sobolevGauss_proper` proves is a PROPER subset of
`L²(γ)`. So the Cc^∞ class is proper too, which is the non-triviality
check with real content.
-/

/-- The Cc^∞-tested class is a PROPER subset of `L²(γ)` — inherited from
    the Stein class through §5, so the equality of classes is not an
    equality of everything. -/
theorem smooth_proper :
    ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ ¬ ∃ g : ℝ → ℝ, SmoothSteinPair f g := by
  obtain ⟨f, hf, hns⟩ := HermiteHilbertBasis.exists_memLp_not_steinPair
  exact ⟨f, hf, fun ⟨g, hg⟩ => hns ⟨g, steinPair_of_smoothSteinPair hg⟩⟩

/-- Both witnesses of the chain, now on the Cc^∞ side. -/
theorem smooth_witnesses :
    SmoothSteinPair (fun x : ℝ => x) (fun _ => 1)
      ∧ SmoothSteinPair (fun x => |x|) AbsSteinWitness.sgn :=
  ⟨SteinSmoothTest.smoothSteinPair_id_one, SteinSmoothTest.abs_smoothSteinPair⟩

end

end W6Converse
