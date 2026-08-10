/-
  SteinSmoothTest.lean — the Cc^∞-defined Gaussian Sobolev class, written
  down at last, and one half of WALLS W6 proved.

  WHY. W6 says the Cc^∞-defined space "has no formal counterpart in the
  estate", and on that basis the comparison with the Stein class has been
  classified as an open QUESTION since 2 August. The first half of that
  sentence turned out to be a habit rather than a fact. **The Stein class
  and the textbook space differ only in which test functions are used**,
  and once that is seen the Cc^∞ class is four lines to define:
  `SmoothSteinPair f g` is the same Gaussian integration-by-parts pairing
  `∫ f·(x·φ − φ′) dγ = ∫ g·φ dγ`, with `φ` ranging over smooth compactly
  supported functions instead of over polynomials.

  WHAT THIS FILE PROVES:
  1. **`integral_mul_eq_tsum_coeff`** — polarised Parseval,
     `∫ f·h dγ = Σ n!·cₙ(f)·cₙ(h)`. Immediate from yesterday's
     `hermiteBasis` through `HilbertBasis.tsum_inner_mul_inner`; the
     estate had only the `‖f‖²` form. This is the engine.
  2. **`smoothSteinPair_of_steinPair`** — **half of W6**. Every Stein pair
     is a Cc^∞ pair, so the Stein class is CONTAINED in the textbook
     space. Proved through coefficients: the transformed test function has
     `cₙ(x·φ − φ′) = cₙ₋₁(φ)` (`coeff_testfun`, from the estate's
     `stein_general` and `derivative_H_succ`), after which both sides of
     the pairing are literally the same series
     `Σ (m+1)!·c_{m+1}(f)·c_m(φ)`. Proved for the LARGER C¹-compactly-
     supported test family, so the Cc^∞ statement is a corollary and the
     theorem is the stronger of the two.
  3. **`abs_smoothSteinPair`** — and therefore |x| lies in the Cc^∞-defined
     class. **That is ERRATUM 46's premise, assumed by the estate since
     2 August, now a theorem.** `AbsSteinWitness` gave that as the reason
     its witness cannot settle W6 and could not prove the reason; it can
     now, as a one-line consequence of (2).
  4. **`test_family_nonempty`** — and none of this is vacuous. Were there
     no smooth compactly supported functions, `SmoothSteinPair` would hold
     of every pair and (2) would say nothing. A bump is exhibited, with
     its value at the centre computed.

  ONE IDENTIFICATION FLAGGED RATHER THAN ASSERTED, per ERRATUM 46 — which
  was written yesterday about exactly this failure mode, so it would be a
  poor joke to repeat it here. `SmoothSteinPair` is the Cc^∞-tested
  GAUSSIAN integration-by-parts pairing. The textbook `W^{1,2}(γ)` is
  usually written with LEBESGUE weak derivatives: `∫ f·ψ′ dx = −∫ g·ψ dx`
  for `ψ ∈ Cc^∞`. **The two are the same condition**, by the substitution
  `ψ = φ·ρ` with `ρ` the Gaussian density: `ψ′ = (φ′ − x·φ)·ρ`, and
  `φ ↦ φ·ρ` is a bijection of `Cc^∞` because `ρ` is smooth and nowhere
  zero. That computation is standard, it is written out here so a reader
  can check it, and **it is NOT machine-checked** — it needs the
  Lebesgue/Gaussian density bridge, which is its own unit. So: what §4
  proves is containment in the Cc^∞-tested IBP class; that this class is
  the textbook space is stated, sourced to a one-line computation, and
  left as a named residue rather than absorbed into the claim.

  WHAT THIS DOES NOT DO. **W6 is not settled.** The converse —
  `SmoothSteinPair f g → SteinPair f g`, the textbook space contained in
  the Stein class — is NOT proved. §5 states it as `W6Converse` and proves
  `w6_of_converse`: it is exactly what stands between here and the wall
  falling. The route is named there.

  **CORRECTED IN PLACE 2026-08-10 (`ERRATUM 92`), original left standing.**
  `W6Converse.w6Converse_holds : SteinSmoothTest.W6Converse` discharges it,
  and with `w6_of_converse` the wall fell — `WALLS.md` records W6 as closed
  in one dimension and in every dimension. **"W6 is not settled" was true
  when written and has been false since**; a reader who stopped at this
  paragraph would have carried the wrong status for a week. **What has changed is the wall's
  kind**: W6 was a question we could not settle partly because we could
  not state it. It is stated, one direction is proved, and the other has
  an address.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermiteHilbertBasis
import AbsSteinWitness
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Abs

namespace SteinSmoothTest

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass SteinCoefficients HermiteHilbertBasis
open PoincareBeyondPolynomials

noncomputable section

/-! ## 1. Polarised Parseval

The estate had Parseval in the `‖f‖² = Σ n!cₙ²` form only. Yesterday's
`hermiteBasis` gives the bilinear form for free, and everything below is
an application of it.
-/

theorem factorial_cast_ne_zero (n : ℕ) : ((n.factorial : ℝ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr n.factorial_ne_zero

/-- The algebraic step both halves of §1 end on. -/
theorem sqrt_mul_sqrt_mul (n : ℕ) (a b : ℝ) :
    Real.sqrt (n.factorial : ℝ) * a * (Real.sqrt (n.factorial : ℝ) * b)
      = (n.factorial : ℝ) * (a * b) := by
  linear_combination (a * b) * sqrt_factorial_mul_self n

theorem coeff_congr_ae {f h : ℝ → ℝ} (hfh : f =ᵐ[gauss] h) (n : ℕ) :
    coeff n f = coeff n h := by
  have hint : (∫ x, f x * (H n).eval x ∂gauss) = ∫ x, h x * (H n).eval x ∂gauss :=
    integral_congr_ae (by filter_upwards [hfh] with x hx; rw [hx])
  rw [integral_mul_H, integral_mul_H] at hint
  exact mul_left_cancel₀ (factorial_cast_ne_zero n) hint

/-- The `n`-th basis pairing IS the `n`-th coefficient, up to `√(n!)`. -/
theorem inner_basis (F : Lp ℝ 2 gauss) (n : ℕ) :
    inner ℝ (hermiteBasis n) F = Real.sqrt (n.factorial : ℝ) * coeff n (F : ℝ → ℝ) := by
  rw [← HilbertBasis.repr_apply_apply]
  exact repr_apply F n

theorem summable_coeff_mul {f h : ℝ → ℝ} (hf : MemLp f 2 gauss) (hh : MemLp h 2 gauss) :
    Summable fun n : ℕ => (n.factorial : ℝ) * (coeff n f * coeff n h) := by
  have hs := HilbertBasis.summable_inner_mul_inner hermiteBasis (hf.toLp f) (hh.toLp h)
  refine hs.congr fun n => ?_
  rw [real_inner_comm (hermiteBasis n) (hf.toLp f), inner_basis, inner_basis,
    ← coeff_congr_ae hf.coeFn_toLp n, ← coeff_congr_ae hh.coeFn_toLp n]
  exact sqrt_mul_sqrt_mul n _ _

/-- **POLARISED PARSEVAL.** `∫ f·h dγ = Σ n!·cₙ(f)·cₙ(h)`. -/
theorem integral_mul_eq_tsum_coeff {f h : ℝ → ℝ} (hf : MemLp f 2 gauss)
    (hh : MemLp h 2 gauss) :
    ∫ x, f x * h x ∂gauss = ∑' n : ℕ, (n.factorial : ℝ) * (coeff n f * coeff n h) := by
  have key := HilbertBasis.tsum_inner_mul_inner hermiteBasis (hf.toLp f) (hh.toLp h)
  rw [inner_toLp] at key
  rw [← key]
  refine tsum_congr fun n => ?_
  rw [real_inner_comm (hermiteBasis n) (hf.toLp f), inner_basis, inner_basis,
    ← coeff_congr_ae hf.coeFn_toLp n, ← coeff_congr_ae hh.coeFn_toLp n]
  exact sqrt_mul_sqrt_mul n _ _

/-! ## 2. The two test-function classes

`SmoothSteinPair` is W6's object: the same pairing, tested against
`Cc^∞`. `C1SteinPair` tests against the LARGER family of C¹ compactly
supported functions, hence is the SMALLER class — which is why §4's
theorem is proved there and specialised here.
-/

/-- **The Cc^∞-defined Gaussian Sobolev pairing** — the textbook object
    WALLS W6 compares the Stein class against, expressible at last. -/
def SmoothSteinPair (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 gauss ∧ MemLp g 2 gauss ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * (x * φ x - deriv φ x) ∂gauss = ∫ x, g x * φ x ∂gauss

/-- The same pairing tested against C¹ compactly supported functions. -/
def C1SteinPair (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 gauss ∧ MemLp g 2 gauss ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ x, f x * (x * φ x - deriv φ x) ∂gauss = ∫ x, g x * φ x ∂gauss

/-- More test functions is a stronger condition: the C¹-tested class sits
    inside the Cc^∞-tested one. -/
theorem smoothSteinPair_of_c1 {f g : ℝ → ℝ} (h : C1SteinPair f g) :
    SmoothSteinPair f g :=
  ⟨h.1, h.2.1, fun φ hφ hc => h.2.2 φ (hφ.of_le (by exact_mod_cast le_top)) hc⟩

/-! ## 3. Test functions are square-integrable, and what their transform's
       coefficients are

`coeff_testfun` is the whole computation. Two integrations by parts, both
already in the estate: `stein_general` (Gaussian IBP for C¹ functions of
polynomial growth — a compactly supported C¹ function is one, with `m = 0`)
and `derivative_H_succ` (`Hₙ₊₁′ = (n+1)·Hₙ`, which the estate proved
because Mathlib does not have it).
-/

theorem memLp_of_compactSupport {φ : ℝ → ℝ} (hcont : Continuous φ)
    (hc : HasCompactSupport φ) : MemLp φ 2 gauss := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  refine memLp_of_bounded (a := -C) (b := C) ?_ hcont.aestronglyMeasurable 2
  filter_upwards with x
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact ⟨by linarith [neg_abs_le (φ x)], by linarith [le_abs_self (φ x)]⟩

theorem memLp_mul_id {φ : ℝ → ℝ} (hcont : Continuous φ) (hc : HasCompactSupport φ) :
    MemLp (fun x : ℝ => x * φ x) 2 gauss :=
  memLp_of_compactSupport (continuous_id.mul hcont) hc.mul_left

theorem memLp_testfun {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    MemLp (fun x : ℝ => x * φ x - deriv φ x) 2 gauss :=
  (memLp_mul_id hφ.continuous hc).sub
    (memLp_of_compactSupport hφ.continuous_deriv_one hc.deriv)

/-- The integral of the transformed test function against `Hₙ` collapses
    to its pairing with `Hₙ′`. This is the Gaussian IBP, once. -/
theorem integral_testfun_H {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (n : ℕ) :
    ∫ x, (x * φ x - deriv φ x) * (H n).eval x ∂gauss
      = ∫ x, φ x * (derivative (H n)).eval x ∂gauss := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hderiv : ∀ x, HasDerivAt φ (deriv φ x) x := fun x => (hdiff x).hasDerivAt
  obtain ⟨C₀, hC₀⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨C₁, hC₁⟩ := hc.deriv.exists_bound_of_continuous hφ.continuous_deriv_one
  have hb : ∀ x, |φ x| ≤ max C₀ C₁ * (1 + x ^ 2) ^ 0 := by
    intro x
    have h := hC₀ x
    rw [Real.norm_eq_abs] at h
    simpa using h.trans (le_max_left _ _)
  have hb' : ∀ x, |deriv φ x| ≤ max C₀ C₁ * (1 + x ^ 2) ^ 0 := by
    intro x
    have h := hC₁ x
    rw [Real.norm_eq_abs] at h
    simpa using h.trans (le_max_right _ _)
  have hib := stein_general hderiv hb hb' (H n)
  have hφm := memLp_of_compactSupport hφ.continuous hc
  have hI1 : Integrable (fun x : ℝ => (x * φ x) * (H n).eval x) gauss :=
    MemLp.integrable_mul (memLp_mul_id hφ.continuous hc)
      (GaussianPoincare.memLp_polynomial_gaussianReal (H n) 0 1)
  have hI2 : Integrable (fun x : ℝ => deriv φ x * (H n).eval x) gauss :=
    MemLp.integrable_mul (memLp_of_compactSupport hφ.continuous_deriv_one hc.deriv)
      (GaussianPoincare.memLp_polynomial_gaussianReal (H n) 0 1)
  have hI3 : Integrable (fun x : ℝ => φ x * (X * H n).eval x) gauss :=
    MemLp.integrable_mul hφm
      (GaussianPoincare.memLp_polynomial_gaussianReal (X * H n) 0 1)
  have hI4 : Integrable (fun x : ℝ => φ x * (derivative (H n)).eval x) gauss :=
    MemLp.integrable_mul hφm
      (GaussianPoincare.memLp_polynomial_gaussianReal (derivative (H n)) 0 1)
  have hcongr : ∫ x, (x * φ x - deriv φ x) * (H n).eval x ∂gauss
      = ∫ x, ((x * φ x) * (H n).eval x - deriv φ x * (H n).eval x) ∂gauss :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hxmul : ∫ x, (x * φ x) * (H n).eval x ∂gauss
      = ∫ x, φ x * (X * H n).eval x ∂gauss :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Polynomial.eval_mul, Polynomial.eval_X]; ring)
  have hcombine : ∫ x, φ x * (X * H n - derivative (H n)).eval x ∂gauss
      = (∫ x, φ x * (X * H n).eval x ∂gauss)
        - ∫ x, φ x * (derivative (H n)).eval x ∂gauss := by
    rw [← integral_sub hI3 hI4]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Polynomial.eval_sub]; ring)
  rw [hcongr, integral_sub hI1 hI2, hib, hcombine, hxmul]
  ring

/-- **The coefficients of the transformed test function.** For `φ` of class
    C¹ with compact support, `cₙ(x·φ − φ′) = cₙ₋₁(φ)`, and `c₀ = 0`. -/
theorem coeff_testfun {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (n : ℕ) :
    coeff n (fun x : ℝ => x * φ x - deriv φ x)
      = if n = 0 then 0 else coeff (n - 1) φ := by
  have hkey := integral_testfun_H hφ hc n
  rw [integral_mul_H] at hkey
  cases n with
  | zero =>
      rw [if_pos rfl]
      have h0 : ∫ x, φ x * (derivative (H 0)).eval x ∂gauss = 0 := by
        simp
      rw [h0] at hkey
      simpa using hkey
  | succ m =>
      rw [if_neg (Nat.succ_ne_zero m), Nat.succ_sub_one]
      rw [derivative_H_succ] at hkey
      have hev : ∫ x, φ x * ((((m : ℝ) + 1) • H m)).eval x ∂gauss
          = ((m : ℝ) + 1) * ∫ x, φ x * (H m).eval x ∂gauss := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Polynomial.eval_smul, smul_eq_mul]
        ring
      rw [hev, integral_mul_H, Nat.factorial_succ] at hkey
      have hm := factorial_cast_ne_zero m
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast at hkey
      field_simp at hkey ⊢
      nlinarith [hkey]

/-! ## 4. Half of W6

Both sides of the Cc^∞ pairing expand, by §1, into series in the Hermite
coefficients. The Stein recursion makes them the same series.
-/

/-- **THE STEIN CLASS IS CONTAINED IN THE C¹-TESTED CLASS.** -/
theorem c1SteinPair_of_steinPair {f g : ℝ → ℝ} (h : SteinPair f g) :
    C1SteinPair f g := by
  refine ⟨h.1, h.2.1, fun φ hφ hc => ?_⟩
  have hT := memLp_testfun hφ hc
  have hφm := memLp_of_compactSupport hφ.continuous hc
  rw [integral_mul_eq_tsum_coeff h.1 hT, integral_mul_eq_tsum_coeff h.2.1 hφm,
    (summable_coeff_mul h.1 hT).tsum_eq_zero_add]
  have hzero : ((Nat.factorial 0 : ℕ) : ℝ)
      * (coeff 0 f * coeff 0 fun x : ℝ => x * φ x - deriv φ x) = 0 := by
    rw [coeff_testfun hφ hc 0, if_pos rfl]
    ring
  rw [hzero, zero_add]
  refine tsum_congr fun n => ?_
  rw [coeff_testfun hφ hc (n + 1), if_neg (Nat.succ_ne_zero n), Nat.succ_sub_one,
    coeff_steinPair h n, Nat.factorial_succ]
  push_cast
  ring

/-- **THE STEIN CLASS IS CONTAINED IN THE Cc^∞-DEFINED SOBOLEV CLASS.**
    Half of WALLS W6, and the half that was never obviously true: the two
    test families are INCOMPARABLE (ERRATA 35), so no inclusion follows
    from counting test functions. It follows from the coefficients. -/
theorem smoothSteinPair_of_steinPair {f g : ℝ → ℝ} (h : SteinPair f g) :
    SmoothSteinPair f g :=
  smoothSteinPair_of_c1 (c1SteinPair_of_steinPair h)

/-! ## 5. The other half, stated as the obstruction it is

Not proved, and not hidden inside a docstring. The missing implication is
named, and what it would buy is a theorem.

**The route.** Given `SmoothSteinPair f g`, one wants the pairing at an
arbitrary polynomial `q`. Fix a bump `χ` with `χ = 1` on `[-1,1]` and
support in `[-2,2]` (`test_family_nonempty` builds one), and test against
`φ_R(x) = q(x)·χ(x/R)`, which IS Cc^∞. Then `(q·χ_R)′ = q′·χ_R + q·χ_R′`
with `|χ_R′| ≤ ‖χ′‖_∞/R`, so the error term is at most
`‖χ′‖_∞/R · ‖f·q‖_{L¹(γ)} → 0`, and dominated convergence handles the
rest. **What is missing is the Lean plumbing, not the idea**: a scaled
bump family with a uniform derivative bound, and two dominated-convergence
arguments. That is a unit of work, not a wall — but it has not been done,
so W6 stands.
-/

/-- The exact missing implication. -/
def W6Converse : Prop := ∀ f g : ℝ → ℝ, SmoothSteinPair f g → SteinPair f g

/-- **The second residue, named for the same reason.** That the Cc^∞-tested
    Gaussian pairing IS the textbook Lebesgue-weak-derivative Sobolev space
    is a substitution `ψ = φ·ρ`, not a theorem in this file. It is written
    out in the header; it needs the Lebesgue/Gaussian density bridge to
    formalise. Recorded here so that "we defined the textbook space" is a
    claim with a visible gap rather than a sentence a reader must take on
    trust — which is precisely what ERRATUM 46 was about. -/
def TextbookBridge : Prop :=
  ∀ f g : ℝ → ℝ, MemLp f 2 gauss → MemLp g 2 gauss →
    (SmoothSteinPair f g ↔
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, f x * deriv ψ x = -∫ x, g x * ψ x)

/-- **And it is exactly what stands between here and W6 falling.** With the
    converse, the Stein class and the Cc^∞-defined Sobolev class coincide;
    §4 supplies the other direction unconditionally. -/
theorem w6_of_converse (hconv : W6Converse) (f g : ℝ → ℝ) :
    SteinPair f g ↔ SmoothSteinPair f g :=
  ⟨smoothSteinPair_of_steinPair, hconv f g⟩

/-! ## 6. ERRATUM 46's premise, verified

`AbsSteinWitness` has said since 2 August that its witness cannot settle
W6 "because |x| lies in that Sobolev space too" — an external fact the
estate could not express, let alone prove, and one that is load-bearing:
were it false, `stein_strict_classes` would settle W6 outright. §4 makes
it a corollary.
-/

/-- **|x| lies in the Cc^∞-defined Gaussian Sobolev class**, with partner
    `sgn`. The assumption is retired. -/
theorem abs_smoothSteinPair : SmoothSteinPair (fun x => |x|) AbsSteinWitness.sgn :=
  smoothSteinPair_of_steinPair AbsSteinWitness.steinPair_abs

/-- Stated as the negative it was used as: this witness does NOT separate
    the two classes, and now that is a theorem rather than a belief. -/
theorem abs_does_not_separate :
    SteinPair (fun x => |x|) AbsSteinWitness.sgn
      ∧ SmoothSteinPair (fun x => |x|) AbsSteinWitness.sgn :=
  ⟨AbsSteinWitness.steinPair_abs, abs_smoothSteinPair⟩

/-! ## 7. Review round 39 — the ways this file could say nothing

**"There might be no test functions, and `SmoothSteinPair` would be
vacuously true of everything."** This is the attack that matters, because
`SmoothSteinPair` is a `∀` over a family the file never otherwise
inhabits. A bump is built and its value at the centre computed, so the
family is nonempty and the quantifier bites.

**"The class might be empty, and §4 would be about nothing."** It is not:
`(X, 1)` is in it by `steinPair_id_one` and §4, and so is `(|x|, sgn)` by
§6 — a pair with no everywhere-pointwise derivative.

**"Polarised Parseval might be the old Parseval in disguise."** It is not
the old one — the estate had only `‖f‖²` — and §1 is derived from the
`HilbertBasis`, not from `HermiteParseval.parseval`.
-/

/-- A concrete bump: 1 on the closed unit ball, supported in the ball of
    radius 2. -/
def unitBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- **The test family is not empty.** Smooth, compactly supported, and
    not the zero function. -/
theorem test_family_nonempty :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ φ 0 = 1 :=
  ⟨(unitBump : ℝ → ℝ), ContDiffBump.contDiff _, ContDiffBump.hasCompactSupport _,
    ContDiffBump.one_of_mem_closedBall _
      (Metric.mem_closedBall_self unitBump.rIn_pos.le)⟩

/-- The class is inhabited by the sharp witness of the whole Poincaré
    chain. -/
theorem smoothSteinPair_id_one : SmoothSteinPair (fun x : ℝ => x) (fun _ => 1) :=
  smoothSteinPair_of_steinPair steinPair_id_one

/-- And by a pair whose second component is not a pointwise derivative of
    the first anywhere — so the Cc^∞ class, like the Stein class, is not
    secretly a class of differentiable functions. -/
theorem smoothSteinPair_abs_nontrivial :
    SmoothSteinPair (fun x => |x|) AbsSteinWitness.sgn
      ∧ ∀ g : ℝ → ℝ, ¬ (∀ x, HasDerivAt (fun y => |y|) (g x) x) := by
  refine ⟨abs_smoothSteinPair, fun g hg => ?_⟩
  have h0 := hg 0
  exact absurd h0.differentiableAt not_differentiableAt_abs_zero

end

end SteinSmoothTest
