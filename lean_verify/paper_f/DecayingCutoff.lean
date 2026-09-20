/-
  DecayingCutoff: L19's forced exponential for DECAYING cutoffs, and the three moments as
  the integrals they were said to be — so "all three moments equal 1" is exactly the choice
  `κ = 1`

  Campaign 3 hardening unit 174 (20 September 2026). Found while reading the binders of
  `SpectralCutoffFactorises.cutoff_exponential_of_factorises` to compute the moments of the
  cutoff it forces.

  WHY. Spine link L19 ("spectral action → exponential forced") has its arrow as a theorem:
  a positive, monotone cutoff whose action factorises over tensor sums is `exp (c · x)`
  (`cutoff_exponential_of_factorises`, `cutoff_one_parameter`). Its `Monotone f` is Mathlib's
  NON-DECREASING, and under it `c = log (f 1) ≥ 0` is a theorem (`log_nonneg_of_monotone`
  below): **no decaying cutoff — `e^{−v}` included — is in that hypothesis class**, and the
  header's *"what no theorem here supplies is that the constant is negative"* understates it:
  there the constant cannot be negative. `ERRATUM 678`. The physics uses a DECAYING cutoff
  (`Tr f(D²/Λ²)` with `f` falling off), so the case L19 needs is the one the theorem did not
  cover. This file covers it, by reflection: `x ↦ f (−x)` carries antitone to monotone and
  preserves factorisation, so a positive, ANTITONE, factorising cutoff is `exp (−(κ · x))` with
  `κ = log (f (−1)) ≥ 0`. It then computes the moments `F3_10a_HeatKernelCanonicity`'s header
  states — as the integrals it writes, which no declaration of that file states (`ERRATUM 559`
  found `Γ 1 = 1`, `1! = 1`, `exp 0 = 1` standing in for them): `f(0) = 1` for EVERY positive
  factorising cutoff (so the line *"f₄ = f(0) = 1"* carries no information about `κ`),
  `∫₀^∞ e^{−κx} dx = 1/κ`, `∫₀^∞ x e^{−κx} dx = 1/κ²`; and *all three equal 1* holds IF AND
  ONLY IF `κ = 1`. The normalisation `ASSUMPTIONS_LEDGER` 12 records is therefore exactly one
  real choice, named.

  WHAT IS PROVED.
  (1) `factorises_comp_neg`, `monotone_comp_neg_of_antitone`: reflection preserves
      `Factorises` and turns `Antitone` into `Monotone`.
  (2) `cutoff_zero`: a positive factorising cutoff has `f 0 = 1` (from `f 0 = f 0 · f 0`).
  (3) `cutoff_exponential_of_antitone_factorises`, `cutoff_one_parameter_antitone`: a positive,
      antitone, factorising cutoff is `exp (−(log (f (−1)) · x))`, with `log (f (−1)) ≥ 0`.
      `decaying_inhabited`: `x ↦ exp (−x)` is in the class (`ERRATUM 557`'s rule).
  (4) `log_nonneg_of_monotone`, `one_le_of_monotone`: in the MONOTONE class the exponent is
      `≥ 0` and `f x ≥ 1` for `x ≥ 0` — the class contains no decaying cutoff.
  (5) `integral_exp_neg_mul` (`= 1/κ`), `integral_mul_exp_neg_one` (`∫₀^∞ x e^{−x} = 1`, via
      `Real.Gamma_eq_integral` at `2`), `integral_mul_exp_neg_mul` (`= 1/κ²`), all for `κ > 0`;
      `moments_eq_one_iff`: both integrals equal `1` iff `κ = 1`.
  (6) `witness_action_decaying`: the witness's `Tr exp (−κ Dsym²) = 2 + 2 e^{−4κ}`, the
      decaying cutoff applied to the one Dirac operator this estate has under CCM's axioms
      with `D ≠ 0` (unit 172).

  NOT PROVED, said exactly.
  • Which `κ` the cascade picks: nothing here or elsewhere in the estate fixes it; `κ = 1` is
    a normalisation of `Λ`, and `moments_eq_one_iff` says precisely that and no more.
  • Any coupling value. `G = 3π/Λ²`, `g² = 384π²/N` and the rest are not touched; `a₂`, `a₄`
    and the heat-kernel expansion are `WALLS` §W5 and beyond it.
  • The factorisation hypothesis on a cutoff is still a hypothesis: `Factorises` is what the
    Kronecker-sum shape gives for `exp` (unit 9) and what order-one forces on the regular
    bimodule (unit 172); for the cascade's own `D` it is an input (`L40433`).
  • Continuity or measurability routes to the exponential form: only the monotone/antitone
    route is written, as in `F4_1h`.
  • `f₄ = f(0)` is `F3_10a`'s convention; CCM's moment conventions differ, and no theorem
    here adjudicates between them.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). Every theorem about a cutoff `f` takes
  `∀ x, 0 < f x` and `Factorises f`, plus `Antitone f` (3) or `Monotone f` (4);
  `cutoff_zero` takes positivity and factorisation only. The three integral theorems with a
  scale take `0 < κ`; `integral_mul_exp_neg_one`, `decaying_inhabited` and
  `witness_action_decaying` take nothing.
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OrderOneCutoffFactorises

open MeasureTheory Set
open SpectralCutoffFactorises
open scoped Matrix.Norms.Operator

namespace DecayingCutoff

/-- Reflection `x ↦ f (−x)` preserves factorisation. -/
theorem factorises_comp_neg (f : ℝ → ℝ) (hf : Factorises f) : Factorises (fun x => f (-x)) := by
  intro p q a b
  have h := hf p q (fun i => -a i) (fun j => -b j)
  simpa only [neg_add] using h

/-- Reflection turns an antitone cutoff into a monotone one. -/
theorem monotone_comp_neg_of_antitone (f : ℝ → ℝ) (hf : Antitone f) :
    Monotone (fun x => f (-x)) :=
  fun _ _ hxy => hf (neg_le_neg hxy)

/-- A positive factorising cutoff is `1` at `0` — so *`f₄ = f(0) = 1`* says nothing about `κ`. -/
theorem cutoff_zero (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x) (hfact : Factorises f) : f 0 = 1 := by
  have h := semigroup_of_factorises f hfact 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hpos 0).ne' (by rw [mul_one]; exact h.symm)

/-- **L19'S ARROW FOR A DECAYING CUTOFF.** Positive, antitone and factorising ⟹ `exp (−(κ x))` with
`κ = log (f (−1))`. -/
theorem cutoff_exponential_of_antitone_factorises (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hanti : Antitone f) (hfact : Factorises f) (x : ℝ) :
    f x = Real.exp (-(Real.log (f (-1)) * x)) := by
  have h := cutoff_exponential_of_factorises (fun y => f (-y)) (fun y => hpos (-y))
    (monotone_comp_neg_of_antitone f hanti) (factorises_comp_neg f hfact) (-x)
  simp only [neg_neg] at h
  rw [h, mul_neg]

/-- The decaying cutoff has one parameter, and it is NON-NEGATIVE. -/
theorem cutoff_one_parameter_antitone (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x)
    (hanti : Antitone f) (hfact : Factorises f) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, f x = Real.exp (-(κ * x)) := by
  refine ⟨Real.log (f (-1)), ?_, cutoff_exponential_of_antitone_factorises f hpos hanti hfact⟩
  have h1 : f 0 ≤ f (-1) := hanti (by norm_num)
  rw [cutoff_zero f hpos hfact] at h1
  exact Real.log_nonneg h1

/-- **The monotone class has a non-negative exponent** — `cutoff_one_parameter`'s constant cannot be
negative (`ERRATUM 678`). -/
theorem log_nonneg_of_monotone (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x) (hmon : Monotone f)
    (hfact : Factorises f) : 0 ≤ Real.log (f 1) := by
  have h1 : f 0 ≤ f 1 := hmon (by norm_num)
  rw [cutoff_zero f hpos hfact] at h1
  exact Real.log_nonneg h1

/-- In the monotone class `f x ≥ 1` on `x ≥ 0`: no decay. -/
theorem one_le_of_monotone (f : ℝ → ℝ) (hpos : ∀ x, 0 < f x) (hmon : Monotone f)
    (hfact : Factorises f) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ f x := by
  have h1 : f 0 ≤ f x := hmon hx
  rwa [cutoff_zero f hpos hfact] at h1

/-- `∫₀^∞ e^{−κx} dx = 1/κ` (`F3_10a`'s `f₀`, at scale `κ`). -/
theorem integral_exp_neg_mul (κ : ℝ) (hκ : 0 < κ) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(κ * x)) = 1 / κ := by
  have h := integral_comp_mul_left_Ioi (fun y => Real.exp (-y)) 0 hκ
  simp only [mul_zero] at h
  rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

/-- `∫₀^∞ x e^{−x} dx = 1` — the integral `F3_10a` writes for `f₂` and proves as `Γ 2 = 1! = 1`;
here it IS the integral, via `Real.Gamma_eq_integral`. -/
theorem integral_mul_exp_neg_one : ∫ x in Ioi (0 : ℝ), x * Real.exp (-x) = 1 := by
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  have h2 : Real.Gamma 2 = 1 := by
    have := Real.Gamma_nat_eq_factorial 1
    norm_num at this ⊢
  have e : (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) = fun x => x * Real.exp (-x) := by
    funext x
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
  rw [h2, e] at h
  exact h.symm

/-- `∫₀^∞ x e^{−κx} dx = 1/κ²` (`F3_10a`'s `f₂`, at scale `κ`). -/
theorem integral_mul_exp_neg_mul (κ : ℝ) (hκ : 0 < κ) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(κ * x)) = 1 / κ ^ 2 := by
  have h := integral_comp_mul_left_Ioi (fun y => y * Real.exp (-y)) 0 hκ
  simp only [mul_zero] at h
  rw [integral_mul_exp_neg_one, smul_eq_mul, mul_one] at h
  have h' : ∫ x in Ioi (0 : ℝ), κ * x * Real.exp (-(κ * x))
      = κ * ∫ x in Ioi (0 : ℝ), x * Real.exp (-(κ * x)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [h'] at h
  have e : κ * (1 / κ ^ 2) = κ⁻¹ := by field_simp
  exact mul_left_cancel₀ hκ.ne' (h.trans e.symm)

/-- **ALL THREE MOMENTS EQUAL ONE IFF `κ = 1`.** With `f(0) = 1` automatic, this is the whole
content of *the moments are fixed*: one real normalisation. -/
theorem moments_eq_one_iff (κ : ℝ) (hκ : 0 < κ) :
    ((∫ x in Ioi (0 : ℝ), Real.exp (-(κ * x))) = 1
      ∧ (∫ x in Ioi (0 : ℝ), x * Real.exp (-(κ * x))) = 1) ↔ κ = 1 := by
  rw [integral_exp_neg_mul κ hκ, integral_mul_exp_neg_mul κ hκ]
  constructor
  · rintro ⟨h, -⟩
    exact ((div_eq_one_iff_eq hκ.ne').mp h).symm
  · rintro rfl
    norm_num

/-- The antitone class is inhabited: `x ↦ e^{−x}` (`ERRATUM 557`'s rule). -/
theorem decaying_inhabited :
    ∃ f : ℝ → ℝ, (∀ x, 0 < f x) ∧ Antitone f ∧ Factorises f :=
  ⟨fun x => Real.exp (-x), fun x => Real.exp_pos (-x),
    fun _ _ h => Real.exp_le_exp.mpr (neg_le_neg h), factorises_comp_neg Real.exp exp_factorises⟩

/-- The decaying cutoff on the witness: `Tr exp (−κ Dsym²) = 2 + 2 e^{−4κ}` (unit 172's trace). -/
theorem witness_action_decaying (κ : ℝ) :
    (NormedSpace.exp ((-(κ : ℂ)) • (RealSpectralWitness.Dsym * RealSpectralWitness.Dsym))).trace
      = 2 + 2 * Complex.exp (-(4 * κ)) := by
  rw [OrderOneCutoffFactorises.trace_exp_smul_Dsym_sq, mul_neg]

end DecayingCutoff
