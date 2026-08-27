/-
  SteinGeneralPi.lean — the n-dimensional membership criterion, and with it
  the Gaussian Poincaré inequality for an arbitrary C¹ function.

  WHY. `W6ConversePi` put the n-dimensional Poincaré inequality on the
  textbook Sobolev space, and that made the class's emptiness the binding
  problem rather than its definition: the estate could name exactly TWO
  members of that class — the constants (`TextbookSobolevPi.const_mem`) and
  the coordinates (`W6ConversePi.coord_sobolevWeakPi`) — each put there by
  hand, one at a time. The Hermite-tested class is far better populated
  (every Hermite product, by `HermitePiPoincare.Hpi_mem`, and `|xᵢ|`), but
  the estate's only arrow runs FROM the textbook class INTO the Hermite one,
  so none of that carries back. Every criterion is a catalogue. This file
  supplies the criterion.

  THE ITEM AS OPENED ASSUMED THE WRONG SHAPE, and saying so is the point of
  the first section. `UNLOCK_WATCHLIST`'s entry, written 9 August, took the
  1-dimensional twin `PoincareBeyondPolynomials.stein_general` as the model:
  Gaussian integration by parts proved by FTC on the line with the boundary
  terms shown to vanish at ±∞. The boundary term is there because the 1-d
  statement tests against POLYNOMIALS, which do not decay. The n-dimensional
  target `TextbookSobolevPi.SobolevWeakPi` tests against `Cc^∞`, and a
  compactly supported test function has no boundary term to kill. So:

  WHAT THIS FILE PROVES:
  1. **`integral_mul_partial`** — the pairing, and it needs NO growth
     hypothesis. Mathlib's several-variable integration by parts concludes
     `∫ f·∂ᵥg = −∫ (∂ᵥf)·g`, which at `g = ψ` and `v = eᵢ` IS the
     `SobolevWeakPi` clause with no rearrangement; all five of its
     hypotheses fall to continuity times compact support.
  2. **`sobolevWeakPi_of_contDiff`** — therefore **every C¹ function whose
     value and gradient are square-integrable against `γⁿ` is a member of
     the textbook class, with its actual gradient as the weak one.** The
     hypotheses are exactly what the conclusion needs; polynomial growth is
     offered in §3 as a sufficient condition for the L² clauses, not baked
     into the criterion.
  3. **`poincare_contDiff`** — and so the Gaussian Poincaré inequality in n
     dimensions holds for an arbitrary such `f`, with no polynomial, no
     Hermite coefficient, and no Stein pairing anywhere in the hypothesis.
     **The step that makes the 1-d proof long does not recur here**: the
     vanishing-boundary work is `W6ConversePi`'s cutoff argument, done once
     and reused through `steinPairPi_of_sobolevWeakPi`.
  4. **`memLp_of_polyGrowth`** — polynomial growth suffices for the L²
     clauses, through `GaussPiExp.memLp_exp_sumAbs` and the elementary
     `1 + s² ≤ (1+s)² ≤ exp(2s)`. It asks only for A.E.-STRONG
     MEASURABILITY, matching the 1-d twin; it read `Continuous h` until
     `SteinDifferentiablePi` needed it for a discontinuous gradient, and the
     proof never used more than the weaker hypothesis.
  5. **`sin_coord_mem`** — and the criterion is exercised rather than
     merely stated: `x ↦ sin xᵢ` is a member, with gradient `cos xᵢ · eᵢ`.
     It is bounded (`sin_coord_bounded`) and non-constant
     (`sin_coord_nonconstant`), and no non-constant polynomial is bounded —
     **that last step is standard and is NOT machine-checked here**, so what
     this file proves is the two bounds, not the non-polynomiality itself.
     Unlike `AbsSteinWitnessPi`'s witness it is reached by a GENERAL theorem
     rather than by a computation tailored to it. `poincare_sin` runs the
     inequality on it.

  WHAT THIS DOES NOT DO. The criterion is sufficient, not necessary, and
  visibly so: `AbsSteinWitnessPi.absCoord_steinPairPi` puts `|xᵢ|` in the
  Stein class and `absCoord_not_ae_differentiable` proves it is not a.e.
  equal to any differentiable function, so **being C¹ is not necessary for
  membership of the class the inequality is proved on** —
  `criterion_not_necessary`. **That is NOT the statement that §2's
  containment is strict**, and the difference matters: §2 lands in
  `SobolevWeakPi`, and whether `|xᵢ|` belongs THERE is not settled anywhere
  in the estate, because the one arrow runs out of `SobolevWeakPi` rather
  than into it.

  **⚠ SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`).** *"whether `|xᵢ|`
  belongs THERE is not settled anywhere in the estate"* is false:
  `SteinSmoothPi` proves `SobolevWeakPi n (AbsSteinWitnessPi.absCoord n i)
  (AbsSteinWitnessPi.sgnCoord n i)` — `|xᵢ|` is in the textbook class, with
  `sgnCoord` as its weak derivative. **The reason given was the wrong one too**:
  the arrow's direction was never the obstacle, because membership was proved
  directly rather than transported along it (`ERRATUM 302`). What still stands
  is the first half — being `C¹` is not necessary for membership of the Stein
  class — and the distinction from §2's containment being strict.

  **And this file does not settle the
  reverse containment** `SteinPairPi → SmoothSteinPairPi`: it produces
  members of the textbook class, which is the small side of the one arrow
  the estate has, so it cannot close a gap that runs the other way.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import W6ConversePi
import AbsSteinWitnessPi
import GaussPiExp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace SteinGeneralPi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open GaussPiDensity HermitePiStein HermitePiPoincare TextbookSobolevPi
open W6ConversePi GaussPiExp

noncomputable section

/-! ## 1. The pairing, with no growth hypothesis at all

Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` wants three
integrability facts and two differentiability facts. Against a compactly
supported test function every one of them is "a continuous function times a
compactly supported continuous function", so the whole section is
bookkeeping. That is the difference from the 1-dimensional twin, and it is
not a cleverness: it is what testing against `Cc^∞` instead of against
polynomials buys.
-/

variable {n : ℕ}

theorem continuous_gradient {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous fun x => fderiv ℝ f x (Pi.single i (1:ℝ)) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem differentiable_of_contDiff_one {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

/-- **`∫ f·∂ᵢψ dx = −∫ (∂ᵢf)·ψ dx`** for `f ∈ C¹(ℝⁿ)` and `ψ ∈ Cc^∞(ℝⁿ)`,
    with no hypothesis on the size of `f` anywhere. -/
theorem integral_mul_partial {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin n) {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ x, f x * fderiv ℝ ψ x (Pi.single i (1:ℝ)))
      = -∫ x, fderiv ℝ f x (Pi.single i (1:ℝ)) * ψ x := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous fun x : Fin n → ℝ => fderiv ℝ f x (Pi.single i (1:ℝ)) :=
    continuous_gradient hf i
  have h1 : Integrable
      (fun x : Fin n → ℝ => fderiv ℝ f x (Pi.single i (1:ℝ)) * ψ x) volume :=
    (hgc.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have h2 : Integrable
      (fun x : Fin n → ℝ => f x * fderiv ℝ ψ x (Pi.single i (1:ℝ))) volume :=
    (hfc.mul (continuous_partial n hψ i)).integrable_of_hasCompactSupport
      (hasCompactSupport_partial n hcψ i).mul_left
  have h3 : Integrable (fun x : Fin n → ℝ => f x * ψ x) volume :=
    (hfc.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Fin n → ℝ))) (v := Pi.single i (1:ℝ)) h1 h2 h3
    (fun x _ => (differentiable_of_contDiff_one hf).differentiableAt)
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)

/-! ## 2. The criterion, and the inequality it delivers -/

/-- **THE MEMBERSHIP CRITERION.** A C¹ function whose value and gradient are
    square-integrable against `γⁿ` belongs to the textbook Gaussian Sobolev
    space, and its weak gradient is its actual one. -/
theorem sobolevWeakPi_of_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hmem : MemLp f 2 (gaussPi n))
    (hgrad : ∀ i, MemLp (fun x => fderiv ℝ f x (Pi.single i (1:ℝ))) 2 (gaussPi n)) :
    SobolevWeakPi n f (fun i x => fderiv ℝ f x (Pi.single i (1:ℝ))) :=
  ⟨hmem, hgrad, fun i _ψ hψ hcψ => integral_mul_partial hf i hψ hcψ⟩

/-- The same, on the `Cc^∞`-tested class, by stair N5. -/
theorem smoothSteinPairPi_of_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hmem : MemLp f 2 (gaussPi n))
    (hgrad : ∀ i, MemLp (fun x => fderiv ℝ f x (Pi.single i (1:ℝ))) 2 (gaussPi n)) :
    SmoothSteinPairPi n f (fun i x => fderiv ℝ f x (Pi.single i (1:ℝ))) :=
  (smoothSteinPairPi_iff_sobolevWeakPi n _ _).mpr
    (sobolevWeakPi_of_contDiff hf hmem hgrad)

/-- And on the Hermite-tested class, through `W6ConversePi` — which is where
    the vanishing-boundary work that the 1-d twin does by hand actually
    lives, done once. -/
theorem steinPairPi_of_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hmem : MemLp f 2 (gaussPi n))
    (hgrad : ∀ i, MemLp (fun x => fderiv ℝ f x (Pi.single i (1:ℝ))) 2 (gaussPi n)) :
    SteinPairPi n f (fun i x => fderiv ℝ f x (Pi.single i (1:ℝ))) :=
  steinPairPi_of_sobolevWeakPi n (sobolevWeakPi_of_contDiff hf hmem hgrad)

/-- **THE GAUSSIAN POINCARÉ INEQUALITY IN n DIMENSIONS FOR AN ARBITRARY C¹
    FUNCTION.** `Var_γⁿ(f) ≤ Σᵢ ∫ (∂ᵢf)² dγⁿ`, with the ordinary pointwise
    partial derivatives on the right and no polynomial, Hermite coefficient
    or Stein pairing in the hypothesis. -/
theorem poincare_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hmem : MemLp f 2 (gaussPi n))
    (hgrad : ∀ i, MemLp (fun x => fderiv ℝ f x (Pi.single i (1:ℝ))) 2 (gaussPi n)) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      ≤ ∑ i : Fin n, ∫ x, fderiv ℝ f x (Pi.single i (1:ℝ))
          * fderiv ℝ f x (Pi.single i (1:ℝ)) ∂gaussPi n :=
  poincare_steinPi n (steinPairPi_of_contDiff hf hmem hgrad)

/-! ## 3. Polynomial growth as a sufficient condition for the L² clauses

The estate already has the hard half: `GaussPiExp.memLp_exp_sumAbs` puts
`exp(c·Σᵢ|xᵢ|)` in `L²(γⁿ)` for EVERY real `c`. What is left is elementary —
`1 + s² ≤ (1+s)²` and `1 + s ≤ exp s`.
-/

/-- The sup norm on `Fin n → ℝ` is at most the sum of the absolute values.
    True in dimension `0` too, where both sides are `0`. -/
theorem norm_le_sumAbs (x : Fin n → ℝ) : ‖x‖ ≤ sumAbs n x := by
  refine pi_norm_le_iff_of_nonneg (sumAbs_nonneg n x) |>.mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- `(1 + t²)^m ≤ exp(2m·t)` for `t ≥ 0`. -/
theorem poly_le_exp {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    (1 + t ^ 2) ^ m ≤ Real.exp (2 * m * t) := by
  have hstep : 1 + t ^ 2 ≤ Real.exp t ^ 2 := by
    have h1 : (1 : ℝ) + t ≤ Real.exp t := by
      have := Real.add_one_le_exp t
      linarith
    have h2 : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    have h3 : (1 + t) ^ 2 ≤ Real.exp t ^ 2 := by nlinarith [Real.exp_pos t]
    linarith
  calc (1 + t ^ 2) ^ m ≤ (Real.exp t ^ 2) ^ m := by
        refine pow_le_pow_left₀ (by positivity) hstep m
    _ = Real.exp (2 * m * t) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- **Polynomial growth suffices.** Any a.e.-strongly-measurable `h` with
    `|h x| ≤ C·(1 + ‖x‖²)^m` is in `L²(γⁿ)`.

    *This asked for `Continuous h` until `SteinDifferentiablePi` needed it for
    the partial derivative of a merely differentiable function, which need not
    be continuous. The proof never used more than measurability — the
    continuity was spent on one `.aestronglyMeasurable` — and the 1-d twin
    `PoincareBeyondPolynomials.memLp_of_polyGrowth` had taken the weaker
    hypothesis from the start.* -/
theorem memLp_of_polyGrowth {h : (Fin n → ℝ) → ℝ}
    (hc : AEStronglyMeasurable h (gaussPi n)) {C : ℝ}
    {m : ℕ} (hb : ∀ x, |h x| ≤ C * (1 + ‖x‖ ^ 2) ^ m) :
    MemLp h 2 (gaussPi n) := by
  have hC : 0 ≤ C := by
    have h0 := hb 0
    have hpos : (0 : ℝ) < (1 + ‖(0 : Fin n → ℝ)‖ ^ 2) ^ m := by positivity
    nlinarith [abs_nonneg (h 0)]
  refine MemLp.of_le ((memLp_exp_sumAbs n (2 * m)).const_mul C)
    hc (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ C * Real.exp (2 * (m : ℝ) * sumAbs n x))]
  refine (hb x).trans ?_
  have hmono : (1 + ‖x‖ ^ 2) ^ m ≤ (1 + sumAbs n x ^ 2) ^ m := by
    refine pow_le_pow_left₀ (by positivity) ?_ m
    have := norm_le_sumAbs x
    nlinarith [norm_nonneg x, sumAbs_nonneg n x]
  have hchain : (1 + ‖x‖ ^ 2) ^ m ≤ Real.exp (2 * (m : ℝ) * sumAbs n x) :=
    hmono.trans (poly_le_exp (sumAbs_nonneg n x) m)
  exact mul_le_mul_of_nonneg_left hchain hC

/-! ## 4. The criterion, exercised

A criterion that produces no new member is a criterion whose usefulness is
asserted rather than shown, and ERRATUM 48 is about exactly that: when a
unit's contribution is "this makes X possible", the check is to attempt X.
`sin xᵢ` is bounded and non-constant — both proved below — and no
non-constant polynomial is bounded, which is why it is a genuinely new entry
in the catalogue. That last inference is standard and is stated here as
prose, not proved.
-/

/-- `x ↦ sin xᵢ` is C¹, and its partial derivative in the `i`-th direction
    is `cos xᵢ`. -/
theorem hasFDerivAt_sinCoord (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => Real.sin (y i))
      (Real.cos (x i) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have hproj : HasFDerivAt (fun y : Fin n → ℝ => y i)
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact (Real.hasDerivAt_sin (x i)).comp_hasFDerivAt x hproj

theorem contDiff_sinCoord (i : Fin n) :
    ContDiff ℝ 1 fun y : Fin n → ℝ => Real.sin (y i) :=
  (Real.contDiff_sin.of_le le_top).comp (contDiff_apply ℝ ℝ i)

theorem fderiv_sinCoord (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => Real.sin (y i)) x (Pi.single i (1:ℝ))
      = Real.cos (x i) := by
  rw [(hasFDerivAt_sinCoord i x).fderiv]
  simp

/-- **A NEW MEMBER, PRODUCED BY THE CRITERION.** `x ↦ sin xᵢ` is in the
    textbook class with gradient `cos xᵢ · eᵢ`. Bounded and non-constant,
    hence not a polynomial. -/
theorem sin_coord_mem (i : Fin n) :
    SobolevWeakPi n (fun x => Real.sin (x i))
      (fun j x => fderiv ℝ (fun y : Fin n → ℝ => Real.sin (y i)) x
        (Pi.single j (1:ℝ))) := by
  refine sobolevWeakPi_of_contDiff (contDiff_sinCoord i) ?_ fun j => ?_
  · exact memLp_of_polyGrowth (C := 1) (m := 0)
      (Real.continuous_sin.comp (continuous_apply i)).aestronglyMeasurable
      fun x => by simpa using Real.abs_sin_le_one (x i)
  · refine memLp_of_polyGrowth (C := 1) (m := 0)
      ((continuous_gradient (contDiff_sinCoord i) j)).aestronglyMeasurable fun x => ?_
    rw [(hasFDerivAt_sinCoord i x).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, pow_zero, mul_one]
    rw [abs_mul]
    have hs : |(Pi.single j (1:ℝ) : Fin n → ℝ) i| ≤ 1 := by
      rw [Pi.single_apply]
      split <;> simp
    calc |Real.cos (x i)| * |(Pi.single j (1:ℝ) : Fin n → ℝ) i|
        ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _) hs (abs_nonneg _) zero_le_one
      _ = 1 := by ring

/-- Bounded — and the bound is not attained by being constant. -/
theorem sin_coord_bounded (i : Fin n) (x : Fin n → ℝ) : |Real.sin (x i)| ≤ 1 :=
  Real.abs_sin_le_one (x i)

/-- Non-constant, in every dimension in which the coordinate `i` exists. -/
theorem sin_coord_nonconstant (i : Fin n) :
    Real.sin ((0 : Fin n → ℝ) i)
      ≠ Real.sin ((Pi.single i (Real.pi / 2) : Fin n → ℝ) i) := by
  simp

/-- And the inequality runs on it. -/
theorem poincare_sin (i : Fin n) :
    (∫ x, Real.sin (x i) * Real.sin (x i) ∂gaussPi n)
        - (∫ x : Fin n → ℝ, Real.sin (x i) ∂gaussPi n) ^ 2
      ≤ ∑ j : Fin n, ∫ x, fderiv ℝ (fun y : Fin n → ℝ => Real.sin (y i)) x
            (Pi.single j (1:ℝ))
          * fderiv ℝ (fun y : Fin n → ℝ => Real.sin (y i)) x (Pi.single j (1:ℝ))
          ∂gaussPi n :=
  poincare_sobolevWeakPi n (sin_coord_mem i)

/-! ## 5. Review round 59 — the ways this could be hollow

**"The criterion could be vacuous, or could reproduce only what was already
known."** §4 produces `sin xᵢ`, bounded and non-constant. The textbook
class's previously known members were exactly the constants and the
coordinates — the first is not non-constant, the second is not bounded — so
this is neither. It arrives from the general theorem rather than from a
computation tailored to it, which is the whole point of having a
criterion.

**"The criterion could be an equivalence in disguise, so that C¹ is the
whole class."** It is not, and the estate can prove it is not:
`AbsSteinWitnessPi.absCoord_not_ae_differentiable` says `|xᵢ|` is not a.e.
equal to ANY differentiable function, while `absCoord_steinPairPi` puts it
in the class. So the class the inequality is proved on is strictly larger
than what any C¹ criterion reaches, and that is recorded immediately below
as a theorem rather than left as a remark.

**"§3 could be doing nothing, because `memLp_exp_sumAbs` already does the
work."** It does the hard half, and that is the point — the estate built it
on 11 August for a completely different purpose (the exponential-observable
OS2 chain), and it is being reused here. What §3 adds is the elementary
domination, which is the only part that is about polynomial growth at all.

**"The pairing could be the 1-d argument in disguise, and the claim that
the boundary term is absent could be wrong."** The boundary term is absent
because it is never formed: `integral_mul_partial` calls Mathlib's
several-variable statement once, and that statement's hypotheses are three
integrability facts and two differentiability facts, none of them a limit.
The vanishing-boundary work is real and it is in `W6ConversePi`, which is
imported and used by `steinPairPi_of_contDiff` — so the claim is not that
the work disappeared, but that it was done once and is not repeated here.
-/

/-- **THE CRITERION IS SUFFICIENT, NOT NECESSARY**, and the estate can
    exhibit the gap: `|xᵢ|` is in the Stein class and is not a.e. equal to
    any differentiable function, so no C¹ criterion reaches it. -/
theorem criterion_not_necessary (hn : 0 < n) :
    ∃ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SteinPairPi n f g ∧ ∀ h : (Fin n → ℝ) → ℝ, Differentiable ℝ h → ¬ (h =ᵐ[gaussPi n] f) := by
  refine ⟨AbsSteinWitnessPi.absCoord n ⟨0, hn⟩, AbsSteinWitnessPi.sgnCoord n ⟨0, hn⟩,
    AbsSteinWitnessPi.absCoord_steinPairPi n ⟨0, hn⟩, fun h hh =>
      AbsSteinWitnessPi.absCoord_not_ae_differentiable n ⟨0, hn⟩ h hh⟩

end

end SteinGeneralPi
