import PlusMagnetisation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The boundary-field integral is a ratio of sums — and at `h = 0` it is zero

`ERRATUM 86` recorded that four file headers had asserted, without checking, that what
separates this Peierls chain from `IsingBoundaryField.MagnetisationBound` is "the `h → 0⁺`
limit". The correction was to call the comparison **unexamined**. This file examines it, and
the answer is worse than unexamined: **`h → 0` is not merely the wrong route, it is a
disproof.**

## Two things, and the first is plumbing

* **`integral_isingMeasure`** — `∫ f ∂(isingMeasure n h β)` **is** the ratio of finite sums
  `(∑_σ f σ e^{-β H_h σ}) / (∑_σ e^{-β H_h σ})`. `PlusMagnetisation`'s header named this as
  one of the two things separating its theorem from `MagnetisationBound`, and called it "the
  object". It is now an identity with a proof rather than a gap: the Gibbs measure of
  `FiniteGibbs` is a density against the counting measure, and on a finite type an integral
  against the counting measure is a sum.

  **This does not by itself close anything.** Read carefully what it does and does not
  match. It removes the mismatch of *kind* — integral against a measure, versus ratio of
  sums — and leaves the mismatch of *domain* untouched: this sum runs over **all**
  configurations of the **field** Hamiltonian, and `PlusMagnetisation`'s runs over the
  **`+` class** of the **field-free** one. Same shape, different objects.

* **`integral_magnetisation_zero_field`** — at `h = 0` the magnetisation integral is
  **exactly zero**, at every `β` and in every box. The Hamiltonian at zero field is the
  field-free one, which is flip-invariant, and the magnetisation is flip-odd, so the sum is
  its own negative.

## Why that is a disproof and not a caveat

`MagnetisationBound β h m` asks for `m · n² ≤ ∫ magnetisation`. At `h = 0` the right-hand
side is `0`, so **`MagnetisationBound β 0 m` holds exactly when `m ≤ 0`** — that is
`magnetisationBound_zero_field_iff`, a *refutation* rather than an estimate, and sharp:
every positive `m` fails and every non-positive one passes for the empty reason. More: the
integral is continuous in `h`, so it tends to `0` as `h → 0` from either side
(`tendsto_integral_zero_field`). A sentence that named `h → 0⁺` as the route from this chain
to `MagnetisationBound` was therefore naming the one limit along which the conclusion
provably fails.

**Where the `h → 0⁺` story does belong.** For a *bulk* field in the *infinite-volume* limit,
`lim_{h ↓ 0} lim_{n → ∞}` is the standard definition of spontaneous magnetisation and the
order of the two limits is the whole content. Nothing here contradicts that. What is refuted
is the finite-volume reading, which is the only reading this estate can state, because
`MagnetisationBound` quantifies over boxes at a **fixed** `h` and `isingHB` carries a
**boundary** field.

## What this leaves

The comparison is no longer unexamined and no longer open in the `h → 0` direction. Which
direction *does* recover a `+` boundary condition from a boundary field is a separate
question, answered in `BoundaryFieldLimit`. `MagnetisationBound` remains untouched, and is
now known to be **false at `h = 0`** for positive `m`.
-/

namespace BoundaryFieldRatio

open IsingFiniteVolume IsingBoundaryField MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The partition sum is positive -/

/-- The boundary-field partition sum, over **all** configurations, is positive: a finite sum
of exponentials over a nonempty type. -/
theorem partition_pos (n : ℕ) (h β : ℝ) :
    0 < ∑ σ : Config n, Real.exp (-β * isingHB n h σ) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

/-! ## 2. The integral is the ratio of sums

`FiniteGibbs.gibbs` is `Z⁻¹ • (ν.withDensity e^{-βH})` with `ν` the counting measure, and on
a finite type `∫ f ∂count = ∑ f`. Three rewrites and a cast. -/

/-- **THE OBJECT, IDENTIFIED.** The integral of `f` against the boundary-field Gibbs measure
is the ratio of finite sums that every statement in this chain is written with. -/
theorem integral_isingMeasure (n : ℕ) (h β : ℝ) (f : Config n → ℝ) :
    ∫ σ, f σ ∂(isingMeasure n h β) =
      (∑ σ : Config n, f σ * Real.exp (-β * isingHB n h σ)) /
        (∑ σ : Config n, Real.exp (-β * isingHB n h σ)) := by
  have hmeas : Measurable
      (fun σ : Config n => ENNReal.ofReal (Real.exp (-β * isingHB n h σ))) :=
    measurable_of_countable _
  have hZ : FiniteGibbs.Z β (isingHB n h) (Measure.count : Measure (Config n))
      = ENNReal.ofReal (∑ σ : Config n, Real.exp (-β * isingHB n h σ)) := by
    rw [FiniteGibbs.Z, lintegral_count, tsum_fintype,
      ENNReal.ofReal_sum_of_nonneg (fun σ _ => (Real.exp_pos _).le)]
  rw [isingMeasure, FiniteGibbs.gibbs, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun σ => ENNReal.ofReal_lt_top),
    integral_count, hZ]
  have hpos := partition_pos n h β
  have hinner : ∑ x : Config n, (ENNReal.ofReal (Real.exp (-β * isingHB n h x))).toReal • f x
      = ∑ σ : Config n, f σ * Real.exp (-β * isingHB n h σ) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le, hinner, smul_eq_mul, inv_mul_eq_div]

/-! ## 3. At zero field the magnetisation integral is exactly zero

The flip is an involution of the configurations; it fixes `isingH` and negates the
magnetisation, so the weighted sum equals its own negative. -/

/-- The flip-weighted sum vanishes: `∑_σ M(σ) e^{-β H(σ)} = 0` for the **field-free**
Hamiltonian. -/
theorem sum_magnetisation_weight_zero (n : ℕ) (β : ℝ) :
    ∑ σ : Config n, magnetisation n σ * Real.exp (-β * isingH n σ) = 0 := by
  have hinv : Function.Involutive (IsingFiniteVolume.flip : Config n → Config n) := by
    intro σ; funext p; simp [IsingFiniteVolume.flip]
  have hbij : Function.Bijective (IsingFiniteVolume.flip : Config n → Config n) :=
    hinv.bijective
  have hswap : ∑ σ : Config n,
        magnetisation n (IsingFiniteVolume.flip σ) *
          Real.exp (-β * isingH n (IsingFiniteVolume.flip σ))
      = ∑ σ : Config n, magnetisation n σ * Real.exp (-β * isingH n σ) :=
    Fintype.sum_bijective IsingFiniteVolume.flip hbij _ _ fun _ => rfl
  have hterm : ∀ σ : Config n,
      magnetisation n (IsingFiniteVolume.flip σ) *
          Real.exp (-β * isingH n (IsingFiniteVolume.flip σ))
        = -(magnetisation n σ * Real.exp (-β * isingH n σ)) := by
    intro σ
    rw [magnetisation_flip, isingH_flip]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), Finset.sum_neg_distrib] at hswap
  linarith

/-- **AT ZERO FIELD THE MAGNETISATION IS ZERO.** Not small, not bounded — zero, at every
inverse temperature and in every box. -/
theorem integral_magnetisation_zero_field (n : ℕ) (β : ℝ) :
    ∫ σ, magnetisation n σ ∂(isingMeasure n 0 β) = 0 := by
  rw [integral_isingMeasure]
  have hterm : ∀ σ : Config n, magnetisation n σ * Real.exp (-β * isingHB n 0 σ)
      = magnetisation n σ * Real.exp (-β * isingH n σ) := by
    intro σ; rw [isingHB_zero]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), sum_magnetisation_weight_zero, zero_div]

/-! ## 4. So `h → 0` is the wrong limit, provably -/

/-- **`MagnetisationBound` IS FALSE AT ZERO FIELD.** For every positive `m` and every `β`,
`MagnetisationBound β 0 m` fails — at the one-site box already, where it asks `m ≤ 0`.

This is the first statement in this chain that refutes rather than estimates, and it is
what `ERRATUM 86` was missing: the `h → 0⁺` route named in four headers was not merely
unchecked, it runs into a proof that the limit value is zero. -/
theorem not_magnetisationBound_zero_field (β m : ℝ) (hm : 0 < m) :
    ¬ MagnetisationBound β 0 m := by
  intro hbound
  have h1 := hbound 1 Nat.one_pos
  rw [integral_magnetisation_zero_field] at h1
  norm_num at h1
  linarith

/-- **AND THE REFUTATION IS SHARP.** At zero field `MagnetisationBound β 0 m` holds for
exactly the non-positive `m`, and holds there only because the bound asks for nothing. There
is no residual reading of the zero-field statement under which it says something true. -/
theorem magnetisationBound_zero_field_iff (β m : ℝ) :
    MagnetisationBound β 0 m ↔ m ≤ 0 := by
  constructor
  · intro hbound
    by_contra hm
    exact not_magnetisationBound_zero_field β m (lt_of_not_ge hm) hbound
  · intro hm n hn
    rw [integral_magnetisation_zero_field]
    have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg hm hn2

/-- The integral is continuous in the field strength: a ratio of finite sums of
exponentials, with a denominator that never vanishes. -/
theorem continuous_integral_magnetisation (n : ℕ) (β : ℝ) :
    Continuous fun h : ℝ => ∫ σ, magnetisation n σ ∂(isingMeasure n h β) := by
  have heq : (fun h : ℝ => ∫ σ, magnetisation n σ ∂(isingMeasure n h β))
      = fun h : ℝ => (∑ σ : Config n, magnetisation n σ * Real.exp (-β * isingHB n h σ)) /
          (∑ σ : Config n, Real.exp (-β * isingHB n h σ)) := by
    funext h; exact integral_isingMeasure n h β _
  rw [heq]
  have hnum : Continuous fun h : ℝ =>
      ∑ σ : Config n, magnetisation n σ * Real.exp (-β * isingHB n h σ) := by
    refine continuous_finset_sum _ fun σ _ => continuous_const.mul (Real.continuous_exp.comp ?_)
    simp only [isingHB]
    fun_prop
  have hden : Continuous fun h : ℝ => ∑ σ : Config n, Real.exp (-β * isingHB n h σ) := by
    refine continuous_finset_sum _ fun σ _ => Real.continuous_exp.comp ?_
    simp only [isingHB]
    fun_prop
  exact hnum.div hden fun h => (partition_pos n h β).ne'

/-- **AND THE LIMIT AS THE FIELD IS TURNED OFF IS ZERO**, from either side, so in
particular along `h → 0⁺`. The sentence corrected by `ERRATUM 86` named exactly the limit
along which the magnetisation vanishes. -/
theorem tendsto_integral_zero_field (n : ℕ) (β : ℝ) :
    Tendsto (fun h : ℝ => ∫ σ, magnetisation n σ ∂(isingMeasure n h β)) (nhds 0) (nhds 0) := by
  have := (continuous_integral_magnetisation n β).tendsto 0
  rwa [integral_magnetisation_zero_field] at this

end BoundaryFieldRatio
