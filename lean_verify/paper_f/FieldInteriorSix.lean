import FieldInterior
import ExplicitThresholdCeiling

/-!
# The textbook contour count, carried to the route that is actually live

On 12 August the Peierls count was sharpened: the contours being counted are **cycles**, so
`PeierlsCover.card_cycCandidates_le_three` replaces `4^L` by `2 · 3^L`, and the estimate runs
under `6 e^{−4β} ≤ 1/2` with error `44 (6 e^{−4β})³` in place of `8 e^{−4β} ≤ 1/2` and
`22 (8 e^{−4β})³`. That improvement was carried through the **conditioned** chain —
`ExplicitThreshold.cond_le_six`, `magnetisation_ge_of_six` — and stopped there.

**It never reached the field chain.** `FieldCover.field_peierls_small` and every statement
above it (`FieldInterior.field_peierls_small_all`, `interiorDown_expectation_le`,
`interiorDown_expectation_beta_one`) still run on `8 e^{−4β} ≤ 1/2` and `22 (8 e^{−4β})³`.
That matters because of which chain is live: `PlusClassVanishes.tendsto_plusProb_zero` says
the `+` class the conditioned chain conditions on is asymptotically invisible under the
estate's own measure, so **the field chain is the one an argument for
`IsingBoundaryField.MagnetisationBound` has to go through**, and it was the one left on the
old constant.

## The composition was already available

Nothing new about contours is proved here. `FieldCover.field_peierls` bounds the field
probability by a sum over `PeierlsConditional.plusFamily` — **the same family the conditioned
chain uses** — and both the sharper family bound (`plusFamily_sum_le_three`) and the sharper
series bound (`SeriesBound.sum_le_cube_six`) already exist. The three compose. What follows is
that composition and its consequences.

## What comes out

* `field_peierls_small_six`, `field_peierls_small_all_six` — the per-site bound under the
  **weaker** hypothesis with the **smaller** error.
* `interiorDown_expectation_le_six` — the expected number of sites down with an interior
  cluster is at most `44 (6 e^{−4β})³ · n²`, at any field strength and no boundary condition.
* `interiorDown_expectation_beta_one_six` — at `β ≥ 1` the constant is below `3/50`, where
  `FieldInterior.interiorDown_expectation_beta_one` gave `3/40`.
* `interiorDown_expectation_five_sixths` — and at `β ≥ 5/6` the interior minority phase is
  **under half the box**. `β ≥ 5/6` is below the only *numerical* temperature the field chain
  had (`FieldInterior.interiorDown_expectation_beta_one`, at `β ≥ 1`), and — the sharper
  statement, because the old chain's hypothesis `8 e^{−4β} ≤ 1/2` holds from `β ≈ 0.694` and
  so is not itself a temperature — **the eight-count cannot reach the half statement there at
  all**: `six_buys_the_half`.
* `beta_gt_of_interior_half` — the ceiling, in the shape `ExplicitThresholdCeiling`
  established: this estimate cannot put the interior minority phase under half the box at any
  `β ≤ 4/5`. So `5/6` is within `4%` of what the route can give.
* `beta_gt_of_interior_half_eight` — and the **eight**-count's ceiling for the same statement
  is `β > 5/6` itself, so `six_buys_the_half` is a `¬` and not a failed attempt.

## What is unchanged

**This is still not a magnetisation bound**, for exactly the reason `FieldInterior`'s header
gives: `∑_p P(p down)` has a second term — sites whose down cluster reaches the edge — which
is the typical case at fixed `h` in a large box and which nothing here touches. A better
constant on the interior term does not create a bound on the other one.
`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace FieldInteriorSix

open IsingFiniteVolume IsingBoundaryField DualObstruction FieldCover FieldInterior

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The composition the field chain never made -/

/-- **THE FIELD PEIERLS BOUND WITH THE TEXTBOOK CONSTANT.** Weaker hypothesis than
`FieldCover.field_peierls_small`, smaller bound, same proof shape: the same union bound over
`plusFamily`, then the cycle count and the cycle series bound that the conditioned chain has
used since 12 August. -/
theorem field_peierls_small_six (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 6 * Real.exp (-(4 * β)) ≤ 1 / 2) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 :=
  le_trans (FieldCover.field_peierls hn h β hi hj)
    (le_trans (PeierlsConditional.plusFamily_sum_le_three _ β)
      (SeriesBound.sum_le_cube_six β hβ _))

/-- **AT EVERY SITE.** Boundary sites cost nothing, by
`FieldInterior.downInside_empty_of_boundary`: the event is empty there. -/
theorem field_peierls_small_all_six (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 6 * Real.exp (-(4 * β)) ≤ 1 / 2) (x : Site n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 := by
  classical
  by_cases hb : isBoundary x = true
  · rw [downInside_empty_of_boundary hb, Finset.sum_empty, zero_div]
    positivity
  · have hi : x.1.val + 1 < n := by
      have := x.1.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    have hj : x.2.val + 1 < n := by
      have := x.2.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    exact field_peierls_small_six hn h hβ hi hj

/-- **THE COUNT OVER THE WHOLE BOX, WITH THE TEXTBOOK CONSTANT.** At any field strength, with
no boundary condition, and under `6 e^{−4β} ≤ 1/2`. -/
theorem interiorDown_expectation_le_six (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 6 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    (∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 * ((n : ℝ) * n) := by
  classical
  set Z : ℝ := ∑ σ : Config n, Real.exp (-β * isingHB n h σ) with hZ
  have hZpos : 0 < Z := FieldEnergy.partition_pos n h β
  rw [sum_interiorDown_eq, div_le_iff₀ hZpos]
  have hsite : ∀ p : Site n, (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => DownInside σ p), Real.exp (-β * isingHB n h σ))
      ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 * Z := by
    intro p
    have hp := field_peierls_small_all_six hn h hβ p
    rw [div_le_iff₀ hZpos] at hp
    exact hp
  calc ∑ p : Site n, ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => DownInside σ p), Real.exp (-β * isingHB n h σ)
      ≤ ∑ _p : Site n, 44 * (6 * Real.exp (-(4 * β))) ^ 3 * Z :=
        Finset.sum_le_sum fun p _ => hsite p
    _ = 44 * (6 * Real.exp (-(4 * β))) ^ 3 * ((n : ℝ) * n) * Z := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [show (Fintype.card (Site n) : ℝ) = (n : ℝ) * n from by
          simp [Site, Fintype.card_prod]]
        ring

/-- **AND IT DOMINATES THE STATEMENT IT REPLACES, EVERYWHERE THAT ONE APPLIES.** Wherever
`FieldInterior.field_peierls_small_all` has a hypothesis, this file's version has one too, and
its bound is the smaller of the two (`SeriesBound.six_cube_le_eight_cube`). The header's claim
"weaker hypothesis, smaller bound" is this theorem and not a remark. -/
theorem six_dominates_eight (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) (x : Site n) :
    ((∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
          Real.exp (-β * isingHB n h σ)) /
        (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
        ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3) ∧
      44 * (6 * Real.exp (-(4 * β))) ^ 3 ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 := by
  refine ⟨field_peierls_small_all_six hn h ?_ x, SeriesBound.six_cube_le_eight_cube β⟩
  have hpos : (0 : ℝ) < Real.exp (-(4 * β)) := Real.exp_pos _
  linarith

/-! ## 2. Two temperatures, and the second is below anything this chain had

`44 (6 e^{−4β})³ = 9504 e^{−12β}`, so a temperature at which `12β` is a whole number costs one
power of `Real.exp_one_gt_d9` and nothing else — the same observation that let
`ExplicitThreshold` §3b reach `11/12`. -/

/-- `e^{12} > 158400`, from `Real.exp_one_gt_d9` and a twelfth power. -/
theorem exp_twelve_gt : (158400 : ℝ) < Real.exp 12 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ 12 = Real.exp 12 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc (158400 : ℝ) < (2.718 : ℝ) ^ 12 := by norm_num
    _ ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) he.le 12
    _ = Real.exp 12 := hpow

/-- `e^{10} > 19008`, likewise. -/
theorem exp_ten_gt : (19008 : ℝ) < Real.exp 10 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ 10 = Real.exp 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc (19008 : ℝ) < (2.718 : ℝ) ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) he.le 10
    _ = Real.exp 10 := hpow

/-- `e^{−12β} ≤ 1/19008` at `β ≥ 5/6`, where `12β = 10`. -/
theorem exp_twelve_le_five_sixths {β : ℝ} (hβ : 5 / 6 ≤ β) :
    Real.exp (-(12 * β)) ≤ 1 / 19008 := by
  have hmono : Real.exp (-(12 * β)) ≤ Real.exp (-10) :=
    Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-10) ≤ 1 / 19008 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt (by norm_num) exp_ten_gt)
  exact le_trans hmono hinv

/-- The threshold hypothesis at `β ≥ 5/6`, by comparing cubes rather than the numbers —
`ExplicitThreshold.thr_of_eleven_twelfths`'s trick at a lower temperature. -/
theorem thr_of_five_sixths {β : ℝ} (hβ : 5 / 6 ≤ β) :
    6 * Real.exp (-(4 * β)) ≤ 1 / 2 := by
  have hcube : Real.exp (-(4 * β)) ^ 3 < (1 / 12 : ℝ) ^ 3 := by
    rw [ExplicitThreshold.exp_cube]
    calc Real.exp (-(12 * β)) ≤ 1 / 19008 := exp_twelve_le_five_sixths hβ
      _ < (1 / 12 : ℝ) ^ 3 := by norm_num
  have := lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 1 / 12) hcube
  linarith

/-- **AT `β ≥ 1` THE CONSTANT IS BELOW `3/50`**, where `FieldInterior`'s eight-count version
gave `3/40`. Same temperature, same statement, smaller number — the count is the only thing
that changed. -/
theorem interiorDown_expectation_beta_one_six (hn : 0 < n) (h : ℝ) {β : ℝ} (hβ : 1 ≤ β) :
    (∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ (3 / 50 : ℝ) * ((n : ℝ) * n) := by
  have hthr : 6 * Real.exp (-(4 * β)) ≤ 1 / 2 :=
    thr_of_five_sixths (by linarith)
  refine le_trans (interiorDown_expectation_le_six hn h hthr) ?_
  have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
  have hcube : (6 * Real.exp (-(4 * β))) ^ 3 = 216 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  have hmono : Real.exp (-(12 * β)) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-12) ≤ 1 / 158400 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt (by norm_num) exp_twelve_gt)
  rw [hcube]
  nlinarith [hmono, hinv, hn2]

/-- The six-count error term is at most a half from `β = 5/6` up: `9504 e^{−12β} ≤ 9504/19008`. -/
theorem eps_le_of_five_sixths {β : ℝ} (hβ : 5 / 6 ≤ β) :
    44 * (6 * Real.exp (-(4 * β))) ^ 3 ≤ 1 / 2 := by
  have hcube : (6 * Real.exp (-(4 * β))) ^ 3 = 216 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  rw [hcube]
  nlinarith [exp_twelve_le_five_sixths hβ]

/-- **AND AT `β ≥ 5/6` THE INTERIOR MINORITY PHASE IS UNDER HALF THE BOX.** Below the only
numerical temperature the field chain had — `FieldInterior`'s statements are at `β ≥ 1` — and,
by `six_buys_the_half` below, below anything the eight-count can say in this shape at all.

Weaker in what it asserts — a half rather than `3/50` — and that is the trade the temperature
buys. -/
theorem interiorDown_expectation_five_sixths (hn : 0 < n) (h : ℝ) {β : ℝ} (hβ : 5 / 6 ≤ β) :
    (∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ (1 / 2 : ℝ) * ((n : ℝ) * n) := by
  refine le_trans (interiorDown_expectation_le_six hn h (thr_of_five_sixths hβ)) ?_
  have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
  nlinarith [eps_le_of_five_sixths hβ, hn2]

/-! ## 3. And the ceiling, so the number is not chased further than it goes -/

/-- `e^{48} < 19008⁵`, from `Real.exp_one_lt_d9` and a forty-eighth power. -/
theorem exp_fortyeight_lt : Real.exp 48 < (19008 : ℝ) ^ 5 := by
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 1 ^ 48 = Real.exp 48 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc Real.exp 48 = Real.exp 1 ^ 48 := hpow.symm
    _ ≤ (2.7183 : ℝ) ^ 48 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 48
    _ < (19008 : ℝ) ^ 5 := by norm_num

/-- `e^{48/5} < 19008`, by taking fifth powers. -/
theorem exp_fortyeight_fifths_lt : Real.exp (48 / 5 : ℝ) < 19008 := by
  have h5 : Real.exp (48 / 5 : ℝ) ^ 5 = Real.exp 48 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlt : Real.exp (48 / 5 : ℝ) ^ 5 < (19008 : ℝ) ^ 5 := by
    rw [h5]
    exact exp_fortyeight_lt
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) hlt

/-- **THIS ESTIMATE CANNOT PUT THE INTERIOR MINORITY PHASE UNDER HALF THE BOX AT OR BELOW
`β = 4/5`.** So `interiorDown_expectation_five_sixths` is within `4%` of everything the route
gives, and the exact limit is `ln(19008)/12 ≈ 0.82106` — arithmetic outside Lean, labelled as
`ERRATUM 46` requires.

A fact about the estimate, not about the model, exactly as in `ExplicitThresholdCeiling`. -/
theorem beta_gt_of_interior_half {β : ℝ}
    (h : 44 * (6 * Real.exp (-(4 * β))) ^ 3 ≤ 1 / 2) : 4 / 5 < β := by
  have hcube : (6 * Real.exp (-(4 * β))) ^ 3 = 216 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  rw [hcube] at h
  have hE : Real.exp (-(12 * β)) ≤ 1 / 19008 := by linarith
  have hEE : (19008 : ℝ) ≤ Real.exp (12 * β) :=
    ExplicitThresholdCeiling.exp_ge_of_exp_neg_le (by norm_num) hE
  have hlt : Real.exp (48 / 5 : ℝ) < Real.exp (12 * β) :=
    lt_of_lt_of_le exp_fortyeight_fifths_lt hEE
  have h12 : (48 / 5 : ℝ) < 12 * β := Real.exp_lt_exp.mp hlt
  linarith

/-- `e^{10} < 22528`, from `Real.exp_one_lt_d9` and a tenth power — the companion of
`exp_ten_gt`, in the other direction. -/
theorem exp_ten_lt : Real.exp 10 < (22528 : ℝ) := by
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 1 ^ 10 = Real.exp 10 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc Real.exp 10 = Real.exp 1 ^ 10 := hpow.symm
    _ ≤ (2.7183 : ℝ) ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 10
    _ < 22528 := by norm_num

/-- **THE EIGHT-COUNT CANNOT PUT THE INTERIOR MINORITY PHASE UNDER HALF THE BOX AT OR BELOW
`β = 5/6`.** Its error term is `22 (8 e^{−4β})³ = 11264 e^{−12β}`, and `e^{10} < 22528`. -/
theorem beta_gt_of_interior_half_eight {β : ℝ}
    (h : 22 * (8 * Real.exp (-(4 * β))) ^ 3 ≤ 1 / 2) : 5 / 6 < β := by
  have hcube : (8 * Real.exp (-(4 * β))) ^ 3 = 512 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  rw [hcube] at h
  have hE : Real.exp (-(12 * β)) ≤ 1 / 22528 := by linarith
  have hEE : (22528 : ℝ) ≤ Real.exp (12 * β) :=
    ExplicitThresholdCeiling.exp_ge_of_exp_neg_le (by norm_num) hE
  have hlt : Real.exp 10 < Real.exp (12 * β) := lt_of_lt_of_le exp_ten_lt hEE
  have h12 : (10 : ℝ) < 12 * β := Real.exp_lt_exp.mp hlt
  linarith

/-- **THE SHARPER COUNT BUYS THE HALF STATEMENT OUTRIGHT, ON THE LIVE CHAIN.** At `β = 5/6`
the six-count error term is under a half and the eight-count one *cannot* be — meeting it
would force `β > 5/6`.

`ExplicitThresholdCeiling.six_buys_the_temperature` is the same shape for the conditioned
chain at `β = 11/12`. This is that statement where it matters: the chain that does not
condition on `+`. -/
theorem six_buys_the_half :
    (44 * (6 * Real.exp (-(4 * (5 / 6 : ℝ)))) ^ 3 ≤ 1 / 2) ∧
      ¬ (22 * (8 * Real.exp (-(4 * (5 / 6 : ℝ)))) ^ 3 ≤ 1 / 2) := by
  refine ⟨eps_le_of_five_sixths le_rfl, fun h => ?_⟩
  have := beta_gt_of_interior_half_eight h
  linarith

end FieldInteriorSix
