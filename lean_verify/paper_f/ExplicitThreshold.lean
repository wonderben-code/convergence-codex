import BoundaryFieldLimit
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The temperature, exhibited

Every low-temperature statement in this chain is of the form `∀ᶠ β in atTop`, and
`SeriesBound`'s header says plainly what that costs:

> `∀ᶠ β in atTop` says "for all large enough `β`", with the threshold *not* exhibited. The
> proof is by a limit, so a reader wanting an explicit temperature will not find one here.

**This file finds one.** Nothing new is proved about the model; what happens is that the two
explicit inequalities already in the chain — `SideLength.peierls_closed_form` and
`SeriesBound.sum_le_cube` — are carried through the four filter statements that were built on
top of them, so that the conclusion comes with a number.

## The explicit chain

* **`cond_le`** — if `8 e^{-4β} ≤ 1/2` then, in **every** box and at **every** site
  (boundary sites included, where the event is empty), the conditional probability that the
  site is down given `+` boundary conditions is at most `22 (8 e^{-4β})³`.
* **`magnetisation_ge_of`** — hence the conditional magnetisation is at least
  `(1 - 44 (8 e^{-4β})³) n²`. Both hypotheses and conclusion are inequalities in `β`; there
  is no filter anywhere.

## And a number

`Real.exp_one_gt_d9` turns that into arithmetic:

> **`magnetisation_two_thirds`** — at `β ≥ 1`, in **every** box, the conditional expectation
> of the magnetisation given `+` boundary conditions is at least `⅔ n²`.

**How good is `1`?** Two comparisons, and both are arithmetic done **outside** Lean and
labelled as such, because a number quoted in the estate's voice is what `ERRATUM 46` is
about. (i) *Against this chain's own limit*: the closed form cannot be used at all unless
`8 e^{-4β} ≤ 1/2`, and `1` is within about half of that. (ii) *Against the physics*: Onsager's
critical value for the square lattice is `β ≈ 0.4407` in the single-count convention, hence
about `0.22` in this estate's double-counted one — **an external fact this estate does not
prove**. So the threshold is roughly four to five times the truth.

**⚠ CLAUSE (i) SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`, found by
`ERRATUM 311`).** *"The closed form cannot be used at all unless `8 e^{-4β} ≤ 1/2`"* stopped
being true when §1's `cond_le_six` landed **in this same file**: there is now a closed form
under `6 e^{-4β} ≤ 1/2`, a strictly weaker hypothesis, and `magnetisation_two_thirds_six`
reaches `⅔ n²` at `β ≥ 11/12` rather than `β ≥ 1`.
`ExplicitThresholdCeiling.six_buys_the_temperature` proves that gap is real. **Clause (ii)
and the conclusion stand**: `11/12` against `0.22` is still four to five times the truth,
and a Peierls argument still gives a finite temperature and never the right one.

**A Peierls argument gives
a finite temperature, never the right one**; what has changed is that the estate now names
its finite temperature instead of naming none.

**`magnetisation_half_measure`** carries the conclusion to the estate's own measure object via
`BoundaryFieldLimit.tendsto_integral`, where the `∀ᶠ h` remains — that quantifier is the
subject of `PlusClassVanishes` and is not touched here.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace ExplicitThreshold

open IsingFiniteVolume IsingBoundaryField DualObstruction MeasureTheory Filter
open PlusMagnetisation PeierlsConditional SeriesBound

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The conditional estimate, with the threshold written down -/

/-- **THE PEIERLS ESTIMATE WITH AN EXPLICIT TEMPERATURE.** Under `8 e^{-4β} ≤ 1/2`, in every
box and at **every** site, the conditional probability that the site is down given `+`
boundary conditions is at most `22 (8 e^{-4β})³`.

Boundary sites are included and cost nothing: under `+` boundary the event is empty. -/
theorem cond_le (hn : 0 < n) {β : ℝ} (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) (x : Site n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingH n σ))
      ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 := by
  classical
  have hrhs : (0 : ℝ) ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 := by positivity
  by_cases hb : isBoundary x = true
  · rw [down_empty_of_boundary hb, Finset.sum_empty, zero_div]
    exact hrhs
  · have hi : x.1.val + 1 < n := by
      have := x.1.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    have hj : x.2.val + 1 < n := by
      have := x.2.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    exact le_trans (peierls_conditional hn β hi hj)
      (le_trans (plusFamily_sum_le _ β) (sum_le_cube β hβ _))

/-- **THE SAME ESTIMATE AT THE TEXTBOOK CONSTANT.** Under `6 e^{-4β} ≤ 1/2` — a strictly
weaker hypothesis than `cond_le`'s, so a strictly lower temperature threshold, `ln 12 / 4 ≈
0.621` against `ln 16 / 4 ≈ 0.693` — the same conditional probability is at most
`44 (6 e^{-4β})³`, which `SeriesBound.six_cube_le_eight_cube` shows is the smaller bound.

The entire gain is one hypothesis that was being discarded: the contours counted are
**cycles**, and a cycle cannot immediately reverse (`WalkCount` §1b, `ERRATUM 126`). -/
theorem cond_le_six (hn : 0 < n) {β : ℝ} (hβ : 6 * Real.exp (-(4 * β)) ≤ 1 / 2) (x : Site n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingH n σ))
      ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 := by
  classical
  have hrhs : (0 : ℝ) ≤ 44 * (6 * Real.exp (-(4 * β))) ^ 3 := by positivity
  by_cases hb : isBoundary x = true
  · rw [down_empty_of_boundary hb, Finset.sum_empty, zero_div]
    exact hrhs
  · have hi : x.1.val + 1 < n := by
      have := x.1.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    have hj : x.2.val + 1 < n := by
      have := x.2.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    exact le_trans (peierls_conditional hn β hi hj)
      (le_trans (plusFamily_sum_le_three _ β) (sum_le_cube_six β hβ _))

/-! ## 2. The magnetisation, with the threshold written down

`PlusMagnetisation.magnetisation_ge`'s argument, with the explicit bound of §1 in place of an
`ε` supplied by a filter. -/

/-- **THE CONDITIONAL MAGNETISATION, WITH AN EXPLICIT TEMPERATURE.** Under
`8 e^{-4β} ≤ 1/2`, in every box, the conditional expectation of the magnetisation given `+`
boundary conditions is at least `(1 - 44 (8 e^{-4β})³) n²`. -/
theorem magnetisation_ge_of (hn : 0 < n) {β : ℝ} (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    (1 - 2 * (22 * (8 * Real.exp (-(4 * β))) ^ 3)) * ((n : ℝ) * n) ≤
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
  classical
  set ε : ℝ := 22 * (8 * Real.exp (-(4 * β))) ^ 3 with hε
  set Z : ℝ := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    Real.exp (-β * isingH n σ) with hZ
  have hZpos : 0 < Z := plus_partition_pos β
  rw [le_div_iff₀ hZpos]
  have hsplit : ∀ p : Site n, ((Finset.univ : Finset (Config n)).filter
      (fun σ => PlusBoundary σ)).filter (fun σ => σ p = false) =
      (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ ∧ σ p = false) := by
    intro p; ext σ; simp
  have hnum : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
      magnetisation n σ * Real.exp (-β * isingH n σ) =
      ∑ p : Site n, (Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ)) := by
    have hexp : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        magnetisation n σ * Real.exp (-β * isingH n σ) =
          ∑ p : Site n, spin (σ p) * Real.exp (-β * isingH n σ) := by
      intro σ _
      rw [magnetisation, Finset.sum_mul]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [sum_spin_eq β p, hsplit p]
  rw [hnum]
  have hsite : ∀ p : Site n, (1 - 2 * ε) * Z ≤
      Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ) := by
    intro p
    have hle := cond_le hn hβ p
    rw [div_le_iff₀ hZpos] at hle
    nlinarith
  calc (1 - 2 * ε) * ((n : ℝ) * n) * Z
      = ∑ _p : Site n, (1 - 2 * ε) * Z := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [show (Fintype.card (Site n) : ℝ) = (n : ℝ) * n from by
          simp [Site, Fintype.card_prod]]
        ring
    _ ≤ _ := Finset.sum_le_sum fun p _ => hsite p

/-- **THE SAME MAGNETISATION BOUND AT THE TEXTBOOK CONSTANT.** Hypothesis
`6 e^{-4β} ≤ 1/2` rather than `8 e^{-4β} ≤ 1/2`, and `ε = 44 (6 e^{-4β})³` rather than
`22 (8 e^{-4β})³` — weaker hypothesis, smaller `ε`, so a better bound at a lower
temperature. Proof identical to `magnetisation_ge_of` with `cond_le_six` in place of
`cond_le`; `ERRATUM 126`.

**What this does NOT sharpen, and this time the trace was followed.** `magnetisation_two_thirds`
and `magnetisation_half_measure` are stated at `β ≥ 1`, and `β ≥ 1` already satisfies both
hypotheses, so their statements are unchanged. Getting a *lower* `β` out of them needs a new
exponential estimate at a non-integer point — `exp_le_of_one_le` is proved from
`Real.exp_one_gt_d9` and an integer power — and that is not done here. -/
theorem magnetisation_ge_of_six (hn : 0 < n) {β : ℝ} (hβ : 6 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    (1 - 2 * (44 * (6 * Real.exp (-(4 * β))) ^ 3)) * ((n : ℝ) * n) ≤
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
  classical
  set ε : ℝ := 44 * (6 * Real.exp (-(4 * β))) ^ 3 with hε
  set Z : ℝ := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    Real.exp (-β * isingH n σ) with hZ
  have hZpos : 0 < Z := plus_partition_pos β
  rw [le_div_iff₀ hZpos]
  have hsplit : ∀ p : Site n, ((Finset.univ : Finset (Config n)).filter
      (fun σ => PlusBoundary σ)).filter (fun σ => σ p = false) =
      (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ ∧ σ p = false) := by
    intro p; ext σ; simp
  have hnum : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
      magnetisation n σ * Real.exp (-β * isingH n σ) =
      ∑ p : Site n, (Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ)) := by
    have hexp : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        magnetisation n σ * Real.exp (-β * isingH n σ) =
          ∑ p : Site n, spin (σ p) * Real.exp (-β * isingH n σ) := by
      intro σ _
      rw [magnetisation, Finset.sum_mul]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [sum_spin_eq β p, hsplit p]
  rw [hnum]
  have hsite : ∀ p : Site n, (1 - 2 * ε) * Z ≤
      Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ) := by
    intro p
    have hle := cond_le_six hn hβ p
    rw [div_le_iff₀ hZpos] at hle
    nlinarith
  calc (1 - 2 * ε) * ((n : ℝ) * n) * Z
      = ∑ _p : Site n, (1 - 2 * ε) * Z := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [show (Fintype.card (Site n) : ℝ) = (n : ℝ) * n from by
          simp [Site, Fintype.card_prod]]
        ring
    _ ≤ _ := Finset.sum_le_sum fun p _ => hsite p

/-! ## 3. And at `β ≥ 1` the arithmetic closes -/

/-- `8 e^{-4β} ≤ 3/20` from `β ≥ 1`, via `Real.exp_one_gt_d9`. -/
theorem exp_le_of_one_le {β : ℝ} (hβ : 1 ≤ β) : 8 * Real.exp (-(4 * β)) ≤ 3 / 20 := by
  have hmono : Real.exp (-(4 * β)) ≤ Real.exp (-4) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 : (54.5 : ℝ) < Real.exp 4 := by
    rw [← hpow]
    calc (54.5 : ℝ) < (2.718 : ℝ) ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he.le 4
  have hneg : Real.exp (-4) < 1 / 54.5 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) h4
  nlinarith [hmono, hneg]

/-- **A TEMPERATURE, AT LAST.** At `β ≥ 1`, in **every** box, the conditional expectation of
the magnetisation given `+` boundary conditions is at least `⅔ n²`.

Not the critical temperature and not close to it — see the header — but a number, where the
chain previously offered only "large enough". -/
theorem magnetisation_two_thirds (hn : 0 < n) {β : ℝ} (hβ : 1 ≤ β) :
    (2 / 3 : ℝ) * ((n : ℝ) * n) ≤
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
  have ht := exp_le_of_one_le hβ
  have ht0 : 0 < 8 * Real.exp (-(4 * β)) := by positivity
  have hthr : 8 * Real.exp (-(4 * β)) ≤ 1 / 2 := by linarith
  refine le_trans ?_ (magnetisation_ge_of hn hthr)
  have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
  have hcube : (8 * Real.exp (-(4 * β))) ^ 3 ≤ (3 / 20 : ℝ) ^ 3 :=
    pow_le_pow_left₀ ht0.le ht 3
  nlinarith [hcube, hn2]

/-! ## 3b. And with the textbook constant the temperature comes down

`exp_le_of_one_le` above needs `β ≥ 1` because it bounds `exp (-4β)` by `exp (-4)` and
`4` is a whole number. **The cube in the estimate is what lets a fraction in**: `ε` involves
`(6 e^{-4β})³ = 216 e^{-12β}`, and `12β` is a whole number at `β = 11/12`. So the argument
runs at `11/12` with no new kind of estimate — the same `Real.exp_one_gt_d9`, raised to the
eleventh rather than the fourth.

**And it needs the new constant.** At `β = 11/12` the old chain gives
`22 (8 e^{-4β})³ = 11264 e^{-12β} ≈ 0.188`, so `1 - 2ε ≈ 0.624 < ⅔` and
`magnetisation_two_thirds` would fail. The textbook constant gives
`44 (6 e^{-4β})³ = 9504 e^{-12β} ≈ 0.159`, and `1 - 2ε ≈ 0.678 > ⅔`. **This is the first
statement in the estate that the sharper count buys outright rather than merely improves.**
-/

/-- `e^11 > 59000`, from `Real.exp_one_gt_d9` and an eleventh power. -/
theorem exp_eleven_gt : (59000 : ℝ) < Real.exp 11 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ 11 = Real.exp 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc (59000 : ℝ) < (2.718 : ℝ) ^ 11 := by norm_num
    _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) he.le 11
    _ = Real.exp 11 := hpow

/-- `e^{-4β}` cubed is `e^{-12β}`, which is the whole trick: it turns the fractional
exponent `4 · (11/12)` into the whole number `11`. -/
theorem exp_cube {β : ℝ} : Real.exp (-(4 * β)) ^ 3 = Real.exp (-(12 * β)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_twelve_le {β : ℝ} (hβ : 11 / 12 ≤ β) : Real.exp (-(12 * β)) ≤ 1 / 59000 := by
  have hmono : Real.exp (-(12 * β)) ≤ Real.exp (-11) :=
    Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-11) ≤ 1 / 59000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt (by norm_num) exp_eleven_gt)
  exact le_trans hmono hinv

/-- The threshold hypothesis at `β ≥ 11/12`, by comparing cubes rather than the numbers. -/
theorem thr_of_eleven_twelfths {β : ℝ} (hβ : 11 / 12 ≤ β) :
    6 * Real.exp (-(4 * β)) ≤ 1 / 2 := by
  have hcube : Real.exp (-(4 * β)) ^ 3 < (1 / 12 : ℝ) ^ 3 := by
    rw [exp_cube]
    calc Real.exp (-(12 * β)) ≤ 1 / 59000 := exp_twelve_le hβ
      _ < (1 / 12 : ℝ) ^ 3 := by norm_num
  have := lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0:ℝ) ≤ 1 / 12) hcube
  linarith

/-- The error term at `β ≥ 11/12`. -/
theorem eps_le_of_eleven_twelfths {β : ℝ} (hβ : 11 / 12 ≤ β) :
    44 * (6 * Real.exp (-(4 * β))) ^ 3 ≤ 9504 / 59000 := by
  have h : (6 * Real.exp (-(4 * β))) ^ 3 = 216 * Real.exp (-(12 * β)) := by
    rw [mul_pow, exp_cube]
    norm_num
  rw [h]
  have := exp_twelve_le hβ
  nlinarith [Real.exp_pos (-(12 * β))]

/-- **THE SAME `⅔ n²`, AT `β ≥ 11/12` RATHER THAN `β ≥ 1`.** Everything else is verbatim
`magnetisation_two_thirds`; the temperature is the only thing that changed, and it changed
because the contours being counted are cycles. -/
theorem magnetisation_two_thirds_six (hn : 0 < n) {β : ℝ} (hβ : 11 / 12 ≤ β) :
    (2 / 3 : ℝ) * ((n : ℝ) * n) ≤
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
  refine le_trans ?_ (magnetisation_ge_of_six hn (thr_of_eleven_twelfths hβ))
  have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
  nlinarith [eps_le_of_eleven_twelfths hβ, hn2]

/-! ## 4. The same constant against the estate's own measure -/

/-- **AT `β ≥ 1`, AND AGAINST `isingMeasure`.** For every box, at all large enough field
strength, the boundary-field expectation of the magnetisation is at least `½ n²`.

The `∀ᶠ h` is `BoundaryFieldLimit`'s and stays: `PlusClassVanishes` is why it cannot be
removed by conditioning. What is new here is that the **temperature** is a number. -/
theorem magnetisation_half_measure (hn : 0 < n) {β : ℝ} (hβ : 1 ≤ β) :
    ∀ᶠ h : ℝ in atTop,
      ((n : ℝ) * n) / 2 ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β) := by
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hlim := BoundaryFieldLimit.tendsto_integral n hβ0 (magnetisation n)
  have hge := magnetisation_two_thirds hn hβ
  have hn2 : (0 : ℝ) < (n : ℝ) * n := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hlt : ((n : ℝ) * n) / 2 <
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
    nlinarith [hge, hn2]
  exact (hlim.eventually (lt_mem_nhds hlt)).mono fun h hh => hh.le

/-- **AND THE MEASURE-LEVEL STATEMENT AT `β ≥ 11/12`.** Verbatim
`magnetisation_half_measure` with the sharper temperature; the `∀ᶠ h` is
`BoundaryFieldLimit`'s and is untouched, for the reason `PlusClassVanishes` gives. -/
theorem magnetisation_half_measure_six (hn : 0 < n) {β : ℝ} (hβ : 11 / 12 ≤ β) :
    ∀ᶠ h : ℝ in atTop,
      ((n : ℝ) * n) / 2 ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β) := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have hlim := BoundaryFieldLimit.tendsto_integral n hβ0 (magnetisation n)
  have hge := magnetisation_two_thirds_six hn hβ
  have hn2 : (0 : ℝ) < (n : ℝ) * n := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hlt : ((n : ℝ) * n) / 2 <
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
    nlinarith [hge, hn2]
  exact (hlim.eventually (lt_mem_nhds hlt)).mono fun h hh => hh.le

end ExplicitThreshold
