import BoundaryStratum
import FieldThreshold

/-!
# The field threshold, logarithmic in the box instead of quadratic

`FieldThreshold.magnetisation_threshold` delivers, for every box, a field strength at which the
Peierls conclusion already holds — and that strength grows like `n²`. Its header named the single
crude step responsible and `UNLOCK_WATCHLIST`'s *logarithmic field threshold* item costed the
repair. `BoundaryStratum.sum_offPlus_le` did the repair at the level of the estimate. **This file
is the assembly**, and it is the whole point of the previous three units:

> **`magnetisation_sharp_threshold`** — for `0 ≤ m < 1`, at every low enough temperature, in
> **every** box, `MagnetisationBoundAt n β h m` holds as soon as
> `h ≥ 8 + log (B / log (1 + c)) / (2β)`, with `B` the number of boundary sites and
> `c = (1−m)/(2(1+m))`.

`B` is linear in the side, so the threshold is **`8 + O(log n / β)`** where the previous one was
`n² log 2 / (2β)`. Both are proved; **neither is uniform in the box**, and that is the point the
next section makes as a theorem rather than a remark.

## What made the assembly possible, and it was not this file

`magnetisationBoundAt_of_bound` used to take the crude bound `2^(n·n)·e^{−2βh} ≤ u` inline.
Generalising it to take the off-`+` bound **abstractly** — any `u` with
`∑_{σ ∉ +} … ≤ u·Zplus` — is what let a second supplier be plugged in, and it dropped **four**
hypotheses on the way (`0 < β`, `0 ≤ h`, `0 ≤ u`, and the concrete shape); the fourth surfaced
only after the first three were gone, which is the useful part of the observation.
`FieldThreshold.offBound_of_pow` recovers the old supplier; `BoundaryStratum.sum_offPlus_le` is
the new one. **The two thresholds now differ only in which lemma is passed at one argument
position.**

## The arithmetic, in one line

Feeding the new estimate needs `(1 + x)^B − 1 ≤ c` with `x = e^{(16−2h)β}`. Since `1 + x ≤ e^x`,
it is enough that `e^{Bx} ≤ 1 + c`, i.e. `B·x ≤ log(1 + c)`, i.e. `x ≤ log(1+c)/B` — and taking
logarithms turns that into the threshold above. **Every step is monotone and none is tight**; the
`8` is `16/2` and inherits the whole looseness of `FlipEnergy`'s constant.

## What this does NOT do

**It does not close the uniformity gap, and `sharpThreshold_atTop` proves it does not.** The
threshold still tends to infinity with the box — `log n` rather than `n²`, but infinity all the
same — so no single field strength serves every box and
`IsingBoundaryField.MagnetisationBound` remains exactly where it was. That was predicted in the
watchlist item before any of this was built, and it is worth being blunt that the prediction held:
**three units of real work moved the gap from enormous to small and did not remove it.**

**And the old threshold is not superseded.** `BoundaryStratum`'s header records that the two
estimates are incomparable — the new one carries an `e^{16β}` the old does not — so at a small box
and low temperature `FieldThreshold.magnetisation_threshold` is still the better statement. Both
are kept.
-/

namespace SharpThreshold

open IsingFiniteVolume IsingBoundaryField DualObstruction BoundaryFieldLimit
open BoundaryStratum FieldThreshold
open MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The boundary is not empty -/

/-- **THE BOUNDARY HAS AT LEAST `n` SITES** — the whole first row, since `isBoundary` fires on
`p.1.val = 0` whatever the second coordinate is. Stated as `n ≤ B` rather than `0 < B` because §4
needs the growth and not merely the non-emptiness. -/
theorem card_bdrySites_ge (hn : 0 < n) : n ≤ (bdrySites n).card := by
  classical
  have hinj : Function.Injective (fun j : Fin n => (⟨⟨0, hn⟩, j⟩ : Site n)) :=
    fun a b hab => congrArg Prod.snd hab
  have hsub : (Finset.univ : Finset (Fin n)).image (fun j => (⟨⟨0, hn⟩, j⟩ : Site n))
      ⊆ bdrySites n := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [isBoundary]⟩
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = ((Finset.univ : Finset (Fin n)).image (fun j => (⟨⟨0, hn⟩, j⟩ : Site n))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (bdrySites n).card := Finset.card_le_card hsub

theorem card_bdrySites_pos (hn : 0 < n) : 0 < (bdrySites n).card :=
  lt_of_lt_of_le hn (card_bdrySites_ge hn)

/-- **AND IT GROWS**, so §4 needs no hypothesis about the boundary. -/
theorem card_bdrySites_atTop :
    Tendsto (fun n : ℕ => ((bdrySites n).card : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact_mod_cast card_bdrySites_ge hn

/-! ## 2. The threshold -/

/-- **THE SHARP THRESHOLD.** `8` comes from `FlipEnergy`'s `16`, halved; the rest is `log B`
against the slack `log (1 + c)` the target leaves. -/
noncomputable def sharpThreshold (n : ℕ) (β m : ℝ) : ℝ :=
  8 + Real.log (((bdrySites n).card : ℝ) /
    Real.log (1 + (1 - m) / (2 * (1 + m)))) / (2 * β)

/-- **CLEARING THE THRESHOLD MAKES THE BINOMIAL FACTOR SMALL.** The three monotone steps of the
header, in order: `x ≤ L/B`, then `(1+x)^B ≤ e^{Bx}`, then `e^{Bx} ≤ 1 + c`. -/
theorem binomial_le {β h c : ℝ} {B : ℕ} (hβ : 0 < β) (hB : 0 < B) (hc : 0 < c)
    (hh : 8 + Real.log ((B : ℝ) / Real.log (1 + c)) / (2 * β) ≤ h) :
    (1 + Real.exp ((16 - 2 * h) * β)) ^ B - 1 ≤ c := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hL : (0 : ℝ) < Real.log (1 + c) := Real.log_pos (by linarith)
  have h2β : (0 : ℝ) < 2 * β := by linarith
  -- x ≤ L / B
  have hxle : Real.exp ((16 - 2 * h) * β) ≤ Real.log (1 + c) / (B : ℝ) := by
    have hdiv : Real.log ((B : ℝ) / Real.log (1 + c)) ≤ (h - 8) * (2 * β) := by
      have h1 : Real.log ((B : ℝ) / Real.log (1 + c)) / (2 * β) ≤ h - 8 := by linarith
      rwa [div_le_iff₀ h2β] at h1
    have hkey : (16 - 2 * h) * β ≤ Real.log (Real.log (1 + c) / (B : ℝ)) := by
      rw [Real.log_div (ne_of_gt hBpos) (ne_of_gt hL)] at hdiv
      rw [Real.log_div (ne_of_gt hL) (ne_of_gt hBpos)]
      nlinarith [hdiv]
    calc Real.exp ((16 - 2 * h) * β)
        ≤ Real.exp (Real.log (Real.log (1 + c) / (B : ℝ))) := Real.exp_le_exp.mpr hkey
      _ = Real.log (1 + c) / (B : ℝ) := Real.exp_log (by positivity)
  -- (1+x)^B ≤ exp (B x) ≤ 1 + c
  have hxpos : (0 : ℝ) < Real.exp ((16 - 2 * h) * β) := Real.exp_pos _
  have hstep : (1 + Real.exp ((16 - 2 * h) * β)) ^ B
      ≤ Real.exp (Real.exp ((16 - 2 * h) * β)) ^ B := by
    refine pow_le_pow_left₀ (by linarith) ?_ B
    have := Real.add_one_le_exp (Real.exp ((16 - 2 * h) * β))
    linarith
  have hexp : Real.exp (Real.exp ((16 - 2 * h) * β)) ^ B
      = Real.exp ((B : ℝ) * Real.exp ((16 - 2 * h) * β)) := by
    rw [Real.exp_nat_mul]
  have hBx : (B : ℝ) * Real.exp ((16 - 2 * h) * β) ≤ Real.log (1 + c) := by
    have := mul_le_mul_of_nonneg_left hxle hBpos.le
    rw [mul_div_cancel₀ _ (ne_of_gt hBpos)] at this
    linarith
  have hfin : Real.exp ((B : ℝ) * Real.exp ((16 - 2 * h) * β)) ≤ 1 + c :=
    calc Real.exp ((B : ℝ) * Real.exp ((16 - 2 * h) * β))
        ≤ Real.exp (Real.log (1 + c)) := Real.exp_le_exp.mpr hBx
      _ = 1 + c := Real.exp_log (by linarith)
  rw [hexp] at hstep
  linarith

/-! ## 3. The assembly -/

/-- **THE PEIERLS CONCLUSION AT A THRESHOLD LOGARITHMIC IN THE BOX.** Same statement as
`FieldThreshold.magnetisation_threshold`; the only difference is which off-`+` bound is passed. -/
theorem magnetisation_sharp_threshold {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ) (h : ℝ), sharpThreshold n β m ≤ h →
      MagnetisationBoundAt n β h m := by
  have hε : (0 : ℝ) < (1 - m) / 4 := by linarith
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  have hc : (0 : ℝ) < (1 - m) / (2 * (1 + m)) := div_pos (by linarith) (by linarith)
  filter_upwards [PlusMagnetisation.magnetisation_ge hε, eventually_gt_atTop (0 : ℝ)]
    with β hβ hβ0 n h hthr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun hcon => absurd hcon (lt_irrefl 0)
  refine magnetisationBoundAt_of_bound (q := 1 - 2 * ((1 - m) / 4))
    (u := (1 - m) / (2 * (1 + m))) hm0 ?_ (hβ n hn) ?_
  · simp only [sharpThreshold] at hthr
    refine (BoundaryStratum.sum_offPlus_le hβ0.le n).trans ?_
    have hZ : (0 : ℝ) ≤ ∑ τ ∈ (Finset.univ : Finset (Config n)).filter
        (fun τ => PlusBoundary τ), Real.exp (-β * isingH n τ) :=
      (PeierlsConditional.plus_partition_pos β).le
    exact mul_le_mul_of_nonneg_right
      (binomial_le (B := (bdrySites n).card) (c := (1 - m) / (2 * (1 + m)))
        hβ0 (card_bdrySites_pos hn) hc hthr) hZ
  · have hval : m * (1 + (1 - m) / (2 * (1 + m))) + (1 - m) / (2 * (1 + m))
        = 1 - 2 * ((1 - m) / 4) := by
      field_simp
      ring
    exact le_of_eq hval

/-! ## 4. And it still is not uniform — a theorem, not a remark -/

/-- **THE SHARP THRESHOLD ALSO GROWS WITHOUT BOUND.** `log n` instead of `n²`, and still
`→ ∞`, so `IsingBoundaryField.MagnetisationBound` is exactly where it was. The watchlist item
predicted this before the work was done; it is stated here so the prediction is on the record as
having held. -/
theorem sharpThreshold_atTop {β m : ℝ} (hβ : 0 < β) (hm0 : 0 ≤ m) (hm : m < 1) :
    Tendsto (fun n : ℕ => sharpThreshold n β m) atTop atTop := by
  have hB : Tendsto (fun n : ℕ => ((bdrySites n).card : ℝ)) atTop atTop := card_bdrySites_atTop
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  have hc : (0 : ℝ) < (1 - m) / (2 * (1 + m)) := div_pos (by linarith) (by linarith)
  have hL : (0 : ℝ) < Real.log (1 + (1 - m) / (2 * (1 + m))) := Real.log_pos (by linarith)
  have h2β : (0 : ℝ) < 2 * β := by linarith
  have hdiv : Tendsto (fun n : ℕ => ((bdrySites n).card : ℝ) /
      Real.log (1 + (1 - m) / (2 * (1 + m)))) atTop atTop :=
    Filter.Tendsto.atTop_div_const hL hB
  have hlog := Real.tendsto_log_atTop.comp hdiv
  have hscale : Tendsto (fun n : ℕ => Real.log (((bdrySites n).card : ℝ) /
      Real.log (1 + (1 - m) / (2 * (1 + m)))) / (2 * β)) atTop atTop :=
    Filter.Tendsto.atTop_div_const h2β hlog
  exact Filter.tendsto_atTop_add_const_left atTop 8 hscale

end SharpThreshold
