import BoundaryFieldLimit

/-!
# An explicit field threshold — the rate `BoundaryFieldLimit` said it did not have

`BoundaryFieldLimit` §5 proves the Peierls conclusion against the estate's own boundary-field
measure, *for all large enough `h`*, box by box. Its §6 names the residue exactly — one quantifier
— and then says, of the route rather than of the mathematics:

> **And that swap is not free.** Say exactly why, as a fact about the proof rather than a guess
> about the mathematics: the limit above is taken with the box **fixed**, and **no rate is
> exhibited for it anywhere**, so there is nothing in this argument from which a threshold
> independent of `n` could be extracted. Whether one exists is **not decided here**. What is
> established is that the value at `h = ∞` is a *limit* of the finite-`h` values, so **any route to
> `MagnetisationBound` must add information about how that limit is approached** — information this
> file does not have and does not guess at.

**This file supplies that information.** It does not take a limit at all: it bounds the
finite-`h` measure directly, and produces an `h` at which the bound already holds.

> **`magnetisation_threshold`** — for `0 ≤ m < 1`, at every low enough temperature, in **every**
> box, `MagnetisationBoundAt n β h m` holds as soon as
> `h ≥ (n² log 2 − log ((1−m)/(2(1+m)))) / (2β)`.

No sign hypothesis on `h` is needed: `fieldThreshold_pos` shows the threshold is already positive,
so clearing it forces `0 < h`. The first draft carried `0 ≤ h` as a hypothesis and it came off in
review; `magnetisationBoundAt_of_bound` shed a redundant `0 ≤ u` the same way.

The mechanism is that the field factor `exp(−2βh·D σ)` is `1` on the `+` class and at most
`exp(−2βh)` off it, so the whole off-`+` contribution is controlled by *how many configurations
there are* times *how large a Boltzmann weight can get* — and both are explicit:
`isingH_allTrue_le` says the all-up configuration minimises the energy, so its weight dominates
every other, and it lies in the `+` class, so `Zplus` is at least that weight. The count is
`2^(n·n)`. No limit, no rate extracted from a limit: an inequality at finite `h`.

## And it does NOT reach `MagnetisationBound`, which is stated here as a theorem

The threshold grows — quadratically in the side. **`fieldThreshold_atTop`** proves it tends to
infinity with the box, so no single `h` is delivered for all boxes and the residue named in
`BoundaryFieldLimit` §6 is untouched. That is a theorem here rather than a caveat, because a
caveat is exactly what a reader would skip.

**What has changed is the shape of the gap, not its width.** Before: "for all large enough `h`",
with no rate, so the question *what does the threshold depend on* had no answer at all. Now: the
threshold is `(n² log 2 + C(m))/(2β)`, and the whole of its `n`-dependence enters through one
crude step — bounding the number of off-`+` configurations by **all** `2^(n·n)` of them, each at
the **maximal** Boltzmann weight. Every configuration with `k` wrong boundary spins is counted as
if `k = 1` and as if it were the ground state. So the exponent `n²` is an artefact of that step and
not a feature of the model, and **a sharper count is the obvious next fence to remove** — the
honest expectation is that the true dependence is a surface effect, but this file does not prove
that and does not claim it.

**What is NOT claimed.** That the threshold is optimal, that it is the best this route gives, or
that `MagnetisationBound` is true or false. `BoundaryFieldLimit` §6's "whether one exists is not
decided here" is still not decided.

## The next fence, named precisely, and NOT attempted

Worked out when this file was reviewed, and written down so the next attempt starts from an
estimate rather than from "sharpen the count". Stratify the off-`+` sum by `k = D σ` instead of
collapsing it:

`∑_{σ ∉ +} w(σ) e^{−2βhk(σ)} = ∑_{k ≥ 1} e^{−2βhk} ∑_{D σ = k} w(σ)`.

The inner sum is where the crude step lives. Flipping the `k` wrong boundary spins of `σ` lands in
the `+` class, and the map `σ ↦ (the flipped set, the flipped configuration)` is **injective**, so

`∑_{D σ = k} w(σ) ≤ C(B, k) · e^{cβk} · Zplus`,

with `B` the number of boundary sites and `c` a constant from the energy comparison. Summing the
binomial series gives `(1 + e^{(c−2h)β})^B − 1`, which is `O(1)` as soon as
`B·e^{(c−2h)β} = O(1)` — that is, **`h ≳ c/2 + log B / (2β)`**. `B` is linear in the side, so this
route's threshold would be **logarithmic in `n`** where the one proved above is quadratic.

**Why it is not attempted here** — *and the reason first given was false, corrected in place
under `ERRATUM 131` rather than edited away*. The paragraph read:

> the energy comparison needs `isingH (flip S σ) ≤ isingH σ + c·|S|`, whose constant comes from a
> bound on the number of neighbours of a site — and **the estate has no degree bound for `adj`** …
> That bound is itself a bounded build … and nothing here has tried it.

**Both claims were wrong.** `PlusClassVanishes` has had `card_adj_le_four` and `card_adj_le_four'`
— the degree bound, in exactly the form used — and `isingH_flipAt_le`, the single-site energy
comparison with the same constant `16`, since long before this file. The probe behind the word
"none" scanned the first `20` of the `96` files that mention `adj`; `PlusClassVanishes` is the
`74`th. `FlipEnergy.isingH_flipOn_le` has since generalised that comparison from one site to an
arbitrary set, so **the energy leg is now done and was never the obstacle it was billed as**.

**What actually remains** are the other two legs, and neither is bookkeeping: stratifying the
off-`+` sum by the number of wrong boundary spins, and proving the flip map injective on each
stratum so the binomial coefficient is an upper bound. Those are **not attempted**.

**And the logarithmic threshold would not close the uniformity gap either**: `log n → ∞` too. It
would make the remaining gap smaller, not absent.
-/

namespace FieldThreshold

open IsingFiniteVolume IsingBoundaryField DualObstruction BoundaryFieldLimit
open MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The all-up configuration is the ground state, and it has `+` boundary

Two facts, and neither is decoration: the first makes one Boltzmann weight dominate every other,
and the second puts that weight inside `Zplus`. Together they turn "the off-`+` sum is small" into
an inequality with an explicit constant. -/

/-- **THE ALL-UP CONFIGURATION MINIMISES THE ENERGY.** Termwise: each `adj` term of `σ` is a
product of two spins, so at most `1`, which is what the all-up term is. -/
theorem isingH_allTrue_le (n : ℕ) (σ : Config n) :
    isingH n (fun _ => true) ≤ isingH n σ := by
  have hterm : ∀ p q : Site n,
      (if adj p q then spin (σ p) * spin (σ q) else 0)
        ≤ (if adj p q then spin ((fun _ => true : Config n) p) *
            spin ((fun _ => true : Config n) q) else 0) := by
    intro p q
    by_cases hpq : adj p q
    · simp only [if_pos hpq, spin]
      cases σ p <;> cases σ q <;> norm_num
    · simp [hpq]
  simp only [isingH, neg_le_neg_iff]
  exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q

/-- The all-up configuration has `+` boundary, trivially — but it is what puts the ground-state
weight inside `Zplus` rather than merely inside `Z`. -/
theorem plusBoundary_allTrue (n : ℕ) : PlusBoundary (fun _ : Site n => true) :=
  fun _ _ => rfl

/-- The ground-state Boltzmann weight. -/
noncomputable def groundWeight (n : ℕ) (β : ℝ) : ℝ :=
  Real.exp (-β * isingH n (fun _ => true))

theorem groundWeight_pos (n : ℕ) (β : ℝ) : 0 < groundWeight n β := Real.exp_pos _

/-- **AND SO IT DOMINATES EVERY WEIGHT**, for `β ≥ 0`. -/
theorem weight_le_groundWeight {β : ℝ} (hβ : 0 ≤ β) (σ : Config n) :
    Real.exp (-β * isingH n σ) ≤ groundWeight n β := by
  refine Real.exp_le_exp.mpr ?_
  have := isingH_allTrue_le n σ
  nlinarith

/-- The `+` partition function is at least the ground-state weight, because the ground state is
in the `+` class. -/
theorem groundWeight_le_plus (n : ℕ) (β : ℝ) :
    groundWeight n β ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
      Real.exp (-β * isingH n σ) := by
  refine Finset.single_le_sum (f := fun σ => Real.exp (-β * isingH n σ))
    (fun σ _ => (Real.exp_pos _).le) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, plusBoundary_allTrue n⟩

/-! ## 2. The magnetisation is bounded by the volume -/

theorem abs_magnetisation_le (n : ℕ) (σ : Config n) :
    |magnetisation n σ| ≤ (n : ℝ) * n := by
  have h1 : |magnetisation n σ| ≤ ∑ _p : Site n, (1 : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun p _ => le_of_eq (abs_spin (σ p))
  refine h1.trans (le_of_eq ?_)
  simp [Finset.card_univ, Fintype.card_prod]

/-! ## 3. Off the `+` class the field factor is at most `exp (−2βh)`

This is the whole mechanism, and it needs `D σ ≥ 1`, which is `downCount_eq_zero_iff` read
contrapositively. -/

theorem field_factor_le {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) {σ : Config n}
    (hσ : ¬ PlusBoundary σ) :
    Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) ≤ Real.exp (-(2 * β * h)) := by
  have hne : downCount n σ ≠ 0 := fun h0 => hσ ((downCount_eq_zero_iff n σ).mp h0)
  have h1 : (1 : ℝ) ≤ (downCount n σ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  refine Real.exp_le_exp.mpr ?_
  have hbh : 0 ≤ 2 * β * h := by positivity
  nlinarith

theorem field_factor_le_one {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (σ : Config n) :
    Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) ≤ 1 := by
  refine Real.exp_le_one_iff.mpr ?_
  have hbh : 0 ≤ 2 * β * h := by positivity
  have : (0 : ℝ) ≤ (downCount n σ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ## 4. So the off-`+` part of either sum is at most `2^(n·n) · exp(−2βh)` ground weights -/

/-- The number of configurations, explicitly. -/
theorem card_config (n : ℕ) : Fintype.card (Config n) = 2 ^ (n * n) :=
  IsingContourSeparation.card_config n

-- `dupname_scan.py` (ERRATUM 271): re-derived `IsingContourSeparation.card_config`, which this
-- file imports. Name and statement kept; the duplicate proof is gone.
theorem sum_offPlus_le {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (C : ℝ) (hC : 0 ≤ C) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        C * Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      ≤ ((2 : ℝ) ^ (n * n) * Real.exp (-(2 * β * h))) * (C * groundWeight n β) := by
  have hbound : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
      C * Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
        ≤ Real.exp (-(2 * β * h)) * (C * groundWeight n β) := by
    intro σ hσ
    have hnp : ¬ PlusBoundary σ := (Finset.mem_filter.mp hσ).2
    have h1 : Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) ≤ Real.exp (-(2 * β * h)) :=
      field_factor_le hβ hh hnp
    have h2 : Real.exp (-β * isingH n σ) ≤ groundWeight n β := weight_le_groundWeight hβ σ
    have h3 : 0 ≤ C * Real.exp (-β * isingH n σ) := by positivity
    calc C * Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
        ≤ C * Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h)) := by
          exact mul_le_mul_of_nonneg_left h1 h3
      _ ≤ Real.exp (-(2 * β * h)) * (C * groundWeight n β) := by
          rw [mul_comm (Real.exp (-(2 * β * h))) _]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 hC) (Real.exp_pos _).le
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  have hcard : (((Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ)).card : ℝ) ≤ (2 : ℝ) ^ (n * n) := by
    have h1 := Finset.card_le_univ
      ((Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ))
    rw [card_config] at h1
    exact_mod_cast h1
  rw [nsmul_eq_mul]
  have hpos : (0 : ℝ) ≤ Real.exp (-(2 * β * h)) * (C * groundWeight n β) := by
    have := (groundWeight_pos n β).le
    positivity
  calc (((Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ)).card : ℝ) *
        (Real.exp (-(2 * β * h)) * (C * groundWeight n β))
      ≤ (2 : ℝ) ^ (n * n) * (Real.exp (-(2 * β * h)) * (C * groundWeight n β)) :=
        mul_le_mul_of_nonneg_right hcard hpos
    _ = ((2 : ℝ) ^ (n * n) * Real.exp (-(2 * β * h))) * (C * groundWeight n β) := by ring

/-! ## 5. The two sums, split at the `+` class -/

theorem sum_split (β h : ℝ) (g : Config n → ℝ) :
    ∑ σ : Config n, g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      = (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ), g σ)
        + ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
            g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Config n))
    (fun σ => PlusBoundary σ)]
  congr 1
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h0 : downCount n σ = 0 :=
    (downCount_eq_zero_iff n σ).mpr (Finset.mem_filter.mp hσ).2
  rw [h0]
  simp

/-! ## 6. The bound at finite `h`

No limit is taken. The `+` part of each sum is the Peierls chain's own object; the rest is
controlled by §4, and the two are combined without ever dividing by a quantity that could be
negative — the target is cleared as `m·n²·Den ≤ Num`, which is why `0 ≤ m` appears. -/

/-- **THE FINITE-`h` MAGNETISATION BOUND.** If the `+`-conditioned ratio is at least `q·n²` and the
off-`+` mass is at most `u·Zplus`, then `MagnetisationBoundAt n β h m` holds whenever
`m(1 + u) + u ≤ q`. `hoff` is where `h` enters, and it is an inequality at a **finite** `h`, not a
statement about a limit.

*Generalised after the fact, and FOUR hypotheses came off.* The first version took the concrete
`2^(n·n)·e^{−2βh} ≤ u` in place of `hoff`, and needed `0 < β`, `0 ≤ h` and `0 ≤ u` besides. Taking
the off-`+` bound **abstractly** drops all of them: every one of the three was there to feed
`sum_offPlus_le`, which is no longer called. `h` and `β` now carry no sign condition at all —
nothing below reads either direction — and `u ≥ 0` follows from `hoff`. The fourth was found by
the unused-variable linter after the other three, which is worth recording: **removing hypotheses
exposes more of them.** `offBound_of_pow` recovers the old hypothesis, and
**`BoundaryStratum.sum_offPlus_le` is the sharper supplier this generalisation exists for.** -/
theorem magnetisationBoundAt_of_bound {n : ℕ} {β h u m q : ℝ} (hm0 : 0 ≤ m)
    (hoff : (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => ¬ PlusBoundary σ), Real.exp (-β * isingH n σ) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
      ≤ u * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ))
    (hplus : q * ((n : ℝ) * n) ≤
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)))
    (hmq : m * (1 + u) + u ≤ q) :
    MagnetisationBoundAt n β h m := by
  classical
  intro hn
  set Zp := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    Real.exp (-β * isingH n σ) with hZp
  set Np := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    magnetisation n σ * Real.exp (-β * isingH n σ) with hNp
  have hZppos : 0 < Zp := PeierlsConditional.plus_partition_pos β
  have hn2 : (0 : ℝ) < (n : ℝ) * n := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hgw : groundWeight n β ≤ Zp := groundWeight_le_plus n β
  -- the denominator
  set Den := ∑ σ : Config n, Real.exp (-β * isingH n σ) *
    Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) with hDen
  have hDsplit : Den = Zp + ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ), Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) :=
    sum_split β h (fun σ => Real.exp (-β * isingH n σ))
  have hOffD_nonneg : 0 ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ), Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) :=
    Finset.sum_nonneg fun σ _ => by positivity
  have hOffD_le : (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ), Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) ≤ u * Zp := hoff
  have hDenpos : 0 < Den := by rw [hDsplit]; linarith
  have hDenle : Den ≤ Zp * (1 + u) := by rw [hDsplit]; nlinarith
  -- the numerator
  set Num := ∑ σ : Config n, magnetisation n σ * Real.exp (-β * isingH n σ) *
    Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) with hNum
  have hNsplit : Num = Np + ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ), magnetisation n σ * Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) :=
    sum_split β h (fun σ => magnetisation n σ * Real.exp (-β * isingH n σ))
  have hOffN_ge : -(u * (((n : ℝ) * n) * Zp)) ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => ¬ PlusBoundary σ), magnetisation n σ * Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
    rw [neg_le]
    rw [← Finset.sum_neg_distrib]
    have hterm : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        -(magnetisation n σ * Real.exp (-β * isingH n σ) *
            Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
          ≤ ((n : ℝ) * n) * Real.exp (-β * isingH n σ) *
            Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
      intro σ _
      have hM : -magnetisation n σ ≤ (n : ℝ) * n :=
        (neg_le_abs _).trans (abs_magnetisation_le n σ)
      have hfac : 0 ≤ Real.exp (-β * isingH n σ) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by positivity
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    have hpull : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        ((n : ℝ) * n) * Real.exp (-β * isingH n σ) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
        = ((n : ℝ) * n) * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
            (fun σ => ¬ PlusBoundary σ), Real.exp (-β * isingH n σ) *
              Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [hpull]
    have hstep := mul_le_mul_of_nonneg_left hoff hn2.le
    nlinarith [hstep]
  -- the plus ratio, cleared of its division
  have hplus' : q * ((n : ℝ) * n) * Zp ≤ Np := by
    rw [le_div_iff₀ hZppos] at hplus
    exact hplus
  -- assemble
  rw [BoundaryFieldLimit.integral_eq n h β (magnetisation n), ← hNum, ← hDen,
    le_div_iff₀ hDenpos]
  have hmn : 0 ≤ m * ((n : ℝ) * n) := by positivity
  have step1 : m * ((n : ℝ) * n) * Den ≤ m * ((n : ℝ) * n) * (Zp * (1 + u)) :=
    mul_le_mul_of_nonneg_left hDenle hmn
  refine step1.trans ?_
  have step2 : Np - u * (((n : ℝ) * n) * Zp) ≤ Num := by rw [hNsplit]; linarith
  refine le_trans ?_ step2
  have hpos : (0 : ℝ) < ((n : ℝ) * n) * Zp := by positivity
  have hstep : (m * (1 + u) + u) * (((n : ℝ) * n) * Zp) ≤ q * (((n : ℝ) * n) * Zp) :=
    mul_le_mul_of_nonneg_right hmq hpos.le
  nlinarith [hstep, hplus']

/-- **THE CRUDE OFF-`+` BOUND, IN THE ABSTRACT SHAPE THE LEMMA ABOVE NOW TAKES.** This is what
`magnetisationBoundAt_of_bound` used to have inlined; lifting it out is what let the lemma be
stated against an arbitrary supplier, and `BoundaryStratum.sum_offPlus_le` is the other one. -/
theorem offBound_of_pow {n : ℕ} {β h u : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hu : (2 : ℝ) ^ (n * n) * Real.exp (-(2 * β * h)) ≤ u) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
      ≤ u * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ) := by
  classical
  have hu0 : (0 : ℝ) ≤ u := le_trans (by positivity) hu
  have hgw : groundWeight n β ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => PlusBoundary σ), Real.exp (-β * isingH n σ) := groundWeight_le_plus n β
  have hrw : ∀ σ : Config n, Real.exp (-β * isingH n σ) *
      Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      = 1 * Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := fun σ => by ring
  rw [Finset.sum_congr rfl fun σ _ => hrw σ]
  refine (sum_offPlus_le hβ hh 1 zero_le_one).trans ?_
  have h1 : (2 : ℝ) ^ (n * n) * Real.exp (-(2 * β * h)) * (1 * groundWeight n β)
      ≤ u * (1 * groundWeight n β) :=
    mul_le_mul_of_nonneg_right hu (by have := (groundWeight_pos n β).le; positivity)
  refine h1.trans ?_
  have h2 : (1 : ℝ) * groundWeight n β
      ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ) := by rw [one_mul]; exact hgw
  exact mul_le_mul_of_nonneg_left h2 hu0

/-! ## 7. The threshold, explicitly -/

/-- **THE THRESHOLD.** Everything about the box enters through the `n²` in front of `log 2`, and
that factor comes from counting **all** `2^(n·n)` configurations — see the header. -/
noncomputable def fieldThreshold (n : ℕ) (β m : ℝ) : ℝ :=
  ((n : ℝ) * n * Real.log 2 - Real.log ((1 - m) / (2 * (1 + m)))) / (2 * β)

theorem pow_two_exp_le {n : ℕ} {β h c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hh : ((n : ℝ) * n * Real.log 2 - Real.log c) / (2 * β) ≤ h) :
    (2 : ℝ) ^ (n * n) * Real.exp (-(2 * β * h)) ≤ c := by
  have hcast : ((n : ℝ) * n) = ((n * n : ℕ) : ℝ) := by push_cast; ring
  have h2 : (2 : ℝ) ^ (n * n) = Real.exp (((n : ℝ) * n) * Real.log 2) := by
    rw [hcast, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [h2, ← Real.exp_add]
  have h2β : (0 : ℝ) < 2 * β := by linarith
  rw [div_le_iff₀ h2β] at hh
  calc Real.exp ((n : ℝ) * n * Real.log 2 + -(2 * β * h))
      ≤ Real.exp (Real.log c) := Real.exp_le_exp.mpr (by nlinarith)
    _ = c := Real.exp_log hc

/-- **THE THRESHOLD IS POSITIVE**, because `(1−m)/(2(1+m)) ≤ 1/2 < 1` makes its logarithm
negative. So clearing the threshold already forces `0 < h`, and no separate sign hypothesis on the
field is needed below — the first draft of `magnetisation_threshold` carried one. -/
theorem fieldThreshold_pos {n : ℕ} {β m : ℝ} (hβ : 0 < β) (hm0 : 0 ≤ m) (hm : m < 1) :
    0 < fieldThreshold n β m := by
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  have hc : (0 : ℝ) < (1 - m) / (2 * (1 + m)) := div_pos (by linarith) (by linarith)
  have hclt : (1 - m) / (2 * (1 + m)) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hlog : Real.log ((1 - m) / (2 * (1 + m))) < 0 := Real.log_neg hc hclt
  have hnum : (0 : ℝ) < (n : ℝ) * n * Real.log 2 - Real.log ((1 - m) / (2 * (1 + m))) := by
    have : (0 : ℝ) ≤ (n : ℝ) * n * Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
      positivity
    linarith
  exact div_pos hnum (by linarith)

/-- **THE PEIERLS CONCLUSION AT AN EXPLICIT FIELD STRENGTH.** For `0 ≤ m < 1`, at every low enough
temperature, in **every** box, `MagnetisationBoundAt n β h m` holds as soon as `h` clears
`fieldThreshold n β m`.

`BoundaryFieldLimit` §5 gives the same conclusion "for all large enough `h`" with no rate. This is
the rate, and §6 there named its absence as the missing information. -/
theorem magnetisation_threshold {m : ℝ} (hm0 : 0 ≤ m) (hm : m < 1) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ) (h : ℝ), fieldThreshold n β m ≤ h →
      MagnetisationBoundAt n β h m := by
  have hε : (0 : ℝ) < (1 - m) / 4 := by linarith
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  have hc : (0 : ℝ) < (1 - m) / (2 * (1 + m)) := div_pos (by linarith) (by linarith)
  filter_upwards [PlusMagnetisation.magnetisation_ge hε, eventually_gt_atTop (0 : ℝ)]
    with β hβ hβ0 n h hthr
  have hh : (0 : ℝ) ≤ h := le_trans (fieldThreshold_pos hβ0 hm0 hm).le hthr
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun hcon => absurd hcon (lt_irrefl 0)
  refine magnetisationBoundAt_of_bound (q := 1 - 2 * ((1 - m) / 4))
    (u := (1 - m) / (2 * (1 + m))) hm0 ?_ (hβ n hn) ?_
  · exact offBound_of_pow hβ0.le hh (pow_two_exp_le hβ0 hc hthr)
  · have hval : m * (1 + (1 - m) / (2 * (1 + m))) + (1 - m) / (2 * (1 + m))
        = 1 - 2 * ((1 - m) / 4) := by
      field_simp
      ring
    exact le_of_eq hval

/-! ## 8. And it does not reach `MagnetisationBound` — as a theorem, not a caveat -/

/-- **THE THRESHOLD GROWS WITHOUT BOUND IN THE BOX.** So `magnetisation_threshold` delivers no
single field strength serving every box, and `IsingBoundaryField.MagnetisationBound` is untouched.
Stated as a theorem because the alternative is a sentence a reader skips. -/
theorem fieldThreshold_atTop {β m : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => fieldThreshold n β m) atTop atTop := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2β : (0 : ℝ) < 2 * β := by linarith
  have hform : (fun n : ℕ => fieldThreshold n β m)
      = fun n : ℕ => (Real.log 2 / (2 * β)) * ((n : ℝ) * n)
        + (-(Real.log ((1 - m) / (2 * (1 + m)))) / (2 * β)) := by
    funext n
    simp only [fieldThreshold]
    field_simp
    ring
  rw [hform]
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (Real.log 2 / (2 * β)) * ((n : ℝ) * n)) atTop atTop :=
    hsq.const_mul_atTop (by positivity)
  exact hmul.atTop_add tendsto_const_nhds

/-- **AND SO THE RESIDUE IS UNMOVED.** `magnetisationBound_of_uniform` still needs a single `h`;
this file supplies one per box and proves the supply grows. What changed is that the `n`-dependence
is now an explicit function rather than an unknown. -/
theorem not_uniform_from_threshold {β m : ℝ} (hβ : 0 < β) :
    ¬ ∃ H : ℝ, ∀ n : ℕ, fieldThreshold n β m ≤ H := by
  rintro ⟨H, hH⟩
  have := (fieldThreshold_atTop (m := m) hβ).eventually_ge_atTop (H + 1)
  obtain ⟨n, hn⟩ := this.exists
  linarith [hH n]

end FieldThreshold
