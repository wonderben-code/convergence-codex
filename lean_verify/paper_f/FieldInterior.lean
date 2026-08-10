import FieldCover
import ExplicitThreshold

/-!
# Every site, an explicit temperature, and a count over the whole box

`FieldCover` bounds the boundary-field probability that a site is down **with a down cluster
that never touches the boundary** — but only at **interior** sites, and only under an
inequality in `β`. This file removes the first restriction, instantiates the second, and adds
the statement over the whole box that the two together make possible.

## The hypothesis that was not needed

`FieldCover.field_peierls_small` asks for `x` to be interior. It need not: if `x` is a
**boundary** site then `DownInside σ x` is already false — its second clause, applied to `x`
itself, says `x` is not on the boundary. So the event is **empty** there and the bound holds
for nothing, exactly as `PlusMagnetisation.down_empty_of_boundary` does for the `+` chain.
That is `field_peierls_small_all`, and it matters for the same reason it mattered there: a
count over the box cannot skip the edge.

## The count

With every site covered, the weights add:

> **`interiorDown_expectation_le`** — at any field strength and with `8 e^{-4β} ≤ 1/2`, the
> boundary-field **expected number of sites that are down with an interior cluster** is at
> most `22 (8 e^{-4β})³ · n²`.
>
> **`interiorDown_expectation_beta_one`** — and at `β ≥ 1` that constant is below `3/40`.

`interiorDown` counts sites, `sum_interiorDown_eq` is the Fubini swap that turns the count
into the per-site sums, so "expected number" is a theorem here rather than a remark.

## What it does not say, and this is the same boundary as `FieldCover`'s

It bounds the **interior** part of the minority phase. The rest — sites whose down cluster
reaches the edge of the box — is not bounded here and, at a fixed field strength in a large
box, is the **typical** case (`PlusClassVanishes.tendsto_plusProb_zero`). So this is **not**
a bound on the magnetisation: `∑_p P(p down)` has a second term that this file does not
touch, and `UNLOCK_WATCHLIST`'s step S3b — a second energy–entropy estimate, per
`ERRATUM 89` — is what would bound it.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace FieldInterior

open IsingFiniteVolume IsingBoundaryField DualObstruction FieldCover

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The interiority hypothesis was free -/

/-- Under the field there is no configuration with a **boundary** site down whose cluster
misses the boundary — the site is in its own cluster. So the event is empty there. -/
theorem downInside_empty_of_boundary {x : Site n} (hx : isBoundary x = true) :
    (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
  rintro ⟨-, hmiss⟩
  rw [hmiss x (SimpleGraph.Reachable.refl x)] at hx
  exact Bool.noConfusion hx

/-- **THE BOUND AT EVERY SITE.** For an interior site this is
`FieldCover.field_peierls_small`; for a boundary site the numerator is zero. -/
theorem field_peierls_small_all (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) (x : Site n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 := by
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
    exact field_peierls_small hn h hβ hi hj

/-! ## 2. Counting the sites, not just testing one -/

/-- How many sites of `σ` are down with a cluster that never touches the boundary. -/
noncomputable def interiorDown (σ : Config n) : ℕ :=
  ((Finset.univ : Finset (Site n)).filter (fun p => DownInside σ p)).card

/-- The Fubini swap: the weighted count over configurations is the sum over sites of the
weighted events. This is what makes "expected number of sites" a theorem rather than a
remark about linearity. -/
theorem sum_interiorDown_eq (h β : ℝ) :
    ∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)
      = ∑ p : Site n, ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
          (fun σ => DownInside σ p), Real.exp (-β * isingHB n h σ) := by
  classical
  have hcard : ∀ σ : Config n, (interiorDown σ : ℝ)
      = ∑ p : Site n, (if DownInside σ p then (1 : ℝ) else 0) := by
    intro σ
    rw [interiorDown, ← Finset.sum_boole]
  simp only [hcard, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hd : DownInside σ p <;> simp [hd]

/-- **THE INTERIOR MINORITY PHASE IS A VANISHING FRACTION OF THE BOX.** At **any** field
strength, with no boundary condition, and under `8 e^{-4β} ≤ 1/2`: the boundary-field
expected number of sites that are down with a cluster never touching the boundary is at most
`22 (8 e^{-4β})³ · n²`.

**It is not a magnetisation bound.** `∑_p P(p down)` has a second term — sites whose cluster
does reach the edge — which is the typical case at fixed `h` in a large box and which nothing
here bounds. -/
theorem interiorDown_expectation_le (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    (∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 * ((n : ℝ) * n) := by
  classical
  set Z : ℝ := ∑ σ : Config n, Real.exp (-β * isingHB n h σ) with hZ
  have hZpos : 0 < Z := FieldEnergy.partition_pos n h β
  rw [sum_interiorDown_eq, div_le_iff₀ hZpos]
  have hsite : ∀ p : Site n, (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
      (fun σ => DownInside σ p), Real.exp (-β * isingHB n h σ))
      ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 * Z := by
    intro p
    have := field_peierls_small_all hn h hβ p
    rw [div_le_iff₀ hZpos] at this
    exact this
  calc ∑ p : Site n, ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => DownInside σ p), Real.exp (-β * isingHB n h σ)
      ≤ ∑ _p : Site n, 22 * (8 * Real.exp (-(4 * β))) ^ 3 * Z :=
        Finset.sum_le_sum fun p _ => hsite p
    _ = 22 * (8 * Real.exp (-(4 * β))) ^ 3 * ((n : ℝ) * n) * Z := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [show (Fintype.card (Site n) : ℝ) = (n : ℝ) * n from by
          simp [Site, Fintype.card_prod]]
        ring

/-- **AND AT `β ≥ 1` THE CONSTANT IS BELOW `3/40`.** `ExplicitThreshold.exp_le_of_one_le`
supplies the arithmetic; the point is that the temperature is a number here too. -/
theorem interiorDown_expectation_beta_one (hn : 0 < n) (h : ℝ) {β : ℝ} (hβ : 1 ≤ β) :
    (∑ σ : Config n, (interiorDown σ : ℝ) * Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ (3 / 40 : ℝ) * ((n : ℝ) * n) := by
  have ht := ExplicitThreshold.exp_le_of_one_le hβ
  have ht0 : 0 < 8 * Real.exp (-(4 * β)) := by positivity
  have hthr : 8 * Real.exp (-(4 * β)) ≤ 1 / 2 := by linarith
  refine le_trans (interiorDown_expectation_le hn h hthr) ?_
  have hn2 : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
  have hcube : (8 * Real.exp (-(4 * β))) ^ 3 ≤ (3 / 20 : ℝ) ^ 3 :=
    pow_le_pow_left₀ ht0.le ht 3
  nlinarith [hcube, hn2]

end FieldInterior
