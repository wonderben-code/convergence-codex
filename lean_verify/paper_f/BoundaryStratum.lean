import FlipEnergy
import BoundaryFieldLimit

/-!
# The off-`+` mass, counted by which boundary spins are wrong

`FieldThreshold` bounds the off-`+` contribution by **all** `2^(n·n)` configurations, each at the
**maximal** Boltzmann weight — a configuration with twenty wrong boundary spins charged as if it
had one and as if it were the ground state. That single step is where the whole `n²` in its
threshold comes from, and `UNLOCK_WATCHLIST`'s *logarithmic field threshold* item split the repair
into three legs. This file is those three legs, and they came out as **one** step rather than
three:

> **`sum_offPlus_le`** — for `β ≥ 0` and **any** `h`,
> `∑_{σ ∉ +} e^{−βH σ} e^{−2βh·D σ} ≤ ((1 + e^{(16−2h)β})^B − 1) · Zplus`,
> with `B` the number of boundary sites.

*No sign condition on `h`* — the watchlist item expected one and the estimate does not need it,
because the field factor enters only through the exponent `(16 − 2h)β` and never through an
inequality that would fix its direction. `β ≥ 0` is used once, in the energy comparison.

Compare the old bound, `2^(n·n) e^{−2βh} · (ground weight)`. The new one is **exponential in the
boundary rather than in the volume**, and it decays in `h` at every one of the `B` places at once
instead of only at the worst.

**The two are INCOMPARABLE, and saying "sharper" without this would be an overclaim.** *This
paragraph is arithmetic done outside Lean and is labelled as such rather than left looking like
the rest.* For large `h` the new bound behaves like `B·e^{16β}·e^{−2βh}` against the old
`2^(n·n)·e^{−2βh}`, so the new one wins by a factor `2^(n·n)/(B e^{16β})` — enormous in `n`, which
is the regime the uniformity question lives in. But it carries an `e^{16β}` the old one does not,
and `B` is only linear, so at a **small box and low temperature the old bound is the better of the
two**: at `n = 2`, `B = 4` and `2^(n·n) = 16`, so the new one is worse as soon as
`4e^{16β} > 16`, i.e. `β > log 4 / 16 ≈ 0.087`. Nothing below depends on the comparison; it is
recorded so that "sharper" is read as *sharper where it matters* and not as *sharper*.

## Why it is one step and not three

The watchlist proposed stratifying by `k = D σ`, injecting each stratum into
`bdrySites.powersetCard k ×ˢ (+ class)`, and summing a binomial series. Every stratum needs its own
injection and its own bound, and then the strata have to be reassembled.

**Taking the same map globally removes the stratification entirely.** Send `σ` to the pair
*(which boundary spins are wrong, the configuration with exactly those flipped)*. That map is
injective on **all** of `Config` at once — `flipOn` is an involution, so the second component
flipped back on the first recovers `σ` — and it lands in `(powerset of the boundary) ×ˢ (+ class)`,
with the empty set hit only by configurations already in `+`. So there is one injection, and the
binomial series is not summed by hand at all: `∑_{S ⊆ B} x^{|S|} = (1+x)^{|B|}` is `Finset.prod_add`
with both factors constant, and the `−1` is the `S = ∅` term erased.

The weight comparison along the map is `FlipEnergy.isingH_flipOn_le`, which is where the `16` in
the exponent comes from and the only place the previous unit is used.

## What this does NOT do

**It does not restate the field threshold.** `FieldThreshold.magnetisation_threshold` is unchanged
and still quadratic in the side; assembling this estimate into a sharper threshold is a separate
unit and is **not done here**. Until it is, this file is a better bound that nothing consumes, and
that is said rather than left for a reader to discover.

**And the sharper threshold would still not be uniform.** `(1+x)^B − 1` is `O(1)` only once
`B·x = O(1)`, i.e. `h ≳ 8 + log B / (2β)`, which grows with the box — slowly, but it grows.
`FieldThreshold.fieldThreshold_atTop` makes that point for the current threshold and the same point
survives the sharpening.
-/

namespace BoundaryStratum

open IsingFiniteVolume IsingBoundaryField DualObstruction BoundaryFieldLimit FlipEnergy

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Which boundary spins are wrong -/

/-- The boundary sites at which `σ` is down. `downCount` is its cardinality, definitionally. -/
def downSet (n : ℕ) (σ : Config n) : Finset (Site n) :=
  (bdrySites n).filter fun p => σ p = false

theorem downSet_card (n : ℕ) (σ : Config n) : (downSet n σ).card = downCount n σ := rfl

theorem downSet_subset (n : ℕ) (σ : Config n) : downSet n σ ⊆ bdrySites n :=
  Finset.filter_subset _ _

theorem mem_bdrySites {p : Site n} : p ∈ bdrySites n ↔ isBoundary p = true := by
  simp [bdrySites]

/-- **FLIPPING EXACTLY THE WRONG BOUNDARY SPINS LANDS IN THE `+` CLASS.** -/
theorem plusBoundary_flipOn_downSet (σ : Config n) :
    PlusBoundary (flipOn (downSet n σ) σ) := by
  intro p hp
  by_cases h : σ p = false
  · have hmem : p ∈ downSet n σ :=
      Finset.mem_filter.mpr ⟨mem_bdrySites.mpr hp, h⟩
    simp [flipOn, hmem, h]
  · have hmem : p ∉ downSet n σ := by
      simp only [downSet, Finset.mem_filter, not_and]
      exact fun _ => h
    simp only [flipOn, if_neg hmem]
    cases hb : σ p
    · exact absurd hb h
    · rfl

/-- `flipOn S` is an involution — the fact that makes the pairing injective. -/
theorem flipOn_flipOn (S : Finset (Site n)) (σ : Config n) : flipOn S (flipOn S σ) = σ := by
  funext p
  by_cases h : p ∈ S <;> simp [flipOn, h]

/-- **THE PAIRING.** `σ` goes to *(which boundary spins are wrong, the configuration with exactly
those flipped)*. -/
def pairMap (n : ℕ) (σ : Config n) : Finset (Site n) × Config n :=
  (downSet n σ, flipOn (downSet n σ) σ)

/-- **AND IT IS INJECTIVE ON EVERYTHING**, not stratum by stratum: flip the second component back
on the first and `σ` reappears. This is the step that makes the stratification unnecessary. -/
theorem pairMap_injective : Function.Injective (pairMap n) := by
  intro σ σ' hpair
  have h1 : downSet n σ = downSet n σ' := congrArg Prod.fst hpair
  have h2 : flipOn (downSet n σ) σ = flipOn (downSet n σ') σ' := congrArg Prod.snd hpair
  have hstep : flipOn (downSet n σ) (flipOn (downSet n σ) σ)
      = flipOn (downSet n σ) (flipOn (downSet n σ') σ') := by rw [h2]
  rwa [flipOn_flipOn, ← h1, flipOn_flipOn] at hstep

/-- Off the `+` class the wrong-spin set is non-empty, which is what erases `S = ∅` from the
target and turns `(1+x)^B` into `(1+x)^B − 1`. -/
theorem downSet_ne_empty {σ : Config n} (hσ : ¬ PlusBoundary σ) : downSet n σ ≠ ∅ := by
  intro hempty
  refine hσ ((downCount_eq_zero_iff n σ).mp ?_)
  rw [← downSet_card, hempty, Finset.card_empty]

/-! ## 2. The binomial sum, which is `Finset.prod_add` with both factors constant -/

theorem sum_powerset_pow (s : Finset (Site n)) (x : ℝ) :
    ∑ t ∈ s.powerset, x ^ t.card = (x + 1) ^ s.card := by
  classical
  have h := Finset.prod_add (fun _ : Site n => x) (fun _ : Site n => (1 : ℝ)) s
  simpa [Finset.prod_const, Finset.prod_const_one] using h.symm

theorem sum_powerset_erase (s : Finset (Site n)) (x : ℝ) :
    ∑ t ∈ s.powerset.erase ∅, x ^ t.card = (x + 1) ^ s.card - 1 := by
  classical
  have hmem : (∅ : Finset (Site n)) ∈ s.powerset := Finset.empty_mem_powerset s
  have h := Finset.sum_erase_add s.powerset (fun t => x ^ t.card) hmem
  simp only [Finset.card_empty, pow_zero] at h
  rw [sum_powerset_pow] at h
  linarith

/-! ## 3. The weight comparison along the pairing -/

/-- **THE ONE PLACE `FlipEnergy` IS USED.** Along the pairing the Boltzmann weight grows by at most
`e^{16β|S|}`, and the field factor shrinks by `e^{−2βh|S|}`; together that is `x^{|S|}` with
`x = e^{(16−2h)β}`. -/
theorem term_le {β h : ℝ} (hβ : 0 ≤ β) (σ : Config n) :
    Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      ≤ Real.exp ((16 - 2 * h) * β) ^ (downSet n σ).card *
        Real.exp (-β * isingH n (flipOn (downSet n σ) σ)) := by
  set S := downSet n σ with hS
  set k : ℕ := S.card with hk
  have hflip : isingH n (flipOn S σ) ≤ isingH n σ + 16 * (k : ℝ) := isingH_flipOn_le S σ
  have hpow : Real.exp ((16 - 2 * h) * β) ^ k = Real.exp ((16 - 2 * h) * β * (k : ℝ)) := by
    rw [mul_comm ((16 - 2 * h) * β) (k : ℝ), Real.exp_nat_mul]
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hcount : ((downCount n σ : ℕ) : ℝ) = (k : ℝ) := by rw [hk, hS, downSet_card]
  rw [hcount]
  nlinarith [hflip, hβ]

/-! ## 4. The estimate -/

/-- **THE OFF-`+` MASS, EXPONENTIAL IN THE BOUNDARY RATHER THAN IN THE VOLUME.** -/
theorem sum_offPlus_le {β h : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      ≤ ((1 + Real.exp ((16 - 2 * h) * β)) ^ (bdrySites n).card - 1) *
        ∑ τ ∈ (Finset.univ : Finset (Config n)).filter (fun τ => PlusBoundary τ),
          Real.exp (-β * isingH n τ) := by
  classical
  set x : ℝ := Real.exp ((16 - 2 * h) * β) with hx
  set A := (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ) with hA
  set P := (Finset.univ : Finset (Config n)).filter (fun τ => PlusBoundary τ) with hP
  set T := ((bdrySites n).powerset.erase ∅) ×ˢ P with hT
  set G : Finset (Site n) × Config n → ℝ :=
    fun z => x ^ z.1.card * Real.exp (-β * isingH n z.2) with hG
  -- termwise, along the pairing
  have step1 : ∑ σ ∈ A, Real.exp (-β * isingH n σ) *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      ≤ ∑ σ ∈ A, G (pairMap n σ) :=
    Finset.sum_le_sum fun σ _ => term_le hβ σ
  refine step1.trans ?_
  -- the injective image
  have himg : ∑ σ ∈ A, G (pairMap n σ) = ∑ z ∈ A.image (pairMap n), G z :=
    (Finset.sum_image (pairMap_injective.injOn)).symm
  rw [himg]
  have hsub : A.image (pairMap n) ⊆ T := by
    intro z hz
    obtain ⟨σ, hσA, rfl⟩ := Finset.mem_image.mp hz
    have hnp : ¬ PlusBoundary σ := (Finset.mem_filter.mp hσA).2
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_erase.mpr
        ⟨downSet_ne_empty hnp, Finset.mem_powerset.mpr (downSet_subset n σ)⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, plusBoundary_flipOn_downSet σ⟩
  have hnn : ∀ z ∈ T, z ∉ A.image (pairMap n) → 0 ≤ G z := by
    intro z _ _
    have : (0 : ℝ) < x := Real.exp_pos _
    positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  -- and the product splits
  have hprod : ∑ z ∈ T, G z
      = (∑ S ∈ (bdrySites n).powerset.erase ∅, x ^ S.card) *
        ∑ τ ∈ P, Real.exp (-β * isingH n τ) := by
    rw [hT, Finset.sum_product, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum]
  rw [hprod, sum_powerset_erase]
  have hcomm : (x + 1) = (1 + x) := by ring
  rw [hcomm]

end BoundaryStratum
