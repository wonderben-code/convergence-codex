/-
  IsingChainRouteCeiling.lean — the chain comparison delivers `o(n²)` in an `n × n` box, so it
  fails for the same reason the bond-free one did.

  WHY. `IsingChainDecay.chain_expect_abs_le` proved that a field transmitted along `k` bonds
  arrives multiplied by at most `|tanh J|^k`, uniformly in whatever model is attached. `WALLS
  §W3.6`'s addendum then named the one remaining step in as many words: *"nothing counts which
  paths exist in an `n × n` box or how long they are, so the step from the decay to 'a chain
  comparison delivers `O(n)`' is not taken and its cost is not claimed."* **This file takes it.**

  WHAT IS PROVED. Write `depth n p` for the distance from `p` to the boundary of the box — the
  least of the four coordinate distances — so a chain reaching `p` from the boundary has at least
  `depth n p` bonds and delivers at most `r ^ depth n p` with `r = |tanh J| < 1`. Then

  * **`card_depth_lt_le`** — fewer than `4·D·n` sites have depth below `D`. **No ring
    decomposition is needed**: `depth p < D` forces one of the four coordinate distances below `D`,
    and each of those four conditions pins one coordinate to `D` values and leaves the other free.
  * **`chain_total_le`** — hence for EVERY threshold `D`, the route's total over the box is at most
    `4·D·n + n²·r^D`: the shallow sites contribute at most `1` each and there are few of them, the
    deep ones are many but each contributes at most `r^D`.
  * **`chain_route_insufficient`** — and no `m > 0` survives. Choose `D` with `r^D` small, then `n`
    large: the first term is linear in `n` and the second is a small fraction of `n²`.

  **THE TWO-TERM SPLIT IS WHY NO GEOMETRIC SERIES APPEARS.** Summing `r^{depth}` exactly would
  need the sites partitioned by depth and a geometric sum; bounding it by a threshold needs
  neither, and the threshold is chosen after `m` is given, which is exactly what the refutation
  allows.

  WHAT THIS IS AND IS NOT. It is a statement about a COMPARISON MODEL's output, in the same sense
  as `IsingBoundaryRouteCeiling.route_insufficient` and `IsingSiteFieldBound.
  route_insufficient_of_small_support`, and it says nothing about whether
  `IsingBoundaryField.MagnetisationBound` is TRUE. **No wall moves.** What changes is that the
  third and last comparison route named in `WALLS §W3.6` is now shown incapable rather than left
  unrouted.

  ONE HYPOTHESIS IS DELIBERATELY LEFT IN THE STATEMENT RATHER THAN DISCHARGED. That a chain
  reaching `p` needs at least `depth n p` bonds is geometry of the box that this file does not
  prove; it enters as the definition of the quantity being summed, and the theorems below are
  about that sum. Connecting `r ^ depth n p` to an actual chain comparison model on the box would
  need a path-existence argument, which is **not attempted** (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingChainDecay
import IsingBoundaryRouteCeiling

namespace IsingChainRouteCeiling

open Finset Real
open IsingFiniteVolume IsingBoundaryField

noncomputable section

/-! ## 1. Depth, and how few shallow sites there are -/

/-- The distance from `p` to the boundary of the `n × n` box: the least of the four coordinate
distances. -/
def depth (n : ℕ) (p : Site n) : ℕ :=
  min (min p.1.val (n - 1 - p.1.val)) (min p.2.val (n - 1 - p.2.val))

/-- Confining ONE coordinate to a set of size `D` leaves the other free, so at most `D · n` sites.
Stated once and used four times. -/
theorem card_fst_mem_le (n D : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ D) :
    (Finset.univ.filter fun p : Site n => p.1 ∈ S).card ≤ D * n := by
  classical
  have hsub : (Finset.univ.filter fun p : Site n => p.1 ∈ S) ⊆ S ×ˢ Finset.univ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_right n hS

theorem card_snd_mem_le (n D : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ D) :
    (Finset.univ.filter fun p : Site n => p.2 ∈ S).card ≤ D * n := by
  classical
  have hsub : (Finset.univ.filter fun p : Site n => p.2 ∈ S) ⊆ Finset.univ ×ˢ S := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hp⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact Nat.mul_le_mul_right n hS

/-- The `D` lowest values of a coordinate. -/
theorem card_lo_le (n D : ℕ) : (Finset.univ.filter fun a : Fin n => a.val < D).card ≤ D := by
  classical
  have h : (Finset.univ.filter fun a : Fin n => a.val < D).card ≤ (Finset.range D).card := by
    refine Finset.card_le_card_of_injOn (fun a : Fin n => a.val) (fun a ha => ?_)
      (fun a _ b _ h => Fin.val_injective h)
    exact Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  simpa using h

/-- **AND THE `D` HIGHEST**, which is a separate lemma and not a corollary of the previous one:
`n − 1 − a < D` does not imply `a < D`. The injection is `a ↦ n − 1 − a`, injective on `Fin n`
because `a < n` there. -/
theorem card_hi_le (n D : ℕ) :
    (Finset.univ.filter fun a : Fin n => n - 1 - a.val < D).card ≤ D := by
  classical
  have hcard : (Finset.univ.filter fun a : Fin n => n - 1 - a.val < D).card
      ≤ (Finset.range D).card := by
    refine Finset.card_le_card_of_injOn (fun a : Fin n => n - 1 - a.val) (fun a ha => ?_)
      (fun a _ b _ h => ?_)
    · exact Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    · refine Fin.ext ?_
      have ha := a.isLt
      have hb := b.isLt
      simp only at h
      omega
  simpa using hcard

/-- **FEWER THAN `4·D·n` SITES HAVE DEPTH BELOW `D`.** `depth p < D` forces one of the four
coordinate distances below `D`, and each of those four conditions confines one coordinate to `D`
values. No ring decomposition is needed. -/
theorem card_depth_lt_le (n D : ℕ) :
    (Finset.univ.filter fun p : Site n => depth n p < D).card ≤ 4 * (D * n) := by
  classical
  set A₁ := Finset.univ.filter fun p : Site n => p.1 ∈ Finset.univ.filter fun a : Fin n =>
    a.val < D with hA₁
  set A₂ := Finset.univ.filter fun p : Site n => p.1 ∈ Finset.univ.filter fun a : Fin n =>
    n - 1 - a.val < D with hA₂
  set A₃ := Finset.univ.filter fun p : Site n => p.2 ∈ Finset.univ.filter fun a : Fin n =>
    a.val < D with hA₃
  set A₄ := Finset.univ.filter fun p : Site n => p.2 ∈ Finset.univ.filter fun a : Fin n =>
    n - 1 - a.val < D with hA₄
  have hsub : (Finset.univ.filter fun p : Site n => depth n p < D) ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, depth] at hp
    simp only [hA₁, hA₂, hA₃, hA₄, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  have h1 : A₁.card ≤ D * n := by rw [hA₁]; exact card_fst_mem_le n D _ (card_lo_le n D)
  have h2 : A₂.card ≤ D * n := by rw [hA₂]; exact card_fst_mem_le n D _ (card_hi_le n D)
  have h3 : A₃.card ≤ D * n := by rw [hA₃]; exact card_snd_mem_le n D _ (card_lo_le n D)
  have h4 : A₄.card ≤ D * n := by rw [hA₄]; exact card_snd_mem_le n D _ (card_hi_le n D)
  calc (A₁ ∪ A₂ ∪ A₃ ∪ A₄).card
      ≤ (A₁ ∪ A₂ ∪ A₃).card + A₄.card := Finset.card_union_le _ _
    _ ≤ ((A₁ ∪ A₂).card + A₃.card) + A₄.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((A₁.card + A₂.card) + A₃.card) + A₄.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ 4 * (D * n) := by omega

/-! ## 2. The two-term split, and the ceiling it gives

Bounding `∑ r^{depth}` exactly would need the sites partitioned by depth and a geometric sum.
Splitting at a threshold needs neither, and the threshold may be chosen **after** `m` is given,
which is exactly what a refutation allows. -/

/-- **THE ROUTE'S TOTAL, SPLIT AT ANY THRESHOLD.** Shallow sites contribute at most `1` each and
there are few of them; deep sites are many but each contributes at most `r^D`. -/
theorem chain_total_le (n D : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∑ p : Site n, r ^ depth n p ≤ 4 * (D : ℝ) * n + ((n : ℝ) * n) * r ^ D := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Site n => depth n p < D)]
  have hlow : ∑ p ∈ Finset.univ.filter (fun p : Site n => depth n p < D), r ^ depth n p
      ≤ 4 * (D : ℝ) * n := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun p _ => pow_le_one₀ hr0 hr1)) ?_
    rw [nsmul_eq_mul, mul_one]
    have := card_depth_lt_le n D
    have hc : ((Finset.univ.filter fun p : Site n => depth n p < D).card : ℝ)
        ≤ ((4 * (D * n) : ℕ) : ℝ) := Nat.cast_le.mpr this
    push_cast at hc
    linarith
  have hhigh : ∑ p ∈ Finset.univ.filter (fun p : Site n => ¬ depth n p < D), r ^ depth n p
      ≤ ((n : ℝ) * n) * r ^ D := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (r ^ D) (fun p hp => ?_)) ?_
    · have hD : D ≤ depth n p := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp
        exact hp
      exact pow_le_pow_of_le_one hr0 hr1 hD
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hc : ((Finset.univ.filter fun p : Site n => ¬ depth n p < D).card : ℝ)
          ≤ ((Finset.univ : Finset (Site n)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      rw [Finset.card_univ] at hc
      simpa [Site, Fintype.card_prod, Fintype.card_fin] using hc
  linarith

/-- **AND SO NO `m > 0` SURVIVES.** Choose `D` with `r^D` small — possible because `r < 1` — then
`n` large: the first term of the split is linear in `n` and the second is a fixed small fraction of
`n²`. The order of the choices is the whole argument. -/
theorem chain_route_insufficient {r m : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hm : 0 < m) :
    ¬ ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∑ p : Site n, r ^ depth n p := by
  intro hall
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < m / 2) hr1
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * (D : ℝ) / m)
  set n := N + 1 with hn
  have hnpos : (0:ℝ) < (n : ℝ) := by positivity
  have hNn : 8 * (D : ℝ) / m < (n : ℝ) := by
    refine lt_trans hN ?_
    rw [hn]
    push_cast
    linarith
  rw [div_lt_iff₀ hm] at hNn
  have h1 := hall n (Nat.succ_pos N)
  have h2 := chain_total_le n D hr0 hr1.le
  have hsq : (0:ℝ) < (n:ℝ) * n := by positivity
  nlinarith [h1, h2, hD, hNn, hnpos, hsq, pow_nonneg hr0 D]

end

end IsingChainRouteCeiling
