import PairingSharp
import LatticeTruncatedDecay

/-!
# The truncated correlation, at the sharp exponent

`PairingSharp.abs_prod_le_sq_of_not_respects` sharpened the bound **on one crossing pairing** from
`ε·M^(r−1)` to `ε²·M^(r−2)`, and the previous unit said plainly that this was not yet carried up
to the integral. **This carries it up**, and the decay exponent doubles: the truncated correlation
falls like `r^{2N}` rather than `r^N`, which is what
`LatticeFourPointClustering.connected_smeared_le` has at order four and what this now gives at
every even-sized split.

## What the extra hypothesis is, and why it is not a restriction in practice

`Even S.card`. The parity argument is what forces a second crossing, and it needs the near group
to have an even number of members. **At odd `|S|` the whole correlation vanishes anyway** — one
side of the split is odd, so its own correlation is zero and so is the product — so nothing is
lost that anybody wanted.

## What is proved

* **`abs_integral_prod_sub_mul_le_sq`** — the sum bound at the sharp exponent;
* **`truncated_abs_le_sq`** — and with `GreenClustering.cross_abs_le` in it, geometric decay at
  **twice** the rate: `≤ P(k)·(C²rᴺ/m²)²·(C²/m²)^(k/2−2)`.

## What is NOT here

The same two things the linear version names: the constant `P(k) = (k−1)‼` still grows faster
than geometrically, so this is a fixed-order bound and not a cluster expansion; and everything is
at a fixed finite graph. **Not costed** (`ERRATUM 194`).
-/

namespace LatticeTruncatedSharp

open Equiv Function Involutions PairWeightRep PairingSplit PairingBound PairingSharp
open PairingCluster LatticeTruncatedDecay
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay GreenClustering
open LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The sum bound at the sharp exponent -/

/-- **THE SUM BOUND, QUADRATIC IN THE CROSS-PROPAGATOR.** Identical in shape to
`PairingCluster.abs_integral_prod_sub_mul_le`, with `PairingSharp`'s per-term bound in place of
`PairingBound`'s and `Even S.card` as the price. -/
theorem abs_integral_prod_sub_mul_le_sq (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    (S : Finset (Fin k)) (hS : Even S.card) {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hall : ∀ i j, |dotG G m (a i) (a j)| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) * (ε ^ 2 * M ^ (k / 2 - 2)) := by
  classical
  have hc0 : (0 : ℝ) ≤ ε ^ 2 * M ^ (k / 2 - 2) := mul_nonneg (sq_nonneg _) (pow_nonneg hM0 _)
  rw [integral_prod_sub_mul_eq hm a S]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ ∈ Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1),
      |∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i))|
        ≤ ε ^ 2 * M ^ (k / 2 - 2) := by
    intro σ hσ
    have hns : ¬ RespectsSplit S σ.1 := (Finset.mem_filter.mp hσ).2
    have hb := abs_prod_le_sq_of_not_respects (σ := σ.1) σ.2
      (w := fun i j => dotG G m (a i) (a j)) (fun i j => dotG_comm hm _ _)
      (S := S) (R := Finset.univ.filter (fun i => i < σ.1 i)) (isRepSet_filter_lt σ.2.1)
      hM0 hcross hall hS hns
    rwa [card_filter_lt_eq σ.2, Fintype.card_fin] at hb
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  exact_mod_cast Finset.card_filter_le _ _

/-! ## 2. And the decay exponent doubles -/

/-- **THE TRUNCATED CORRELATION FALLS LIKE `r^{2N}`.** The same composition as
`LatticeTruncatedDecay.truncated_abs_le`, at the sharp per-term bound. -/
theorem truncated_abs_le_sq (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2
            * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 2)) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ decayRate Δ m := decayRate_nonneg Δ hm
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by positivity
  have hU0 : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hl1 : ∀ i, (0 : ℝ) ≤ ∑ p, |(a i).ofLp p| :=
    fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_integral_prod_sub_mul_le_sq hm a S hS (by positivity) ?_ ?_
  · intro i hi j hj
    refine (dotG_abs_le_of_sep hm hΔ (a i) (a j) (hsep i hi j hj)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hK0
  · intro i j
    refine (dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hU0

end LatticeTruncatedSharp
