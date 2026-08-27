import LatticeTruncatedSharp

/-!
# Counting the pairings that actually cross

`PairingCluster` and `LatticeTruncatedSharp` both end the same way: having bounded each crossing
pairing, they bound *how many there are* by the number of pairings **in total**. That last step
throws information away, and at order four it is exactly the difference between this estate's two
bounds. `LatticeFourPointClustering.connected_smeared_le` carries the constant **2**; running the
general machinery at the same instance gives **3**, because `Fin 4` has three perfect matchings
and only two of them cross the split `{0, 1}`.

**So the general bound was not weaker for a mathematical reason — it was weaker because of a
relaxation on its last line.** This file stops one step earlier.

## What is proved

* **`abs_integral_prod_sub_mul_le_count`** — the sum bound with the number of **crossing**
  pairings in it rather than the number of pairings;
* `count_le_card` — and that this is never worse than the published form, so nothing is lost;
* **`crossing_card_fin_four`** — **the check**, by `decide`: at `Fin 4` split `{0, 1}` the
  crossing pairings number **2**, not 3. **That is `connected_smeared_le`'s constant exactly**,
  and it is the first time the general route reaches it.

## What is NOT here

The remaining difference from `connected_smeared_le`, which is now one thing and not two: that
bound uses `‖f‖₁·‖g‖₁` where this uses `C²` for a common bound `C` on every test function's `ℓ¹`
norm. Carrying the two norms separately through `PairingBound` and `PairingSharp` would close it.
**Not done, not costed** (`ERRATUM 194`).
-/

namespace LatticeTruncatedCount

open Equiv Function Involutions PairWeightRep PairingSplit PairingBound PairingSharp
open PairingCluster LatticeTruncatedSharp
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The bound, with the crossing count in it -/

/-- **THE SUM BOUND, STOPPING ONE STEP EARLIER.** Identical to
`LatticeTruncatedSharp.abs_integral_prod_sub_mul_le_sq` up to its last line, which relaxed the
number of CROSSING pairings to the number of pairings. -/
theorem abs_integral_prod_sub_mul_le_count (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hall : ∀ i j, |dotG G m (a i) (a j)| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Finset.univ.filter
            (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
        * (ε ^ 2 * M ^ (k / 2 - 2)) := by
  classical
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
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  rwa [nsmul_eq_mul] at this

/-- And it is never worse than the published form, so replacing one by the other loses nothing. -/
theorem count_le_card {k : ℕ} (S : Finset (Fin k)) :
    ((Finset.univ.filter
        (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) := by
  exact_mod_cast Finset.card_filter_le _ _

/-! ## 2. The check -/

/-- **THE CHECK.** `Fin 4` has three perfect matchings and only **two** of them cross the split
`{0, 1}` — the one pairing `0` with `1` does not. **Two is
`LatticeFourPointClustering.connected_smeared_le`'s constant**, which the general route reaches
here for the first time; the published form gives three. -/
theorem crossing_card_fin_four :
    (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin 4)) =>
        ¬ RespectsSplit ({0, 1} : Finset (Fin 4)) σ.1)).card = 2 := by
  decide

end LatticeTruncatedCount
