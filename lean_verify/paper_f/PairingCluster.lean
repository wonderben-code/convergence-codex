import PairingBound
import PairingRelabel

/-!
# The truncated correlation IS the crossing pairings, and it is bounded

`PairingRelabel.integral_prod_split` needed the propagator across the split to vanish. **The
identity underneath it needs nothing at all**, and that is this file's first result: the
difference between a correlation and the product of its two halves' correlations **is exactly the
sum over the pairings that cross**. No hypothesis, no estimate — an equation.

The estimate follows by bounding each crossing term (`PairingBound`) and counting them.

## What is proved

* **`integral_prod_sub_mul_eq`** — for the correlated Gaussian field on a finite graph, at every
  order and **with no hypothesis on the propagator**:

  ```
  ∫ ∏ᵢ⟪aᵢ,ω⟫  −  (∫ ∏_{i∈S}⟪aᵢ,ω⟫)·(∫ ∏_{i∉S}⟪aᵢ,ω⟫)  =  ∑ over the CROSSING pairings.
  ```

  That is the truncated (connected) correlation across the split, identified term by term;
* **`abs_integral_prod_sub_mul_le`** — hence it is at most `N · ε · M^(k/2 − 1)`, where `ε`
  bounds the propagator across the split, `M` bounds it everywhere, and `N` is the number of
  perfect matchings of `Fin k`;
* `integral_prod_split_of_cross_eq_zero` — **the check**: at `ε = 0` the bound forces the
  difference to vanish, which is `PairingRelabel.integral_prod_split` again. The two routes are
  different — that theorem deletes the crossing terms inside the pairing sum, this one bounds
  their total and sends the bound to zero — and they must agree.

## What is NOT here

Any statement about the graph. `ε` is a hypothesis here, not a consequence: turning *"the two
groups are far apart"* into a numerical `ε` is `GreenDecay`/`GreenClustering`'s business and is
not done here. **Not costed** (`ERRATUM 194`). Finite volume throughout.

**⚠ ANSWERED, pointer added 2026-08-27 (`ERRATUM 314`); the sentence is kept as written
(`ERRATUM 94`) and stays true of this file.** `LatticeTruncatedDecay.truncated_abs_le` takes the
separation hypothesis and produces `decayRate Δ m ^ N`, which is exactly that conversion.
-/

namespace PairingCluster

open Equiv Function Involutions PairWeightRep PairingSplit PairingRestrict PairingGlue
open PairingWeight PairingBound PairingRelabel
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The truncated correlation, exactly -/

/-- **THE TRUNCATED CORRELATION IS THE CROSSING PAIRINGS, AND THIS NEEDS NO HYPOTHESIS.** Every
step is an identity: Isserlis at every order, the sum split by whether a matching respects the
split, and the respecting half factorised. -/
theorem integral_prod_sub_mul_eq (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    (S : Finset (Fin k)) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
      = ∑ σ ∈ Finset.univ.filter
          (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i)) := by
  classical
  have hfac : (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
        * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
      = ∑ σ ∈ Finset.univ.filter
          (fun σ : ↑(perfectMatchings (Fin k)) => RespectsSplit S σ.1),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i)) := by
    rw [← sum_pm_eq_integral hm a (fun x : {x : Fin k // x ∈ S} => (x : Fin k)),
      ← sum_pm_eq_integral hm a (fun y : {y : Fin k // y ∉ S} => (y : Fin k)),
      ← sum_respecting_eq_mul S (fun i j => dotG G m (a i) (a j)),
      sum_filter_eq_sum_subtype S
        (fun σ => ∏ i ∈ Finset.univ.filter (fun i => i < σ i), dotG G m (a i) (a (σ i)))]
  rw [IsserlisAll.isserlisGeneral_all hm k a, hfac,
    show (∑ σ : ↑(perfectMatchings (Fin k)), pairProduct G m a σ.1)
      = ∑ σ : ↑(perfectMatchings (Fin k)),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i)) from rfl,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ↑(perfectMatchings (Fin k)))
      (fun σ => RespectsSplit S σ.1)]
  ring

/-! ## 2. And it is small -/

/-- **THE ESTIMATE.** Each crossing pairing carries a factor from across the split, bounded by
`ε`, and `k/2 − 1` others bounded by `M`; there are at most `N` pairings in all. -/
theorem abs_integral_prod_sub_mul_le (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    (S : Finset (Fin k)) {ε M : ℝ} (hε0 : 0 ≤ ε) (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hall : ∀ i j, |dotG G m (a i) (a j)| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) * (ε * M ^ (k / 2 - 1)) := by
  classical
  have hc0 : (0 : ℝ) ≤ ε * M ^ (k / 2 - 1) := mul_nonneg hε0 (pow_nonneg hM0 _)
  rw [integral_prod_sub_mul_eq hm a S]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ ∈ Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1),
      |∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i))|
        ≤ ε * M ^ (k / 2 - 1) := by
    intro σ hσ
    have hns : ¬ RespectsSplit S σ.1 := (Finset.mem_filter.mp hσ).2
    have hb := abs_prod_le_of_not_respects (σ := σ.1) σ.2
      (w := fun i j => dotG G m (a i) (a j)) (fun i j => dotG_comm hm _ _)
      (S := S) (R := Finset.univ.filter (fun i => i < σ.1 i)) (isRepSet_filter_lt σ.2.1)
      hM0 hcross hall hns
    rwa [card_filter_lt_eq σ.2, Fintype.card_fin] at hb
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  exact_mod_cast Finset.card_filter_le _ _

/-! ## 3. The check

`PairingRelabel.integral_prod_split` deletes the crossing pairings inside the pairing sum; §2
bounds their total. At `ε = 0` the bound is zero, so the difference vanishes — and that is the
same conclusion, reached without deleting anything. -/

/-- **THE CHECK.** At `ε = 0` the estimate recovers `PairingRelabel.integral_prod_split`, by a
route that never deletes a term: it bounds the crossing terms' total and the bound is zero. -/
theorem integral_prod_split_of_cross_eq_zero (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k))
    (hzero : ∀ i ∈ S, ∀ j ∉ S, dotG G m (a i) (a j) = 0) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
      = (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
        * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m)) := by
  classical
  -- a crude but always-available bound: the sum of every entry's absolute value
  obtain ⟨M, hM0, hall⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i j, |dotG G m (a i) (a j)| ≤ M := by
    refine ⟨∑ p : Fin k × Fin k, |dotG G m (a p.1) (a p.2)|,
      Finset.sum_nonneg fun p _ => abs_nonneg _, fun i j => ?_⟩
    exact Finset.single_le_sum (f := fun p : Fin k × Fin k => |dotG G m (a p.1) (a p.2)|)
      (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
  have hb := abs_integral_prod_sub_mul_le hm a S (ε := 0) le_rfl hM0
    (fun i hi j hj => by rw [hzero i hi j hj]; simp) hall
  simp only [zero_mul, mul_zero] at hb
  have := abs_nonpos_iff.mp hb
  linarith [this]

end PairingCluster
