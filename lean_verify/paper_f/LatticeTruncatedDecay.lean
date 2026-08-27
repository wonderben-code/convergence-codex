import PairingCluster
import GreenClustering

/-!
# The truncated correlation decays, at every order

`PairingCluster.abs_integral_prod_sub_mul_le` bounds the truncated correlation by `N·ε·M^(k/2−1)`
and says plainly that `ε` is a **hypothesis, not a consequence** — nothing in it mentions a graph.
`GreenClustering.cross_abs_le` is the estate's statement that turns *"the supports are `N` steps
apart"* into a number. **This composes them**, and what comes out is exponential decay of the
truncated correlation at every order.

## The uniform bound is the separated bound at zero separation

`abs_integral_prod_sub_mul_le` wants a bound `M` on the propagator between ANY two of the test
functions, separated or not. That is `cross_abs_le` at `N = 0`: its separation hypothesis reads
*"unreachable, or `0 ≤ dist"*, whose second disjunct is free, and `decayRate ^ 0 = 1`. **So no new
estimate is needed for the unseparated pairs** — the same theorem supplies both constants.

## What is proved

* `dotG_abs_le_of_sep` and `dotG_abs_le` — the separated and uniform bounds on `dotG`, both from
  `cross_abs_le`, the second at `N = 0`;
* **`truncated_abs_le`** — for the correlated Gaussian field on a finite graph of degree at most
  `Δ`, with every test function of `ℓ¹` norm at most `C`, and the two groups' supports `N` steps
  apart (or in different components):

  ```
  |∫∏ᵢ⟪aᵢ,ω⟫ − (∫∏_{i∈S})·(∫∏_{i∉S})| ≤ P(k) · C²·rᴺ/m² · (C²/m²)^(k/2−1)
  ```

  with `r = decayRate Δ m < 1` and `P(k)` the number of perfect matchings of `Fin k`.
  **Geometric in `N`, at every order.**
* `truncated_eq_zero_of_not_reachable` — **the check**, and it is a limit case rather than a
  restatement: when no support point of one group reaches any of the other, the bound holds at
  **every** `N`, and `decayRate < 1` forces the truncated correlation to be exactly zero. The
  estate reaches that same conclusion by a different route —
  `PairingRelabel.integral_prod_split` deletes the crossing pairings — and the two must agree.

## What is NOT here

**The infinite volume, and the constant's behaviour in `k`.** `P(k)` is `(k−1)‼`, which grows
faster than geometrically, so this bound is useful at fixed order and says nothing about summing
over orders. That is what a cluster expansion is for and none of it is here. **Not costed**
(`ERRATUM 194`). Finite volume throughout.
-/

namespace LatticeTruncatedDecay

open Equiv Function Involutions PairingSplit PairingCluster
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay GreenClustering
open LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The two constants, from one theorem -/

/-- The separated bound, in `dotG`'s vocabulary. -/
theorem dotG_abs_le_of_sep (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f.ofLp p ≠ 0 → g.ofLp q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |dotG G m f g|
      ≤ (∑ p, |f.ofLp p|) * (∑ q, |g.ofLp q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
  cross_abs_le hm hΔ _ _ hsep

/-- **AND THE UNIFORM BOUND IS THE SAME THEOREM AT ZERO SEPARATION.** The separation hypothesis
at `N = 0` reads *"unreachable, or `0 ≤ dist`"*, whose second disjunct is free. -/
theorem dotG_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    (f g : EuclideanSpace ℝ V) :
    |dotG G m f g| ≤ (∑ p, |f.ofLp p|) * (∑ q, |g.ofLp q|) * (m ^ 2)⁻¹ := by
  have h := dotG_abs_le_of_sep hm hΔ (N := 0) f g (fun p q _ _ => Or.inr (Nat.zero_le _))
  simpa using h

/-! ## 2. The decay -/

/-- **THE TRUNCATED CORRELATION DECAYS GEOMETRICALLY IN THE SEPARATION, AT EVERY ORDER.** Each
crossing pairing carries a propagator between the two groups, and that one is small because the
supports are far apart; the rest are bounded uniformly. -/
theorem truncated_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
            * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 1)) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ decayRate Δ m := decayRate_nonneg Δ hm
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by positivity
  have hU0 : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hl1 : ∀ i, (0 : ℝ) ≤ ∑ p, |(a i).ofLp p| :=
    fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_integral_prod_sub_mul_le hm a S (by positivity) (by positivity) ?_ ?_
  · intro i hi j hj
    refine (dotG_abs_le_of_sep hm hΔ (a i) (a j) (hsep i hi j hj)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hK0
  · intro i j
    refine (dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hU0

/-! ## 3. The check

The bound holds at every `N` for which the supports are `N` apart. When they are in different
components that is EVERY `N`, and `decayRate Δ m < 1` sends the bound to zero — so the truncated
correlation is exactly zero, which `PairingRelabel.integral_prod_split` also concludes by deleting
the crossing pairings. The routes differ: one takes a limit, the other deletes terms. -/

/-- **THE CHECK, AND IT IS A LIMIT ARGUMENT RATHER THAN A RESTATEMENT.** With the two groups in
different components the estimate holds at **every** `N`; `decayRate Δ m < 1` sends the bound to
zero, so the truncated correlation is exactly zero. `PairingRelabel.integral_prod_split` reaches
that conclusion by DELETING the crossing pairings, and this reaches it by letting a bound on them
tend to zero — neither proof passes through the other. -/
theorem truncated_eq_zero_of_not_reachable (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {k : ℕ} (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k))
    (hnr : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
      = (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
        * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m)) := by
  classical
  -- an `ℓ¹` bound that exists at every `k`, the zero-test-function case included
  set C : ℝ := ∑ i : Fin k, ∑ p, |(a i).ofLp p| with hCdef
  have hC0 : (0 : ℝ) ≤ C :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C :=
    fun i => Finset.single_le_sum
      (f := fun i : Fin k => ∑ p, |(a i).ofLp p|)
      (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  set X : ℝ := ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
      - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
        * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
    with hXdef
  have hbound : ∀ N : ℕ, |X| ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
      * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
          * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 1)) := by
    intro N
    exact truncated_abs_le hm hΔ a S hC0 hC
      (fun i hi j hj p q hp hq => Or.inl (hnr i hi j hj p q hp hq))
  -- and the bound tends to zero, because `decayRate < 1`
  have hr : |decayRate Δ m| < 1 := by
    rw [abs_of_nonneg (decayRate_nonneg Δ hm)]
    exact decayRate_lt_one Δ hm
  have htend : Filter.Tendsto
      (fun N : ℕ => (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
            * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 1)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun N : ℕ => decayRate Δ m ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
    have := ((h0.const_mul ((m : ℝ) ^ 2)⁻¹).const_mul (C * C)).const_mul
      ((Fintype.card ↑(perfectMatchings (Fin k)) : ℝ))
    simp only [mul_zero] at this
    convert this.mul_const ((C * C * (m ^ 2)⁻¹) ^ (k / 2 - 1)) using 2 with N
    · ring
    · ring
  have hle : |X| ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hbound)
  have hX : X = 0 := abs_nonpos_iff.mp hle
  rw [hXdef] at hX
  linarith [hX]

end LatticeTruncatedDecay
