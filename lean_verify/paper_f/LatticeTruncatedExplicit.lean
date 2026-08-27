import LatticeTruncatedCount
import PairingCount

/-!
# The truncated bound with its constant written out

`LatticeTruncatedCount` put the number of **crossing** pairings into the constant, and
`PairingCount` turned that number into a formula. Both records then said the same thing was left
undone: **the bound still carries a `Finset.card` in its statement, and nobody has substituted the
formula.** This substitutes it.

The result is the first statement on this line whose constant a reader can evaluate without
enumerating anything: at `2n` test functions split into groups of `2j` and `2(n−j)`, the truncated
correlation is bounded by

  `((2n−1)‼ − (2j−1)‼·(2(n−j)−1)‼) · ε² · M^(n−2)`

and, with the decay estimate composed in, by the same constant times `(C²rᴺ/m²)²·(C²/m²)^(n−2)`.

**AND AT FOUR TEST FUNCTIONS THAT CONSTANT IS THE NUMERAL `2`.** `3‼ − 1‼·1‼ = 3 − 1 = 2`, and
`M^(n−2)` is `M⁰`, so the general machinery's bound at order four reads
`≤ 2·(C²rᴺ/m²)²` — **the shape of `LatticeFourPointClustering.connected_smeared_le` exactly**, with
`C²` in place of `‖f‖₁·‖g‖₁`. That single substitution is now the whole of the difference between
the general route and the special one, where three units ago it was a weaker exponent, a larger
constant AND the norms.

## What is proved

* `truncated_abs_le_count` — the decay composition of `LatticeTruncatedSharp.truncated_abs_le_sq`
  re-run against the crossing count rather than the total. A re-run, not a new argument;
* **`abs_integral_prod_sub_mul_le_explicit`** — the sum bound with the double factorials in it;
* **`truncated_abs_le_explicit`** — the decay bound with the double factorials in it;
* **`truncated_abs_le_four`** — **the payoff**, and the one statement here a reader can compare
  with `connected_smeared_le` line by line: at four test functions the constant is `2`.

## What is NOT here

**The comparison itself, as a theorem.** `truncated_abs_le_four` has the same constant and the same
power of the decay rate as `connected_smeared_le`, but it is stated at four arbitrary test functions
and that one is stated at the pattern `(f, f, g, g)`. Instantiating this chain at `![f, f, g, g]`
and `S = {0, 1}` and landing on `connected_smeared_le`'s left-hand side is a further step —
`LatticeSplitFourCheck` already has the three product identities it would need — and it is **not
done, not costed** (`ERRATUM 194`). Until it is, the agreement of the two constants is something a
reader checks by eye and not something the estate proves.

**And the norms are untouched**, because they are not a counting question: carrying `‖f‖₁` and
`‖g‖₁` separately through `PairingBound` and `PairingSharp` is what would close the last gap.
-/

namespace LatticeTruncatedExplicit

open Equiv Function Involutions PairingSplit PairingCount PairingCluster
open LatticeTruncatedSharp LatticeTruncatedCount LatticeTruncatedDecay
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The decay composition, against the crossing count

`LatticeTruncatedSharp.truncated_abs_le_sq`'s proof, with `abs_integral_prod_sub_mul_le_count` in
place of `abs_integral_prod_sub_mul_le_sq`. Nothing else changes: the two `ℓ¹` estimates it feeds
in are the same ones. -/

/-- The truncated correlation, bounded by the CROSSING count times the decayed constant. -/
theorem truncated_abs_le_count (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Finset.univ.filter
            (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2
            * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 2)) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ decayRate Δ m := decayRate_nonneg Δ hm
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by positivity
  have hU0 : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hl1 : ∀ i, (0 : ℝ) ≤ ∑ p, |(a i).ofLp p| :=
    fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_integral_prod_sub_mul_le_count hm a S hS (by positivity) ?_ ?_
  · intro i hi j hj
    refine (dotG_abs_le_of_sep hm hΔ (a i) (a j) (hsep i hi j hj)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hK0
  · intro i j
    refine (dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC i) (hC j) (hl1 j) hC0) hU0

/-! ## 2. The constant, written out

`PairingCount.card_crossing_doubleFactorial` is the substitution. It asks for both the index set and
the split to have even size, which is why the statements below are indexed by `Fin (2 * n)` and
`S.card = 2 * j` rather than by `k` and `Even S.card`: those are the same hypotheses, said in the
form the formula needs. -/

/-- **THE SUM BOUND, WITH ITS CONSTANT EVALUATED.** -/
theorem abs_integral_prod_sub_mul_le_explicit (hm : m ≠ 0) {n j : ℕ}
    (a : Fin (2 * n) → EuclideanSpace ℝ V) (S : Finset (Fin (2 * n))) (hS : S.card = 2 * j)
    {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j' ∉ S, |dotG G m (a i) (a j')| ≤ ε)
    (hall : ∀ i j', |dotG G m (a i) (a j')| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin (2 * n) // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin (2 * n) // y ∉ S},
              (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Nat.doubleFactorial (2 * n - 1)
            - Nat.doubleFactorial (2 * j - 1) * Nat.doubleFactorial (2 * (n - j) - 1) : ℕ) : ℝ)
        * (ε ^ 2 * M ^ (n - 2)) := by
  have hcard : (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin (2 * n))) => ¬ RespectsSplit S σ.1)).card
        = Nat.doubleFactorial (2 * n - 1)
          - Nat.doubleFactorial (2 * j - 1) * Nat.doubleFactorial (2 * (n - j) - 1) :=
    card_crossing_doubleFactorial S (by rw [Fintype.card_fin]) hS
  have hdiv : 2 * n / 2 - 2 = n - 2 := by omega
  have h := abs_integral_prod_sub_mul_le_count hm a S (by rw [hS]; exact even_two_mul j) hM0
    hcross hall
  rwa [hcard, hdiv] at h

/-- **THE DECAY BOUND, WITH ITS CONSTANT EVALUATED.** -/
theorem truncated_abs_le_explicit (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N n j : ℕ}
    (a : Fin (2 * n) → EuclideanSpace ℝ V) (S : Finset (Fin (2 * n))) (hS : S.card = 2 * j)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j' ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j').ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin (2 * n) // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin (2 * n) // y ∉ S},
              (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Nat.doubleFactorial (2 * n - 1)
            - Nat.doubleFactorial (2 * j - 1) * Nat.doubleFactorial (2 * (n - j) - 1) : ℕ) : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2
            * (C * C * (m ^ 2)⁻¹) ^ (n - 2)) := by
  have hcard : (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin (2 * n))) => ¬ RespectsSplit S σ.1)).card
        = Nat.doubleFactorial (2 * n - 1)
          - Nat.doubleFactorial (2 * j - 1) * Nat.doubleFactorial (2 * (n - j) - 1) :=
    card_crossing_doubleFactorial S (by rw [Fintype.card_fin]) hS
  have hdiv : 2 * n / 2 - 2 = n - 2 := by omega
  have h := truncated_abs_le_count hm hΔ a S (by rw [hS]; exact even_two_mul j) hC0 hC hsep
  rwa [hcard, hdiv] at h

/-! ## 3. The payoff, at four test functions -/

/-- **THE CONSTANT AT ORDER FOUR IS `2`.** `3‼ − 1‼·1‼ = 2` and `M⁰ = 1`, so the general machinery
— thirteen files from `PairingSplit` — bounds the truncated four-point correlation by
`2·(C²rᴺ/m²)²`. **That is `LatticeFourPointClustering.connected_smeared_le`'s constant and its
power of the decay rate**, with `C²` where that estimate has `‖f‖₁·‖g‖₁`. -/
theorem truncated_abs_le_four (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (a : Fin 4 → EuclideanSpace ℝ V) (S : Finset (Fin 4)) (hS : S.card = 2)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j' ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j').ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ 2 * (C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 := by
  have h := truncated_abs_le_explicit (n := 2) (j := 1) hm hΔ a S (by rw [hS]) hC0 hC hsep
  norm_num [Nat.doubleFactorial] at h
  exact h

end LatticeTruncatedExplicit
