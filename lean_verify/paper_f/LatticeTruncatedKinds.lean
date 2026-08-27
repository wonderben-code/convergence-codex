import LatticeTruncatedNorms
import PairingKinds

/-!
# The truncated bound with a separate estimate on each side of the split

`LatticeTruncatedNorms` carries one `ℓ¹` norm per side, and its record says where the two are
merged: **the factor that must bound every pair, same-side ones included, can only be
`max(Cs,Ct)²` for a uniform bound.** `PairingKinds.abs_prod_le_worst` removes the need for a
uniform bound at the level of one pairing. This carries that to the integral.

The result estimates the near-near factors by `Ms`, the far-far factors by `Mt` and the two
crossing factors by `ε`, **with the exponents fixed by the sizes of the two sides** —
`(|S|−2)/2` and `(|Sᶜ|−2)/2` — and no maximum anywhere.

## What is proved

* **`abs_integral_prod_sub_mul_le_kinds`** — the sum bound with a separate estimate per kind.
  **Its cross hypothesis is `ε² ≤ Ms·Mt` and not `ε ≤ Ms` together with `ε ≤ Mt`**, which is what
  the trade reads like and is strictly stronger: at the clustering instance the two separately
  force `Cs = Ct`, collapsing the generality the two-norm bound exists for, while the product form
  reads `r^{2N} ≤ 1` and is free;
* **`truncated_abs_le_kinds`** — the decay composition, with `Cs²/m²` on the near side and
  `Ct²/m²` on the far one where `LatticeTruncatedNorms` has `max(Cs,Ct)²/m²` for both;
* **`kinds_le_max`** — **the check, and it is a comparison rather than an instance.** The new
  per-pairing bound is at most `max(Ms,Mt)^(k/2−2)·ε²`, which is the old one: the two exponents
  add to `k/2 − 2` exactly, and if they did not this would fail.

## What is NOT here

**Any improvement at order four.** At `k = 4` and `|S| = 2` both exponents are `0`, so this bound
and its predecessor are the same number. **The check is deliberately NOT at order four for that
reason** — an instance that cannot distinguish the two proves nothing about the sharpening, and
`PairingGlue`'s record already carries the estate's rule that a check which cannot fail is not one.

**Nothing on the clustering line.** §3 does the decay composition, so `LatticeTruncatedNorms`'
last remaining slack — `max(Cs,Ct)²` where the two sides deserve `Cs²` and `Ct²` — is gone. What
remains is what it has been since the first file: the infinite volume, the continuum, and a
constant super-geometric in the order.
-/

namespace LatticeTruncatedKinds

open Equiv Function Involutions PairingSplit PairingCluster PairingKinds
open LatticeTruncatedCount GreenDecay
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The sum bound, kind by kind -/

/-- **THE TRUNCATED CORRELATION, WITH A SEPARATE ESTIMATE ON EACH SIDE.** `Ms` bounds the
propagator between two near indices, `Mt` between two far ones, `ε` across — and the exponents are
the sizes of the two sides, not a count of anything. -/
theorem abs_integral_prod_sub_mul_le_kinds (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {ε Ms Mt : ℝ} (hMs0 : 0 ≤ Ms) (hMt0 : 0 ≤ Mt) (hε2 : ε ^ 2 ≤ Ms * Mt)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hnear : ∀ i ∈ S, ∀ j ∈ S, |dotG G m (a i) (a j)| ≤ Ms)
    (hfar : ∀ i ∉ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ Mt) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Finset.univ.filter
            (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
        * (Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2) := by
  classical
  rw [integral_prod_sub_mul_eq hm a S]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ ∈ Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1),
      |∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i))|
        ≤ Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2 := by
    intro σ hσ
    have hns : ¬ RespectsSplit S σ.1 := (Finset.mem_filter.mp hσ).2
    refine abs_prod_le_worst σ.2 S (fun i j => dotG G m (a i) (a j))
      hMs0 hMt0 hε2 ?_ ?_ ?_ hS hns
    · -- the two directions of "exactly one end is in `S`"; the second needs `dotG` symmetric.
      -- `dsimp only` first: the goal arrives beta-unreduced as `(fun i j => dotG ..) i (σ i)`
      -- and `rw [dotG_comm]` cannot see a pattern through the redex.
      intro i hi
      dsimp only
      by_cases hiS : i ∈ S
      · exact hcross i hiS (σ.1 i) (fun h => hi (iff_of_true hiS h))
      · have hσi : σ.1 i ∈ S := by
          by_contra h
          exact hi (iff_of_false hiS h)
        rw [dotG_comm hm]
        exact hcross (σ.1 i) hσi i hiS
    · intro i hiS hσi
      dsimp only
      exact hnear i hiS (σ.1 i) hσi
    · intro i hiS hσi
      dsimp only
      exact hfar i hiS (σ.1 i) hσi
  have hc0 : (0 : ℝ) ≤ Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2 := by
    positivity
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  rwa [nsmul_eq_mul] at this

/-! ## 2. The check

**A COMPARISON AND NOT AN INSTANCE**, because at the one instance this estate checks everything
else against — four test functions split two and two — the two bounds are the same number, both
exponents being zero. An instance that cannot tell them apart says nothing about the sharpening.
What CAN fail is the arithmetic of the exponents: they must add to `k/2 − 2` exactly. -/

/-- **THE CHECK.** The per-pairing bound of §1 is at most `max(Ms,Mt)^(k/2−2)·ε²`, which is
`LatticeTruncatedCount`'s. The two exponents `(|S|−2)/2` and `(|Sᶜ|−2)/2` add to `k/2 − 2`, and a
mis-stated exponent would break this. -/
theorem kinds_le_max {k : ℕ} (S : Finset (Fin k)) {ε Ms Mt : ℝ}
    (hMs0 : 0 ≤ Ms) (hMt0 : 0 ≤ Mt)
    (hS : Even S.card) (hT : Even Sᶜ.card) (hk : 2 ≤ S.card) (hk' : 2 ≤ Sᶜ.card) :
    Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2
      ≤ max Ms Mt ^ (k / 2 - 2) * ε ^ 2 := by
  -- BOTH sides must be even, and the hypothesis is not decoration: at `|S| = |Sᶜ| = 3`, `k = 6`
  -- the two halved exponents are `0` and `0` while `k/2 − 2` is `1`, so the identity fails.
  have hsum : (S.card - 2) / 2 + (Sᶜ.card - 2) / 2 = k / 2 - 2 := by
    have hcompl : S.card + Sᶜ.card = k := by
      have hc : Sᶜ.card = Fintype.card (Fin k) - S.card := Finset.card_compl S
      have hle : S.card ≤ Fintype.card (Fin k) := by
        simpa [Finset.card_univ] using Finset.card_le_univ S
      rw [Fintype.card_fin] at hc hle
      omega
    obtain ⟨p, hp⟩ := hS
    obtain ⟨q, hq⟩ := hT
    omega
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg ε)
  rw [← hsum, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ hMs0 (le_max_left _ _) _)
    (pow_le_pow_left₀ hMt0 (le_max_right _ _) _) (by positivity) (by positivity)

/-! ## 3. The decay composition

`LatticeTruncatedNorms`' route with three constants instead of two. **The proof is a re-run and
the STATEMENT is not**: the near-near factors now carry `Cs²/m²` and the far-far ones `Ct²/m²`,
where that file has `max(Cs,Ct)²/m²` for both.

**AND THIS IS WHERE `abs_prod_le_worst`'s HYPOTHESIS HAD TO BE WEAKENED.** With `ε = Cs·Ct·rᴺ/m²`,
`Ms = Cs²/m²` and `Mt = Ct²/m²`, the conditions `ε ≤ Ms` and `ε ≤ Mt` read `Ct·rᴺ ≤ Cs` and
`Cs·rᴺ ≤ Ct` — **which at `N = 0` force `Cs = Ct`**, collapsing the whole point of two norms.
`ε² ≤ Ms·Mt` reads `r^{2N} ≤ 1` and costs nothing. The composition is what found it. -/

/-- **THE DECAY BOUND WITH A SEPARATE NORM ON EACH SIDE, AND NO MAXIMUM.** -/
theorem truncated_abs_le_kinds (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hCs : ∀ i ∈ S, ∑ p, |(a i).ofLp p| ≤ Cs) (hCt : ∀ i ∉ S, ∑ p, |(a i).ofLp p| ≤ Ct)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Finset.univ.filter
            (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
        * ((Cs * Cs * (m ^ 2)⁻¹) ^ ((S.card - 2) / 2)
            * (Ct * Ct * (m ^ 2)⁻¹) ^ ((Sᶜ.card - 2) / 2)
            * (Cs * Ct * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ decayRate Δ m := decayRate_nonneg Δ hm
  have hr1 : decayRate Δ m ≤ 1 := le_of_lt (decayRate_lt_one Δ hm)
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by positivity
  have hU0 : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hl1 : ∀ i, (0 : ℝ) ≤ ∑ p, |(a i).ofLp p| :=
    fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine abs_integral_prod_sub_mul_le_kinds hm a S hS (by positivity) (by positivity) ?_ ?_ ?_ ?_
  · -- `ε² ≤ Ms·Mt` is `r^{2N} ≤ 1`, and nothing else
    have hrN : decayRate Δ m ^ N ≤ 1 := pow_le_one₀ hr0 hr1
    have : (Cs * Ct * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2
        ≤ (Cs * Ct * (1 * (m ^ 2)⁻¹)) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hrN hU0) (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  · intro i hi j hj
    refine (LatticeTruncatedDecay.dotG_abs_le_of_sep hm hΔ (a i) (a j) (hsep i hi j hj)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hCs i hi) (hCt j hj) (hl1 j) hCs0) hK0
  · intro i hi j hj
    refine (LatticeTruncatedDecay.dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hCs i hi) (hCs j hj) (hl1 j) hCs0) hU0
  · intro i hi j hj
    refine (LatticeTruncatedDecay.dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hCt i hi) (hCt j hj) (hl1 j) hCt0) hU0

end LatticeTruncatedKinds
