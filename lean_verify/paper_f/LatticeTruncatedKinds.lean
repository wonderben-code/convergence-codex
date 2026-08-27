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

* **`abs_integral_prod_sub_mul_le_kinds`** — the sum bound with a separate estimate per kind;
* **`kinds_le_max`** — **the check, and it is a comparison rather than an instance.** The new
  per-pairing bound is at most `max(Ms,Mt)^(k/2−2)·ε²`, which is the old one: the two exponents
  add to `k/2 − 2` exactly, and if they did not this would fail.

## What is NOT here

**Any improvement at order four.** At `k = 4` and `|S| = 2` both exponents are `0`, so this bound
and its predecessor are the same number. **The check is deliberately NOT at order four for that
reason** — an instance that cannot distinguish the two proves nothing about the sharpening, and
`PairingGlue`'s record already carries the estate's rule that a check which cannot fail is not one.

**And the decay composition.** Turning `Ms`, `Mt` and `ε` into `ℓ¹` norms and a decay rate is
`LatticeTruncatedNorms`' route, and running it again here would restate that file with three
constants instead of two. **Not done, not costed** (`ERRATUM 194`).
-/

namespace LatticeTruncatedKinds

open Equiv Function Involutions PairingSplit PairingCluster PairingKinds
open LatticeTruncatedCount
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The sum bound, kind by kind -/

/-- **THE TRUNCATED CORRELATION, WITH A SEPARATE ESTIMATE ON EACH SIDE.** `Ms` bounds the
propagator between two near indices, `Mt` between two far ones, `ε` across — and the exponents are
the sizes of the two sides, not a count of anything. -/
theorem abs_integral_prod_sub_mul_le_kinds (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {ε Ms Mt : ℝ} (hε0 : 0 ≤ ε) (hεs : ε ≤ Ms) (hεt : ε ≤ Mt)
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
    refine abs_prod_le_worst σ.2 S (fun i j => dotG G m (a i) (a j)) hε0 hεs hεt ?_ ?_ ?_ hS hns
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
    have hMs0 : (0:ℝ) ≤ Ms := le_trans hε0 hεs
    have hMt0 : (0:ℝ) ≤ Mt := le_trans hε0 hεt
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
    (hε0 : 0 ≤ ε) (hεs : ε ≤ Ms) (hεt : ε ≤ Mt)
    (hS : Even S.card) (hT : Even Sᶜ.card) (hk : 2 ≤ S.card) (hk' : 2 ≤ Sᶜ.card) :
    Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2
      ≤ max Ms Mt ^ (k / 2 - 2) * ε ^ 2 := by
  have hMs0 : (0:ℝ) ≤ Ms := le_trans hε0 hεs
  have hMt0 : (0:ℝ) ≤ Mt := le_trans hε0 hεt
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

end LatticeTruncatedKinds
