import LatticeOddSplitSharp
import LatticeFourPointExact

/-!
# Where the clustering bounds have content, and where they are `0 ≤ 0`

`LatticeTruncatedDecay.truncated_abs_le` and `LatticeTruncatedSharp.truncated_abs_le_sq` bound

```
∫ ∏ᵢ ⟪aᵢ,ω⟫ − (∫ ∏_{i ∈ S} ⟪aᵢ,ω⟫)(∫ ∏_{i ∉ S} ⟪aᵢ,ω⟫)
```

at `k` factors split by `S`. **Neither says which `(k, |S|)` it says anything at**, and until now
the estate did not either. `LatticeTruncatedOdd.integral_prod_eq_zero_of_odd_card` settles it, and
the answer is a clean three-way split.

* **`k` odd** — the quantity is **`0`**, at every split, and `|S|` even or odd makes no
  difference: `truncated_eq_zero_of_odd_card`.
* **`k` even, `|S|` odd** — it is the FULL correlation
  (`LatticeTruncatedOdd.truncated_eq_full_of_odd`), and the sharp bound is **false** there
  (`LatticeOddSplitSharp.sharp_without_even_card_is_false`).
* **`k` even, `|S|` even** — the genuine case, where both bounds apply and neither is empty
  (`truncated_pos_at_even_split`).

**At odd `k` the sharp bound is literally `0 ≤ 0`.** Not "small", not "true for a good reason":
the left side is `|0|` and the right side is `(#pairings of Fin k)·(…)`, and an odd set has no
pairings at all, so `#` is `0` and the product is `0`. `sharpBody_of_odd_card` therefore holds
**with no hypotheses whatsoever** — not `0 ≤ M`, not `hcross`, not `hall`, not `Even S.card`.

**AND THAT IS THE CASE THE SENTENCE `ERRATUM 307` WITHDREW WAS DESCRIBING.** That sentence said
of an odd SPLIT that *"the statement there is `0 = 0` either way"*. It is `0 = 0` — at odd `k`,
which is a different condition, and the one place in this whole table where nothing is being
claimed. The observation was real and attached to the wrong row.

## What is proved

* **`truncated_eq_zero_of_odd_card`** — at odd `k`, the truncated correlation is `0` for **every**
  `a` and **every** `S`. Both terms vanish: the first because `k` is odd, the second because one
  side of any split of an odd set is odd;
* **`sharpBody_of_odd_card`** — so `LatticeOddSplitSharp.SharpBody` holds there unconditionally,
  and `truncated_abs_le_sq` carries no information at odd `k` whatever its hypotheses say;
* `truncated_abs_le_zero_of_odd_card` — the same for any non-negative right-hand side, so the
  reading is not an artefact of the sharp bound's particular constant;
* **`truncated_ne_zero_at_even_split`** — and the genuine case is not vacuous either: at `k = 4`,
  `S = {0,1}` and every test function equal to one `g ≠ 0`, the quantity is `2 (gᵀGg)² > 0`. With
  `LatticeTruncatedOdd.truncated_const_fin_four_pos` at the odd split, **both `k`-even rows of the
  table are shown non-trivial at a concrete instance.**

## What this does NOT do

**It does not improve either bound.** Every theorem here is about where the existing statements
have content, not about how good they are where they do. Nothing about the constant, the exponent
or the order of growth changes. Finite volume throughout. **No wall moves. No published tag
moves.**
-/

namespace LatticeTruncatedContent

open Equiv Function Involutions PairingSplit PairingCluster
open MeasureTheory ProbabilityTheory GraphLaplacian
open LatticeIsserlisSmeared LatticeMoments LatticeSobolevPoincare
open LatticeTruncatedOdd LatticeOddSplitSharp LatticeFourPointExact

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. At odd `k` the quantity is zero -/

/-- **AT AN ODD NUMBER OF FACTORS THE TRUNCATED CORRELATION VANISHES, AT EVERY SPLIT.**
Both terms go, for the same reason at different sets: `Fin k` is odd, and one side of any split of
an odd set is odd. No hypothesis on the propagator, the graph or the test functions. -/
theorem truncated_eq_zero_of_odd_card (hm : m ≠ 0) {k : ℕ} (hk : Odd k)
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
      = 0 := by
  have hfull : ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m) = 0 :=
    integral_prod_eq_zero_of_odd_card hm (by rwa [Fintype.card_fin]) a
  have hsum : S.card + Sᶜ.card = k := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  rcases Nat.even_or_odd S.card with hS | hS
  · -- `|S|` is even, so `|Sᶜ|` is odd and the second factor of the product vanishes
    have hT : Odd Sᶜ.card := by
      rcases hS with ⟨t, ht⟩
      rcases hk with ⟨n, hn⟩
      exact ⟨n - t, by omega⟩
    have h2 : ∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ))
        ∂(gaussianField G m) = 0 := by
      refine integral_prod_eq_zero_of_odd_card hm ?_ _
      rwa [show Fintype.card {y : Fin k // y ∉ S} = Sᶜ.card from
        (Fintype.card_congr (Equiv.subtypeEquivRight (fun x => (Finset.mem_compl).symm))).trans
          (Fintype.card_coe _)]
    rw [hfull, h2, mul_zero, sub_zero]
  · rw [hfull, integral_prod_subtype_eq_zero_of_odd hm a hS, zero_mul, sub_zero]

/-! ## 2. So both bounds are empty there -/

/-- **AND THE SHARP BOUND AT ODD `k` IS `0 ≤ 0`.** `LatticeOddSplitSharp.SharpBody` is
`abs_integral_prod_sub_mul_le_sq`'s conclusion, and at odd `k` it holds with **no hypotheses at
all** — not `0 ≤ M`, not `hcross`, not `hall`, not `Even S.card`. The left side is `|0|` by §1;
the right side is `0` because an odd set has no pairings
(`Involutions.card_perfectMatchings_eq_zero_of_odd`), so the cardinal factor in front is `0`.
**This is the row of the table where the theorem says nothing**, and it is the row the sentence
`ERRATUM 307` withdrew was really describing. -/
theorem sharpBody_of_odd_card (hm : m ≠ 0) {k : ℕ} (hk : Odd k)
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (ε M : ℝ) :
    SharpBody G m a S ε M := by
  have hcard : Fintype.card ↑(perfectMatchings (Fin k)) = 0 :=
    card_perfectMatchings_eq_zero_of_odd _
      (by rw [Fintype.card_fin]; exact Nat.not_even_iff_odd.mpr hk)
  rw [SharpBody, truncated_eq_zero_of_odd_card hm hk a S, hcard]
  simp

/-- The same reading without the sharp bound's particular right-hand side in it: at odd `k` the
quantity is under **every** non-negative number, so no bound of this shape has content there. -/
theorem truncated_abs_le_zero_of_odd_card (hm : m ≠ 0) {k : ℕ} (hk : Odd k)
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) {C : ℝ} (hC : 0 ≤ C) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ C := by
  rw [truncated_eq_zero_of_odd_card hm hk a S, abs_zero]
  exact hC

/-! ## 3. And the genuine case is not vacuous -/

/-- **THE `k`-EVEN, `|S|`-EVEN ROW IS NOT `0` EITHER.** Four factors all equal to one `g ≠ 0`,
split `{0,1}` against `{2,3}`: `PairingCluster.integral_prod_sub_mul_eq` turns the quantity into
the crossing sum and `LatticeFourPointExact.sum_crossing_fin_four` evaluates it, giving
`2 (gᵀGg)²`. With `LatticeTruncatedOdd.truncated_const_fin_four_pos` at the odd split, **both
`k`-even rows of the table now carry a concrete instance that is not zero**, so the trichotomy is
a statement about three live cases and not about one live case and two empty ones. -/
theorem truncated_ne_zero_at_even_split (hm : m ≠ 0) (g : EuclideanSpace ℝ V) :
    ∫ ω, (∏ i, (inner ℝ (![g, g, g, g] i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (![g, g, g, g] x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (![g, g, g, g] y) ω : ℝ)) ∂(gaussianField G m))
      = 2 * (linVar G m g) ^ 2 := by
  rw [integral_prod_sub_mul_eq hm ![g, g, g, g] ({0, 1} : Finset (Fin 4)),
    sum_crossing_fin_four (G := G) (m := m) g g, linVar_eq_dotG]

/-- And it is strictly positive off `g = 0`, by `LatticeSobolevPoincare.linVar_pos`. -/
theorem truncated_pos_at_even_split (hm : m ≠ 0) {g : EuclideanSpace ℝ V} (hg : g ≠ 0) :
    0 < ∫ ω, (∏ i, (inner ℝ (![g, g, g, g] i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (![g, g, g, g] x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (![g, g, g, g] y) ω : ℝ)) ∂(gaussianField G m)) := by
  rw [truncated_ne_zero_at_even_split hm g]
  have hpos : 0 < (linVar G m g) ^ 2 := pow_pos (linVar_pos hm hg) 2
  linarith

end LatticeTruncatedContent
