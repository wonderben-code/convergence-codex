import LatticeTruncatedSharp
import LatticeOddVanishing
import LatticeSobolevPoincare

/-!
# The odd split, and a correction to what the sharp bound's hypothesis costs

`LatticeTruncatedSharp.truncated_abs_le_sq` carries `Even S.card`, and **this file's own records
said that hypothesis cost nothing**, in these words:

> At odd `|S|` the whole correlation vanishes anyway — one side of the split is odd, so its own
> correlation is zero and so is the product — so nothing is lost that anybody wanted.

**The last clause is false, and this file proves what is true instead.** The truncated correlation
is a DIFFERENCE,

```
∫ ∏ᵢ ⟪aᵢ,ω⟫ − (∫ ∏_{i ∈ S} ⟪aᵢ,ω⟫)(∫ ∏_{i ∉ S} ⟪aᵢ,ω⟫),
```

and at odd `|S|` only the **second** term vanishes. The first is a correlation of `k` factors, and
when `k` is even it is generally nonzero. So the truncated correlation at an odd split is not
`0 = 0`: it is **the full correlation**, and the hypothesis `Even S.card` excludes a case in which
the statement has content.

The old sentence is right about `k` odd, where the full correlation vanishes too. It conflated
`|S|` odd with `k` odd. `ERRATA.md` carries the correction; here is the mathematics.

## What is proved

* **`integral_prod_eq_zero_of_odd_card`** — `LatticeOddVanishing.integral_prod_odd_eq_zero` at an
  arbitrary finite index type of odd cardinality rather than at `Fin (2n+1)`. The negation
  symmetry never cared how the factors were labelled, and dropping `Fin` is what lets the theorem
  reach a **side of a split**, which is a subtype and not a `Fin`;
* `integral_prod_subtype_eq_zero_of_odd` — the side of the split itself;
* `not_respectsSplit_of_odd` — at odd `|S|` **no** pairing respects the split;
* **`truncated_eq_full_of_odd`** — the correction: at odd `|S|` the truncated correlation IS the
  full correlation;
* **`truncated_eq_full_of_odd_two_ways`** — the same statement by a route sharing no step: through
  `PairingCluster.integral_prod_sub_mul_eq` and `IsserlisAll.isserlisGeneral_all`, i.e. through the
  pairing combinatorics rather than through the `ω ↦ −ω` symmetry;
* **`full_abs_le_of_odd`** — the honest consequence for `LatticeTruncatedDecay.truncated_abs_le`:
  at an odd split that theorem is bounding the **full** correlation, with no subtraction in it;
* **`truncated_const_fin_four`** and **`truncated_const_fin_four_pos`** — the witness. At `k = 4`,
  `S = {0}`, and every test function equal to one `f ≠ 0`, the truncated correlation is
  `3 (fᵀGf)² > 0`. That is the refutation of "`0 = 0` either way", at a concrete instance;
* **`card_cross_eq_one_of_card_eq_one`** — and the reason the sharp exponent is not merely
  unproved at an odd split. `PairingParity.two_le_card_cross` needs `Even S.card` because the
  crossing count has the parity of `|S|`; at `|S| = 1` the crossing count is exactly `1` for
  **every** pairing, so `2 ≤ c` is false rather than unavailable, and `ε²` cannot be reached.

## What this does NOT claim

**It does not exhibit a graph where the sharp bound fails numerically.** It shows the quantity is
generally nonzero and that the crossing count that would force `ε²` is `1`. Turning that into a
refuting instance needs a concrete `G`, `m` and separated test functions, and is not done here.

**No wall moves, no published tag moves, and `truncated_abs_le_sq` is unchanged** — it was always
true; what was false was a sentence about it.
-/

namespace LatticeTruncatedOdd

open Equiv Function Involutions PairingSplit PairingRestrict PairingParity
open PairingCluster LatticeTruncatedDecay IsserlisAll
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay
open LatticeIsserlisSmeared LatticeMoments LatticeSobolevPoincare WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Odd correlations, at any index type -/

/-- **EVERY ODD CORRELATION VANISHES, WHATEVER THE FACTORS ARE INDEXED BY.**
`LatticeOddVanishing.integral_prod_odd_eq_zero` says this at `Fin (2n+1)`; its proof uses nothing
about `Fin` beyond `Fintype.card_fin`, and this is the same proof with that step deleted. The
generalisation is what makes the theorem usable below, where the index type is `{i // i ∈ S}`. -/
theorem integral_prod_eq_zero_of_odd_card (hm : m ≠ 0) {ι : Type*} [Fintype ι]
    (hodd : Odd (Fintype.card ι)) (f : ι → EuclideanSpace ℝ V) :
    ∫ ω, (∏ i, (inner ℝ (f i) ω : ℝ)) ∂(gaussianField G m) = 0 := by
  refine LatticeOddVanishing.integral_odd_eq_zero (G := G) hm (fun ω => ?_)
  have h1 : ∀ i, (inner ℝ (f i) (-ω) : ℝ) = -(inner ℝ (f i) ω : ℝ) := fun i =>
    inner_neg_right (f i) ω
  simp only [h1, Finset.prod_neg, Finset.card_univ]
  rw [hodd.neg_one_pow]
  ring

/-- **ONE SIDE OF AN ODD SPLIT HAS NO CORRELATION.** The side is a subtype, whose cardinality is
the `Finset`'s card (`Fintype.card_coe`), so the theorem above applies to it directly. -/
theorem integral_prod_subtype_eq_zero_of_odd (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) {S : Finset (Fin k)} (hS : Odd S.card) :
    ∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m) = 0 := by
  refine integral_prod_eq_zero_of_odd_card (G := G) hm ?_ _
  rwa [Fintype.card_coe]

/-! ## 2. The correction -/

/-- **AT AN ODD SPLIT NOTHING RESPECTS IT.** `PairingRestrict.even_card_of_respects` says a
respected side is even; contrapose. This is the combinatorial shadow of the analytic fact above,
and §3 shows the two really do give the same answer.

**It needs neither `Fintype ι` nor `DecidableEq ι`**, and neither does
`card_cross_eq_one_of_card_eq_one` need the first. A draft carried both; the build reported them
unused and they were removed rather than silenced, as `PairingSharp.abs_le_of_mem_crossSet`
records for the same reason. -/
theorem not_respectsSplit_of_odd {ι : Type*} {S : Finset ι}
    (hS : Odd S.card) {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) :
    ¬ RespectsSplit S σ := fun h =>
  (Nat.not_even_iff_odd.mpr hS) (even_card_of_respects hσ h)

/-- **THE TRUNCATED CORRELATION AT AN ODD SPLIT IS THE FULL CORRELATION.**
Only the product term dies. The first term is a correlation of `k` factors and is untouched by
`|S|` being odd — which is exactly what the sentence quoted at the top of this file got wrong. -/
theorem truncated_eq_full_of_odd (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    {S : Finset (Fin k)} (hS : Odd S.card) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
      = ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m) := by
  rw [integral_prod_subtype_eq_zero_of_odd hm a hS, zero_mul, sub_zero]

/-! ## 3. The same statement, through the pairings instead -/

/-- **AND AGAIN, SHARING NO STEP WITH §2.** `PairingCluster.integral_prod_sub_mul_eq` turns the
truncated correlation into the sum over the pairings that CROSS the split; at an odd split every
pairing crosses, so that sum is the sum over all pairings, which is the full correlation by
`IsserlisAll.isserlisGeneral_all`. The route above goes through the `ω ↦ −ω` symmetry of the
measure and never mentions a pairing; this one goes through the combinatorics and never mentions
the symmetry. -/
theorem truncated_eq_full_of_odd_two_ways (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    {S : Finset (Fin k)} (hS : Odd S.card) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))
      = ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m) := by
  classical
  have hfil : (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)) = Finset.univ :=
    Finset.filter_true_of_mem fun σ _ => not_respectsSplit_of_odd hS σ.2
  rw [integral_prod_sub_mul_eq hm a S, hfil]
  exact (isserlisGeneral_all hm k a).symm

/-! ## 4. What `truncated_abs_le` is actually bounding there -/

/-- **AT AN ODD SPLIT, `LatticeTruncatedDecay.truncated_abs_le` BOUNDS THE FULL CORRELATION.**
Same hypotheses, same right-hand side, no subtraction on the left. This is a statement about a
correlation rather than about a difference of them, and it is the content the excluded case
actually has. -/
theorem full_abs_le_of_odd (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) {S : Finset (Fin k)} (hS : Odd S.card) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ∑ p, |(a i).ofLp p| ≤ C)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
        * ((C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
            * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 1)) := by
  have h := truncated_abs_le (G := G) hm hΔ a S hC0 hC hsep
  rwa [truncated_eq_full_of_odd hm a hS] at h

/-! ## 5. The witness -/

/-- **THE REFUTATION, AT A CONCRETE INSTANCE.** Four factors, all equal to one `f`, split as
`{0}` against the rest. `|S| = 1` is odd, so §2 applies and the truncated correlation is the
fourth moment, which `LatticeMoments.moment_four` evaluates. -/
theorem truncated_const_fin_four (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (∏ _i : Fin 4, (inner ℝ f ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ _x : {x : Fin 4 // x ∈ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m))
          * (∫ ω, (∏ _y : {y : Fin 4 // y ∉ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m))
      = 3 * (linVar G m f) ^ 2 := by
  have hodd : Odd (({0} : Finset (Fin 4)).card) := by
    rw [Finset.card_singleton]; exact odd_one
  have h : (∫ ω, (∏ _i : Fin 4, (inner ℝ f ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ _x : {x : Fin 4 // x ∈ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m))
          * (∫ ω, (∏ _y : {y : Fin 4 // y ∉ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m)))
      = ∫ ω, (∏ _i : Fin 4, (inner ℝ f ω : ℝ)) ∂(gaussianField G m) :=
    truncated_eq_full_of_odd (G := G) hm (fun _ => f) hodd
  rw [h, show (∫ ω, (∏ _i : Fin 4, (inner ℝ f ω : ℝ)) ∂(gaussianField G m))
      = ∫ ω, (inner ℝ f ω : ℝ) ^ 4 ∂(gaussianField G m) from by
        refine congrArg _ (funext fun ω => ?_)
        simp]
  exact moment_four hm f

/-- **AND IT IS NOT ZERO**, whenever `f` is not. `LatticeSobolevPoincare.linVar_pos` is where the
positive-definiteness of the Green function enters. **This is the whole correction in one
inequality**: at an odd split the truncated correlation is strictly positive here, so the claim
that the statement is `0 = 0` either way was false. -/
theorem truncated_const_fin_four_pos (hm : m ≠ 0) {f : EuclideanSpace ℝ V} (hf : f ≠ 0) :
    0 < ∫ ω, (∏ _i : Fin 4, (inner ℝ f ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ _x : {x : Fin 4 // x ∈ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m))
          * (∫ ω, (∏ _y : {y : Fin 4 // y ∉ ({0} : Finset (Fin 4))}, (inner ℝ f ω : ℝ))
              ∂(gaussianField G m)) := by
  rw [truncated_const_fin_four hm f]
  have hpos : 0 < (linVar G m f) ^ 2 := pow_pos (linVar_pos hm hf) 2
  linarith

/-! ## 6. Why the sharp exponent is not merely unproved there -/

/-- **AT `|S| = 1` THE CROSSING COUNT IS EXACTLY ONE, FOR EVERY PAIRING.**
`PairingParity.two_le_card_cross` gets `2 ≤ c` from `Even S.card` and `1 ≤ c` together, and
`PairingParity.card_cross_parity` says `c` has the parity of `|S|`. At `|S| = 1` that leaves
`c = 1` and no room: the single member of `S` is not fixed by `σ`, so its partner lies outside.
**So `ε²` is not reachable at an odd split by any sharpening of the same argument** — the
hypothesis `Even S.card` in `LatticeTruncatedSharp` is load-bearing, not decorative. -/
theorem card_cross_eq_one_of_card_eq_one {ι : Type*} [DecidableEq ι]
    {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) {S : Finset ι} (hS : S.card = 1) :
    (S.filter (fun i => σ i ∉ S)).card = 1 := by
  classical
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
  have hne : σ i ≠ i := hσ.2 i
  have hfil : ({i} : Finset ι).filter (fun j => σ j ∉ ({i} : Finset ι)) = {i} := by
    refine Finset.filter_true_of_mem fun j hj => ?_
    rw [Finset.mem_singleton] at hj
    subst hj
    simpa using hne
  rw [hfil, Finset.card_singleton]

end LatticeTruncatedOdd
