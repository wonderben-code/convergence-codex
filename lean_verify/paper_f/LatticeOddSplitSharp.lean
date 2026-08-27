import LatticeTruncatedOdd
import LatticeSplitFourCheck

/-!
# `Even S.card` cannot be dropped, and a claim the previous unit made about itself

`LatticeTruncatedOdd` corrected a sentence saying `LatticeTruncatedSharp`'s parity hypothesis costs
nothing, and left the strongest form of the correction **unproved and marked as unproved**:

> **What this does NOT claim.** It does not exhibit a graph where the sharp bound fails
> numerically. It shows the quantity is generally nonzero and that the crossing count that would
> force `ε²` is `1`. Turning that into a refuting instance needs a concrete `G`, `m` and separated
> test functions, and is not done here.

**It is done here, and it needs no separation and no particular graph.**
`abs_integral_prod_sub_mul_le_sq`'s conclusion is FALSE at `k = 4`, `S = {0}`,
`a = ![½g, g, g, g]` for any `g ≠ 0` on any finite graph at any `m ≠ 0` — with **every one of its
other hypotheses satisfied**, `hM0`, `hcross` and `hall` alike. The theorem below states them and
the negated conclusion together, so that a reader can see it is a counterexample and not a
mismatched instantiation.

The mechanism is the one `card_cross_eq_one_of_card_eq_one` predicted. At an odd split every
pairing crosses exactly once, so the truncated correlation is **linear** in the cross-propagator,
while the sharp bound is **quadratic** in it. Scaling one test function down drives the ratio
apart: the instance below fails by a factor of `2`, and `½` could be any `t ∈ (0,1)` with the
failure growing like `1/t`.

## And a correction to the previous unit's account of itself

That file said its generalisation of `LatticeOddVanishing.integral_prod_odd_eq_zero` off
`Fin (2n+1)` **"is what lets it reach a side of a split, which is a subtype and not a `Fin`"**.
**That overstates it.** A side of a split is a finite type of known cardinality, so
`Fintype.equivFinOfCardEq` transports the `Fin` statement onto it directly, and
`integral_prod_subtype_eq_zero_of_odd_via_fin` below does exactly that in four lines. **The
generalisation is shorter, not necessary**, and the two theorems are proved here to be
interchangeable rather than argued about. The overstatement is the same shape as the error that
unit was written to correct — a true observation with a conclusion drawn past it — which is why it
is fixed by proving the alternative rather than by rewording the sentence.

## What is proved

* `truncated_half_fin_four` — the value: `3/2 · (gᵀGg)²`, from `LatticeIsserlisFour.isserlis_four`
  and `LatticeTruncatedOdd.truncated_eq_full_of_odd`;
* **`sharp_needs_even_card`** — the hypotheses, and the negated conclusion, in one statement;
* **`sharp_without_even_card_is_false`** — the headline: that theorem with the one hypothesis
  deleted, and nothing else changed, does not hold;
* `sharp_with_even_card_holds` — the check. Putting the hypothesis back makes the same body an
  `exact` of `abs_integral_prod_sub_mul_le_sq`, so a transcription slip would not elaborate;
* `integral_prod_subtype_eq_zero_of_odd_via_fin` and
  `integral_prod_subtype_eq_zero_of_odd_two_ways` — the relabelling route, and the previous unit's
  theorem re-proved through it.

## What is still NOT claimed

**`truncated_abs_le_sq` is not weakened and does not need to be.** It carries `Even S.card`; this
file shows that hypothesis is necessary, which is a statement about the theorem's sharpness, not
about its correctness. Nothing here says anything about even splits. Finite volume throughout.
**No wall moves. No published tag moves.**
-/

namespace LatticeOddSplitSharp

open Equiv Function Involutions PairingSplit PairingCluster
open MeasureTheory ProbabilityTheory GraphLaplacian
open LatticeIsserlisSmeared LatticeIsserlisFour LatticeMoments LatticeSobolevPoincare
open LatticeSteinIdentity LatticeSplitFourCheck LatticeTruncatedOdd

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The value at the counterexample -/

/-- **THE TRUNCATED CORRELATION AT `![½g, g, g, g]`, SPLIT `{0}` AGAINST THE REST.**
`|S| = 1` is odd, so `LatticeTruncatedOdd.truncated_eq_full_of_odd` says the quantity is the full
four-point correlation, and `LatticeIsserlisFour.isserlis_four` evaluates that. All three pairings
of `Fin 4` contribute the same thing, because three of the four test functions are equal. -/
theorem truncated_half_fin_four (hm : m ≠ 0) (g : EuclideanSpace ℝ V) :
    ∫ ω, (∏ i, (inner ℝ (![(1/2 : ℝ) • g, g, g, g] i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0} : Finset (Fin 4))},
              (inner ℝ (![(1/2 : ℝ) • g, g, g, g] x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0} : Finset (Fin 4))},
              (inner ℝ (![(1/2 : ℝ) • g, g, g, g] y) ω : ℝ)) ∂(gaussianField G m))
      = 3 / 2 * (linVar G m g) ^ 2 := by
  have hodd : Odd (({0} : Finset (Fin 4)).card) := by
    rw [Finset.card_singleton]; exact odd_one
  rw [truncated_eq_full_of_odd hm ![(1/2 : ℝ) • g, g, g, g] hodd,
    show (fun ω => ∏ i, (inner ℝ (![(1/2 : ℝ) • g, g, g, g] i) ω : ℝ))
        = fun ω => (inner ℝ ((1/2 : ℝ) • g) ω : ℝ) * (inner ℝ g ω : ℝ) * (inner ℝ g ω : ℝ)
            * (inner ℝ g ω : ℝ) from
      funext fun ω => prod_fin_four ((1/2 : ℝ) • g) g g g ω,
    isserlis_four hm ((1/2 : ℝ) • g) g g g, dotG_smul_left, linVar_eq_dotG]
  ring

/-! ## 2. The hypothesis is necessary -/

/-- **`abs_integral_prod_sub_mul_le_sq` IS FALSE WITHOUT `Even S.card`, AND EVERY OTHER HYPOTHESIS
OF IT HOLDS HERE.** The four conjuncts are, in order, that theorem's `hM0`, its `hcross` at
`ε = |dotG (½g) g|`, its `hall` at `M = dotG g g`, and the negation of its conclusion. The split
is `{0}`, whose card is `1` — the one hypothesis missing.

**Where the factor of two comes from.** The quantity is `3/2 · c²` with `c = gᵀGg > 0`
(`truncated_half_fin_four`), while the bound is `3 · ((c/2)² · c⁰) = 3/4 · c²`. That gap is the
content of `card_cross_eq_one_of_card_eq_one`: at an odd split each pairing crosses **once**, so
the truncated correlation is linear in the cross-propagator while the bound is quadratic, and
scaling `½` down to `t` widens the failure like `1/t`.

**`LatticeSobolevPoincare.linVar_pos` is the only place the graph enters**, and all it needs is
that the Green form is positive definite — no connectivity, no separation, no particular `G`. -/
theorem sharp_needs_even_card (hm : m ≠ 0) {g : EuclideanSpace ℝ V} (hg : g ≠ 0) :
    (0 : ℝ) ≤ dotG G m g g
      ∧ (∀ i ∈ ({0} : Finset (Fin 4)), ∀ j ∉ ({0} : Finset (Fin 4)),
          |dotG G m (![(1/2 : ℝ) • g, g, g, g] i) (![(1/2 : ℝ) • g, g, g, g] j)|
            ≤ |dotG G m ((1/2 : ℝ) • g) g|)
      ∧ (∀ i j, |dotG G m (![(1/2 : ℝ) • g, g, g, g] i) (![(1/2 : ℝ) • g, g, g, g] j)|
            ≤ dotG G m g g)
      ∧ ¬ (|∫ ω, (∏ i, (inner ℝ (![(1/2 : ℝ) • g, g, g, g] i) ω : ℝ)) ∂(gaussianField G m)
              - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0} : Finset (Fin 4))},
                    (inner ℝ (![(1/2 : ℝ) • g, g, g, g] x) ω : ℝ)) ∂(gaussianField G m))
                * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0} : Finset (Fin 4))},
                    (inner ℝ (![(1/2 : ℝ) • g, g, g, g] y) ω : ℝ)) ∂(gaussianField G m))|
            ≤ (Fintype.card ↑(perfectMatchings (Fin 4)) : ℝ)
              * (|dotG G m ((1/2 : ℝ) • g) g| ^ 2
                  * (dotG G m g g) ^ (4 / 2 - 2))) := by
  have hc : (0 : ℝ) < dotG G m g g := linVar_eq_dotG (G := G) (m := m) g ▸ linVar_pos hm hg
  have hhalf : dotG G m ((1/2 : ℝ) • g) g = 1 / 2 * dotG G m g g := dotG_smul_left g g (1/2 : ℝ)
  have habs : |dotG G m ((1/2 : ℝ) • g) g| = 1 / 2 * dotG G m g g := by
    rw [hhalf, abs_of_pos]; linarith
  refine ⟨hc.le, ?_, ?_, ?_⟩
  · -- `hcross`: the only crossing pair is `½g` against `g`, whose value IS `ε`
    intro i hi j hj
    rw [Finset.mem_singleton] at hi
    subst hi
    fin_cases j <;> simp_all
  · -- `hall`: every entry is `t • g` with `0 < t ≤ 1`, so every value is at most `c`.
    -- Stated through the coefficient rather than by enumerating the sixteen pairs: after
    -- `fin_cases` the index sits under a beta-redex, `Matrix.cons_val_zero` does not fire, and
    -- a `simp` that reduces it is doing more work than the mathematics needs.
    have hentry : ∀ i : Fin 4, ∃ t : ℝ, 0 < t ∧ t ≤ 1
        ∧ ![(1/2 : ℝ) • g, g, g, g] i = t • g := by
      intro i
      fin_cases i
      · exact ⟨1/2, by norm_num, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, le_rfl, (one_smul ℝ g).symm⟩
      · exact ⟨1, by norm_num, le_rfl, (one_smul ℝ g).symm⟩
      · exact ⟨1, by norm_num, le_rfl, (one_smul ℝ g).symm⟩
    intro i j
    obtain ⟨s, hs0, hs1, hsi⟩ := hentry i
    obtain ⟨t, ht0, ht1, htj⟩ := hentry j
    rw [hsi, htj, dotG_smul_left, dotG_smul_right,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ s * (t * dotG G m g g))]
    calc s * (t * dotG G m g g) ≤ 1 * (1 * dotG G m g g) :=
          mul_le_mul hs1 (mul_le_mul ht1 le_rfl hc.le zero_le_one) (by positivity) zero_le_one
      _ = dotG G m g g := by ring
  · -- the conclusion: `3/2·c²` against `3·(c/2)² = 3/4·c²`
    rw [truncated_half_fin_four hm g, habs, card_perfectMatchings_fin_four, linVar_eq_dotG]
    have hsq : (0 : ℝ) < (dotG G m g g) ^ 2 := pow_pos hc 2
    rw [abs_of_pos (by linarith)]
    norm_num
    linarith

/-- **SO THE THEOREM WITH `Even S.card` DELETED IS FALSE.** The quantified body below is
`abs_integral_prod_sub_mul_le_sq`'s statement with that one hypothesis removed and nothing else
changed — same binders, same `ε` and `M`, same right-hand side — and it does not hold. This is the
headline: **the hypothesis is necessary, not merely convenient.** -/
theorem sharp_without_even_card_is_false (hm : m ≠ 0) {g : EuclideanSpace ℝ V} (hg : g ≠ 0) :
    ¬ (∀ {k : ℕ} (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) {ε M : ℝ}, 0 ≤ M →
        (∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε) →
        (∀ i j, |dotG G m (a i) (a j)| ≤ M) →
        |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
            - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
              * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
          ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) * (ε ^ 2 * M ^ (k / 2 - 2))) := by
  intro h
  obtain ⟨hM0, hcross, hall, hno⟩ := sharp_needs_even_card (G := G) hm hg
  exact hno (h (k := 4) ![(1/2 : ℝ) • g, g, g, g] ({0} : Finset (Fin 4)) hM0 hcross hall)

/-- **AND THE CHECK THAT THE PROPOSITION JUST REFUTED IS THE RIGHT ONE.** A statement transcribed
by hand can drift from the theorem it claims to be. Putting `Even S.card` back turns the body above
into something `abs_integral_prod_sub_mul_le_sq` proves **by `exact`, with no massaging** — so this
declaration does not elaborate if a binder, an exponent or a side of the inequality was copied
wrong. It is a declared duplicate of that theorem (`ERRATUM 176`), kept for the check and for
nothing else. -/
theorem sharp_with_even_card_holds (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    (S : Finset (Fin k)) (hS : Even S.card) {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hall : ∀ i j, |dotG G m (a i) (a j)| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) * (ε ^ 2 * M ^ (k / 2 - 2)) :=
  LatticeTruncatedSharp.abs_integral_prod_sub_mul_le_sq hm a S hS hM0 hcross hall

/-! ## 3. The relabelling route the previous unit said was not there -/

/-- **THE `Fin` STATEMENT REACHES A SIDE OF A SPLIT AFTER ALL.** A side of a split is a finite
type whose cardinality is known, so `Fintype.equivFinOfCardEq` carries
`LatticeOddVanishing.integral_prod_odd_eq_zero` onto it and `Equiv.prod_comp` moves the product
across. **This is written to refute `LatticeTruncatedOdd`'s own account of why its generalisation
was needed**, and it is four lines. -/
theorem integral_prod_subtype_eq_zero_of_odd_via_fin (hm : m ≠ 0) {k n : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) {S : Finset (Fin k)} (hS : S.card = 2 * n + 1) :
    ∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m) = 0 := by
  have hcard : Fintype.card {x : Fin k // x ∈ S} = 2 * n + 1 := by rw [Fintype.card_coe]; exact hS
  set e : {x : Fin k // x ∈ S} ≃ Fin (2 * n + 1) := Fintype.equivFinOfCardEq hcard with he
  rw [show (fun ω => ∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ))
      = fun ω => ∏ i : Fin (2 * n + 1), (inner ℝ (a (e.symm i)) ω : ℝ) from
    funext fun ω => (Equiv.prod_comp e.symm (fun x => (inner ℝ (a x) ω : ℝ))).symm]
  exact LatticeOddVanishing.integral_prod_odd_eq_zero hm n (fun i => a (e.symm i))

/-- **AND IT PROVES THE PREVIOUS UNIT'S THEOREM OUTRIGHT.** Byte-identical in statement to
`LatticeTruncatedOdd.integral_prod_subtype_eq_zero_of_odd`, declared as a duplicate on the estate's
`_two_ways` pattern (`ERRATUM 176`), and reached without the generalisation that theorem was said
to need. `Odd` unfolds to `∃ n, card = 2n + 1`, which is the relabelling's hypothesis exactly, so
there is nothing between the two but the equivalence. -/
theorem integral_prod_subtype_eq_zero_of_odd_two_ways (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) {S : Finset (Fin k)} (hS : Odd S.card) :
    ∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m) = 0 := by
  obtain ⟨n, hn⟩ := hS
  exact integral_prod_subtype_eq_zero_of_odd_via_fin hm a hn

end LatticeOddSplitSharp
