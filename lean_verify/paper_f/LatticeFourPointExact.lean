import LatticeFourPointViaGeneral

/-!
# The connected four-point function, summed over the pairings that cross

Every file on this line since `PairingCluster` has bounded the truncated correlation. But
`PairingCluster.integral_prod_sub_mul_eq` is an **equality** — the truncated correlation *is* the
sum over the pairings that cross the split, with no hypothesis on the propagator at all — and at
four test functions that sum can be evaluated rather than estimated.

`LatticeFourPointViaGeneral`'s record named this as the thing not done, and said why it was worth
doing: **it is a check on the VALUE rather than on a bound.** Two bounds agreeing is no evidence
either is right; two computations of the same number, sharing nothing, is.

## What is proved

* `crossing_pairs_fin_four` — the one decidable fact the evaluation needs: **every** pairing of
  `Fin 4` that crosses `{0, 1}` sends `0` and `1` into `{2, 3}` and keeps exactly `{0, 1}` as its
  representatives. Proved by `decide` over the permutation group, with no arithmetic in it;
* **`sum_crossing_fin_four`** — the sum over the crossing pairings equals `2·(f·Gg)²`. No integral
  appears in it: each of the two pairings contributes `(f·Gg)²`, and
  **`LatticeTruncatedCount.crossing_card_fin_four` supplies the `2`**;
* **`connected_smeared_two_ways`** — so the truncated correlation at `![f, f, g, g]` and
  `S = {0, 1}` equals `2·(f·Gg)²`, reached through sixteen files. **Its statement is
  byte-identical to `LatticeIsserlisSmeared.connected_smeared`, deliberately**, and it is named on
  the estate's `_two_ways` pattern so a duplicate-statement grep finds a declared reason rather
  than an accident;
* **`connected_four_agrees`** — **THE CHECK, and it is `PairingCluster.integral_prod_sub_mul_eq` at
  this instance PROVED WITHOUT IT.** One side is evaluated combinatorially, the other by
  `LatticeIsserlisSmeared.connected_smeared`, which polarises a fourth moment and mentions no
  pairing, no involution, no split and no relabelling. **The central identity of the whole line is
  re-derived by a route that shares nothing with it.**

**This is where the `2` finally does work.** In `LatticeTruncatedCount` it was a constant in a
bound and could have been any upper estimate; here it is the number of terms in a sum whose value
is being computed, and a wrong count would give a wrong number.

## What is NOT here

**Any order but four**, and for the reason `LatticeSplitFourCheck` recorded: the estate has an
independent formula at no other order, so a comparison at six would be the chain against itself.

**And the norms**, which remain the one difference between the general clustering estimate and
`LatticeFourPointClustering.connected_smeared_le`. Nothing in this file touches them — it is about
an exact value, and that difference lives in the bounds.
-/

namespace LatticeFourPointExact

open Equiv Function Involutions PairingSplit PairingCluster
open LatticeTruncatedCount LatticeSplitFourCheck
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. What a crossing pairing of four objects looks like

One `decide`, over the permutation group and nothing else. It is stated as a conjunction rather
than as two lemmas because both halves are read at the same moment in the evaluation below. -/

/-- **EVERY PAIRING OF `Fin 4` THAT CROSSES `{0, 1}` HAS THE SAME SHAPE.** Its representatives are
exactly `{0, 1}`, and it sends `0` and `1` into `{2, 3}`. There are two such pairings and they
differ only in which of `2, 3` receives which. -/
theorem crossing_pairs_fin_four (σ : ↑(perfectMatchings (Fin 4)))
    (hσ : ¬ RespectsSplit ({0, 1} : Finset (Fin 4)) σ.1) :
    Finset.univ.filter (fun i => i < σ.1 i) = {0, 1}
      ∧ ((σ.1 0 = 2 ∧ σ.1 1 = 3) ∨ (σ.1 0 = 3 ∧ σ.1 1 = 2)) := by
  revert hσ
  revert σ
  decide

/-! ## 2. The sum, evaluated

No integral appears in this section. The sum over the crossing pairings is a finite sum of products
of propagators, and `crossing_pairs_fin_four` is enough to evaluate it. -/

/-- **THE SUM OVER THE CROSSING PAIRINGS.** Each of the two contributes `(f·Gg)²`, and
`LatticeTruncatedCount.crossing_card_fin_four` supplies the `2`. **This is where that count finally
does work**: in `LatticeTruncatedCount` it was a constant in a bound and any over-estimate would
have done; here it is the number of terms in a sum whose value is being computed, and a wrong count
gives a wrong number. -/
theorem sum_crossing_fin_four (f g : EuclideanSpace ℝ V) :
    (∑ σ ∈ Finset.univ.filter
        (fun σ : ↑(perfectMatchings (Fin 4)) => ¬ RespectsSplit ({0, 1} : Finset (Fin 4)) σ.1),
      ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
        dotG G m (![f, f, g, g] i) (![f, f, g, g] (σ.1 i)))
      = 2 * (dotG G m f g) ^ 2 := by
  classical
  have hterm : ∀ σ ∈ Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin 4)) => ¬ RespectsSplit ({0, 1} : Finset (Fin 4)) σ.1),
      (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
        dotG G m (![f, f, g, g] i) (![f, f, g, g] (σ.1 i))) = (dotG G m f g) ^ 2 := by
    intro σ hmem
    obtain ⟨hrep, hval⟩ := crossing_pairs_fin_four σ (Finset.mem_filter.mp hmem).2
    rw [hrep, Finset.prod_insert (by decide), Finset.prod_singleton]
    rcases hval with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> simp [sq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, crossing_card_fin_four, nsmul_eq_mul]
  norm_num

/-! ## 3. The chain's answer -/

/-- **THE TRUNCATED FOUR-POINT CORRELATION, THROUGH SIXTEEN FILES.**
`PairingCluster.integral_prod_sub_mul_eq` says it IS the sum over the crossing pairings — an
equality, with no hypothesis on the propagator — and §2 evaluates that sum.

**THIS STATEMENT IS BYTE-IDENTICAL TO `LatticeIsserlisSmeared.connected_smeared` AND THAT IS THE
POINT.** It is kept, and named on the estate's `_two_ways` pattern —
`Involutions.card_involutions_fin_six_two_ways` and its sibling — so that a duplicate-statement
grep finds a declared reason here rather than an accident. What differs is the route: that one
polarises a fourth moment, this one comes through every file from `PairingSplit`. -/
theorem connected_smeared_two_ways (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      = 2 * (dotG G m f g) ^ 2 := by
  classical
  have h := integral_prod_sub_mul_eq (G := G) (m := m) hm ![f, f, g, g]
    ({0, 1} : Finset (Fin 4))
  rw [show (fun ω => ∏ i : Fin 4, (inner ℝ (![f, f, g, g] i) ω : ℝ))
      = fun ω => (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_fin_four f f g g ω]; ring,
    show (fun ω => ∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] x) ω : ℝ)) = fun ω => (inner ℝ f ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_lower_two f f g g ω]; ring,
    show (fun ω => ∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] y) ω : ℝ)) = fun ω => (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_upper_two f f g g ω]; ring] at h
  rw [h, sum_crossing_fin_four f g]

/-! ## 4. The check

**The statement below is `PairingCluster.integral_prod_sub_mul_eq` at this one instance, and its
proof does not use it.** The left-hand side is evaluated combinatorially by §2; the right-hand side
is evaluated by `LatticeIsserlisSmeared.connected_smeared`, which polarises a fourth moment and
mentions no pairing, no involution, no split and no relabelling. **So the central identity of the
whole line is re-derived here by a route that shares nothing with it.** A sign, an index, an
orientation or a miscount anywhere in `PairingSplit` through `PairingCluster` would break it. -/

/-- **THE CHECK.** The sum over the crossing pairings and the truncated correlation are the same
number, established without `integral_prod_sub_mul_eq`. -/
theorem connected_four_agrees (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    (∑ σ ∈ Finset.univ.filter
        (fun σ : ↑(perfectMatchings (Fin 4)) => ¬ RespectsSplit ({0, 1} : Finset (Fin 4)) σ.1),
      ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
        dotG G m (![f, f, g, g] i) (![f, f, g, g] (σ.1 i)))
      = (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)) := by
  rw [sum_crossing_fin_four f g, connected_smeared hm f g]

end LatticeFourPointExact
