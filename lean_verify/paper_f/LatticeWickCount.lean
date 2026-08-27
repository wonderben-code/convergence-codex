import Involutions
import LatticeWickThree

/-!
# The Gaussian moment IS the number of pairings

`LatticeWickRecursion.wickCoeff k` is `(k−1)‼` on the evens and `0` on the odds, and
`moment_eq_wickCoeff` says `∫⟪f,ω⟫^k = c_k·(fᵀGf)^{k/2}` — every moment of a smeared lattice
field, in one equation with no parity case. `Involutions.perfectMatchings (Fin k)` is the set of
ways to pair `k` objects, and `card_perfectMatchings_fin_eq_doubleFactorial` says there are
`(2k−1)‼` of them at even size and none at odd.

**Those are the same number, and this file says so.** After it, the estate's moment formula reads
as what Wick's theorem actually asserts on the diagonal:

```
∫⟪f,ω⟫^k = (number of pairings of k objects) · (fᵀGf)^{k/2}
```

with the coefficient a **count** rather than a double factorial that happens to appear.

## Why this is worth a file

The `UNLOCK_WATCHLIST` item on general-order Isserlis was blocked on four things: no index type
for the pairings, no count for them, no Gaussian integration by parts against a general product,
and no map from a pairing to the propagator product its term carries. `Involutions` removed the
first two. **This removes nothing further — it JOINS them to the analysis**, which is a smaller
thing than removing a blocker and is worth doing because the two halves were built four files
apart and nothing connected them.

**What it is NOT.** It is the DIAGONAL: all `k` test functions equal. General-order Isserlis at
`k` distinct functions needs the map from a pairing to `∏⟨fᵢ,Gfⱼ⟩`, and that map is Wick's
theorem itself; it is not here and this file does not shorten it. The other blocker — Gaussian
integration by parts for the correlated field at a PRODUCT observable, which the estate has only
for the exponential (`LatticeSteinIdentity`) and for a power of one test function
(`LatticeWickRecursion`) — is untouched.

## What is proved

* **`wickCoeff_eq_card_perfectMatchings`** — `c_k = |perfectMatchings (Fin k)|`, both parities in
  one statement, off `card_perfectMatchings_fin_eq_doubleFactorial` and
  `card_perfectMatchings_fin_odd`;
* **`moment_eq_card_perfectMatchings`** — hence the moment formula with the count in it;
* `moment_six_eq_fifteen_pairings` — the case `k = 6`, where the `15` that
  `LatticeWickTwo.wick_two_order_six` reaches as `3 + 12` and
  `LatticeWickThree.wick_three_order_six` reaches as `3·3 + 6` is exhibited as the cardinality of
  a set of permutations. **Four routes to one number**, the fourth being `decide` in
  `Involutions`.

**No wall moves. No published tag moves.** Finite volume throughout.
-/

namespace LatticeWickCount

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared
open LatticeMomentsGeneral LatticeWickRecursion Involutions

/-- **THE COEFFICIENT IS A COUNT.** `wickCoeff k` was defined as `(k−1)‼` on the evens and `0` on
the odds, which is exactly the two branches of `|perfectMatchings (Fin k)|`. -/
theorem wickCoeff_eq_card_perfectMatchings (k : ℕ) :
    wickCoeff k = (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h2 : k = 2 * j := by omega
    subst h2
    rw [wickCoeff_even, card_perfectMatchings_fin_eq_doubleFactorial]
  · subst hj
    rw [wickCoeff_odd, card_perfectMatchings_fin_odd]
    norm_num

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **EVERY MOMENT OF A SMEARED LATTICE FIELD IS THE NUMBER OF PAIRINGS TIMES A POWER OF THE
PROPAGATOR**, which is what Wick's theorem says on the diagonal. No parity hypothesis: at odd `k`
there are no pairings and the count is `0`. -/
theorem moment_eq_card_perfectMatchings (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m)
      = (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ) * (linVar G m f) ^ (k / 2) := by
  rw [moment_eq_wickCoeff hm f k, wickCoeff_eq_card_perfectMatchings]

/-- `k = 6`: `∫⟪f,ω⟫⁶ = |perfectMatchings (Fin 6)|·(fᵀGf)³`, and the cardinality is `15`.

**Four routes to that number and no shared step between them:** `LatticeMomentsGeneral.moment_even`
by iterated derivatives of the generating functional; `LatticeWickTwo.wick_two_order_six` as
`3 + 12` by differentiating under an integral sign twice; `LatticeWickThree.wick_three_order_six`
as `3·3 + 6` by doing it three times; and `Involutions.card_perfectMatchings_fin_six` by `decide`
over the `720` permutations of a six-element set. -/
theorem moment_six_eq_fifteen_pairings (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 6 ∂(gaussianField G m)
      = (Fintype.card ↑(perfectMatchings (Fin 6)) : ℝ) * (linVar G m f) ^ 3 := by
  have h := moment_eq_card_perfectMatchings (G := G) hm f 6
  norm_num at h
  exact h

theorem card_perfectMatchings_fin_six_is_fifteen :
    Fintype.card ↑(perfectMatchings (Fin 6)) = 15 :=
  card_perfectMatchings_fin_six

end LatticeWickCount
