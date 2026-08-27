import LatticeTruncatedDecay
import LatticeIsserlisFour

/-!
# The split chain, checked at four test functions against a formula that does not use it

The eight files from `PairingSplit` to `LatticeTruncatedDecay` each carry a check of their own,
and each of those checks is local: it tests the file against the file below it, or against an
enumeration. **None of them tests the whole chain against a number computed without it.** This
file does, at the one order where the estate has an independent formula.

`LatticeIsserlisFour.isserlis_four` computes `∫⟪A,ω⟫⟪B,ω⟫⟪C,ω⟫⟪D,ω⟫` by **polarising a fourth
moment twice** — no pairings, no involutions, no split, no relabelling, no Isserlis at general
order. Set the four cross-propagators to zero and it collapses to `⟨A,GB⟩·⟨C,GD⟩`.
`PairingRelabel.integral_prod_split` reaches the same integral through all eight files. **They
must agree, and a sign, an index or an orientation wrong anywhere in the chain would break it.**

## What is proved

* `prod_fin_four`, `prod_lower_two`, `prod_upper_two` — the three products written out. Bookkeeping,
  separated so the theorem below is about the two routes rather than about `Finset` manipulation;
* `split_four_via_chain` — the chain's answer: the correlation is the product of the two pairs';
* `split_four_via_isserlis` — the independent answer: `⟨A,GB⟩·⟨C,GD⟩`, by polarisation;
* **`split_four_agrees`** — **the check**: the two are the same number.

## What is NOT here

Any order but four, because the estate has an independent formula at no other order — which is the
honest reason and not a choice. At six the only route to the left-hand side is the ladder this
chain is built on, so a comparison there would be the chain against itself. **Not costed**
(`ERRATUM 194`).
-/

namespace LatticeSplitFourCheck

open Equiv Function Involutions PairingSplit
open MeasureTheory ProbabilityTheory GraphLaplacian
open LatticeIsserlisSmeared LatticeIsserlisFour WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The three products -/

omit [DecidableEq V] in
theorem prod_fin_four (A B C D : EuclideanSpace ℝ V) (ω : EuclideanSpace ℝ V) :
    (∏ i : Fin 4, (inner ℝ (![A, B, C, D] i) ω : ℝ))
      = (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) * (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ) := by
  simp [Fin.prod_univ_four]

omit [DecidableEq V] in
theorem prod_lower_two (A B C D : EuclideanSpace ℝ V) (ω : EuclideanSpace ℝ V) :
    (∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![A, B, C, D] x) ω : ℝ))
      = (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) := by
  rw [Finset.prod_coe_sort ({0, 1} : Finset (Fin 4))
    (fun i => (inner ℝ (![A, B, C, D] i) ω : ℝ))]
  rw [show ({0, 1} : Finset (Fin 4)) = {0, 1} from rfl, Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp

omit [DecidableEq V] in
theorem prod_upper_two (A B C D : EuclideanSpace ℝ V) (ω : EuclideanSpace ℝ V) :
    (∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![A, B, C, D] y) ω : ℝ))
      = (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ) := by
  -- `Finset.prod_subtype` goes straight from a `Finset` to the subtype of a PREDICATE, which is
  -- what the split's complement side is; going via `↥Sᶜ` puts a second `Fintype` instance on the
  -- same type and `rw` will not see through it.
  rw [← Finset.prod_subtype ({2, 3} : Finset (Fin 4))
    (p := fun y : Fin 4 => y ∉ ({0, 1} : Finset (Fin 4))) (by decide)
    (fun i => (inner ℝ (![A, B, C, D] i) ω : ℝ))]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  simp

/-! ## 2. The two routes -/

/-- **ROUTE 1: THE CHAIN.** Eight files, from a pairing that crosses a split to this. -/
theorem split_four_via_chain (hm : m ≠ 0) (A B C D : EuclideanSpace ℝ V)
    (hAC : dotG G m A C = 0) (hAD : dotG G m A D = 0)
    (hBC : dotG G m B C = 0) (hBD : dotG G m B D = 0) :
    ∫ ω, (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) * (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ)
        ∂(gaussianField G m)
      = (∫ ω, (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) ∂(gaussianField G m))
        * (∫ ω, (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ) ∂(gaussianField G m)) := by
  have hzero : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)),
      dotG G m (![A, B, C, D] i) (![A, B, C, D] j) = 0 := by
    intro i hi j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have h := PairingRelabel.integral_prod_split hm ![A, B, C, D] ({0, 1} : Finset (Fin 4)) hzero
  simp only [prod_fin_four, prod_lower_two, prod_upper_two] at h
  exact h

/-- **ROUTE 2: POLARISATION.** `isserlis_four` opens the fourth moment twice and mentions no
pairing, no involution, no split and no relabelling. -/
theorem split_four_via_isserlis (hm : m ≠ 0) (A B C D : EuclideanSpace ℝ V)
    (hAC : dotG G m A C = 0) (hAD : dotG G m A D = 0)
    (hBC : dotG G m B C = 0) (hBD : dotG G m B D = 0) :
    ∫ ω, (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) * (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ)
        ∂(gaussianField G m)
      = dotG G m A B * dotG G m C D := by
  rw [isserlis_four hm A B C D, hAC, hAD, hBC, hBD]
  ring

/-! ## 3. The check -/

/-- **THE CHECK.** The chain's answer and polarisation's answer are the same number. Every file
from `PairingSplit` to `PairingRelabel` is on one side of this equation and none of them is on the
other. -/
theorem split_four_agrees (hm : m ≠ 0) (A B C D : EuclideanSpace ℝ V)
    (hAC : dotG G m A C = 0) (hAD : dotG G m A D = 0)
    (hBC : dotG G m B C = 0) (hBD : dotG G m B D = 0) :
    (∫ ω, (inner ℝ A ω : ℝ) * (inner ℝ B ω : ℝ) ∂(gaussianField G m))
        * (∫ ω, (inner ℝ C ω : ℝ) * (inner ℝ D ω : ℝ) ∂(gaussianField G m))
      = dotG G m A B * dotG G m C D := by
  rw [← split_four_via_chain hm A B C D hAC hAD hBC hBD]
  exact split_four_via_isserlis hm A B C D hAC hAD hBC hBD

end LatticeSplitFourCheck
