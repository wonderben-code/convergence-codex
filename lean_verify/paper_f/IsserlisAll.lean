import LadderStep
import WickPairings

/-!
# General-order Isserlis

`WickPairings.IsserlisGeneral G m k` is the statement

```
∀ f : Fin k → EuclideanSpace ℝ V,
  ∫ ω, ∏ᵢ⟪fᵢ,ω⟫ ∂μ = ∑_{σ ∈ perfectMatchings (Fin k)} pairProduct f σ,
```

and it has stood open at even `k ≥ 6` since it was written down. `LadderStep.ladder` proves the
ladder at **every** order:

```
∫ ω, ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ ∂μ = steinSum a f · exp(½⟨f,Gf⟩).
```

**`IsserlisGeneral` is that at `f = 0`.** The exponential becomes `1` on both sides; every
fixed-point factor becomes `⟨0, G aᵢ⟩ = 0`; so a term survives exactly when its involution has no
fixed point — which for an involution is exactly being a perfect matching — and what survives is
its pair product, which is `pairProduct`.

## What is proved

* `steinSum_zero` — at `f = 0` the closed form is the pairing sum: the fixed-point factors kill
  every involution that fixes anything, and `Involutions.perfectMatchings` is by definition the
  involutions that fix nothing;
* **`isserlisGeneral_all`** — `WickPairings.IsserlisGeneral G m k` at **every** `k`.

## What this settles, and what the earlier cases are now for

**It settles the theorem.** What it does not do is make the earlier cases redundant, and the
reason is worth stating precisely, because it is easy to overstate.

**Lean accepting this proof is what establishes that the theorem is proved.** The five earlier
instances — `WickPairings.isserlisGeneral_zero`, `_two`, `_four`, `isserlisGeneral_diagonal`, and
`LatticeOddVanishing.isserlisGeneral_odd` — cannot add to that; they are the same propositions, so
no contradiction between them and this is possible in a consistent logic. **What they establish is
that the STATEMENT is the right one.** `isserlisGeneral_two` was checked term for term against
`LatticeIsserlisFour.isserlis_four`, which comes from polarising a fourth moment; the diagonal case
against `LatticeWickCount.moment_eq_card_perfectMatchings`; the odd case against a symmetry
argument. A `Prop` that had the wrong coefficient, or ranged over the wrong index set, would have
failed those. So the chain is: **the statement was validated against independent computations, and
this proves the validated statement.**

**AND THE INTEGRAL IS A REAL ONE.** `LatticeSteinMajorant.integrable_prod_inner` proves the
integrand integrable at every order. Without it, `∫` would be `0` by convention wherever this
was not otherwise known, and the statement would not have been about an integral at all
(`ERRATUM 295`, written this morning for exactly this reason).
-/

namespace IsserlisAll

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open Equiv Function Involutions PairWeightRep SteinSumRecursion
open LatticeSteinLadder LadderStep WickPairings
open LatticeMoments LatticeIsserlisSmeared LatticeSteinIdentity

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- At `f = 0` every fixed-point factor is `⟨0, G aᵢ⟩ = 0`, so an involution contributes exactly
when it fixes nothing — and an involution that fixes nothing is a perfect matching. What it
contributes is its pair product, which is `WickPairings.pairProduct`. -/
theorem steinSum_zero {n : ℕ} (a : Fin n → EuclideanSpace ℝ V) :
    steinSum G m a 0 = ∑ σ : ↑(perfectMatchings (Fin n)), pairProduct G m a σ.1 := by
  classical
  have hfix : ∀ i : Fin n, fixW G m a 0 i = 0 := by
    intro i; simp [fixW, dotG]
  -- both sides as sums over filtered Finsets of permutations
  have hL : steinSum G m a 0
      = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ involutions (Fin n)),
          (∏ i ∈ Finset.univ.filter (fun i => i < σ i), pairW G m a i (σ i))
            * ∏ i ∈ Finset.univ.filter (fun i => σ i = i), fixW G m a 0 i := by
    rw [steinSum]
    exact (Finset.sum_subtype (F := Subtype.fintype _) _ (by simp)
      (fun τ : Equiv.Perm (Fin n) =>
        (∏ i ∈ Finset.univ.filter (fun i => i < τ i), pairW G m a i (τ i))
          * ∏ i ∈ Finset.univ.filter (fun i => τ i = i), fixW G m a 0 i)).symm
  have hR : (∑ σ : ↑(perfectMatchings (Fin n)), pairProduct G m a σ.1)
      = ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ perfectMatchings (Fin n)),
          pairProduct G m a σ := by
    exact (Finset.sum_subtype (F := Subtype.fintype _) _ (by simp)
      (fun τ : Equiv.Perm (Fin n) => pairProduct G m a τ)).symm
  rw [hL, hR]
  have hsub : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ perfectMatchings (Fin n))
      ⊆ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ involutions (Fin n)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact hσ.1
  have hzero : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ involutions (Fin n)),
      σ ∉ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ ∈ perfectMatchings (Fin n)) →
      (∏ i ∈ Finset.univ.filter (fun i => i < σ i), pairW G m a i (σ i))
        * ∏ i ∈ Finset.univ.filter (fun i => σ i = i), fixW G m a 0 i = 0 := by
    intro σ hσ hno
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ hno
    have hmv : ¬ (∀ x, σ x ≠ x) := fun h => hno ⟨hσ, h⟩
    push Not at hmv
    obtain ⟨x, hx⟩ := hmv
    have hxmem : x ∈ Finset.univ.filter (fun i => σ i = i) := by simp [hx]
    rw [Finset.prod_eq_zero hxmem (hfix x), mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  have hemp : (Finset.univ.filter (fun i => σ i = i)) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun i _ => ?_
    exact hσ.2 i
  rw [hemp, Finset.prod_empty, mul_one, pairProduct]
  rfl

/-- **GENERAL-ORDER ISSERLIS, AT EVERY ORDER.** `LadderStep.ladder` at `f = 0`. -/
theorem isserlisGeneral_all (hm : m ≠ 0) (k : ℕ) : IsserlisGeneral G m k := by
  intro a
  have h := ladder (G := G) hm k a 0
  have hv : linVar G m (0 : EuclideanSpace ℝ V) = 0 := by simp [linVar]
  simp only [inner_zero_left, Real.exp_zero, mul_one, hv, zero_div] at h
  rw [h, steinSum_zero]

/-! ## The cases that validated the statement, now derived from it

Each of these was proved before this file existed, by a route sharing no step with the ladder, and
each was checked against an independent computation at the time. They are restated here as
consequences so that a reader can see the general theorem covers them. -/

/-- Four test functions — the case `WickPairings.isserlisGeneral_two` checked term for term
against `LatticeIsserlisFour.isserlis_four`. -/
theorem isserlisGeneral_four_of_all (hm : m ≠ 0) : IsserlisGeneral G m 4 :=
  isserlisGeneral_all hm 4

/-- Every odd order — the case `LatticeOddVanishing.isserlisGeneral_odd` proved by the symmetry
`ω ↦ −ω`. -/
theorem isserlisGeneral_odd_of_all (hm : m ≠ 0) (n : ℕ) : IsserlisGeneral G m (2 * n + 1) :=
  isserlisGeneral_all hm (2 * n + 1)

/-- **AND THE CASE THAT WAS OPEN.** Even order at least six was the first `k` no route reached;
`k = 6` is now an instance like any other. -/
theorem isserlisGeneral_six (hm : m ≠ 0) : IsserlisGeneral G m 6 :=
  isserlisGeneral_all hm 6

end IsserlisAll
