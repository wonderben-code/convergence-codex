/-
  IsingSupportModel.lean — a model's correlations depend only on the interaction terms whose
  coupling is nonzero. This is the step the previous unit's records named as the residue.

  WHY, PRECISELY. `IsingSumModel` proved that a model presented over an index type `I₁ ⊕ I₂`, with
  each term's sites inside one part, has the first model's correlations. The box's comparison model
  is **not** presented that way and the reason is sharp: `IsingPathComparison.pathCoup` **zeroes**
  the coupling of every bond outside the chosen set rather than removing the index. Read off its
  definition, the model keeping a walk's bonds has

  * `Sum.inl (p, q) ↦ β` when `(p, q)` is one of the walk's bonds and `0` otherwise, and
  * `Sum.inr p ↦ β * h` when `p` is a boundary site and `0` otherwise.

  **The terms that survive are already pure**: a walk bond joins two walk sites, and a field term
  touches one site. It is exactly the **zeroed** bonds — every non-walk pair of the box — whose site
  sets straddle the walk and its complement. So the obstruction is not the sum's shape, which
  `IsingSumModel` fixed, and not the couplings, which are already right; it is that the index type
  still carries terms that contribute nothing. This file removes them.

  `expect_subtype`: for any predicate `P` on the index type with `J i = 0` off `P`, the model
  restricted to `{i // P i}` has **the same** partition function, the same numerators and hence the
  same correlations. Nothing is approximated and no hypothesis relates `P` to the sites.

  WHAT REMAINS, AND IT IS NOT THIS. Composing this with `IsingSumModel.expect_sum` at the box needs
  the box's **sites** exhibited as a disjoint union — walk sites and the rest — and the restricted
  index type exhibited as a disjoint union matching it. `Equiv.sumCompl` supplies the first and
  `IsingModelSplit.expect_congr` transports along it; assembling them is **not attempted here** and
  its cost is not claimed (`ERRATUM 246`).

  **No wall moves. Nothing here is a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingSumModel

namespace IsingSupportModel

open Finset Real
open IsingTransfer2D IsingGriffithsMono

variable {V : Type*} [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]
variable {P : I → Prop} [DecidablePred P]

omit [Fintype V] [DecidableEq V] in
/-- **THE ONE COMPUTATION.** Terms with zero coupling contribute nothing, so the energy of the
restricted model is the energy of the whole one — not close to it, equal to it. -/
theorem energy_subtype (S : I → Finset V) (J : I → ℝ) (h0 : ∀ i, ¬ P i → J i = 0)
    (σ : V → Bool) :
    ∑ i : {i // P i}, J i.val * ∏ v ∈ S i.val, spin (σ v)
      = ∑ i : I, J i * ∏ v ∈ S i, spin (σ v) := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (fun x => by simp)
        (fun i => J i * ∏ v ∈ S i, spin (σ v))]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro x _ hx
  rw [h0 x (by simpa using hx), zero_mul]

theorem part_subtype (S : I → Finset V) (J : I → ℝ) (h0 : ∀ i, ¬ P i → J i = 0) :
    part (fun i : {i // P i} => S i.val) (fun i => J i.val) = part S J :=
  Finset.sum_congr rfl fun σ _ => by rw [energy_subtype S J h0 σ]

theorem num_subtype (S : I → Finset V) (J : I → ℝ) (h0 : ∀ i, ¬ P i → J i = 0) (A : Finset V) :
    num (fun i : {i // P i} => S i.val) (fun i => J i.val) A = num S J A :=
  Finset.sum_congr rfl fun σ _ => by rw [energy_subtype S J h0 σ]

/-- **DROPPING THE TERMS THAT CONTRIBUTE NOTHING CHANGES NO CORRELATION.** No hypothesis relates the
predicate to the sites: the site sets of the discarded terms may be anything at all, and in the
intended application they are exactly the pairs whose two ends lie on opposite sides of the
split. -/
theorem expect_subtype (S : I → Finset V) (J : I → ℝ) (h0 : ∀ i, ¬ P i → J i = 0) (A : Finset V) :
    num (fun i : {i // P i} => S i.val) (fun i => J i.val) A
        / part (fun i : {i // P i} => S i.val) (fun i => J i.val)
      = num S J A / part S J := by
  rw [part_subtype S J h0, num_subtype S J h0]

/-- The intended instance, stated so that the predicate is not chosen by hand: **restricting to the
indices whose coupling is nonzero is always legitimate.** -/
theorem expect_support (S : I → Finset V) (J : I → ℝ) [DecidablePred fun i => J i ≠ 0]
    (A : Finset V) :
    num (fun i : {i // J i ≠ 0} => S i.val) (fun i => J i.val) A
        / part (fun i : {i // J i ≠ 0} => S i.val) (fun i => J i.val)
      = num S J A / part S J :=
  expect_subtype S J (fun _ hi => not_not.mp hi) A

/-! ## 2. Relabelling the sites, in this idiom

The review of §1 found an asymmetry in the toolkit rather than a defect in it, and this section is
the fold-back. `IsingSumModel.expect_congr_index` relabels the **index** type of a `part`/`num`
model, and `IsingModelSplit.expect_congr` relabels **sites** — but only in the bare-energy idiom,
where a model is a function of the configuration. Nothing relabelled the sites of a `part`/`num`
model, which is the form every theorem in this chain is stated in. The composition the box will
need runs through exactly that, so it is proved here.
-/

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem part_congr_site (e : V ≃ W) (S : I → Finset W) (J : I → ℝ) :
    part (fun i => (S i).map e.symm.toEmbedding) J = part S J := by
  simp only [part]
  rw [← IsingModelSplit.sum_relabel e
        (fun υ : W → Bool => exp (∑ i : I, J i * ∏ w ∈ S i, spin (υ w)))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.prod_map]; rfl

theorem num_congr_site (e : V ≃ W) (S : I → Finset W) (J : I → ℝ) (A : Finset W) :
    num (fun i => (S i).map e.symm.toEmbedding) J (A.map e.symm.toEmbedding) = num S J A := by
  simp only [num]
  rw [← IsingModelSplit.sum_relabel e
        (fun υ : W → Bool =>
          (∏ w ∈ A, spin (υ w)) * exp (∑ i : I, J i * ∏ w ∈ S i, spin (υ w)))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_map]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.prod_map]; rfl

/-- **RELABELLING THE SITES OF A `part`/`num` MODEL CHANGES NO CORRELATION.** With
`IsingSumModel.expect_congr_index` this completes the pair: a model is an index type and a site
type, and each may now be moved independently, in the idiom the rest of the chain uses. -/
theorem expect_congr_site (e : V ≃ W) (S : I → Finset W) (J : I → ℝ) (A : Finset W) :
    num (fun i => (S i).map e.symm.toEmbedding) J (A.map e.symm.toEmbedding)
        / part (fun i => (S i).map e.symm.toEmbedding) J
      = num S J A / part S J := by
  rw [part_congr_site, num_congr_site]

end IsingSupportModel
