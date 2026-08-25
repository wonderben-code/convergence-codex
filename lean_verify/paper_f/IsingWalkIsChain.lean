/-
  IsingWalkIsChain.lean — **the box's walk model is a chain.** Not comparable to one, not bounded by
  one: equal to one, as an energy, term for term.

  WHAT THIS COMPLETES. `IsingWalkChainEnergy.eL_walk` wrote the box's region energy as a field at
  `γ m` plus a bond on each step. `IsingChainClosedForm.chainE_field` wrote the chain's energy as a
  field at the base plus a bond on each consecutive pair. `IsingChainIndex.chainWalk` matched the
  sites, **in order and with the ends the right way round**. This file puts the three together:
  carry a configuration of the walk's sites along `chainWalk` and the two sums are the same sum.

  **WHAT IS AND IS NOT ESTABLISHED, SAID PRECISELY BECAUSE THE ARM'S POINT IS A BOUND AND THIS IS
  NOT ONE.** This is an identity between two energies. It says the object the chain theorems talk
  about is the object the box's comparison model presents — which is what makes those theorems
  *applicable*, and nothing more. `IsingChainDecay.chain_expect` still has to be applied, and its
  conclusion is a **decaying** quantity, `tanh J ^ m` times a base correlation; the route ceiling
  already proved (`IsingChainRouteCeiling.chain_route_insufficient`) says a decaying route cannot
  produce the magnetisation bound this arm was opened to reach. **So no wall moves here and none is
  about to**: what this closes is the question *"is the comparison model a chain?"*, which was open
  and is now answered yes, not the question of whether the arm succeeds.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingWalkChainEnergy

namespace IsingWalkIsChain

open Finset Real
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingPathComparison
open IsingBoxRegion IsingWalkOrder IsingChainIndex IsingChainClosedForm IsingWalkChainEnergy
open IsingChainDecay

variable {n : ℕ}

/-- Reading a tower position through `chainWalk` is reading it through `walkOrder`. -/
theorem chainWalk_siteAt (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) (j : Fin (m + 1)) :
    chainWalk γ m hinj (siteAt m j) = walkOrder γ m hinj j := by
  rw [chainWalk, Equiv.trans_apply, siteAt, Equiv.apply_symm_apply]

/-- The box configuration built from a walk configuration agrees with it on the walk. -/
theorem glue_eq (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
    (a : {v // v ∈ walkSites γ m} → Bool) (i : Fin (m + 1)) :
    IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ i.val) = a (walkOrder γ m hinj i) := by
  rw [IsingRegionSplit.glue_pos (mem_walkSites γ m i.val (by omega))]
  rfl

/-- **THE BOX'S WALK MODEL IS A CHAIN.** Its region energy is exactly `IsingChainDecay.chainE` with
bond strength `β` and a field `β * h` at the base. Both sides are energies of the same finite
system; **nothing is estimated and no wall moves.** -/
theorem eL_walk_eq_chainE (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
    (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)
    (a : {v // v ∈ walkSites γ m} → Bool) :
    IsingRegionSplit.eL (boxSet n) (pathCoup n β h (walkBonds γ m)) (Pin γ m) a
      = chainE (fun τ => β * h * IsingTransfer2D.spin (τ 0)) β 0 m
          (fun x => a (chainWalk γ m hinj x)) := by
  rw [eL_walk β h γ m hadj hinj hbnd hoff a, chainE_field,
      ← Fin.sum_univ_eq_sum_range
        (fun j => IsingTransfer2D.spin (IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ j))
          * IsingTransfer2D.spin
              (IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ (j + 1)))) m]
  congr 1
  · have hL : IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ m)
        = a (walkOrder γ m hinj (Fin.last m)) := glue_eq γ m hinj a (Fin.last m)
    rw [hL, ← chainWalk_siteAt γ m hinj (Fin.last m)]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ j.val)
        = a (walkOrder γ m hinj j.castSucc) := glue_eq γ m hinj a j.castSucc
    have h2 : IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ (j.val + 1))
        = a (walkOrder γ m hinj j.succ) := glue_eq γ m hinj a j.succ
    rw [h1, h2, ← chainWalk_siteAt γ m hinj j.castSucc, ← chainWalk_siteAt γ m hinj j.succ]

end IsingWalkIsChain
