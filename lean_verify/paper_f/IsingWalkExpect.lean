/-
  IsingWalkExpect.lean — the comparison model's magnetisation, evaluated.

  `IsingWalkIsChain` proved the box's walk model **is** a chain as an energy. That made the chain
  theorems applicable; this file applies them. The two sums over configurations — the partition
  function and the numerator — are carried across the same matching the energy was, and
  `IsingChainDecay.chain_expect` then computes the ratio.

  `box_walk_expect`: the magnetisation of the comparison model at the walk's starting site is
  **exactly** `tanh β ^ m` times the base model's correlation, where `m` is the walk's length.

  **THIS IS AN EQUALITY AND IT IS THE ARM'S ANSWER, NOT ITS SUCCESS.** `tanh β < 1` for every real
  `β`, so the right-hand side decays geometrically in the walk's length — and
  `IsingChainRouteCeiling.chain_route_insufficient` proves that a route decaying in `depth` cannot
  deliver the magnetisation bound this arm was opened for. **The arm therefore does not close the
  wall, and this file is where that becomes a computation rather than an expectation.** What it does
  give, through `IsingPathComparison.pathCoup_le_integral`, is a genuine lower bound on the box at
  every site — a weak one, decaying with distance to the boundary, but proved.

  WHAT IS LEFT SYMBOLIC, AND DELIBERATELY. The base model here is a single site carrying field
  `β * h`, and its correlation is written `baseNum / basePart` rather than evaluated to
  `tanh (β * h)`. That evaluation is a separate small statement; it is **not attempted here** and
  its cost is not claimed (`ERRATUM 246`). Nothing above depends on it — the decay, and hence the
  arm's fate, is settled by the `tanh β ^ m` factor alone.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingWalkIsChain

namespace IsingWalkExpect

open Finset Real
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingPathComparison
open IsingBoxRegion IsingWalkOrder IsingChainIndex IsingChainClosedForm IsingWalkChainEnergy
open IsingChainDecay IsingPendantSite IsingGriffithsMono IsingWalkIsChain

variable {n : ℕ}

/-- Precomposing configurations with an equivalence of sites permutes the sum.

**THE REGION IS WRITTEN AS A PREDICATE AND NOT AS A `Finset` COERCION, AND THAT IS NOT COSMETIC.**
`{v // v ∈ walkSites γ m}` and `{v // Q v}` are the same type, but Lean equips them with *different*
`Fintype` instances — `Finset.Subtype.fintype` for the first, `Subtype.fintype` for the second — and
`IsingRegionSplit.partL` sums using the second. Stating this lemma over a bare `Finset` made every
later `rw` fail on an instance mismatch that no amount of `apply` or `convert` would see through.
Taking the predicate as a variable puts the instance under this lemma's own binder, where it agrees
with `partL`'s by construction. -/
theorem sum_over_region {Q : Site n → Prop} [DecidablePred Q] {A : Type*} [Fintype A]
    [DecidableEq A] (e : A ≃ {v // Q v}) (F : (A → Bool) → ℝ) :
    ∑ b : {v // Q v} → Bool, F (fun x => b (e x)) = ∑ a : A → Bool, F a :=
  Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
    (fun b => F (fun x => b (e x))) (fun a => F a) (fun _ => rfl)

/-- The chain's base model: a single site carrying the boundary field. -/
abbrev baseE (β h : ℝ) : (Fin 1 → Bool) → ℝ := fun τ => β * h * IsingTransfer2D.spin (τ 0)

theorem siteAt_zero_eq_lastSite (m : ℕ) : siteAt m 0 = lastSite (Fin 1) 0 m := by
  rw [siteAt, Equiv.symm_apply_eq, chainEquivFin_lastSite]

section
variable (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
  (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
  (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
  (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)

include hadj hinj hbnd hoff in
theorem partL_eq :
    IsingRegionSplit.partL (fun v => v ∈ walkSites γ m) (boxSet n)
        (pathCoup n β h (walkBonds γ m)) (Pin γ m)
      = basePart (chainE (baseE β h) β (0 : Fin 1) m) := by
  rw [IsingRegionSplit.partL, basePart,
      ← sum_over_region (Q := fun v => v ∈ walkSites γ m) (chainWalk γ m hinj)
        (fun σ => exp (chainE (baseE β h) β (0 : Fin 1) m σ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [eL_walk_eq_chainE β h γ m hadj hinj hbnd hoff a]

include hadj hinj hbnd hoff in
theorem numL_eq :
    IsingRegionSplit.numL (fun v => v ∈ walkSites γ m) (boxSet n)
        (pathCoup n β h (walkBonds γ m)) (Pin γ m) {γ 0}
      = baseNum (chainE (baseE β h) β (0 : Fin 1) m) (lastSite (Fin 1) 0 m) := by
  rw [IsingRegionSplit.numL, baseNum,
      ← sum_over_region (Q := fun v => v ∈ walkSites γ m) (chainWalk γ m hinj)
        (fun σ => IsingTransfer2D.spin (σ (lastSite (Fin 1) 0 m))
          * exp (chainE (baseE β h) β (0 : Fin 1) m σ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hg : IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ 0)
      = a (walkOrder γ m hinj 0) := glue_eq γ m hinj a 0
  rw [Finset.prod_singleton, hg, ← chainWalk_siteAt γ m hinj 0, siteAt_zero_eq_lastSite,
      eL_walk_eq_chainE β h γ m hadj hinj hbnd hoff a]

include hadj hinj hbnd hoff in
/-- **THE COMPARISON MODEL'S MAGNETISATION, EXACTLY.** `tanh β ^ m` times the base correlation.
An equality, not a bound — and since `tanh β < 1`, a **decaying** one. -/
theorem box_walk_expect :
    num (boxSet n) (pathCoup n β h (walkBonds γ m)) {γ 0}
        / part (boxSet n) (pathCoup n β h (walkBonds γ m))
      = tanh β ^ m * (baseNum (baseE β h) (0 : Fin 1)
          / basePart (baseE β h)) := by
  have hA : ∀ v ∈ ({γ 0} : Finset (Site n)), v ∈ walkSites γ m := by
    intro v hv
    rw [Finset.mem_singleton.mp hv]
    exact mem_walkSites γ m 0 (by omega)
  rw [IsingRegionSplit.expect_eq_left (boxSet n) (pathCoup n β h (walkBonds γ m)) (Pin γ m)
        (fun _ hi => hi) (fun i hi hz => (pathCoup_pure_of_live β h γ m i hz).resolve_left hi)
        {γ 0} hA,
      numL_eq β h γ m hadj hinj hbnd hoff, partL_eq β h γ m hadj hinj hbnd hoff, chain_expect]

end

end IsingWalkExpect
