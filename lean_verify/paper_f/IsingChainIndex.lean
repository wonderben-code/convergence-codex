/-
  IsingChainIndex.lean — the chain's tower of sites, indexed by position, and glued to the walk.

  WHY. `IsingChainDecay.chain_expect` is stated over `chainSite`, a tower built by iterated
  `Option`:
  `chainSite V 0 = V` and `chainSite V (k+1) = Option (chainSite V k)`. `IsingWalkOrder.walkOrder`
  indexes the walk's sites by `Fin (m + 1)`. Neither knows about the other, and the records have
  named exactly this as what remains.

  * `chainEquivFin`: `chainSite (Fin 1) k ≃ Fin (k + 1)`, by recursion, through
    `Equiv.optionCongr` and `finSuccEquiv`.
  * `chainWalk`: composed with `walkOrder`, the tower's sites become the walk's.

  **THE ORIENTATION IS THE CONTENT, AND IT IS PINNED BY TWO THEOREMS RATHER THAN ASSERTED.** A
  cardinality bijection would be worthless twice over — once because a chain is a set of sites *in
  order*, and again because the two ends of this chain are not interchangeable. One end is the base,
  carrying whatever model the chain hangs off; the other is the site added last, whose correlation
  `chain_expect` computes. `chainEquivFin_lastSite` and `chainEquivFin_oldSite` say which is which:
  the site added last goes to `0` and the base goes to `Fin.last`, so through `walkOrder` the newest
  site is `γ 0` and the base is `γ m`. **That is the orientation the box needs and not the other
  one**: in `IsingPathComparison` the walk runs from an interior site to the boundary, the field
  sits at the boundary end, and it is the interior site's correlation that is wanted — so the base
  must be `γ m` and the computed end `γ 0`.

  WHAT REMAINS. This carries the *sites* across, not the *energy*. Exhibiting the walk's model as a
  `chainE` — the recursively built energy `chain_expect` actually consumes — is the next step; it is
  **not attempted here** and its cost is not claimed (`ERRATUM 246`). Nor is `Fin 1` argued to be
  the right base: it is the choice that makes the tower's cardinality `m + 1`, and a base carrying
  more sites is a different statement.

  **No wall moves and nothing here is a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingWalkOrder
import IsingIsolatedSite

namespace IsingChainIndex

open IsingFiniteVolume IsingChainDecay IsingWalkOrder IsingBoxRegion

/-- The tower `chainSite (Fin 1) k`, indexed by position. The site added last is `0`; each older
site is one higher; the base is `Fin.last`. -/
def chainEquivFin : (k : ℕ) → chainSite (Fin 1) k ≃ Fin (k + 1)
  | 0 => Equiv.refl (Fin 1)
  | k + 1 => (Equiv.optionCongr (chainEquivFin k)).trans (finSuccEquiv (k + 1)).symm

/-- **THE CHAIN STRUCTURE IN ONE LINE: ADDING A SITE SHIFTS EVERY EXISTING INDEX UP BY ONE.**
Both endpoint theorems below are instances of this and of `chainEquivFin_none`. It is stated
separately because it, not they, is what an identification of the *energy* will use: it says
consecutive levels of the tower are consecutive positions along the walk, which is the whole
difference between a chain and an unordered set of sites. -/
theorem chainEquivFin_some (k : ℕ) (x : chainSite (Fin 1) k) :
    chainEquivFin (k + 1) (some x) = (chainEquivFin k x).succ := by
  simp [chainEquivFin, Equiv.optionCongr]

/-- And the newly added site takes index `0`. -/
theorem chainEquivFin_none (k : ℕ) :
    chainEquivFin (k + 1) (none : chainSite (Fin 1) (k + 1)) = 0 := by
  simp [chainEquivFin, Equiv.optionCongr]

/-- **THE SITE ADDED LAST IS INDEX `0`.** This is the end whose correlation `chain_expect`
computes. -/
theorem chainEquivFin_lastSite : ∀ k : ℕ, chainEquivFin k (lastSite (Fin 1) 0 k) = 0
  | 0 => rfl
  | k + 1 => chainEquivFin_none k

/-- **THE BASE IS INDEX `Fin.last`.** This is the end the chain hangs off, carrying the model whose
correlation `chain_expect` multiplies by `tanh J ^ k`. -/
theorem chainEquivFin_oldSite :
    ∀ k : ℕ, chainEquivFin k (IsingIsolatedSite.oldSite (Fin 1) 0 k) = Fin.last k
  | 0 => rfl
  | k + 1 => by
    rw [IsingIsolatedSite.oldSite, chainEquivFin_some, chainEquivFin_oldSite k, Fin.succ_last]

variable {n : ℕ}

/-- The chain's sites, read as the walk's sites, in the walk's order. -/
noncomputable def chainWalk (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    chainSite (Fin 1) m ≃ {v // v ∈ walkSites γ m} :=
  (chainEquivFin m).trans (walkOrder γ m hinj)

/-- **THE COMPUTED END OF THE CHAIN IS THE WALK'S STARTING SITE** — in the box, the interior site
whose correlation is wanted. -/
theorem chainWalk_lastSite (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    (chainWalk γ m hinj (lastSite (Fin 1) 0 m)).val = γ 0 := by
  rw [chainWalk, Equiv.trans_apply, chainEquivFin_lastSite, walkOrder_apply]
  simp

/-- **THE BASE OF THE CHAIN IS THE WALK'S LAST SITE** — in the box, the boundary site that carries
the field. -/
theorem chainWalk_oldSite (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    (chainWalk γ m hinj (IsingIsolatedSite.oldSite (Fin 1) 0 m)).val = γ m := by
  rw [chainWalk, Equiv.trans_apply, chainEquivFin_oldSite, walkOrder_apply]
  rfl

end IsingChainIndex
