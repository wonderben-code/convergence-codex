/-
  IsingWalkOrder.lean — the walk's sites, counted and indexed **in the walk's own order**.

  WHY THIS FILE EXISTS, AND IT IS NOT THE REASON THE LAST UNIT GAVE. `IsingWalkEnergy`'s header and
  every record written with it said the next step was a missing injectivity clause on
  `IsingBoxWalk.exists_boundary_walk`. **That was false.** Injectivity is the theorem's fourth
  clause, its docstring calls the walk *self-avoiding* in its first line, and the docstring names
  clause four as "what makes it a path rather than a walk". I asserted the absence from memory
  instead of reading a statement I had written two units earlier (`ERRATUM 258`). The correction is
  recorded where the claim was made; this file is the fold-back, and it is a fold-back by **using**
  the clause rather than by softening what was said.

  * `card_walkSites`: a self-avoiding walk of `m` steps visits exactly `m + 1` sites.
  * `walkOrder`: the equivalence `Fin (m + 1) ≃ {v // v ∈ walkSites γ m}` given by `i ↦ γ i`.

  **THE SECOND IS THE POINT AND THE FIRST IS ONLY ITS INPUT.** Mathlib's `Finset.equivFin` already
  supplies *some* bijection from a finite set to `Fin` of its cardinality, and it is useless here: a
  chain is not a set of sites but a set of sites **in order**, and an arbitrary relabelling destroys
  exactly the structure `IsingChainDecay.chain_expect` consumes. The equivalence proved here is the
  one that sends the index `i` to the site the walk stands on at step `i`, so adjacency in `Fin` is
  adjacency along the walk.

  WHAT REMAINS. `chain_expect` is stated over `IsingChainDecay.chainSite`, a tower built by iterated
  `Option`, not over `Fin`. Relating `Fin (m + 1)` to that tower, and then exhibiting the walk's
  energy as a `chainE`, is the next step; it is **not attempted here** and its cost is not claimed
  (`ERRATUM 246`). **No wall moves and nothing here is a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingBoxRegion

namespace IsingWalkOrder

open Finset
open IsingFiniteVolume IsingBoxRegion

variable {n : ℕ}

/-- **A SELF-AVOIDING WALK OF `m` STEPS VISITS EXACTLY `m + 1` SITES.** The hypothesis is
`IsingBoxWalk.exists_boundary_walk`'s fourth clause verbatim. -/
theorem card_walkSites (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    (walkSites γ m).card = m + 1 := by
  rw [walkSites, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hinj i (by have := Finset.mem_range.mp (Finset.mem_coe.mp hi); omega)
    j (by have := Finset.mem_range.mp (Finset.mem_coe.mp hj); omega) hij

theorem exists_index (γ : ℕ → Site n) (m : ℕ) {v : Site n} (hv : v ∈ walkSites γ m) :
    ∃ i : Fin (m + 1), γ i.val = v := by
  rw [walkSites] at hv
  obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hv
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hgi⟩

/-- **THE WALK'S SITES, INDEXED IN THE WALK'S OWN ORDER.** `Finset.equivFin` would give *some*
bijection and it would be useless: a chain is a set of sites **in order**, and an arbitrary
relabelling destroys precisely the structure the chain theorems consume. This one sends step `i` to
the site the walk stands on at step `i`, so consecutive indices are consecutive sites. -/
noncomputable def walkOrder (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    Fin (m + 1) ≃ {v // v ∈ walkSites γ m} :=
  Equiv.ofBijective
    (fun i => ⟨γ i.val, mem_walkSites γ m i.val (by omega)⟩)
    ⟨fun i j h => Fin.ext (hinj i.val (by omega) j.val (by omega) (congrArg Subtype.val h)),
     fun v => by
       obtain ⟨i, hi⟩ := exists_index γ m v.property
       exact ⟨i, Subtype.ext hi⟩⟩

theorem walkOrder_apply (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) (i : Fin (m + 1)) :
    (walkOrder γ m hinj i).val = γ i.val := rfl

end IsingWalkOrder
