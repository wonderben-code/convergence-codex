import CrossBlockStructure
import IndefiniteCoupling

/-!
# `K₂,₂` is not strict, at every nonzero mass — the two-by-two computation, done

`UNLOCK_WATCHLIST`'s reach-kernel item names its own smallest open instance and then says
plainly that nobody has run it:

> `IndefiniteCoupling.bipGraph` is the obvious first target, one block of size two, where the
> question is whether some nonzero `v` supported on `{0,1}` with `v 0 + v 1 = 0` has
> `(massive *ᵥ v) p = 0` at both `p = 2` and `p = 3`. **That is a two-by-two computation and it
> is NOT DONE HERE.**
>
> LIKELY OUTCOME: strictness or non-strictness of `K₂,₂` at every nonzero mass, decided; and
> either way a first data point on whether block cuts of size `> 1` behave differently from the
> singleton case.

**It is done here, and the answer is that the kernel is not trivial.** `v = (1, −1, 0, 0)`
works, at every mass, for a reason that is visible rather than computational: in `K₂,₂` the sites
`2` and `3` are each joined to **both** of `0` and `1`, so the two `−1` entries of `massive` in
those rows meet `1` and `−1` and cancel. The mass never enters, because it sits only on the
diagonal and `v` vanishes at `2` and `3`.

## What follows

`CrossBlockStructure.strict_iff_reachKernel_trivial` says the reflected form is strict exactly
when the reach kernel is trivial, and `IndefiniteCoupling` has already supplied this graph's
`hcross` (`hcross_bip`, from the all-ones cross-adjacency being positive semidefinite) and its
`IsMirrorHalf` and `IsRefl`. So **`not_strict_bip`: `K₂,₂` with the half `{0,1}` is not strict, at
every nonzero mass.**

## The data point the item asked for, stated exactly

`IndefiniteCoupling`'s point is that this graph satisfies `hcross` **without** the cross-adjacency
being diagonal (`cross_not_diagonal`) — the estate's witness that the diagonal route is
sufficient and not necessary. **This file adds that the same graph is not strict.** So one graph
now carries both: the coupling condition holds, by a route the diagonal criterion cannot see, and
strictness fails.

**What this does NOT say, and the first draft of this header said it.** That draft wrote that
"the singleton intuition does not carry over", which presumes the singleton case is strict.
**That comparison is not made here and is not free.** The estate's positive strictness results —
`SmallSideStrict.reflectionPositive_box_one_strict'`, `..._lattice_one_strict`,
`StrictCriterion.reflectionPositive_box_two_strict` and their torus twins — are about the **width
of the side**, on boxes, tori and the lattice, and carry hypotheses this graph is not tested
against. Comparing them to a cross-adjacency block of size two means checking that, and nothing
here does.

Also not said: it is one graph. Nothing decides whether block cuts of size `> 1` are ever
strict, and nothing bounds how large the reach kernel can be — `ReachKernelDimension` is where
that lives. **A witness settles an instance.**
-/

namespace BipReachKernel

open IndefiniteCoupling StrictBiconditional GraphReflection GraphLaplacian
open scoped Matrix

/-- The witness: `+1` at site `0`, `−1` at site `1`, zero on the other side of the cut. -/
def kerVec : Fin 4 → ℝ := fun p => if p = 0 then 1 else if p = 1 then -1 else 0

theorem kerVec_ne_zero : kerVec ≠ 0 := by
  intro h
  have h0 : kerVec 0 = (0 : Fin 4 → ℝ) 0 := by rw [h]
  simp [kerVec] at h0

/-- `kerVec` vanishes off the half. -/
theorem kerVec_two : kerVec (2 : Fin 4) = 0 := by
  simp [kerVec, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]

theorem kerVec_three : kerVec (3 : Fin 4) = 0 := by
  simp [kerVec, show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide]

/-- The row at site `2`: the operator's two `−1` entries meet `1` and `−1`, and the diagonal
entry — the only place the mass appears — is multiplied by `kerVec 2 = 0`. -/
theorem mulVec_two (m : ℝ) : (massive bipGraph m *ᵥ kerVec) (2 : Fin 4) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, massive_apply, kerVec]
  norm_num [show ¬ bipGraph.Adj 2 2 by decide, show bipGraph.Adj 2 0 by decide,
    show bipGraph.Adj 2 1 by decide, show ¬ bipGraph.Adj 2 3 by decide,
    show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (2 : Fin 4) ≠ 3 by decide, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 1 by decide]

/-- The row at site `3`, identically. -/
theorem mulVec_three (m : ℝ) : (massive bipGraph m *ᵥ kerVec) (3 : Fin 4) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, massive_apply, kerVec]
  norm_num [show ¬ bipGraph.Adj 3 3 by decide, show bipGraph.Adj 3 0 by decide,
    show bipGraph.Adj 3 1 by decide, show ¬ bipGraph.Adj 3 2 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (2 : Fin 4) ≠ 1 by decide]

/-- **THE COMPUTATION THE ITEM ASKED FOR.** `v = (1, −1, 0, 0)` is in the reach kernel of
`K₂,₂` at **every** mass: it is supported on `{0,1}`, and at each of `2` and `3` the operator's
two `−1` entries meet `1` and `−1`. -/
theorem kerVec_mem (m : ℝ) : InReachKernel bipGraph m Hh (∅ : Finset (Fin 4)) kerVec := by
  classical
  constructor
  · intro p hp
    fin_cases p
    · exact absurd (by decide : (0 : Fin 4) ∈ Hh) hp
    · exact absurd (by decide : (1 : Fin 4) ∈ Hh) hp
    · exact kerVec_two
    · exact kerVec_three
  · intro p hp _
    fin_cases p
    · exact absurd (by decide : (0 : Fin 4) ∈ Hh) hp
    · exact absurd (by decide : (1 : Fin 4) ∈ Hh) hp
    · exact mulVec_two m
    · exact mulVec_three m

/-- **THE REACH KERNEL OF `K₂,₂` IS NOT TRIVIAL**, at every mass. -/
theorem reachKernel_nontrivial (m : ℝ) :
    ¬ (∀ v : Fin 4 → ℝ, InReachKernel bipGraph m Hh (∅ : Finset (Fin 4)) v → v = 0) := by
  intro h
  exact kerVec_ne_zero (h kerVec (kerVec_mem m))

/-- **`K₂,₂` IS NOT STRICT, AT EVERY NONZERO MASS.**

The item that asked for the computation asked for exactly this verdict, and this is the answer
it did not predict either way. Through `CrossBlockStructure.strict_iff_reachKernel_trivial`,
with this graph's `hcross` supplied by `IndefiniteCoupling.hcross_bip`. -/
theorem not_strict_bip {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm bipGraph m rho c) := by
  intro hstrict
  refine reachKernel_nontrivial m ?_
  exact (CrossBlockStructure.strict_iff_reachKernel_trivial isMirrorHalf_Hh isRefl_rho_bip hm
    (hcross_bip m)).mp hstrict

end BipReachKernel
