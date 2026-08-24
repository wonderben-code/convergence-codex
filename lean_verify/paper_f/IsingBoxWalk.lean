/-
  IsingBoxWalk.lean — from every site of the box there is a self-avoiding walk to the boundary of
  exactly its own depth, and it is a straight line.

  WHY. This is the step `WALLS §W3.6` and `SPINE`'s 24 August addendum both name as the last one on
  the Griffiths-comparison arm: *"for each site, a path to the boundary of its own depth."*
  Everything else is in place — the pair computed, the one-bond rule at full generality, the fading
  along a path, the count of how few sites lie near the boundary, the ceiling that count gives, and
  the transport that lets the box's other sites be ignored. **This file supplies the geometry those
  need and nothing else.**

  WHAT IS PROVED. `exists_boundary_walk`: for every `p`, a function `γ : ℕ → Site n` with `γ 0 = p`,
  `isBoundary (γ (depth n p))`, `adj (γ k) (γ (k+1))` at every `k < depth n p`, and `γ` injective on
  `{0, …, depth n p}`. **The walk is a straight line** — `depth` is a minimum of four coordinate
  distances, and whichever attains it names the direction to walk in.

  WHY THE FOURTH CLAUSE IS THERE AND IS NOT DECORATION. The first three make `γ` a *walk*; a walk
  may revisit a site, and one that did would not present `depth n p` distinct bonds to compare
  against. The Griffiths comparison this is for needs a *path*, so injectivity is part of the
  statement rather than a remark about the construction. It is free here — each case moves one
  coordinate strictly one way — but it is free only because the construction was chosen to be
  straight, and a statement that did not record it would have to be re-proved by whoever used it.

  TWO CHOICES THAT KEEP THE PROOF SHORT, BOTH DELIBERATE.

  * The walk is a function on **all** of `ℕ`, not on `Fin (depth + 1)`. Only its first
    `depth n p + 1` values are constrained, and taking the domain to be `ℕ` removes every `Fin`
    index manipulation from the statement and from all four cases.
  * The two **outward** cases move by `min k (n - 1 - p.i.val)` rather than clamping the
    destination with `min _ (n - 1)`. The two agree wherever the walk is constrained, but this form
    is `p.i.val + 0` at `k = 0` — closed by the same `simp` as the inward cases — whereas the clamp
    is `min p.i.val (n - 1)` there, which is `p.i.val` only by way of `h1`. Putting the `min` on the
    step rather than on the position is what keeps all four base cases identical.

  WHAT THIS IS NOT. It is geometry of the box: no model, no coupling, no correlation. Assembling it
  with the rest — a comparison model whose bonds are the walk's, with couplings below the box's,
  and Griffiths' second inequality to compare — is the remaining work, and it is **not attempted
  here** (`ERRATUM 246`). **No wall moves.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingChainRouteCeiling

namespace IsingBoxWalk

open Finset
open IsingFiniteVolume IsingBoundaryField IsingChainRouteCeiling

/-- **FROM EVERY SITE THERE IS A STRAIGHT SELF-AVOIDING WALK TO THE BOUNDARY OF EXACTLY ITS OWN
DEPTH.** The fourth clause is what makes it a path rather than a walk. -/
theorem exists_boundary_walk (n : ℕ) (p : Site n) :
    ∃ γ : ℕ → Site n, γ 0 = p ∧ isBoundary (γ (depth n p)) = true ∧
      (∀ k, k < depth n p → adj (γ k) (γ (k + 1))) ∧
      (∀ i ≤ depth n p, ∀ j ≤ depth n p, γ i = γ j → i = j) := by
  have h1 : p.1.val < n := p.1.isLt
  have h2 : p.2.val < n := p.2.isLt
  have hd : depth n p = min (min p.1.val (n - 1 - p.1.val)) (min p.2.val (n - 1 - p.2.val)) := rfl
  -- which of the four coordinate distances attains the minimum
  rcases (by omega : depth n p = p.1.val ∨ depth n p = n - 1 - p.1.val ∨
      depth n p = p.2.val ∨ depth n p = n - 1 - p.2.val) with hA | hB | hC | hD
  · -- inward along the first coordinate
    refine ⟨fun k => (⟨p.1.val - k, by omega⟩, p.2), ?_, ?_, ?_, ?_⟩
    · simp
    · simp only [isBoundary, decide_eq_true_eq]
      left
      omega
    · intro k hk
      right
      refine ⟨rfl, Or.inr ?_⟩
      simp only []
      omega
    · intro i hi j hj hij
      simp only [Prod.mk.injEq, Fin.mk.injEq, and_true] at hij
      omega
  · -- outward along the first coordinate
    refine ⟨fun k => (⟨p.1.val + min k (n - 1 - p.1.val), by omega⟩, p.2), ?_, ?_, ?_, ?_⟩
    · simp
    · simp only [isBoundary, decide_eq_true_eq]
      right; left
      omega
    · intro k hk
      right
      refine ⟨rfl, Or.inl ?_⟩
      simp only []
      omega
    · intro i hi j hj hij
      simp only [Prod.mk.injEq, Fin.mk.injEq, and_true] at hij
      omega
  · -- inward along the second coordinate
    refine ⟨fun k => (p.1, ⟨p.2.val - k, by omega⟩), ?_, ?_, ?_, ?_⟩
    · simp
    · simp only [isBoundary, decide_eq_true_eq]
      right; right; left
      omega
    · intro k hk
      left
      refine ⟨rfl, Or.inr ?_⟩
      simp only []
      omega
    · intro i hi j hj hij
      simp only [Prod.mk.injEq, Fin.mk.injEq, true_and] at hij
      omega
  · -- outward along the second coordinate
    refine ⟨fun k => (p.1, ⟨p.2.val + min k (n - 1 - p.2.val), by omega⟩), ?_, ?_, ?_, ?_⟩
    · simp
    · simp only [isBoundary, decide_eq_true_eq]
      right; right; right
      omega
    · intro k hk
      left
      refine ⟨rfl, Or.inl ?_⟩
      simp only []
      omega
    · intro i hi j hj hij
      simp only [Prod.mk.injEq, Fin.mk.injEq, true_and] at hij
      omega

end IsingBoxWalk
