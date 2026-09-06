import FieldSimpleConnected

/-!
# The involution theorem is strictly weaker than the hypothesis it came from

`FieldSimpleAut.graphAut_involutive` proves a fact about **graphs** from a fact about the
**measure**: if the propagator's spectrum is simple, every automorphism of the graph is an
involution. `FieldSimpleConnected` then noticed that both known failing families — disconnected
graphs and periodic lattices — carry an automorphism of order three or more, and filed the obvious
question: **is the involution condition the characterisation, or only a consequence?** It filed the
question with the reason it is probably only a consequence. It is only a consequence, and two
vertices settle it.

## What is proved

**`perm_involutive_two`, `graphAut_involutive_two`** — on two vertices there are two permutations
and both are involutions, so **every automorphism of every graph on two vertices is an
involution**, for no reason having to do with any spectrum. One `decide +kernel`.

**`not_finrank_le_one_bot_two`** — and the two vertices with no edge between them fail the
hypothesis maximally: their Laplacian is `0`, so the eigenspace at `0` is the whole plane
(`FieldLaplacianInstance.not_finrank_le_one_of_no_adj`).

**`not_equiv_graphAut_involutive`** — **so the converse is false.** The conclusion of
`graphAut_involutive` holds on this graph and its hypothesis fails, in the Laplacian form; and
**`not_eigenvalues_injective_bot_two`** says the same on the propagator side at every non-zero
mass. The involution theorem is a **consequence** of a simple spectrum and does not characterise
it.

## What is NOT here

**THE CONNECTED CASE IS NOT SETTLED AS OF 2026-09-06, AND IT IS THE ONE WORTH SETTLING.** This
witness is
disconnected, and `FieldSimpleConnected.preconnected_of_finrank_le_one` already showed a
disconnected graph fails the hypothesis — so the counterexample fails for a reason that was known
an hour ago, and what it adds is only that **the involution condition does not see that reason**.
The natural repair — *connected, and every automorphism an involution* — is **untouched**. Settling
it needs the spectrum of a connected graph whose automorphisms are all involutions; the estate's
`AsymmetricGraph.asymGraph` is the natural candidate, since an asymmetric graph satisfies the
involution condition vacuously, and **as of 2026-09-06 nothing anywhere in this estate computes
its spectrum** (counted, not assumed — `ERRATUM 450`: `AsymmetricGraph.lean` contains the word
*eigenvalue* **zero** times, and no file other than this one mentions both `asymGraph` and an
eigenvalue). Not attempted, no cost claimed (`ERRATUM 246`).

**NO NEW FAILING FAMILY.** The scoreboard is unchanged: the path graph satisfies the hypothesis;
disconnected graphs and periodic lattices fail it. This file adds a **witness**, not a family, and
the witness is inside a family already recorded.

**THE IMPLICATION IS NOT SHOWN VACUOUS EITHER, AND IS NOT** —
`FieldSimpleAut.graphAut_involutive_line` reaches the involution conclusion on the path graph
through a genuinely simple spectrum, so `graphAut_involutive` has a non-trivial instance. **This
file does not weaken it; it bounds it.**

**NOTHING ABOUT `Fintype.card V ≤ 2` IN GENERAL.** `graphAut_involutive_two` is stated at `Fin 2`
and proved by exhaustion. Transporting it along an equivalence to any two-element type is routine
and **is not done in this file**, because nothing needs it.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **one of the six** takes a non-zero mass,
`not_eigenvalues_injective_bot_two`, and only because `green` is defined as an inverse. Everything
else takes **no mass, no propagator and no hypothesis at all** — `perm_involutive_two` and
`graphAut_involutive_two` do not even mention a Laplacian.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldInvolutionConverse

open Matrix GraphLaplacian FieldAutInvariance

/-! ## 1. On two vertices every permutation is an involution -/

theorem perm_involutive_two (θ : Fin 2 ≃ Fin 2) (p : Fin 2) : θ (θ p) = p := by
  revert p
  revert θ
  decide +kernel

/-! ## 2. So every automorphism of any graph on two vertices is an involution -/

theorem graphAut_involutive_two (G : SimpleGraph (Fin 2)) {θ : Fin 2 ≃ Fin 2}
    (_ : IsGraphAut G θ) (p : Fin 2) : θ (θ p) = p :=
  perm_involutive_two θ p

/-! ## 3. And the edgeless graph on two vertices fails the hypothesis -/

theorem no_adj_bot (i j : Fin 2) : ¬ (⊥ : SimpleGraph (Fin 2)).Adj i j := fun h => h.elim

theorem not_finrank_le_one_bot_two :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :=
  FieldLaplacianInstance.not_finrank_le_one_of_no_adj no_adj_bot (by simp)

/-! ## 4. So the converse of `FieldSimpleAut.graphAut_involutive` is false -/

/-- **THE INVOLUTION THEOREM IS STRICTLY WEAKER THAN THE HYPOTHESIS IT WAS PROVED FROM.**
`FieldSimpleAut.graphAut_involutive` sends a simple spectrum to *every graph automorphism is an
involution*; the two vertices with no edge between them satisfy the conclusion and fail every form
of the hypothesis. -/
theorem not_equiv_graphAut_involutive :
    (∀ θ : Fin 2 ≃ Fin 2, IsGraphAut (⊥ : SimpleGraph (Fin 2)) θ → ∀ p, θ (θ p) = p)
      ∧ ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :=
  ⟨fun _ hθ => graphAut_involutive_two _ hθ, not_finrank_le_one_bot_two⟩

/-- And on the propagator side, at every non-zero mass. -/
theorem not_eigenvalues_injective_bot_two {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green (⊥ : SimpleGraph (Fin 2)) mass).IsHermitian) :
    ¬ Function.Injective hH.eigenvalues :=
  FieldSimpleConverse.not_eigenvalues_injective_of_no_adj hmass hH no_adj_bot (by simp)

end FieldInvolutionConverse
