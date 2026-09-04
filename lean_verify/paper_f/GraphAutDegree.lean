import FieldAutInvariance
import GraphReflection

/-!
# Degree is an automorphism invariant — the hypothesis `IsRefl.degree` did not need

`GraphReflection.IsRefl.degree` proves `G.degree (θ p) = G.degree p`, and it is stated for
`IsRefl`, a structure that **bundles involutivity**: `invol : Function.Involutive θ`. Its proof uses
that field twice.

**Degree preservation does not need it.** For any adjacency-preserving bijection, the neighbours of
`θ p` are the image under `θ` of the neighbours of `p`, and `θ.symm` supplies what involutivity was
being used for.

**And the gap is exactly the one `FieldAutInvariance` exists to close, left open one lemma down.**
That file was written because *"`GraphReflection.IsRefl` carries `invol` as a structure FIELD, so
before `FieldAutInvariance` no non-involutive map could be handed to any of this wall's machinery at
all"*, and `TorusTranslation`, `CycleRotationAut` and `TorusSiteTransitive` exist to exhibit
non-involutive automorphisms. **So the estate has non-involutive automorphisms and could not say
their degree is preserved.**

## What is proved

**`IsGraphAut.neighborFinset_image`** — `G.neighborFinset (θ p) = (G.neighborFinset p).image θ`,
from `Adj (θ p) u ↔ Adj p (θ.symm u)` and nothing else.

**`IsGraphAut.degree`** — `G.degree (θ p) = G.degree p`, no involutivity. `IsRefl.degree` is the
involutive case; it is **not superseded and not edited** (`ERRATUM 337`, `ERRATUM 94`), and with
`IsGraphAut.of_isRefl` it is now derivable from this one, which is recorded beside it rather than
acted on.

**`IsGraphAut.degree_class_image`** — an automorphism permutes each degree class: the image of
`{v | G.degree v = d}` is itself. This is the shape every *"the automorphism group is small"*
argument starts from.

**`IsGraphAut.eq_of_degree_unique`** — if a vertex is the only one of its degree, every automorphism
fixes it. That is the first rung of an asymmetry argument, and the reason this file exists beyond
tidying a hypothesis.

## The item this costs rather than closes

`TorusSiteTransitive` fenced, today: *"**not a proof that some graph has trivial automorphism
group** … no asymmetric graph is constructed anywhere in this estate (grepped), and exhibiting one
is **not attempted and not costed**"*. That fence stands, and the cost is now shaped rather than
absent — which is what `WALLS.md` §W5.0 item 4 did for the curvature rung on 2026-09-02, and what
this estate says a fence is for.

**Probed, not guessed.** Mathlib has **no** asymmetric graph and no trivial-automorphism-group
statement: `--shape 'Aut .* = ⊥|asymmetric'` returns **0** of `316,986` theorem statements.
**A first draft of this paragraph also wrote that `SimpleGraph.Aut` carries no such lemma.**
`--cites-lean` flagged that name as resolving nowhere and it is right: there is no such
declaration at this pin at all, so the sentence claimed a fact about an object that does not
exist. Corrected before the commit, by the mode rather than by me. The estate's vocabulary is
`FieldAutInvariance.IsGraphAut`, a predicate and not a bundled group, so the target reads
`∀ θ, IsGraphAut G θ → θ = Equiv.refl _`.
**Two routes, and the obligation is different in each.**
*Brute force*: the smallest asymmetric graph has six vertices, so `decide` over
`Equiv.Perm (Fin 6)` is `720 × 36` adjacency checks. Decidable, and **the risk is kernel reduction
on `Equiv.Perm`, not the mathematics**.
*By invariant*: the six-vertex example has degree sequence `(1,2,2,3,3,3)`, so
`eq_of_degree_unique` below fixes the degree-`1` vertex outright and `degree_class_image` confines
the rest to two classes — after which the argument is a short case analysis rather than an
enumeration. **This file supplies exactly the lemmas that route needs and stops there.**

**No time estimate is offered and no cost is claimed** (`ERRATUM 194`, `ERRATUM 246`): what is
offered is the shape, and `ERRATUM 194` records four wrong difficulty estimates on this estate's
chains.

> ⚠ **AND THE ORDERING ABOVE IS ITSELF A WRONG ESTIMATE, KEPT AS WRITTEN** (`ERRATUM 94`,
> **`ERRATUM 447`**, the next unit). `AsymmetricGraph.asymGraph_asymmetric` settles all `720`
> permutations by `decide` in **20 seconds**, needing one `inferInstanceAs` and one
> `set_option maxRecDepth` — **neither of them kernel reduction**, which is what this paragraph
> named as the risk. **And the invariant route does not start**: its first step was
> *"`eq_of_degree_unique` fixes the degree-`1` vertex outright"* on the sequence `(1,2,2,3,3,3)`,
> **which has two vertices of degree `1` and so no unique degree at all** — a misreading of a
> hypothesis this same unit proved. **Declining to give a time while giving a confident ordering is
> the same act in a thinner disguise**: an ordering is an estimate. The description of the two
> routes is accurate and is why the paragraph is kept.

## What is NOT here

**No asymmetric graph.** The fence is unchanged; only its cost is now written down.

**Nothing about the automorphism group as a group.** `IsGraphAut` is a predicate, not a bundled
`Aut`, and nothing here builds one.

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GraphAutDegree

open Finset SimpleGraph FieldAutInvariance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbours of `θ p` are the image of the neighbours of `p`. `θ.symm` does the work
involutivity was doing in `GraphReflection.IsRefl.degree`. -/
theorem IsGraphAut.neighborFinset_image {θ : V ≃ V} (h : IsGraphAut G θ) (p : V) :
    G.neighborFinset (θ p) = (G.neighborFinset p).image θ := by
  classical
  ext u
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro hu
    refine ⟨θ.symm u, ?_, by simp⟩
    have hiff := h p (θ.symm u)
    rw [Equiv.apply_symm_apply] at hiff
    exact hiff.mp hu
  · rintro ⟨v, hv, rfl⟩
    exact (h p v).mpr hv

omit [DecidableEq V] in
/-- **DEGREE IS PRESERVED BY EVERY ADJACENCY-PRESERVING BIJECTION**, involutive or not.
`GraphReflection.IsRefl.degree` is the involutive case and stays as written (`ERRATUM 337`). -/
theorem IsGraphAut.degree {θ : V ≃ V} (h : IsGraphAut G θ) (p : V) :
    G.degree (θ p) = G.degree p := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    IsGraphAut.neighborFinset_image h p, Finset.card_image_of_injective _ θ.injective]

/-- **AN AUTOMORPHISM PERMUTES EACH DEGREE CLASS.** Every *"the automorphism group is small"*
argument starts here. -/
theorem IsGraphAut.degree_class_image {θ : V ≃ V} (h : IsGraphAut G θ) (d : ℕ) :
    (Finset.univ.filter fun v => G.degree v = d).image θ
      = Finset.univ.filter fun v => G.degree v = d := by
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hdv : G.degree v = d := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [IsGraphAut.degree h v, hdv]⟩
  · rw [Finset.card_image_of_injective _ θ.injective]

omit [DecidableEq V] in
/-- **A VERTEX ALONE IN ITS DEGREE IS FIXED BY EVERY AUTOMORPHISM.** The first rung of an
asymmetry argument: it is what turns a degree sequence with a unique value into a fixed point. -/
theorem IsGraphAut.eq_of_degree_unique {θ : V ≃ V} (h : IsGraphAut G θ) {v : V}
    (huniq : ∀ w : V, G.degree w = G.degree v → w = v) : θ v = v :=
  huniq (θ v) (IsGraphAut.degree h v)

end GraphAutDegree
