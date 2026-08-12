import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.GaloisConnection.Basic

/-!
# Embedding–projection pairs, and the function-space functor on them

`WALLS.md` §W8.0 lists three things that would have to exist for `D∞`, and the first is:

> *"**Embedding–projection pairs between ω-CPOs**, as a bundled structure with composition. Small,
> and the `GaloisInsertion` lead above may shorten it."*

That lead was recorded as **not checked**. This file builds the structure and checks the lead.

> **`EPPair D E`** — a continuous `emb : D →𝒄 E` and `proj : E →𝒄 D` with `proj ∘ emb = id` and
> `emb ∘ proj ≤ id`. So `D` sits inside `E` as a retract, and the retraction loses information
> only downward.
>
> **`galoisConnection`** — **the lead is real.** An embedding–projection pair *is* a Galois
> connection, `emb a ≤ b ↔ a ≤ proj b`, and both directions are two lines. `proj_emb` then makes
> it the coinsertion case. So the order-theoretic side conditions do match, which §W8.0 said was
> unchecked.
>
> **`refl` and `comp`** — identity and composition, so towers can be built.
>
> **`funEmb` and `funProj`** — **the function-space functor's action on pairs**, which is the step
> the `D∞` tower is made of: from `D ⇄ E`, `f ↦ emb ∘ f ∘ proj` and `g ↦ proj ∘ g ∘ emb`. **Both
> `EPPair` identities are proved for them** (`funProj_funEmb`, `funEmb_funProj_le`).
>
> **`funPair`** — **and they assemble.** `funEmbHom` and `funProjHom` prove the two maps
> continuous, so the functor lands as an `EPPair (D →𝒄 D) (E →𝒄 E)`. The step is complete, and what
> remains of `D∞` is the inverse limit and the bilimit theorem — §W8.0's items 2 and 3.

## What this does NOT do

**It does not build `D∞`, and §W8.0's items 2 and 3 are untouched.** What is here is item 1 and
the complete functor that makes item 2's tower well-defined. **The inverse limit itself — the
object, its ω-CPO structure, and the bilimit theorem that it is a fixed point of this functor — is
not attempted**, and `ReflexiveDomainObstruction.DInfExists` still names the target unproved.

Nothing here is an approximation of the limit or a partial version of it. A tower whose maps exist
is not a tower whose limit exists, and this file supplies only the maps.

**THE PARAGRAPH ABOVE SAID "NOT ATTEMPTED" AND IS SUPERSEDED, 2026-08-12.** Items 2 and 3 were
attempted and they landed — `InverseLimitCPO` builds the limit and its ω-CPO structure, and
`CanonicalTower.bilimit_holds` and `CanonicalTower.dInfExists_holds` prove the bilimit theorem and
discharge `ReflexiveDomainObstruction.DInfExists`, which the sentence above says *still names the
target unproved*. **That clause is now false**; W8 is closed. The paragraph is kept rather than
rewritten, per `IsingTransferMatrix` §7's precedent: what a file said it was not doing, on the day
it said it, is part of why the next estimate is worth anything. This file is item 1 and the functor,
and that is still exactly what it is. Found by `check_ledger.py --attempts` (`ERRATUM 148`).
-/

namespace EmbeddingProjection

open OmegaCompletePartialOrder

universe u

variable {D E F : Type u}
variable [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E]
variable [OmegaCompletePartialOrder F]

/-- **An embedding–projection pair.** `D` is a retract of `E` by continuous maps, and the
composite the other way is below the identity — so `proj` forgets, and forgets downward. -/
structure EPPair (D E : Type u) [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] where
  /-- The embedding. -/
  emb : D →𝒄 E
  /-- The projection. -/
  proj : E →𝒄 D
  /-- The projection undoes the embedding exactly. -/
  proj_emb : ∀ x, proj (emb x) = x
  /-- And the other composite loses information downward. -/
  emb_proj_le : ∀ y, emb (proj y) ≤ y

namespace EPPair

theorem emb_injective (P : EPPair D E) : Function.Injective P.emb := by
  intro x y h
  rw [← P.proj_emb x, ← P.proj_emb y, h]

theorem proj_surjective (P : EPPair D E) : Function.Surjective P.proj :=
  fun x => ⟨P.emb x, P.proj_emb x⟩

/-! ## The `GaloisInsertion` lead, checked

`WALLS` §W8.0 §5 recorded `GaloisConnection` as "the right algebraic shape … **not checked** for
whether the order-theoretic side conditions match; recorded as a lead, not a route." They match. -/

/-- **AN EMBEDDING–PROJECTION PAIR IS A GALOIS CONNECTION.** Forward: apply `proj`, which is
monotone, and use `proj_emb`. Backward: apply `emb`, then `emb_proj_le`. -/
theorem galoisConnection (P : EPPair D E) : GaloisConnection P.emb P.proj := by
  intro a b
  constructor
  · intro h
    have := P.proj.monotone h
    rwa [P.proj_emb] at this
  · intro h
    exact le_trans (P.emb.monotone h) (P.emb_proj_le b)

/-- And `proj ∘ emb = id` is the extra condition that makes it the **coinsertion** case rather
than merely a connection. Stated as the equation rather than as a Mathlib bundling, because the
bundling would fix an orientation this file has no use for. -/
theorem proj_comp_emb (P : EPPair D E) : (P.proj.comp P.emb : D → D) = id :=
  funext P.proj_emb

/-! ## Identity and composition, so a tower is expressible -/

/-- The identity pair. -/
def refl : EPPair D D where
  emb := ContinuousHom.id
  proj := ContinuousHom.id
  proj_emb _ := rfl
  emb_proj_le _ := le_rfl

/-- **Composition.** The `emb ∘ proj ≤ id` clause composes because `emb` is monotone: the inner
composite drops below the identity and the outer pair pushes that down again. -/
def comp (Q : EPPair E F) (P : EPPair D E) : EPPair D F where
  emb := Q.emb.comp P.emb
  proj := P.proj.comp Q.proj
  proj_emb x := by
    change P.proj (Q.proj (Q.emb (P.emb x))) = x
    rw [Q.proj_emb, P.proj_emb]
  emb_proj_le y := by
    change Q.emb (P.emb (P.proj (Q.proj y))) ≤ y
    exact le_trans (Q.emb.monotone (P.emb_proj_le (Q.proj y))) (Q.emb_proj_le y)

/-! ## The function-space functor on pairs

This is the step that makes `D∞`'s tower a tower: each level is the continuous self-maps of the
one below, and the pair relating consecutive levels has to be *derived* from the pair below. -/

/-- `f ↦ emb ∘ f ∘ proj`, carrying a self-map of `D` up to one of `E`. -/
def funEmb (P : EPPair D E) (f : D →𝒄 D) : E →𝒄 E := P.emb.comp (f.comp P.proj)

/-- `g ↦ proj ∘ g ∘ emb`, carrying a self-map of `E` down to one of `D`. -/
def funProj (P : EPPair D E) (g : E →𝒄 E) : D →𝒄 D := P.proj.comp (g.comp P.emb)

/-- **THE FIRST `EPPair` IDENTITY SURVIVES**, and exactly: the two copies of `proj ∘ emb` that
appear cancel independently, so nothing is lost going up and back down. -/
theorem funProj_funEmb (P : EPPair D E) (f : D →𝒄 D) : P.funProj (P.funEmb f) = f := by
  apply DFunLike.ext
  intro x
  change P.proj (P.emb (f (P.proj (P.emb x)))) = f x
  rw [P.proj_emb, P.proj_emb]

/-- **AND SO DOES THE SECOND**, pointwise, using `emb ∘ proj ≤ id` twice and monotonicity of `g`
in between. -/
theorem funEmb_funProj_le (P : EPPair D E) (g : E →𝒄 E) (y : E) :
    P.funEmb (P.funProj g) y ≤ g y := by
  change P.emb (P.proj (g (P.emb (P.proj y)))) ≤ g y
  exact le_trans (P.emb_proj_le _) (g.monotone (P.emb_proj_le y))

/-! ## The functor, assembled

An earlier version of this file stopped one step short of here. It defined `funEmb` and `funProj`,
proved both `EPPair` identities for them, and then named their **continuity** as an open object
with a reduction — *"a build, not a wall, and it is stated here rather than quietly skipped."*
`PROOF_STRATEGY` §3 says to re-attempt the next leg the moment the previous one lands rather than
returning to the queue, so it was attempted, and it is below. The naming is kept because the
reduction it produced is the right shape and because the near-miss recorded on `IsFunContinuous` is
worth keeping. -/

/-- The bundled `funEmb`. Monotone pointwise from `emb`; the `ωSup` clause is pointwise too,
because suprema in a function-space ω-CPO are computed pointwise and `emb` is continuous. -/
def funEmbHom (P : EPPair D E) : (D →𝒄 D) →𝒄 (E →𝒄 E) where
  toFun := P.funEmb
  monotone' _ _ h y := P.emb.monotone (h (P.proj y))
  map_ωSup' c := by
    apply DFunLike.ext
    intro y
    simp [funEmb, ContinuousHom.ωSup_apply, P.emb.ωScottContinuous.map_ωSup, Chain.map]
    congr 1

/-- The bundled `funProj`, by the same argument on the other side. -/
def funProjHom (P : EPPair D E) : (E →𝒄 E) →𝒄 (D →𝒄 D) where
  toFun := P.funProj
  monotone' _ _ h x := P.proj.monotone (h (P.emb x))
  map_ωSup' c := by
    apply DFunLike.ext
    intro x
    simp [funProj, ContinuousHom.ωSup_apply, P.proj.ωScottContinuous.map_ωSup, Chain.map]
    congr 1

/-- **THE FUNCTION-SPACE FUNCTOR ON EMBEDDING–PROJECTION PAIRS.** From a pair `D ⇄ E` it builds a
pair `(D →𝒄 D) ⇄ (E →𝒄 E)`. This is the step `D∞`'s tower is made of, and it is now complete: the
maps are `funEmb`/`funProj`, their continuity is `funEmbHom`/`funProjHom`, and the two `EPPair`
clauses are `funProj_funEmb` and `funEmb_funProj_le`. -/
def funPair (P : EPPair D E) : EPPair (D →𝒄 D) (E →𝒄 E) where
  emb := P.funEmbHom
  proj := P.funProjHom
  proj_emb := P.funProj_funEmb
  emb_proj_le g y := P.funEmb_funProj_le g y

/-- The property this file named as its open step, before `funEmbHom` and `funProjHom` discharged
it an hour later: that a pair's two induced maps on function spaces are continuous.

**A first draft of this `def` said something else and was caught by reading it back.** It read
`∀ _ : EPPair D E, Nonempty (EPPair (D →𝒄 D) (E →𝒄 E))` — *some* pair exists on the function
spaces, which is **not** the statement wanted: it could hold for reasons having nothing to do with
`funEmb` and `funProj`, and a proof of it would not advance the tower by a step. That is
`ERRATUM 108`'s failure exactly — a gap object whose statement is not the thing meant — caught
before it shipped, by the habit that erratum produced. It is kept, now proved, because a `def` that
was going to be the record of a gap is a better record of a near-miss than a deleted one. -/
def IsFunContinuous (P : EPPair D E) : Prop :=
  ∃ (Φ : (D →𝒄 D) →𝒄 (E →𝒄 E)) (Ψ : (E →𝒄 E) →𝒄 (D →𝒄 D)),
    (∀ f, Φ f = P.funEmb f) ∧ (∀ g, Ψ g = P.funProj g)

/-- **AND IT HOLDS FOR EVERY PAIR.** -/
theorem isFunContinuous (P : EPPair D E) : P.IsFunContinuous :=
  ⟨P.funEmbHom, P.funProjHom, fun _ => rfl, fun _ => rfl⟩

/-! ## What is NOT here, and it is now exactly two things

`WALLS` §W8.0 lists three ingredients for `D∞`. **Item 1 is this file's `EPPair`, and the
function-space functor that item 2's tower needs is `funPair`.** What is left is:

* **the inverse limit itself** — the object `lim (Dₙ, pₙ)`, with its ω-CPO structure. Mathlib has
  no inverse limit of ordered structures at all; `Order/DirectedInverseSystem.lean` is a *direct*
  limit of types.
* **the bilimit theorem** — that the limit is a fixed point of `funPair`, i.e. isomorphic to its own
  continuous self-maps. That is what would discharge `ReflexiveDomainObstruction.DInfExists`, and
  it is not attempted.

**Nothing here is an approximation of the limit.** A tower whose maps exist is not a tower whose
limit exists, and this file supplies only the maps.

**SUPERSEDED 2026-08-12, as the header's version of this list is:** both bullets were attempted and
both landed (`InverseLimitCPO`, `CanonicalTower.bilimit_holds`), and
`ReflexiveDomainObstruction.DInfExists` is discharged by `CanonicalTower.dInfExists_holds`. Kept as
written; `ERRATUM 148`. -/

end EPPair

end EmbeddingProjection
