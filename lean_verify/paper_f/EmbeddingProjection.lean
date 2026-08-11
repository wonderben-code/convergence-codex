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
> **`IsFunContinuous`** — and the one thing left before those two assemble into a pair, named as an
> object with `funPair_of_continuous` as its reduction, so it is the whole remaining distance to one
> level of the tower and not a programme.

## What this does NOT do

**It does not build `D∞`, and §W8.0's items 2 and 3 are untouched.** What is here is item 1 and the
functor that makes item 2's tower well-defined. **The inverse limit itself — the object, its ω-CPO
structure, and the bilimit theorem that it is a fixed point of this functor — is not attempted**,
and `ReflexiveDomainObstruction.DInfExists` still names the target unproved.

Nothing here is an approximation of the limit or a partial version of it. A tower whose maps exist
is not a tower whose limit exists, and this file supplies only the maps.
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

/-! ## What is NOT here, and it is one named thing

`funEmb` and `funProj` are the right maps and satisfy both `EPPair` clauses. **They are not
assembled into an `EPPair (D →𝒄 D) (E →𝒄 E)` here**, because that needs them to be *continuous* as
maps between the function-space ω-CPOs — `f ↦ emb ∘ f ∘ proj` must commute with `ωSup` in
`D →𝒄 D`, which is pointwise but is a further proof. It is a build, not a wall, and it is stated
here rather than quietly skipped.

That, plus §W8.0's items 2 and 3 — the inverse limit and the bilimit theorem — is the whole
remaining distance to `D∞`. -/

/-- The one thing this file leaves open, as an object rather than a sentence: **that a pair's
`funEmb` and `funProj` are continuous**, i.e. underlie continuous maps between the function-space
ω-CPOs.

**A first draft of this `def` said something else and was caught by reading it back.** It read
`∀ _ : EPPair D E, Nonempty (EPPair (D →𝒄 D) (E →𝒄 E))` — *some* pair exists on the function
spaces, which is **not** the statement wanted: it could hold for reasons having nothing to do with
`funEmb` and `funProj`, and a proof of it would not advance the tower by a step. That is
`ERRATUM 108`'s failure exactly — a gap object whose statement is not the thing meant — caught
before it shipped, by the habit that erratum produced.

**This is known mathematics, not a conjecture of this project**: the maps are continuous because
`ωSup` in a function-space ω-CPO is pointwise. It is stated per-pair rather than universally so
that it can be *checked on an instance*, which `isFunContinuous_refl` does. -/
def IsFunContinuous (P : EPPair D E) : Prop :=
  ∃ (Φ : (D →𝒄 D) →𝒄 (E →𝒄 E)) (Ψ : (E →𝒄 E) →𝒄 (D →𝒄 D)),
    (∀ f, Φ f = P.funEmb f) ∧ (∀ g, Ψ g = P.funProj g)

/-- **AND THE REDUCTION, so the `def` is not decorative:** granted the continuity, the pair on the
function spaces follows immediately from the two identities already proved. So the remaining
distance from this file to one level of the `D∞` tower is exactly `IsFunContinuous` and nothing
else. -/
theorem funPair_of_continuous {P : EPPair D E} (h : P.IsFunContinuous) :
    Nonempty (EPPair (D →𝒄 D) (E →𝒄 E)) := by
  obtain ⟨Φ, Ψ, hΦ, hΨ⟩ := h
  refine ⟨⟨Φ, Ψ, fun f => ?_, fun g => ?_⟩⟩
  · rw [hΦ f, hΨ (P.funEmb f), P.funProj_funEmb]
  · rw [hΨ g, hΦ (P.funProj g)]
    intro y
    exact P.funEmb_funProj_le g y

/-- **AND IT IS NOT VACUOUS**, checked on an instance rather than assumed: the identity pair
satisfies it with both maps the identity. That is **not** evidence for the general case — the
general case is where the pointwise-`ωSup` argument is needed and this one needs nothing — but a
`def` returning `Prop` with no instance at all is a trap this estate has fallen into before, and
the file that noticed said so. -/
theorem isFunContinuous_refl : (refl : EPPair D D).IsFunContinuous := by
  refine ⟨ContinuousHom.id, ContinuousHom.id, fun f => ?_, fun g => ?_⟩ <;>
    apply DFunLike.ext <;> intro x <;> rfl

end EPPair

end EmbeddingProjection
