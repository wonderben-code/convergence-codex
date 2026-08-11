import InverseLimitCPO

/-!
# The canonical tower `D, [D → D], [[D → D] → [D → D]], …`

`InverseLimitCPO.lean` builds limits of **arbitrary** towers, and its header says exactly what stops
the bilimit theorem from being stateable:

> *"What would have to be stated first is the canonical tower: `D₀` a pointed ω-CPO,
> `Dₙ₊₁ = Dₙ →𝒄 Dₙ`, `step 0` the pair that embeds a point as a constant function and projects by
> evaluating at the bottom element, and `step (n+1) = funPair (step n)`. That needs a bottom
> element, which `OmegaCompletePartialOrder` does not carry, so it needs `OrderBot` alongside.
> **Not built here.**"*

This file builds it, so the bilimit becomes stateable — and states it.

> **`PtCPO`** — an ω-CPO with a bottom element, bundled, because the recursion below has to carry
> both instances up through the levels and a type class cannot be recursive in the level.
>
> **`funStep`** — one level up: the continuous self-maps, which are again an ω-CPO (Mathlib) and
> again have a bottom (the constant `⊥` map, `botHom`).
>
> **`basePair`** — the first rung, `D ⇄ (D →𝒄 D)`: embed a point as the constant function, project
> by **evaluating at `⊥`**. Both `EPPair` clauses hold, and the second is where the bottom element
> earns its place: `const (f ⊥) ≤ f` because `⊥ ≤ y` and `f` is monotone.
>
> **`canonical`** — the tower itself, with `step 0 = basePair` and each later step the previous one
> pushed through `EPPair.funPair`. So every map in the tower is *derived*, which is precisely what
> the wrongly-stated first draft in `InverseLimitCPO` failed to require.
>
> **`Bilimit`** — and now the wall's last ingredient can be written down: that the limit of this
> tower is isomorphic to its own continuous self-maps.

## What this does NOT do

**`Bilimit` is not proved.** It is `WALLS` §W8.0's item 3 and it is the whole of what remains of
that wall. Its proof is a cofinality argument — the limit's self-maps are themselves a limit of the
levels' self-maps, one level shifted — and none of it is here.

**Nothing in this file is evidence for it.** Building the tower makes the statement *sayable*; it
says nothing about whether it is true, and the classical answer being yes is not a proof in this
estate.
-/

namespace CanonicalTower

open OmegaCompletePartialOrder EmbeddingProjection InverseLimitCPO

universe u

/-- **A pointed ω-CPO**, bundled. The levels of the tower are built by recursion on `ℕ` and each
level's instances have to come with it, which a type class cannot do. -/
structure PtCPO where
  /-- The underlying type. -/
  carrier : Type u
  /-- Its ω-CPO structure. -/
  cpo : OmegaCompletePartialOrder carrier
  /-- And a bottom element for it. -/
  bot : @OrderBot carrier (@Preorder.toLE _ (@PartialOrder.toPreorder _ cpo.toPartialOrder))

attribute [instance] PtCPO.cpo PtCPO.bot

/-- The constant-`⊥` map is the bottom of the continuous function space. -/
@[reducible] def botHom (X : PtCPO.{u}) : @OrderBot (X.carrier →𝒄 X.carrier) _ where
  bot := ContinuousHom.const ⊥
  bot_le _ _ := bot_le

/-- **ONE LEVEL UP**: the continuous self-maps, which Mathlib already makes an ω-CPO, with the
constant `⊥` map as bottom. -/
def funStep (X : PtCPO.{u}) : PtCPO.{u} where
  carrier := X.carrier →𝒄 X.carrier
  cpo := inferInstance
  bot := botHom X

/-- **THE FIRST RUNG.** Embed a point as the constant function; project by evaluating at `⊥`.
`proj (emb d) = d` is immediate, and `emb (proj f) ≤ f` is where the bottom element earns its
place: `f ⊥ ≤ f y` for every `y`, because `⊥ ≤ y` and `f` is monotone. -/
def basePair (X : PtCPO.{u}) : EPPair X.carrier (X.carrier →𝒄 X.carrier) where
  emb :=
    { toFun := fun d => ContinuousHom.const d
      monotone' := fun _ _ h _ => h
      map_ωSup' := fun c => by
        apply DFunLike.ext
        intro y
        simp [ContinuousHom.ωSup_apply]
        congr 1 }
  proj :=
    { toFun := fun f => f ⊥
      monotone' := fun _ _ h => h ⊥
      map_ωSup' := fun c => by
        simp [ContinuousHom.ωSup_apply]
        congr 1 }
  proj_emb _ := rfl
  emb_proj_le f y := f.monotone bot_le

/-- The levels of the canonical tower over `X`. -/
def level (X : PtCPO.{u}) : ℕ → PtCPO.{u}
  | 0 => X
  | n + 1 => funStep (level X n)

/-- The step from level `n` to level `n+1`: the base pair at the bottom, and each later one the
previous pushed through the function-space functor. **Every map in this tower is derived**, which
is exactly what a bilimit statement has to require and what `InverseLimitCPO`'s discarded first
draft did not. -/
def step (X : PtCPO.{u}) : ∀ n, EPPair (level X n).carrier (level X (n + 1)).carrier
  | 0 => basePair X
  | n + 1 => EPPair.funPair (step X n)

/-- **THE CANONICAL TOWER.** -/
def canonical (X : PtCPO.{u}) : Tower.{u} where
  carrier n := (level X n).carrier
  cpo n := (level X n).cpo
  step := step X

/-! ## The wall's last ingredient, now sayable -/

/-- **THE BILIMIT PROPERTY**, which is `WALLS` §W8.0's item 3 and the whole of what is left of that
wall: the limit of the canonical tower over a pointed ω-CPO is isomorphic to its own continuous
self-maps.

**Not proved, and nothing in this file is evidence for it.** Building the tower makes the sentence
sayable; the classical answer being yes is not a proof in this estate. The proof is a cofinality
argument — the limit's self-maps are themselves a limit of the levels' self-maps, shifted by one —
and none of it is here.

**The statement quantifies over `X`, deliberately.** The classical construction starts from any
non-trivial pointed ω-CPO, and a statement for one chosen `X` would be weaker than the theorem and
would invite the reader to supply the wrong one. -/
def Bilimit : Prop :=
  ∀ X : PtCPO.{u}, Nonempty (Limit (canonical X) ≃ (Limit (canonical X) →𝒄 Limit (canonical X)))

/-- **AND THE HYPOTHESIS IS NOT VACUOUS**: `PtCPO` is inhabited, by `Prop` with its complete
lattice. So `Bilimit` quantifies over something. Not evidence about the bilimit itself — `Prop` is
a subsingleton in the sense that matters least here, and the interesting towers start from
non-trivial `X` — but a `Prop`-valued `def` over an empty index is a trap this estate has fallen
into before. -/
def propPt : PtCPO.{0} where
  carrier := Prop
  cpo := inferInstance
  bot := inferInstance

end CanonicalTower
