import InverseLimitCPO
import ReflexiveDomainObstruction

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

## What this does NOT do — SUPERSEDED 2026-08-12, see the note below

**`Bilimit` is not proved.** It is `WALLS` §W8.0's item 3 and it is the whole of what remains of
that wall. Its proof is a cofinality argument — the limit's self-maps are themselves a limit of the
levels' self-maps, one level shifted — and none of it is here.

**Nothing in this file is evidence for it.** Building the tower makes the statement *sayable*; it
says nothing about whether it is true, and the classical answer being yes is not a proof in this
estate.

## `Bilimit` IS PROVED, 2026-08-12

The two paragraphs above are kept verbatim and are **both now false of this file**. The cofinality
argument they describe — *"the limit's self-maps are themselves a limit of the levels' self-maps,
one level shifted"* — is exactly the proof, and it turned out to be a correct description of it.
It is assembled in §5 below from three pieces built in `InverseLimitCPO` over the course of the
same day:

* **`ωSup_roundTripChain`** (§8 there) — the round trips through the levels have the identity as
  their supremum;
* **`funLimitEquiv`** (§10) — the self-maps of a limit are the limit of the levels' self-maps, for
  an **arbitrary** tower;
* **`shiftEquiv`** (§11) — dropping a tower's bottom level does not change its limit.

**What this file adds is the last link and it is `rfl`:** `funTower (canonical X)` and
`shift (canonical X)` are the *same tower*, because `level (n+1)` is *defined* as
`funStep (level n)` and `step (n+1)` as `funPair (step n)`. Composing gives `Bilimit`.

**And the target `WALLS` §W8.0 §1 actually names** — *"a **non-trivial** `D` with `D ≅ [D → D]`"* —
needs one thing beyond the isomorphism, which the wall's own §2 is entirely about: the witness must
not be a point. `dInfExists_holds` supplies it, using `Prop` as the seed and
`embHom_injective` to carry non-triviality from level 0 into the limit.

**What is still NOT here.** `Bilimit` is stated with `Nonempty (… ≃ …)`, a bare type equivalence,
which is what the estate's `IsDomainReflexive` and `DInfExists` also ask for. `funLimitOrderIso`
gives the order-isomorphism strengthening for the *arbitrary-tower* statement; **this file does not
transport it through `shiftEquiv`**, which is not an order isomorphism as stated either. So the
stronger form of `Bilimit` itself is available in principle and is not proved here.
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

/-! ## 5. The bilimit, proved

**`WALLS` §W8.0 item 3.** Everything general is in `InverseLimitCPO`; what is special to the
canonical tower is one `rfl` and the choice of a non-trivial seed.

**`funTower_canonical` is definitional and that is the whole trick.** `level X (n+1)` is *defined*
as `funStep (level X n)`, whose carrier is `(level X n).carrier →𝒄 (level X n).carrier`, which is
`funTower (canonical X)`'s level `n`; and `step X (n+1)` is *defined* as `funPair (step X n)`,
which is `funTower (canonical X)`'s step `n`. So the tower of the canonical tower's level self-maps
**is** the canonical tower with its bottom level removed, on the nose. Had either definition been
written differently — `level` by a general recursor, `step` with an intervening cast — this would
be a transport instead, and the section would be longer than it is.

**Non-triviality is the wall's §1 and it is separate from the isomorphism.** `Bilimit` holds for
`X = PUnit` too, where the limit is a point and the isomorphism is vacuous; the wall asks for a
witness that is *not* a point, because its §2 proves the naive equation has only trivial solutions
and the whole subject exists to escape that. `not_subsingleton_limit` carries non-triviality up
from level 0 by `embHom_injective`, and `Prop` — the seed `propPt` already checked to be a
`PtCPO` — is not a subsingleton.

**`dInfExists_holds` is therefore the wall's target in the estate's own words**, and
`dInf_infinite` reads it back through `ReflexiveDomainObstruction`'s own reduction: the witness is
infinite, which is what that file predicted any witness must be.
-/

/-- **THE CANONICAL TOWER'S SELF-MAP TOWER IS ITSELF, SHIFTED**, and it is `rfl`. -/
theorem funTower_canonical (X : PtCPO.{u}) : funTower (canonical X) = shift (canonical X) := rfl

/-- **THE BILIMIT HOLDS.** -/
theorem bilimit_holds : Bilimit.{u} := by
  intro X
  refine ⟨?_⟩
  have e₁ : (Limit (canonical X) →𝒄 Limit (canonical X)) ≃ Limit (funTower (canonical X)) :=
    funLimitEquiv (canonical X)
  have e₂ : Limit (funTower (canonical X)) ≃ Limit (canonical X) := by
    rw [funTower_canonical]
    exact shiftEquiv (canonical X)
  exact (e₁.trans e₂).symm

/-- Level 0 of the canonical tower is `X` itself, so a non-trivial `X` gives a non-trivial limit. -/
theorem not_subsingleton_limit (X : PtCPO.{u}) (h : ¬ Subsingleton X.carrier) :
    ¬ Subsingleton (Limit (canonical X)) := by
  intro hsub
  refine h ⟨fun a b => ?_⟩
  exact embHom_injective (canonical X) 0 (hsub.elim _ _)

/-- `Prop` is not a subsingleton: `True ≠ False`. -/
theorem not_subsingleton_prop : ¬ Subsingleton Prop := by
  intro h
  have : True = False := h.elim True False
  exact this.symm ▸ trivial

/-- **AND SO A NON-TRIVIAL SOLUTION OF SCOTT'S EQUATION EXISTS.** -/
theorem dInfExists_holds : ReflexiveDomainObstruction.DInfExists := by
  refine ⟨Limit (canonical propPt), inferInstance, ?_, bilimit_holds propPt⟩
  exact not_subsingleton_limit propPt not_subsingleton_prop

/-- And it is infinite, by the estate's own reduction. -/
theorem dInf_infinite :
    ∃ (D : Type) (_ : OmegaCompletePartialOrder D), ¬ Subsingleton D ∧ Infinite D :=
  ReflexiveDomainObstruction.dInfExists_infinite dInfExists_holds

/-! ## 6. The witness, checked against this estate's own no-go theorems

**`ReflexiveDomainObstruction` proves two things any solution must satisfy, and neither is implied
by §5.** They are the wall's reason for existing, so the construction is worth holding against
them rather than assuming it clears them.

* **Any solution is infinite** — `not_isDomainReflexive_of_finite`, read as a constraint by
  `dInfExists_infinite`. Discharged in §5 by `dInf_infinite`, which routes the witness through that
  file's own reduction rather than arguing separately.
* **No solution carries the discrete order** — `subsingleton_of_discDomainReflexive`, because on a
  discrete ω-CPO every self-map is continuous and Cantor applies unchanged, with no size
  hypothesis. **This one §5 does not touch**, and a witness that happened to be discretely ordered
  would contradict it. `exists_lt_limit_prop` exhibits two distinct comparable elements —
  `embHom 0 False ≤ embHom 0 True`, distinct because `embHom` is injective — so
  `limit_prop_not_discrete`.

**This is a consistency check, not a new result.** It could not have failed without something else
being wrong; the point is that nobody had run it, and "my construction satisfies my own no-go
theorems' hypotheses" is the kind of thing an estate should be able to say in Lean rather than by
reasoning about it.

**What it is NOT: a proof that the order is interesting.** Two comparable points is the minimum the
obstruction rules out and nothing more. No claim is made here about the witness's order structure
beyond that, and in particular nothing about it being a *domain* in any of the stronger senses.
-/

/-- The witness has two DISTINCT COMPARABLE elements, so its order is not discrete. -/
theorem exists_lt_limit_prop :
    ∃ x y : Limit (canonical propPt), x ≤ y ∧ x ≠ y := by
  refine ⟨embHom (canonical propPt) 0 False, embHom (canonical propPt) 0 True, ?_, ?_⟩
  · exact embFun_mono (canonical propPt) 0 (fun h => h.elim)
  · intro hEq
    have : (False : Prop) = True := embHom_injective (canonical propPt) 0 hEq
    exact this ▸ trivial

/-- **AND THE WITNESS IS NOT A DISCRETE ORDER**, which is what
`ReflexiveDomainObstruction.subsingleton_of_discDomainReflexive` requires of any solution. -/
theorem limit_prop_not_discrete :
    ¬ (∀ x y : Limit (canonical propPt), x ≤ y → x = y) := by
  obtain ⟨x, y, hle, hne⟩ := exists_lt_limit_prop
  exact fun h => hne (h x y hle)

end CanonicalTower
