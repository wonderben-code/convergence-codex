import EmbeddingProjection

/-!
# The inverse limit of a tower of ω-CPOs

`WALLS.md` §W8.0 lists three ingredients for `D∞`. `EmbeddingProjection.lean` supplied item 1 and
the function-space functor. This file is **item 2**:

> *"The inverse limit of a tower of ω-CPOs along such pairs, with its ω-CPO structure. This is the
> substantial one, and it is genuinely absent — Mathlib has direct limits of directed systems of
> types, and nothing in the other direction for ordered structures."*

> **`Tower`** — a family `D : ℕ → Type` of ω-CPOs with an embedding–projection pair between each
> consecutive pair of levels.
>
> **`Limit T`** — the coherent sequences: `x : ∀ n, D n` with `proj n (x (n+1)) = x n`. Ordered
> pointwise, and **an ω-CPO**, with suprema computed level by level. The coherence condition
> survives the supremum because each `proj n` is continuous, which is the whole reason the tower is
> built out of *continuous* maps.
>
> **`proj T n : Limit T →𝒄 D n`** — the limit's own projections, continuous by construction, with
> `proj_succ` recording that they commute with the tower's maps.
>
> **`up`, `down`, `down_up`** — travelling `n` levels up the tower and back down is the identity.
> That is the arithmetic a level-into-limit embedding is built from. **The embedding itself is NOT
> built here** — see the closing section — because the coherent sequence it produces is defined by
> cases on `n < k` versus `n ≥ k` and the two branches live at index `n` and index `k + m`, so it
> needs transport along `k + (n - k) = n`. That is index bookkeeping rather than mathematics, and it
> is named rather than half-done.

## What this does NOT do

**The bilimit theorem is not proved, not attempted, and DELIBERATELY NOT NAMED AS A `def` HERE.**
A first draft of this file did name it, as *"for every tower whose levels are equivalent to the
continuous self-maps of the level below, the limit is equivalent to its own continuous self-maps"*.
**That is not the theorem.** The bilimit theorem is about the tower whose steps ARE
`EPPair.funPair` of the steps below — a tower with arbitrary pairs between levels that merely
happen to be function spaces has no reason to have the property. Writing the weaker sentence and
calling it the gap is `ERRATUM 108` exactly, and `ERRATUM 89` is the rule against naming an object
before the modelling choice inside it has been made.

**What would have to be stated first** is the canonical tower: `D₀` a *pointed* ω-CPO,
`Dₙ₊₁ = Dₙ →𝒄 Dₙ`, `step 0` the pair that embeds a point as a constant function and projects by
evaluating at the bottom element, and `step (n+1) = funPair (step n)`. That needs a bottom element,
which `OmegaCompletePartialOrder` does not carry, so it needs `OrderBot` alongside. **Not built
here.** Once it exists the bilimit is statable, and only then.

**Having a limit is not having `D∞`.** This file builds limits of arbitrary towers; `D∞` is the
limit of one particular tower together with a theorem about it, and only the first half is here.
-/

namespace InverseLimitCPO

open OmegaCompletePartialOrder EmbeddingProjection

universe u

/-- **A tower of ω-CPOs**: a level at every natural number, with an embedding–projection pair from
each level into the next. -/
structure Tower where
  /-- The levels. -/
  carrier : ℕ → Type u
  /-- Each level is an ω-CPO. -/
  cpo : ∀ n, OmegaCompletePartialOrder (carrier n)
  /-- And consecutive levels are related by an embedding–projection pair. -/
  step : ∀ n, @EPPair (carrier n) (carrier (n + 1)) (cpo n) (cpo (n + 1))

attribute [instance] Tower.cpo

variable (T : Tower.{u})

/-- **THE INVERSE LIMIT**: coherent sequences through the tower. -/
def Limit : Type u := { x : ∀ n, T.carrier n // ∀ n, (T.step n).proj (x (n + 1)) = x n }

namespace Limit

instance : PartialOrder (Limit T) where
  le x y := ∀ n, x.1 n ≤ y.1 n
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ n := le_trans (h₁ n) (h₂ n)
  le_antisymm x y h₁ h₂ := Subtype.ext (funext fun n => le_antisymm (h₁ n) (h₂ n))

theorem le_iff {x y : Limit T} : x ≤ y ↔ ∀ n, x.1 n ≤ y.1 n := Iff.rfl

/-- The chain of `n`-th components of a chain of coherent sequences. -/
def levelChain (c : Chain (Limit T)) (n : ℕ) : Chain (T.carrier n) where
  toFun i := (c i).1 n
  monotone' _ _ h := (c.monotone h) n

/-- **THE COHERENCE CONDITION SURVIVES THE SUPREMUM**, because each projection is continuous.
This is the one place the tower's maps being *continuous* rather than merely monotone is used, and
it is the reason the construction works at all. -/
theorem levelChain_coherent (c : Chain (Limit T)) (n : ℕ) :
    (T.step n).proj (ωSup (levelChain T c (n + 1))) = ωSup (levelChain T c n) := by
  rw [(T.step n).proj.ωScottContinuous.map_ωSup]
  congr 1
  apply OrderHom.ext
  funext i
  exact (c i).2 n

instance : OmegaCompletePartialOrder (Limit T) where
  ωSup c := ⟨fun n => ωSup (levelChain T c n), levelChain_coherent T c⟩
  le_ωSup c i n := le_ωSup (levelChain T c n) i
  ωSup_le c x h n := ωSup_le (levelChain T c n) (x.1 n) fun i => h i n

theorem ωSup_apply (c : Chain (Limit T)) (n : ℕ) :
    (ωSup c).1 n = ωSup (levelChain T c n) := rfl

end Limit

/-! ## The limit's projections -/

/-- **The limit's `n`-th projection**, continuous by construction: both the order and the suprema
on `Limit` are level-by-level, so reading off a level is a continuous map. -/
def proj (n : ℕ) : Limit T →𝒄 T.carrier n where
  toFun x := x.1 n
  monotone' _ _ h := h n
  map_ωSup' _ := rfl

/-- The projections commute with the tower's own maps, which is what makes them *the* limit's
projections rather than an unrelated family. -/
theorem proj_succ (n : ℕ) (x : Limit T) : (T.step n).proj (proj T (n + 1) x) = proj T n x :=
  x.2 n

/-! ## Each level embeds in the limit

A coherent sequence is determined by a level together with a rule for everything above it. Going
up uses the tower's embeddings and going down its projections; the composite of `n` steps up and
`n` steps down is the identity, so a level really does sit inside the limit as a retract. -/

/-- `n` steps up the tower from level `k`. -/
def up (k : ℕ) : ∀ n, T.carrier k → T.carrier (k + n)
  | 0, x => x
  | n + 1, x => (T.step (k + n)).emb (up k n x)

/-- `n` steps down from level `k + n`. -/
def down (k : ℕ) : ∀ n, T.carrier (k + n) → T.carrier k
  | 0, x => x
  | n + 1, x => down k n ((T.step (k + n)).proj x)

/-- **DOWN UNDOES UP EXACTLY**, by induction on the number of steps and `proj_emb` at each. -/
theorem down_up (k : ℕ) : ∀ n (x : T.carrier k), down T k n (up T k n x) = x
  | 0, _ => rfl
  | n + 1, x => by
    change down T k n ((T.step (k + n)).proj ((T.step (k + n)).emb (up T k n x))) = x
    rw [(T.step (k + n)).proj_emb]
    exact down_up k n x

/-! ## What remains -/

/-- **`Tower` IS INHABITED**, checked rather than assumed: every level the same ω-CPO, every step
the identity pair. **Not** a witness for anything about `D∞` — its levels are not function spaces
— but a structure with three fields deserves an instance before a file is written about it, which
is the standard `AlgebraicCurvature.lean` set for itself this morning. -/
def constTower (D : Type u) [OmegaCompletePartialOrder D] : Tower.{u} where
  carrier _ := D
  cpo _ := inferInstance
  step _ := EPPair.refl

/-- **AND ITS LIMIT IS `D`**, so `Limit` computes something recognisable on the one tower this file
builds. A coherent sequence over the constant tower has `x (n+1) = x n` at every level, because
every projection is the identity, so it is a constant sequence. The docstring above claimed this
in passing; it is a theorem instead. -/
def limitConstEquiv (D : Type u) [OmegaCompletePartialOrder D] :
    Limit (constTower D) ≃ D where
  toFun x := x.1 0
  invFun d := ⟨fun _ => d, fun _ => rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    induction n with
    | zero => rfl
    | succ k ih => exact ih.trans (x.2 k).symm
  right_inv _ := rfl

end InverseLimitCPO
