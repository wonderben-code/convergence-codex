import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The permutations that fix a function fibrewise, identified and counted

`UNLOCK_WATCHLIST`'s multinomial item records one route to *the multinomial coefficient counts the
arrangements of a multiset* — orbit–stabiliser on `Equiv.Perm ι` acting on `ι → α` by
precomposition — and names the **one step nothing in Mathlib supplies**: the stabiliser.
This file is that step.

> **`glue`** — a permutation of each fibre of `f` glued into a permutation of the domain, through
> `Equiv.sigmaFiberEquiv` and `Equiv.Perm.sigmaCongrRight`.
>
> **`stabEquiv`** — hence `{σ : Perm ι // ∀ i, f (σ i) = f i} ≃ ∀ a, Perm {i // f i = a}`. The
> permutations fixing `f` fibrewise are exactly a choice of permutation of each fibre.
>
> **`card_stab`** — so there are `∏ a, (card of the fibre over a)!` of them.

**Absent from Mathlib, probed in both directions** (`ERRATUM 379`'s rule): `Equiv.Perm.*` names
pairing with `fiber`/`Fiber`/`preserv`/`invariant` are **0**, and the pieces this is built from —
`Equiv.sigmaFiberEquiv`, `Equiv.Perm.sigmaCongrRight`, `Equiv.Perm.subtypePerm` — exist without
anything joining them. The nearest statement is `Equiv.Perm.sigmaCongrRightHom.card_range`, which
counts the range of the gluing map inside `Perm (Σ a, β a)` and says nothing about a function on a
bare type.

## The two-block case is already here, under these four names

`PairingSplit`, `PairingRestrict` and `PairingGlue` build **exactly this construction for a
two-block split**, and share four of this file's names — `glue`, `restrict`, `glue_restrict`,
`restrict_glue` — which is deliberate rather than accidental. The correspondence is exact:
`PairingSplit.RespectsSplit S σ` (`∀ i, σ i ∈ S ↔ i ∈ S`) is `∀ i, f (σ i) = f i` at
`f := fun i => decide (i ∈ S)`; `PairingGlue.glue` is `Equiv.Perm.subtypeCongr` where this file
uses `Equiv.Perm.sigmaCongrRight`; and `PairingGlue.restrict_glue`/`glue_restrict` are the same two
round trips. **This file is that construction with the two blocks replaced by the fibres of an
arbitrary function.**

**The recovery is NOT proved** (`ERRATUM 201`'s discipline, and its cost is not offered —
`ERRATUM 194`, `ERRATUM 246`). It is not a rewrite: the two-block form is a **product** of two
permutation groups and this one is a `∀ a : Bool` indexed family, and
`{i // decide (i ∈ S) = true}` is not `{x // x ∈ S}` on the nose. What is claimed here is that the
constructions correspond, which is why the names are shared, and nothing about either implying the
other in Lean.

## What this is NOT

**It is not the multinomial count.** That needs this together with transitivity — two functions
with equal fibre cardinalities differ by a permutation, which this estate has at
`TorusOrbitCharacterisation.mem_orbit_of_card_eq` — and the cancellation against
`Nat.multinomial_spec`. Neither is here, and no cost is offered for them (`ERRATUM 194`,
`ERRATUM 246`).

**Nothing here is about the torus.** `f` is an arbitrary function between a `Fintype` and a type
with decidable equality; the consumer is named above rather than assumed.
-/

namespace FibrewiseStabiliser

open Equiv Function

variable {ι α : Type*} {f : ι → α}

/-! ## 1. Gluing permutations of the fibres -/

/-- A permutation of each fibre of `f`, glued into a permutation of the domain. -/
def glue (f : ι → α) (p : ∀ a, Perm {i // f i = a}) : Perm ι :=
  (Equiv.sigmaFiberEquiv f).permCongr (Equiv.Perm.sigmaCongrRight p)

/-- The glued permutation, evaluated: it moves `i` by the permutation of `i`'s own fibre. -/
theorem glue_apply (p : ∀ a, Perm {i // f i = a}) (i : ι) :
    glue f p i = ((p (f i)) ⟨i, rfl⟩ : {j // f j = f i}).val := rfl

/-- **GLUING FIXES `f`.** -/
theorem f_glue (p : ∀ a, Perm {i // f i = a}) (i : ι) : f (glue f p i) = f i := by
  rw [glue_apply]
  exact ((p (f i)) ⟨i, rfl⟩).property

/-! ## 2. Restricting a permutation that fixes `f` -/

/-- A permutation fixing `f` restricts to each fibre. -/
def restrict {σ : Perm ι} (hσ : ∀ i, f (σ i) = f i) (a : α) : Perm {i // f i = a} :=
  σ.subtypePerm fun i => by rw [hσ i]

@[simp] theorem restrict_apply {σ : Perm ι} (hσ : ∀ i, f (σ i) = f i) (a : α)
    (x : {i // f i = a}) : (restrict hσ a x).val = σ x.val := rfl

/-- **RESTRICTING THEN GLUING IS THE IDENTITY.** -/
theorem glue_restrict {σ : Perm ι} (hσ : ∀ i, f (σ i) = f i) : glue f (restrict hσ) = σ := by
  ext i
  rw [glue_apply]
  exact restrict_apply hσ (f i) ⟨i, rfl⟩

/-- **GLUING THEN RESTRICTING IS THE IDENTITY.** -/
theorem restrict_glue (p : ∀ a, Perm {i // f i = a}) :
    restrict (f_glue p) = p := by
  funext a
  apply Equiv.ext
  rintro ⟨i, rfl⟩
  apply Subtype.ext
  rw [restrict_apply, glue_apply]

/-! ## 3. The stabiliser, identified -/

/-- **THE PERMUTATIONS FIXING `f` FIBREWISE ARE EXACTLY A CHOICE OF PERMUTATION OF EACH FIBRE.** -/
def stabEquiv (f : ι → α) :
    {σ : Perm ι // ∀ i, f (σ i) = f i} ≃ ∀ a, Perm {i // f i = a} where
  toFun σ := restrict σ.property
  invFun p := ⟨glue f p, f_glue p⟩
  left_inv σ := Subtype.ext (glue_restrict σ.property)
  right_inv p := restrict_glue p

/-! ## 4. And counted -/

variable [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- **SO THERE ARE `∏ₐ (fibre over a)!` OF THEM.** This is the stabiliser factor an
orbit–stabiliser count of functions with prescribed fibre sizes consumes. -/
theorem card_stab (f : ι → α) :
    Fintype.card {σ : Perm ι // ∀ i, f (σ i) = f i}
      = ∏ a : α, Nat.factorial (Fintype.card {i // f i = a}) := by
  rw [Fintype.card_congr (stabEquiv f), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => Fintype.card_perm

end FibrewiseStabiliser
