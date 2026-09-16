/-
  SupportedOn: the functions vanishing off a finite set, over ANY module, at rank
  `#H · finrank W`

  WHY THIS FILE EXISTS. `RE-SWEEP #59` found the estate holding the same construction three
  times. `UNLOCK_WATCHLIST` L26329 is an item about two of them — `NullSpaceDimension.supportedOn`
  (a `Submodule ℝ (V → ℝ)`, referenced in fourteen files) and `GreenDomainMonotone.extZero` — and
  unit 73's `HermitianSignatureEigenvalues.coordSupp` (a `Submodule ℝ (Fin n → ℂ)`) was the third,
  written without anybody noticing the item. **The resemblance is not loose: the two `Submodule`
  versions agree lemma for lemma modulo the prefix** — `mem_supportedOn` against `mem_coordSupp`,
  condition for condition, and `finrank_supportedOn = #H` against `finrank_coordSupp = 2 · #S`.
  **The only difference is the codomain**, and the rank differs by exactly its dimension.

  So this file is one theorem with the two as instances, which is `PROOF_STRATEGY` §7 item 3
  (*deepen, don't broaden — take a result proved under restrictive hypotheses and remove one*).
  The hypothesis removed is **the codomain being the scalars**.

  **AND THE IMPORT DIRECTION IS THE POINT, NOT AN ACCIDENT** (`ERRATUM 576`): a file that
  generalises an old one must be the BASE, or the import graph asserts the opposite of the header.
  So `NullSpaceDimension` and `HermitianSignatureEigenvalues` import this and define their own
  objects as instances of it, rather than this file re-deriving theirs.

  WHAT IS PROVED.
  * **`supportedOn H`** — the `R`-submodule of `V → W` of functions vanishing off `H`, for ANY
    `R`-module `W`. `mem_supportedOn` is `Iff.rfl`, as in both originals.
  * **`supportedOnEquiv`** — restriction to `H` is an `R`-linear isomorphism onto `H → W`.
    Classical decidability is used for the extension by zero, so that neither `Fintype V` nor
    `DecidableEq V` appears in any statement here — this is general linear algebra and must not
    carry a caller's instances. That reasoning is `NullSpaceDimension`'s own, kept verbatim.
  * **`finrank_supportedOn`** — **`finrank R (supportedOn H) = #H · finrank R W`**, off
    `Module.finrank_pi_fintype` at a constant family. At `W = R` this is `#H`, at `W = ℂ` over
    `ℝ` it is `2 · #H`, and the two estate constructions are those two cases.
  * **`finrank_supportedOn_self`** — the `W = R` case stated separately, because that is the one
    fourteen files use and it should not require a reader to evaluate `finrank R R`.

  WHAT IS **NOT** CLAIMED.
  * **Nothing about `GreenDomainMonotone.extZero`**, which L26329 names as the second of its two.
    That one is a plain FUNCTION along an injection `W → V`, not a submodule, so it is a different
    object with a similar name and this file does not subsume it. **The item's complaint was about
    three names for two ideas; this file merges the two that are one idea and leaves the third
    alone, deliberately.**
  * **No infinite-dimensional statement.** `Module.Finite R W` is assumed for the rank, and
    `Module.Free R W` with `StrongRankCondition R` for `finrank_pi_fintype` to apply.
  * **Nothing about the cascade, the spine, or any wall.** This is a dedup with a generalisation
    attached; it moves no verdict anywhere, and `RE-SWEEP #59` records that it unlocks nothing.

  0 sorry. 0 new axioms. `#print axioms`, stated exactly rather than rounded up: `supportedOn`
  and `mem_supportedOn` are on **[propext, Quot.sound]** — no choice at all, the submodule being
  a bare carrier condition — and the three that go through the restriction equivalence are on
  [propext, Classical.choice, Quot.sound], the choice being the `Classical` decidability the
  extension by zero uses.
-/

import Mathlib.LinearAlgebra.Dimension.Constructions

namespace SupportedOn

variable {V : Type*} {R : Type*} {W : Type*}

section Module

variable [Semiring R] [AddCommMonoid W] [Module R W]

/-- The functions `V → W` vanishing off a finite set `H`, as an `R`-submodule. -/
def supportedOn (H : Finset V) : Submodule R (V → W) where
  carrier := {v | ∀ p, p ∉ H → v p = 0}
  add_mem' := by intro u v hu hv p hp; simp [hu p hp, hv p hp]
  zero_mem' := by intro p _; rfl
  smul_mem' := by intro c v hv p hp; simp [hv p hp]

@[simp] theorem mem_supportedOn {H : Finset V} {v : V → W} :
    v ∈ supportedOn (R := R) H ↔ ∀ p, p ∉ H → v p = 0 := Iff.rfl

open scoped Classical in
/-- Restriction to `H` is an `R`-linear isomorphism onto the functions on `H`. Classical
decidability is used for the extension by zero, so that neither `Fintype V` nor `DecidableEq V`
appears in this file's statements. -/
noncomputable def supportedOnEquiv (H : Finset V) :
    supportedOn (R := R) (W := W) H ≃ₗ[R] (H → W) where
  toFun v := fun p => (v : V → W) ↑p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun p => if h : p ∈ H then w ⟨p, h⟩ else 0, by
    intro p hp; exact dif_neg hp⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext p
    dsimp only
    by_cases h : p ∈ H
    · exact dif_pos h
    · rw [dif_neg h]
      exact ((mem_supportedOn (R := R)).1 v.2 p h).symm
  right_inv := by
    intro w
    funext p
    exact dif_pos p.2

end Module

section Rank

variable [Semiring R] [StrongRankCondition R] [AddCommMonoid W] [Module R W]
variable [Module.Free R W] [Module.Finite R W]

/-- **The rank, with the codomain free.** `#H` copies of `W`, so `#H · finrank W`. At `W = R`
this is `#H` and at `W = ℂ` over `ℝ` it is `2 · #H`. -/
theorem finrank_supportedOn (H : Finset V) :
    Module.finrank R (supportedOn (R := R) (W := W) H) = H.card * Module.finrank R W := by
  rw [(supportedOnEquiv (R := R) (W := W) H).finrank_eq,
    Module.finrank_pi_fintype R (M := fun _ : H => W)]
  simp

/-- The scalar case, stated on its own because it is the one the estate's fourteen
`supportedOn` files use. -/
theorem finrank_supportedOn_self (H : Finset V) :
    Module.finrank R (supportedOn (R := R) (W := R) H) = H.card := by
  rw [finrank_supportedOn, Module.finrank_self, mul_one]

end Rank

end SupportedOn
