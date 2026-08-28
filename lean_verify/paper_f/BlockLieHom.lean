import Mathlib.Algebra.Lie.Prod
import BlockLieMorphism

/-!
# `sl(p) ⊕ sl(q) ⊕ ℂ` is a Lie algebra, and `blockDiagMap` is a `LieHom` onto its image

`BlockLieMorphism` proved the intertwining equation and then fenced what it had not done:

> *"No `LieAlgebra` structure is put on the product `sl(p) × sl(q) × ℂ`. `prodBracket` is a
> function, not a `LieRing` instance … `blockDiagMap` is not exhibited here as a `LieHom`."*

Both halves come off here, and neither needed new mathematics — only the right import. Mathlib
gives a `LieRing` on a product (`Mathlib/Algebra/Lie/Prod.lean`), a `LieRing` on `ℂ` from its ring
structure, and a `LieRing` on any `LieSubalgebra`'s subtype. Since
`BlockGrading.sl_toSubmodule` makes `tracelessSub ι` the carrier of `sl ι ℂ`, **`blockDiagMap`
typechecks unchanged as a linear map between the two Lie algebras**; all that was missing was the
bracket condition, which is `BlockLieMorphism.blockDiagMap_lie`.

## What is proved

> **`prod_lie`** — the product bracket is componentwise, by `rfl`, and **`prod_lie_scalar`** — its
> `ℂ` component is always `0`, because `ℂ` is commutative. So *"the `ℂ` factor is central"* is a
> property of Mathlib's structure and not a choice made in this chain.
>
> **`prodBracket_eq`** — `BlockLieMorphism.prodBracket` **was** Mathlib's product bracket, which is
> why the previous unit's equation says what it appeared to say. The two agree on the nose in the
> first two components and by `a * b = b * a` in the third.
>
> **`blockDiagHom`** — the bundled `SlProd p q →ₗ⁅ℂ⁆ sl(p+q)`, with `blockDiagMap` as its linear
> part and `blockDiagMap_lie` as its `map_lie'`.
>
> **`blockDiagEquiv`** at `0 < p`, `0 < q` — a `LieEquiv` from `sl(p) ⊕ sl(q) ⊕ ℂ` **onto its
> range**, from `LieEquiv.ofInjective` and `BlockDiagonalSplit.blockDiagMap_injective`.
>
> **`range_toSubmodule_eq_ker`** — that range's underlying submodule is exactly
> `BlockOffDiagonal.offDiagMap`'s kernel. So the space `BlockOffDiagonal` counted, that
> `BlockDiagonalSplit` exhibited as three summands, and that `BlockGrading` identified with the
> even part of a ℤ/2-grading, **is the isomorphic image of a Lie algebra under a Lie algebra
> isomorphism** — which is the whole of what the chain's prose has been claiming since it began
> calling these things `sl(p)` and `sl(q)`.

## What is NOT claimed

**No new mathematics, and the file says so in its length.** Every theorem here is a repackaging of
`BlockLieMorphism`'s content into Mathlib's structures. The one thing that is genuinely new is
`prodBracket_eq`, and it is new only in the sense that the previous unit could not state it
without this import.

**The isomorphism is onto `blockDiagHom`'s range, not onto a separately named subalgebra.**
`BlockLieMorphism.evenSlLie` is a `LieSubalgebra` of the **matrices**; `(blockDiagHom p q).range`
is a `LieSubalgebra` of the **subtype** `sl(p+q)`. Their underlying sets correspond under
`(sl (Fin p ⊕ Fin q) ℂ).incl`, and **that correspondence is not built here** — no `LieSubalgebra`
comap or map is taken, and no theorem below mentions `evenSlLie`.

**Nothing about the odd part.** It is a module over the even part and this file does not say so;
`BlockGrading`'s fence on `LieModule` stands unchanged.

**No roots, no Cartan subalgebra, no semisimplicity, no Killing form, nothing over `ℝ`, nothing
about `su(n)`, no physics.**

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockLieHom

open Matrix LieAlgebra.SpecialLinear SlAbelianGeneral BlockOffDiagonal BlockDiagonalSplit
open BlockLieMorphism

variable {p q : ℕ}

/-! ## 1. The product, with Mathlib's structure -/

/-- `sl(p) ⊕ sl(q) ⊕ ℂ`, carrying Mathlib's product Lie algebra structure. -/
abbrev SlProd (p q : ℕ) : Type :=
  (sl (Fin p) ℂ) × (sl (Fin q) ℂ) × ℂ

/-- The product bracket is componentwise — this is Mathlib's definition, not a choice made here. -/
theorem prod_lie (x y : SlProd p q) :
    ⁅x, y⁆ = (⁅x.1, y.1⁆, ⁅x.2.1, y.2.1⁆, ⁅x.2.2, y.2.2⁆) := rfl

/-- **THE `ℂ` FACTOR IS CENTRAL FOR A REASON THAT IS NOT THIS CHAIN'S DOING**: `ℂ` is commutative,
so its bracket is identically zero. -/
theorem prod_lie_scalar (x y : SlProd p q) : (⁅x, y⁆ : SlProd p q).2.2 = 0 := by
  rw [prod_lie]
  simp [Ring.lie_def, mul_comm]

/-- **`prodBracket` WAS MATHLIB'S PRODUCT BRACKET.** The previous unit's intertwining equation is
therefore about the structure, not about a function invented to make it true. -/
theorem prodBracket_eq (x y : SlProd p q) : prodBracket x y = ⁅x, y⁆ := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp [prodBracket, Ring.lie_def, mul_comm]

/-! ## 2. The bundled morphism -/

/-- **`blockDiagMap`, BUNDLED AS A MORPHISM OF LIE ALGEBRAS.** Its linear part is unchanged: the
carriers of `sl ι ℂ` and `tracelessSub ι` are the same object (`BlockGrading.sl_toSubmodule`), so
no transport is involved. -/
noncomputable def blockDiagHom (p q : ℕ) : SlProd p q →ₗ⁅ℂ⁆ (sl (Fin p ⊕ Fin q) ℂ) where
  toLinearMap := blockDiagMap
  map_lie' := by
    intro x y
    apply Subtype.ext
    rw [← prodBracket_eq]
    exact (blockDiagMap_lie x y).symm

theorem blockDiagHom_coe (x : SlProd p q) :
    ((blockDiagHom p q x : sl (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
      = blockDiagOf (x.1 : Matrix (Fin p) (Fin p) ℂ) (x.2.1 : Matrix (Fin q) (Fin q) ℂ) x.2.2 :=
  rfl

theorem blockDiagHom_injective (hp : 0 < p) (hq : 0 < q) :
    Function.Injective (blockDiagHom p q) :=
  blockDiagMap_injective hp hq

/-! ## 3. The isomorphism onto the image -/

/-- **`sl(p) ⊕ sl(q) ⊕ ℂ` IS ISOMORPHIC, AS A LIE ALGEBRA, TO ITS IMAGE IN `sl(p+q)`.** -/
noncomputable def blockDiagEquiv (hp : 0 < p) (hq : 0 < q) :
    SlProd p q ≃ₗ⁅ℂ⁆ (blockDiagHom p q).range :=
  LieEquiv.ofInjective _ (blockDiagHom_injective hp hq)

theorem range_toSubmodule :
    ((blockDiagHom p q).range).toSubmodule
      = LinearMap.range (blockDiagMap (p := p) (q := q)) :=
  LieHom.range_toSubmodule _

/-- **AND THAT IMAGE IS THE KERNEL THE WHOLE CHAIN HAS BEEN ABOUT.** `BlockOffDiagonal` counted it,
`BlockDiagonalSplit` exhibited it as three summands, `BlockGrading` identified it with the even
part of a ℤ/2-grading, and it is the image of a Lie algebra isomorphism. -/
theorem range_toSubmodule_eq_ker (hp : 0 < p) (hq : 0 < q) :
    ((blockDiagHom p q).range).toSubmodule
      = LinearMap.ker (offDiagMap (p := p) (q := q)) := by
  rw [range_toSubmodule, range_blockDiagMap_eq_ker hp hq]

end BlockLieHom
