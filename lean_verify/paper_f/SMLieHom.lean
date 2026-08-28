import SMEmbeddingHonest
import BlockLieHom

/-!
# Each factor is a `LieHom`; the assembly cannot be one

`LieAlgebraEmbedding` proves, for each of its three maps into `sl₄(ℂ)`, that
`embed(AB − BA) = embed(A)embed(B) − embed(B)embed(A)`, and its docstrings call this *"the
GENUINE LIE ALGEBRA HOMOMORPHISM PROPERTY … a genuine morphism of Lie algebras sl₃(ℂ) → sl₄(ℂ)"*.
It then reads the package as *"the GENUINE proof that the Standard Model gauge algebra embeds in
su(4) as a Lie subalgebra"*.

**`SMEmbeddingHonest` machine-checked that last reading FALSE weeks ago** (`ERRATA 36`), by showing
the `sl₃` and `sl₂` images do not commute — the blocks share row and column `2` — and that the
assembled linear map has a nonzero kernel and an 11-dimensional range that is not bracket-closed.
**Nothing here re-derives any of that**, and `LieAlgebraEmbedding` carried no pointer to its own
refutation until this file added one.

What today's `sl` identification adds is that both halves can now be said in Mathlib's own
vocabulary, and that the negative can be sharpened from *"the images do not commute"* to
**"no such morphism exists at all"**.

## What is proved

> **`su3Hom`, `su2Hom`, `u1Hom`** — the three maps as honest `LieHom`s into
> `LieAlgebra.SpecialLinear.sl (Fin 4) ℂ`. **Nothing is reproved**: the linear parts are
> `LieAlgebraEmbedding`'s `*EmbedRestricted` **unchanged**, because
> `BlockGrading.sl_toSubmodule` makes `TracelessMatrix n` the carrier of `sl (Fin n) ℂ`, and each
> `map_lie'` is that file's existing bracket theorem, which `Ring.lie_def` makes a statement about
> `⁅·,·⁆` on the nose.
>
> **`no_lieHom_assembling`** — **there is no `LieHom` from `sl₃(ℂ) × sl₂(ℂ) × ℂ` to `sl₄(ℂ)` whose
> first two components are these maps.** In a product the factors commute, a morphism carries that
> to the images, and `SMEmbeddingHonest.su3_su2_images_not_commuting` says the images do not. This
> is the statement *"the Standard Model gauge algebra embeds as a Lie subalgebra"* would need, and
> it is refuted rather than left unproved.

## What is NOT claimed

**Nothing in `SMEmbeddingHonest` is repeated, improved or superseded.** The overlap, the
non-injective assembly, the 11-dimensional range, the failure of bracket-closure and the honest
positive (colour ⊕ `B−L`) are all proved there and are all cited, not restated. **This file adds
one theorem to that work and bundles three maps.**

**`no_lieHom_assembling` fixes the first two components only.** It does not say no morphism from
that product to `sl₄(ℂ)` exists — the zero map is one — and it says nothing about any *other*
choice of embeddings. **The impossibility is of assembling THESE maps**, which is what the
docstring being corrected asserts.

**Nothing about `su(4)`.** The codomain throughout is `sl₄(ℂ)`, complex, of complex dimension
`15`; `su(4)` is real of real dimension `15` and `TracelessRealSplit.finrank_four` separates them.
The corrected docstring says `su(4)` and means `sl₄(ℂ)` — `ERRATUM 325`'s second family, and
`SMEmbeddingHonest`'s own naming paragraph already flags the convention.

**No `LieSubalgebra` is built for any image**, and no `LieEquiv` onto a range is exhibited.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SMLieHom

open Matrix LieAlgebra.SpecialLinear SMEmbeddingHonest

/-! ## 1. The three maps, bundled -/

/-- **`sl₃(ℂ) → sl₄(ℂ)` AS A `LieHom`.** The linear part is `LieAlgebraEmbedding`'s map unchanged
and `map_lie'` is its existing bracket theorem. -/
noncomputable def su3Hom : (sl (Fin 3) ℂ) →ₗ⁅ℂ⁆ (sl (Fin 4) ℂ) where
  toLinearMap := su3EmbedRestricted
  map_lie' := by
    intro A B
    apply Subtype.ext
    exact su3Embed_bracket _ _

/-- **`sl₂(ℂ) → sl₄(ℂ)` AS A `LieHom`.** -/
noncomputable def su2Hom : (sl (Fin 2) ℂ) →ₗ⁅ℂ⁆ (sl (Fin 4) ℂ) where
  toLinearMap := su2EmbedRestricted
  map_lie' := by
    intro A B
    apply Subtype.ext
    exact su2Embed_bracket _ _

/-- **`u(1) → sl₄(ℂ)` AS A `LieHom`.** Both brackets are zero: `ℂ` is commutative and the images
commute with each other. -/
noncomputable def u1Hom : ℂ →ₗ⁅ℂ⁆ (sl (Fin 4) ℂ) where
  toLinearMap := u1EmbedRestricted
  map_lie' := by
    intro a b
    apply Subtype.ext
    have hzero : (⁅a, b⁆ : ℂ) = 0 := by
      rw [Ring.lie_def]
      ring
    rw [hzero]
    have : u1EmbedFn a * u1EmbedFn b - u1EmbedFn b * u1EmbedFn a = 0 := u1Embed_bracket a b
    simpa [map_zero] using this.symm

theorem su3Hom_injective : Function.Injective su3Hom := su3EmbedRestricted_injective

theorem su2Hom_injective : Function.Injective su2Hom := su2EmbedRestricted_injective

theorem u1Hom_injective : Function.Injective u1Hom := u1EmbedRestricted_injective

/-! ## 2. And they cannot be assembled -/

/-- The `sl₃` witness of `SMEmbeddingHonest`, as an element of `sl (Fin 3) ℂ`. -/
noncomputable def e02Sl : sl (Fin 3) ℂ := ⟨e02, e02_mem⟩

/-- The `sl₂` witness, as an element of `sl (Fin 2) ℂ`. -/
noncomputable def d2Sl : sl (Fin 2) ℂ := ⟨d2, d2_mem⟩

theorem lie_su3Hom_su2Hom_ne_zero : ⁅su3Hom e02Sl, su2Hom d2Sl⁆ ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  have hsub : su3EmbedFn e02 * su2EmbedFn d2 - su2EmbedFn d2 * su3EmbedFn e02 = 0 := by
    simpa using hval
  exact su3_su2_images_not_commuting (sub_eq_zero.mp hsub)

/-- **NO `LieHom` FROM THE PRODUCT HAS THESE TWO COMPONENTS.** In `sl₃(ℂ) × sl₂(ℂ) × ℂ` the
factors commute; a morphism carries that to the images; the images do not commute
(`SMEmbeddingHonest.su3_su2_images_not_commuting`). This is exactly what *"the Standard Model
gauge algebra embeds in `sl₄(ℂ)` as a Lie subalgebra"* would require. -/
theorem no_lieHom_assembling :
    ¬ ∃ F : ((sl (Fin 3) ℂ) × (sl (Fin 2) ℂ) × ℂ) →ₗ⁅ℂ⁆ (sl (Fin 4) ℂ),
        (∀ A, F (A, 0, 0) = su3Hom A) ∧ (∀ B, F (0, B, 0) = su2Hom B) := by
  rintro ⟨F, h3, h2⟩
  have hzero : (⁅((e02Sl, 0, 0) : (sl (Fin 3) ℂ) × (sl (Fin 2) ℂ) × ℂ),
      ((0, d2Sl, 0) : (sl (Fin 3) ℂ) × (sl (Fin 2) ℂ) × ℂ)⁆) = 0 := by
    simp
  have hL : F ⁅((e02Sl, 0, 0) : (sl (Fin 3) ℂ) × (sl (Fin 2) ℂ) × ℂ),
      ((0, d2Sl, 0) : (sl (Fin 3) ℂ) × (sl (Fin 2) ℂ) × ℂ)⁆ = 0 := by
    rw [hzero, map_zero]
  rw [LieHom.map_lie, h3, h2] at hL
  exact lie_su3Hom_su2Hom_ne_zero hL

end SMLieHom
