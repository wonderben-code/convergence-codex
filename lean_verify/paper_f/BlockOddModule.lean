import BlockLieMorphism

/-!
# The odd part is a module over the even part, and the action is `B ↦ A·B − B·D`

`BlockGrading` proved `⁅even, odd⁆ ⊆ odd` and then fenced what that does not say:

> *"`lie_evenPart_oddPart` says the bracket lands back in `oddPart`; it does not build a
> `LieRingModule` or a `LieModule` instance, and no theorem here says the odd part is a
> representation of the even part."*

This file removes that fence and computes the representation.

## What is proved

> **`evenMod` and `oddMod`** — both graded pieces as `LieSubmodule ℂ ↥(evenLie p q) (Matrix …)`,
> so the odd part is a module over the even Lie subalgebra in Mathlib's own sense. The
> `LieRingModule` and `LieModule` instances come from `LieSubalgebra.lieRingModule` and
> `LieSubalgebra.lieModule` — **nothing is verified here**; the only input is `BlockGrading`'s two
> bracket rules.
>
> **`lie_fromBlocks_off`** — the action, in blocks:
> `⁅fromBlocks A 0 0 D, fromBlocks 0 B C 0⁆ = fromBlocks 0 (A·B − B·D) (D·C − C·A) 0`.
> **The upper rectangle transforms as `B ↦ A·B − B·D`**, which is the standard action on
> `Hom(ℂ^q, ℂ^p)`, and the lower as `C ↦ D·C − C·A` on `Hom(ℂ^p, ℂ^q)`. This is the sentence the
> physics reading wants and it is here as a matrix identity with no reading attached.
>
> **`sup_eq_top` and `inf_eq_bot`** — the two pieces are complementary **in the lattice of
> `evenLie`-submodules**, not merely in the lattice of `ℂ`-submodules, which is what makes the
> ℤ/2-grading a decomposition of representations.
>
> **`oddMod_ne_bot`** at `0 < p`, `0 < q` — the module is not the zero module, so the previous
> line is not vacuous.

## What is NOT claimed

**Nothing about irreducibility.** Whether `oddMod` is an irreducible `evenLie`-module is **not
proved and not begun**; no `LieModule.IsIrreducible` is mentioned, and the natural first guess is
false as stated, since the odd part visibly splits into the two rectangles as `ℂ`-modules and
whether that splitting is `evenLie`-stable is a question this file does not ask.

**No weight theory, no Cartan subalgebra, no roots.** The eigenvalue `±(p+q)c` computed in
`BlockLieMorphism.lie_centreOf_offDiagOf` is **not** presented as a weight, and no weight space
decomposition is built.

**No tensor identification.** That the odd part "is" `Hom(ℂ^q, ℂ^p) ⊕ Hom(ℂ^p, ℂ^q)` as a module
is **not** stated: `lie_fromBlocks_off` gives the formula on blocks, and no isomorphism to a
tensor product or a Hom-module is constructed.

**Nothing over `ℝ`, nothing about `su(n)`, no physics, no roots, no semisimplicity.**

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockOddModule

open Matrix SlAbelianGeneral BlockOffDiagonal BlockGrading

variable {p q : ℕ}

/-! ## 1. The two pieces as modules over the even subalgebra -/

/-- The even part, as a module over itself. -/
noncomputable def evenMod (p q : ℕ) :
    LieSubmodule ℂ (evenLie p q) (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := evenPart p q
  lie_mem {x _m} h := lie_evenPart_evenPart x.property h

/-- **THE ODD PART, AS A MODULE OVER THE EVEN PART.** -/
noncomputable def oddMod (p q : ℕ) :
    LieSubmodule ℂ (evenLie p q) (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := oddPart p q
  lie_mem {x _m} h := lie_evenPart_oddPart x.property h

theorem evenMod_toSubmodule : (evenMod p q).toSubmodule = evenPart p q := rfl

theorem oddMod_toSubmodule : (oddMod p q).toSubmodule = oddPart p q := rfl

/-- The action is the commutator with the underlying matrix; there is no separate definition. -/
theorem lie_coe (x : evenLie p q) (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    ⁅x, M⁆ = (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * M
      - M * (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := rfl

/-! ## 2. The action, in blocks -/

/-- **`B ↦ A·B − B·D` AND `C ↦ D·C − C·A`.** The two rectangles are acted on from the left by one
diagonal block and from the right by the other. -/
theorem lie_fromBlocks_off (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    ⁅Matrix.fromBlocks A 0 0 D, Matrix.fromBlocks 0 B C 0⁆
      = Matrix.fromBlocks 0 (A * B - B * D) (D * C - C * A) 0 := by
  rw [Ring.lie_def, diag_mul_off, off_mul_diag, BlockLieMorphism.fromBlocks_off_sub]

/-- The same statement with the acting element taken from `evenLie`, which is where the module
structure reads it. -/
theorem lie_mem_oddMod_apply (x : evenLie p q) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) :
    ⁅x, offDiagOf B C⁆
      = Matrix.fromBlocks 0
          ((x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * B
            - B * (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂)
          ((x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂ * C
            - C * (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁) 0 := by
  obtain ⟨A, D, hAD⟩ := exists_of_mem_evenPart x.property
  rw [lie_coe, ← Ring.lie_def, hAD, offDiagOf, lie_fromBlocks_off]
  congr 1

/-! ## 3. The grading is a decomposition of modules -/

/-- **COMPLEMENTARY IN THE LATTICE OF `evenLie`-SUBMODULES**, not only of `ℂ`-submodules. -/
theorem sup_eq_top : evenMod p q ⊔ oddMod p q = ⊤ := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule, evenMod_toSubmodule,
    oddMod_toSubmodule]
  exact codisjoint_iff.mp isCompl_evenPart_oddPart.codisjoint

theorem inf_eq_bot : evenMod p q ⊓ oddMod p q = ⊥ := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [LieSubmodule.inf_toSubmodule, LieSubmodule.bot_toSubmodule, evenMod_toSubmodule,
    oddMod_toSubmodule]
  exact disjoint_iff.mp isCompl_evenPart_oddPart.disjoint

/-- **AND THE ODD MODULE IS NOT ZERO**, so the line above is not vacuous. -/
theorem oddMod_ne_bot (hp : 0 < p) (hq : 0 < q) : oddMod p q ≠ ⊥ := by
  intro h
  have hsub : oddPart p q = ⊥ := by
    rw [← oddMod_toSubmodule, h, LieSubmodule.bot_toSubmodule]
  have hmem : offDiagOf (allOnes p q) 0 ∈ oddPart p q := fromBlocks_off_mem _ _
  rw [hsub, Submodule.mem_bot] at hmem
  have hval := congrFun (congrFun hmem (Sum.inl ⟨0, hp⟩)) (Sum.inr ⟨0, hq⟩)
  simp only [offDiagOf, Matrix.fromBlocks_apply₁₂, allOnes, Matrix.of_apply,
    Matrix.zero_apply] at hval
  exact one_ne_zero hval

end BlockOddModule
