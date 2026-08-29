import SuBlockIdentification
import BlockOddModule

open Matrix

/-!
# The odd piece as a module over the even part, over `ℝ` — and it is not a decomposition of `⊤`

`BlockOddModule` made `BlockGrading`'s two pieces into `LieSubmodule ℂ`s over the even
subalgebra, and fenced the real case: *"Nothing over `ℝ`, nothing about `su(n)`."*
`SuGradedLieAlgebra` fenced it again, by name: *"**No `LieSubmodule` for the odd piece**, over
`ℝ` or otherwise; `BlockOddModule`'s analogue is still unwritten."* This file writes it.

**The interesting part is that it is not the same statement.** Over `ℂ`,
`BlockOddModule.sup_eq_top` says the two pieces span **everything**: `evenMod ⊔ oddMod = ⊤` in
the lattice of `evenLie`-submodules of `Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ`. Over `ℝ` that
is **false**, and this file proves it is false rather than quietly stating the weaker theorem:
`SuBlockGrading.sup_eq` gives `suEven ⊔ suOdd = tracelessSkewMat`, a **proper** submodule of the
same ambient space, because skew-Hermiticity is a real condition that cuts the ambient space down
before the block grading ever acts. The identity matrix is the witness.

## What is proved

> **`suEvenMod`, `suOddMod`** — the two pieces as `LieSubmodule ℝ ↥(suEvenLie p q)` of the
> matrices, from `SuBlockGrading`'s `lie_suEven_suEven` and `lie_suEven_suOdd`. Exactly
> `BlockOddModule`'s definitions with the scalars changed; the brackets were already proved.
>
> **`tracelessSkewMod`** — the ambient traceless skew-Hermitian space is itself a module over the
> even part, which is what makes the next statement expressible at all.
>
> **`sup_eq_tracelessSkewMod`** and **`inf_eq_bot`** — the grading is a decomposition **of
> `tracelessSkewMod`**, in the lattice of `suEvenLie`-submodules and not merely of `ℝ`-submodules.
>
> **`tracelessSkewMod_ne_top`** and **`sup_ne_top`** — **and it is not a decomposition of `⊤`**,
> witnessed by `1`, which is Hermitian rather than skew-Hermitian. This is the real content of the
> difference with `BlockOddModule` and it is a theorem here rather than a remark.
>
> **`suOddMod_ne_bot`** — the odd module is nonzero whenever both blocks are, so none of the above
> is vacuous. From `SuBlockIdentification.finrank_suOdd = 2pq`, which is a dimension rather than a
> witness — a different route from `BlockOddModule.oddMod_ne_bot`, which exhibits a matrix.

## What is NOT claimed

**The ambient module is still `Matrix … ℂ`, not `↥(tracelessSkewLie …)`.** Everything below lives
in the lattice of `suEvenLie`-submodules of the full matrix space; the traceless skew-Hermitian
matrices appear as a `LieSubmodule` of it, not as the ambient object. Restating the grading with
`tracelessSkewLie` as the ambient module is a different construction and is **not** done here.

**No `GradedLieAlgebra` and no `DirectSum`.** `SuGradedLieAlgebra` already carries the graded
structure at the level of `Submodule ℝ`; nothing below re-derives it or upgrades it to modules.

**No group, no compactness, no roots, no semisimplicity**, and the name `su` is used for no
declaration, following `F4_1e_SpectralTripleArithmetic`'s written decision — as `SuBlockGrading`
and `SuGradedLieAlgebra` also do.

**Nothing over `ℂ` is withdrawn.** `BlockOddModule.sup_eq_top` is true over `ℂ` and keeps its
proof; the failure proved here is a fact about the real form, not a correction to it.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SuBlockOddModule

open SuBlockGrading SuBlockIdentification TracelessSkewLie

variable {p q : ℕ}

/-! ## 1. The three modules -/

/-- The even part, as a module over itself. -/
noncomputable def suEvenMod (p q : ℕ) :
    LieSubmodule ℝ (suEvenLie p q) (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := suEven p q
  lie_mem {x _m} h := lie_suEven_suEven x.property h

/-- **THE ODD PART, AS A MODULE OVER THE EVEN PART, OVER `ℝ`.** The statement
`SuGradedLieAlgebra` recorded as unwritten. -/
noncomputable def suOddMod (p q : ℕ) :
    LieSubmodule ℝ (suEvenLie p q) (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := suOdd p q
  lie_mem {x _m} h := lie_suEven_suOdd x.property h

/-- The ambient traceless skew-Hermitian space is a module over the even part too — needed to
say what the grading decomposes, since over `ℝ` the answer is not `⊤`. -/
noncomputable def tracelessSkewMod (p q : ℕ) :
    LieSubmodule ℝ (suEvenLie p q) (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := tracelessSkewMat (Fin p ⊕ Fin q)
  lie_mem {x _m} h := (tracelessSkewLie (Fin p ⊕ Fin q)).lie_mem x.property.2 h

theorem suEvenMod_toSubmodule : (suEvenMod p q).toSubmodule = suEven p q := rfl

theorem suOddMod_toSubmodule : (suOddMod p q).toSubmodule = suOdd p q := rfl

theorem tracelessSkewMod_toSubmodule :
    (tracelessSkewMod p q).toSubmodule = tracelessSkewMat (Fin p ⊕ Fin q) := rfl

/-! ## 2. The decomposition, and what it is a decomposition OF -/

/-- **COMPLEMENTARY IN THE LATTICE OF `suEvenLie`-SUBMODULES** — but inside
`tracelessSkewMod`, not inside `⊤`. -/
theorem sup_eq_tracelessSkewMod :
    suEvenMod p q ⊔ suOddMod p q = tracelessSkewMod p q := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [LieSubmodule.sup_toSubmodule, suEvenMod_toSubmodule, suOddMod_toSubmodule,
    tracelessSkewMod_toSubmodule]
  exact SuBlockGrading.sup_eq

theorem inf_eq_bot : suEvenMod p q ⊓ suOddMod p q = ⊥ := by
  refine LieSubmodule.toSubmodule_injective ?_
  rw [LieSubmodule.inf_toSubmodule, LieSubmodule.bot_toSubmodule, suEvenMod_toSubmodule,
    suOddMod_toSubmodule]
  exact SuBlockGrading.inf_eq_bot

/-! ## 3. And it is NOT a decomposition of `⊤` -/

/-- `1` is Hermitian, not skew-Hermitian, as soon as there is an index to test. -/
theorem one_notMem_tracelessSkewMat (hp : 0 < p) :
    (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∉ tracelessSkewMat (Fin p ⊕ Fin q) := by
  intro h
  have hskew : (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ
      = -(1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := h.1
  rw [Matrix.conjTranspose_one] at hskew
  have h11 := congrFun (congrFun hskew (Sum.inl ⟨0, hp⟩)) (Sum.inl ⟨0, hp⟩)
  rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h11
  norm_num at h11

/-- **THE AMBIENT MODULE IS PROPER**, which is exactly what fails over `ℂ`. -/
theorem tracelessSkewMod_ne_top (hp : 0 < p) : tracelessSkewMod p q ≠ ⊤ := by
  intro h
  have hmem : (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
      ∈ (tracelessSkewMod p q).toSubmodule := by
    rw [h, LieSubmodule.top_toSubmodule]
    exact Submodule.mem_top
  exact one_notMem_tracelessSkewMat hp hmem

/-- **AND THEREFORE THE GRADING IS NOT A DECOMPOSITION OF EVERYTHING.** `BlockOddModule.sup_eq_top`
holds over `ℂ`; its literal analogue over `ℝ` is false, and this is the proof rather than the
observation. -/
theorem sup_ne_top (hp : 0 < p) : suEvenMod p q ⊔ suOddMod p q ≠ ⊤ := by
  rw [sup_eq_tracelessSkewMod]
  exact tracelessSkewMod_ne_top hp

/-! ## 4. Non-vacuity -/

/-- **THE ODD MODULE IS NONZERO**, by its dimension rather than by a witness — a different route
from `BlockOddModule.oddMod_ne_bot`, which exhibits a matrix. -/
theorem suOddMod_ne_bot (hp : 0 < p) (hq : 0 < q) : suOddMod p q ≠ ⊥ := by
  intro h
  have hsub : suOdd p q = ⊥ := by
    rw [← suOddMod_toSubmodule, h, LieSubmodule.bot_toSubmodule]
  have hrank : Module.finrank ℝ (suOdd p q) = 2 * p * q := finrank_suOdd
  rw [hsub] at hrank
  simp only [finrank_bot] at hrank
  have : 0 < 2 * p * q := by positivity
  omega

end SuBlockOddModule
