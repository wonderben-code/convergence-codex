import TracelessSkewDimension
import PatiSalamOffDiagonal

/-!
# The other three broken generators, as a quotient rather than a subtraction

`TracelessSkewDimension.finrank_prod_diff` records that
`dim(su(4) ⊕ su(2) ⊕ su(2)) − dim(SM) = 9`, and fences the physics reading — six leptoquarks plus
three right-handed weak bosons — as *"not proved here: this is `21 − 12`, and nothing in this file
decomposes either space."* `PatiSalamOffDiagonal.su4_real_splits_nine_six` took **six** of the nine:
they are the off-diagonal directions of `su(4)`, and there they are a subspace with a surjection
onto it. Its own header then named what was left:

> **The other three of the nine are untouched.** They come from `su(2)_R ⊕ u(1)_{B−L}` minus
> hypercharge, which is a different computation in a different factor.

**This file does that computation.** The space is four-dimensional — the `B − L` line inside
`su(4)`, one dimension, plus the whole of `su(2)_R`, three — and hypercharge is **one line inside
it**, not inside either summand. Quotient by that line and three dimensions are left.

## The objects, named so that `ERRATUM 316` cannot recur

Everything below lives in `TracelessSkewDimension.traceless n`: the traceless skew-Hermitian
`n × n` matrices, an **`ℝ`**-submodule of `skewAdjoint (Matrix (Fin n) (Fin n) ℂ)`. That is the
object `finrank_prod_diff` counts, so it is the object the fence is about. It is **not**
`CascadeFoundation.TracelessMatrix n`, which is a `ℂ`-submodule of the same dimension over a
different field; confusing the two cost `ERRATUM 316`.

* `blT` — `TracelessSkewDimension.blGen = diag(i, i, i, −3i)`, which is `B − L` scaled by `3i`, as
  an element of `traceless 4`. The scaling is `ERRATUM 316`'s convention and is stated, not proved.
* `t3RT` — `diag(i, −i)` in `traceless 2`, which is `2i · T₃R`.
* `RightSector` — `blLine × traceless 2`, the four dimensions in play.
* `yRep` — `(blT, 3 • t3RT)`, which is `6i · Y` for `Y = T₃R + (B − L)/2`. **The factor of six is
  there only to clear denominators**: what the file uses is the *line* `ℝ ∙ yRep`, and every nonzero
  multiple of a vector spans the same line.

## What is proved

> **`finrank_broken_right`** — `finrank ℝ (RightSector ⧸ ℝ ∙ yRep) = 3`.
>
> **`broken_nine`** — that three plus `PatiSalamOffDiagonal`'s six is the nine, **with both
> summands exhibited as spaces**: a range on one side, a quotient on the other.

**`yRep_fst_ne_zero` and `yRep_snd_ne_zero` are not decoration.** They say hypercharge has a
nonzero component in *each* summand — it is a genuine mixture, not a direction sitting inside
`u(1)_{B−L}` or inside `su(2)_R`. That is why the count is `4 − 1` and not an accident of
`1 − 1 + 3`, and it is the linear-algebra content of the sentence "hypercharge is a combination of
`T₃R` and `B − L`".

## What is NOT proved, and the fence has to stay up

**(i) The identifications are conventions.** That `blGen` *is* `B − L`, that `t3RT` *is* `T₃R`, and
that hypercharge *is* `T₃R + (B − L)/2` are the standard assignments; they are cited to
`WeinbergIndex.yval` and `TracelessSkewDimension.blGen`'s own docstring and are **not theorems
here**. Choose different generators and the arithmetic below is unchanged, which is the honest way
to say that this file computes a dimension and not a physics claim.

**(ii) The reading is physics.** That the three surviving directions are the `W_R^±` and `Z_R`
gauge bosons of a broken right-handed weak interaction is an interpretation. Nothing here mentions
a particle, a mass, a current or a symmetry breaking; `Submodule.span` is not spontaneous symmetry
breaking.

**(iii) No group, no bracket, no representation.** `traceless n` is a subspace of matrices.
`Su2ModuleSixteen` builds the actual `su(2)_L ⊕ su(2)_R` action, but **on the 16-dimensional
fermion representation over `ℚ`** — a different object again, and nothing here connects the two.

**(iv) The quotient's dimension is 3 and `su(2)_R`'s dimension is 3, and they are not the same
space.** The surviving direction is a mixture, so the quotient is not canonically `su(2)_R`; no
isomorphism between them is stated or used.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PatiSalamRightSector

open Matrix TracelessSkewDimension

/-! ## 1. The `B − L` line inside `su(4)` -/

/-- `B − L`, scaled by `3i`, as an element of `traceless 4`. -/
noncomputable def blT : traceless 4 :=
  ⟨⟨blGen, blGen_mem_skewAdjoint⟩, blGen_mem_traceless⟩

theorem blT_ne_zero : blT ≠ 0 := by
  intro h
  have h1 : blGen 0 0 = 0 := congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val h)) 0) 0
  rw [blGen] at h1
  simp [Matrix.diagonal_apply_eq] at h1

/-- The one-dimensional `u(1)_{B−L}` direction. -/
noncomputable def blLine : Submodule ℝ (traceless 4) := Submodule.span ℝ {blT}

theorem finrank_blLine : Module.finrank ℝ blLine = 1 :=
  finrank_span_singleton blT_ne_zero

/-! ## 2. The Cartan of `su(2)_R` -/

/-- `2i · T₃R`, as a matrix. -/
noncomputable def t3RGen : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.I, -Complex.I]

theorem t3RGen_mem_skewAdjoint : t3RGen ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [skewAdjoint.mem_iff, t3RGen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem t3RGen_trace : Matrix.trace t3RGen = 0 := by
  rw [t3RGen, Matrix.trace_diagonal]
  simp [Fin.sum_univ_two]

theorem t3RGen_mem_traceless :
    (⟨t3RGen, t3RGen_mem_skewAdjoint⟩ : skewAdjoint _) ∈ traceless 2 := by
  simp [traceless, traceIm, t3RGen_trace]

/-- `2i · T₃R`, as an element of `traceless 2`. -/
noncomputable def t3RT : traceless 2 :=
  ⟨⟨t3RGen, t3RGen_mem_skewAdjoint⟩, t3RGen_mem_traceless⟩

theorem t3RT_ne_zero : t3RT ≠ 0 := by
  intro h
  have h1 : t3RGen 0 0 = 0 :=
    congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val h)) 0) 0
  rw [t3RGen] at h1
  simp [Matrix.diagonal_apply_eq] at h1

/-! ## 3. The four dimensions, and hypercharge as one line inside them -/

/-- `u(1)_{B−L} ⊕ su(2)_R`. The `su(3)` and `su(2)_L` factors are not here because they are the
unbroken ones; the leptoquark directions are not here because they are
`PatiSalamOffDiagonal.offDiagMapR`'s range. -/
abbrev RightSector := blLine × traceless 2

theorem finrank_rightSector : Module.finrank ℝ RightSector = 4 := by
  rw [Module.finrank_prod, finrank_blLine, finrank_traceless_two]

/-- `6i · Y`, for `Y = T₃R + (B − L)/2`. The six clears denominators and changes nothing: the file
uses the line this vector spans. -/
noncomputable def yRep : RightSector :=
  (⟨blT, Submodule.mem_span_singleton_self blT⟩, (3 : ℝ) • t3RT)

/-- **HYPERCHARGE HAS A `B − L` COMPONENT.** -/
theorem yRep_fst_ne_zero : yRep.1 ≠ 0 := by
  intro h
  exact blT_ne_zero (congrArg Subtype.val h)

/-- **AND A `T₃R` COMPONENT.** Together with the previous theorem: hypercharge is a genuine
mixture, lying in neither summand, which is what makes the quotient below `4 − 1` and not an
accident. -/
theorem yRep_snd_ne_zero : yRep.2 ≠ 0 := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  simpa [yRep, smul_eq_zero, h3] using t3RT_ne_zero

theorem yRep_ne_zero : yRep ≠ 0 := fun h => yRep_fst_ne_zero (congrArg Prod.fst h)

/-- The hypercharge direction. -/
noncomputable def hyperchargeLine : Submodule ℝ RightSector := Submodule.span ℝ {yRep}

theorem finrank_hyperchargeLine : Module.finrank ℝ hyperchargeLine = 1 :=
  finrank_span_singleton yRep_ne_zero

/-! ## 4. Three -/

/-- **THE OTHER THREE BROKEN GENERATORS.** `u(1)_{B−L} ⊕ su(2)_R` is four-dimensional and
hypercharge is one line inside it, so what breaks is three-dimensional — **a quotient of exhibited
spaces, not `4 − 1` on numerals**. -/
theorem finrank_broken_right : Module.finrank ℝ (RightSector ⧸ hyperchargeLine) = 3 := by
  have h := Submodule.finrank_quotient_add_finrank hyperchargeLine
  rw [finrank_hyperchargeLine, finrank_rightSector] at h
  omega

/-- **AND THE NINE IS SIX PLUS THREE, WITH BOTH SUMMANDS EXHIBITED.** The six is the range of
`PatiSalamOffDiagonal.offDiagMapR`, a subspace of `su(4)` with an explicit section; the three is the
quotient above. `TracelessSkewDimension.finrank_prod_diff` said `21 − 12 = 9` and fenced the
reading; this says which nine directions, in which factors.

**The reading itself is still not proved** — see the header. That these six are leptoquarks and
those three are right-handed weak bosons is physics, and this theorem is linear algebra. -/
theorem broken_nine :
    Module.finrank ℝ (LinearMap.range PatiSalamOffDiagonal.offDiagMapR)
      + Module.finrank ℝ (RightSector ⧸ hyperchargeLine) = 9 := by
  rw [PatiSalamOffDiagonal.finrank_range_offDiagMapR, finrank_broken_right]

end PatiSalamRightSector
