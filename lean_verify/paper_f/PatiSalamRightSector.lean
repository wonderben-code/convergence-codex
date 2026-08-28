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
>
> **`blLine_eq_centraliser`** (§5, added the same night) — the `B − L` line **is** the centraliser
> of two colour rotations inside `traceless 4`, so the direction the count starts from is forced
> rather than chosen.

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

**⚠ AMENDED THE SAME NIGHT BY §5, and only in part (`ERRATUM 94`).** The clause is kept because
most of it still holds, but one third of it no longer does. **The `B − L` DIRECTION is not a
convention**: `blLine_eq_centraliser` proves `blLine` is exactly the set of elements of
`traceless 4` commuting with two rotation generators of colour, so the line is **forced**, and the
argument needs no Schur-type input — two brackets and fourteen entry equations close it. **What
remains conventional is the scale and the name**: `blGen` is `3i · (B − L)` rather than `B − L`, and
calling the line `u(1)_{B−L}` rather than "the centraliser of colour in `su(4)`" is an act of
naming. **`t3RT` and `Y` are untouched by this** and remain conventions in full.

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

/-! ## 5. The `B − L` line is not a choice: it is the centraliser of colour -/

/-- `E₀₁ − E₁₀`, block-embedded: a real antisymmetric matrix, hence skew-Hermitian, and traceless
because its diagonal is zero. One of the rotation generators of `so(3) ⊆ su(3)`. -/
noncomputable def so3A : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

/-- `E₀₂ − E₂₀`, block-embedded. -/
noncomputable def so3B : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then -1 else 0

theorem so3A_mem_skewAdjoint : so3A ∈ skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [skewAdjoint.mem_iff, so3A]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem so3B_mem_skewAdjoint : so3B ∈ skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [skewAdjoint.mem_iff, so3B]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem so3A_mem_traceless : (⟨so3A, so3A_mem_skewAdjoint⟩ : skewAdjoint _) ∈ traceless 4 := by
  have h : Matrix.trace so3A = 0 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four, so3A]
  simp [traceless, traceIm, h]

theorem so3B_mem_traceless : (⟨so3B, so3B_mem_skewAdjoint⟩ : skewAdjoint _) ∈ traceless 4 := by
  have h : Matrix.trace so3B = 0 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four, so3B]
  simp [traceless, traceIm, h]

/-- **`B − L` COMMUTES WITH COLOUR**, on these two generators. `ColourEquivariance.bMinusL_comm`
proves the same thing against the whole embedded `su(3)`, over `ℂ` and on the index type
`Fin 3 ⊕ Fin 1`; this is the statement in the object this file uses. -/
theorem blGen_comm_so3A : blGen * so3A = so3A * blGen := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blGen, so3A, Matrix.mul_apply, Matrix.diagonal_apply]

theorem blGen_comm_so3B : blGen * so3B = so3B * blGen := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blGen, so3B, Matrix.mul_apply, Matrix.diagonal_apply]

set_option maxRecDepth 10000 in
/-- **THE COMMUTANT OF TWO COLOUR ROTATIONS IS THE BLOCK-SCALAR DIAGONAL**, and this is the whole
of the entry computation, separated from the two conditions that define `su(4)` because it does not
need them. `[N, so3A] = 0` gives `N 0 0 = N 1 1` and kills `N 0 2, N 0 3, N 1 2, N 1 3, N 2 0,
N 2 1, N 3 0, N 3 1`; `[N, so3B] = 0` gives `N 0 0 = N 2 2` and kills `N 0 1, N 1 0, N 2 3, N 3 2`.
**Two generators suffice and no Schur-type argument is used**: the fourteen entry equations
close it.

Each equation is stated rather than left to whatever `simp` produced — `ERRATUM 318` — so the
argument is legible on the page. -/
theorem eq_diag_of_commutes {N : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : N * so3A = so3A * N) (hB : N * so3B = so3B * N) :
    N = Matrix.diagonal ![N 0 0, N 0 0, N 0 0, N 3 3] := by
  have sA : ∀ i j, (N * so3A) i j = (so3A * N) i j := fun i j => congrFun (congrFun hA i) j
  have sB : ∀ i j, (N * so3B) i j = (so3B * N) i j := fun i j => congrFun (congrFun hB i) j
  -- the entry equations, each stated rather than left to whatever `simp` produced
  have e01 : N 0 0 = N 1 1 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 0 1
  have e02 : N 1 2 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using (sA 0 2).symm
  have e03 : N 1 3 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using (sA 0 3).symm
  have e12 : N 0 2 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 1 2
  have e13 : N 0 3 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 1 3
  have e20 : N 2 1 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 2 0
  have e21 : N 2 0 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 2 1
  have e30 : N 3 1 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 3 0
  have e31 : N 3 0 = 0 := by simpa [Matrix.mul_apply, so3A, Matrix.of_apply] using sA 3 1
  have f02 : N 0 0 = N 2 2 := by simpa [Matrix.mul_apply, so3B, Matrix.of_apply] using sB 0 2
  have f03 : N 2 3 = 0 := by simpa [Matrix.mul_apply, so3B, Matrix.of_apply] using (sB 0 3).symm
  have f12 : N 1 0 = 0 := by simpa [Matrix.mul_apply, so3B, Matrix.of_apply] using sB 1 2
  have f21 : N 0 1 = 0 := by simpa [Matrix.mul_apply, so3B, Matrix.of_apply] using sB 2 1
  have f30 : N 3 2 = 0 := by simpa [Matrix.mul_apply, so3B, Matrix.of_apply] using sB 3 0
  clear sA sB hA hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← e01, ← f02, e02, e03, e12, e13, e20, e21, e30, e31, f03, f12, f21, f30]

/-- **AND THAT IS ALL `su(4)` ALLOWS.** The two remaining constraints are exactly membership in
this space: tracelessness gives `N 3 3 = -3 · N 0 0`, and skew-Hermiticity makes `N 0 0` purely
imaginary. So `N = t • blGen` with `t = (N 0 0).im`, and the `B − L` direction is **forced, not
chosen**. -/
theorem eq_smul_blGen_of_commutes {N : Matrix (Fin 4) (Fin 4) ℂ}
    (hskew : Nᴴ = -N) (htr : Matrix.trace N = 0)
    (hA : N * so3A = so3A * N) (hB : N * so3B = so3B * N) :
    N = (((N 0 0).im : ℝ) : ℂ) • blGen := by
  have hdiag := eq_diag_of_commutes hA hB
  have hre : (N 0 0).re = 0 := by
    have h := congrFun (congrFun hskew 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at h2
    linarith
  have h00 : N 0 0 = (((N 0 0).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have h33 : N 3 3 = -3 * N 0 0 := by
    rw [hdiag] at htr
    simp [Matrix.trace_diagonal, Fin.sum_univ_four] at htr
    linear_combination htr
  -- `t` is generalised so that the diagonal equation is not a rewrite into itself
  suffices h : ∀ t : ℝ, N 0 0 = (t : ℂ) * Complex.I → N = ((t : ℝ) : ℂ) • blGen from
    h _ h00
  intro t ht0
  rw [hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blGen, ht0, h33]
  ring


/-- **AND NOTHING ELSE IN `su(4)` DOES.** The matrix statement above, read inside `traceless 4`:
the two constraints it needs are exactly membership in this space. -/
theorem mem_blLine_of_commutes (M : traceless 4)
    (hA : (M : Matrix (Fin 4) (Fin 4) ℂ) * so3A = so3A * (M : Matrix (Fin 4) (Fin 4) ℂ))
    (hB : (M : Matrix (Fin 4) (Fin 4) ℂ) * so3B = so3B * (M : Matrix (Fin 4) (Fin 4) ℂ)) :
    M ∈ blLine := by
  have hskew : (M : Matrix (Fin 4) (Fin 4) ℂ)ᴴ = -(M : Matrix (Fin 4) (Fin 4) ℂ) :=
    skewAdjoint.mem_iff.mp M.val.property
  have htr : Matrix.trace (M : Matrix (Fin 4) (Fin 4) ℂ) = 0 :=
    trace_eq_zero_of_mem_traceless M.property
  refine Submodule.mem_span_singleton.mpr
    ⟨((M : Matrix (Fin 4) (Fin 4) ℂ) 0 0).im, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (eq_smul_blGen_of_commutes hskew htr hA hB).symm

/-- **THE CENTRALISER OF COLOUR IN `su(4)` IS EXACTLY THE `B − L` LINE.** Both directions:
`blGen` commutes with the two generators, and nothing outside its span does. -/
theorem blLine_eq_centraliser :
    blLine = {M : traceless 4 |
        (M : Matrix (Fin 4) (Fin 4) ℂ) * so3A = so3A * (M : Matrix (Fin 4) (Fin 4) ℂ)
          ∧ (M : Matrix (Fin 4) (Fin 4) ℂ) * so3B = so3B * (M : Matrix (Fin 4) (Fin 4) ℂ)} := by
  ext M
  constructor
  · intro hM
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hM
    have hval : (M : Matrix (Fin 4) (Fin 4) ℂ) = (t : ℂ) • blGen := by
      rw [← ht]
      rfl
    exact ⟨by rw [hval, Matrix.smul_mul, Matrix.mul_smul, blGen_comm_so3A],
           by rw [hval, Matrix.smul_mul, Matrix.mul_smul, blGen_comm_so3B]⟩
  · rintro ⟨hA, hB⟩
    exact mem_blLine_of_commutes M hA hB

end PatiSalamRightSector
