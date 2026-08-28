import TracelessSkewLie

/-!
# The block grading restricts to the compact form, and the grading element becomes `i · t`

`SkewBlockOffDiagonal` split the traceless skew-Hermitian matrices `(p+q)² − 1 = (p² + q² − 1) +
2pq` and its header now says, in as many words, that the real analogue of
`BlockGrading`/`BlockLieMorphism` **is not written and nothing there says the skew block split
respects a bracket**. `BlockLieMorphism` left a second one:

> *"the grading element here is a complex multiple of a block-scalar matrix and is not
> skew-adjoint unless `c` is imaginary; in the physics reading the corresponding generator is
> `i`-times this one, and that reading is not formalised anywhere in this chain."*

Both are closed here.

## What is proved

> **`evenPartR` and `oddPartR`** — the same two block subspaces over `ℝ`, and
> `mem_evenPartR_iff` / `mem_oddPartR_iff` show they cut out the **same conditions** as
> `BlockGrading`'s complex versions, so every bracket rule proved there is available unchanged.
>
> **`suEven` and `suOdd`** — the two graded pieces of the compact form.
> `suOdd_eq` records that the traceless condition is free on the odd side, exactly as it is over
> `ℂ`: `suOdd = oddPartR ⊓ skewSub`.
>
> **The four bracket rules over `ℝ`** — each is `BlockGrading`'s rule met with
> `TracelessSkewLie.lie_mem_skewSub`, and **`suEvenLie`** is the even piece as a
> `LieSubalgebra ℝ (Matrix …)`.
>
> **`sup_eq` and `inf_eq_bot`** — the two pieces are complementary **inside the compact form**:
> `suEven ⊔ suOdd = tracelessSkewMat` and `suEven ⊓ suOdd = ⊥`. So the split
> `SkewBlockOffDiagonal` counted is a ℤ/2-grading of a Lie algebra and not only of a space.
>
> **`centreOf_mem_skewSub_iff`** — the grading element is skew-Hermitian **exactly when its
> parameter is purely imaginary**, and `centreOf_I_mem` gives the family `centreOf p q (i·t)` for
> real `t`. **`lie_centreOf_I_offDiagOf`** is its action on the odd part: multiplication by
> `±(p+q)·i·t`. This is the `i` that the physics reading puts in front of the hypercharge
> generator, and it is now a computation rather than a remark.

## What is NOT claimed

**Nothing about maximal tori, rank, roots, Cartan subalgebras or abelian bounds.** `SlFourAbelian`
and `SlAbelianGeneral` decline that step and this file does not take it; having a grading is not
having a torus.

**No `GradedLieAlgebra` instance over `ℝ`.** `BlockGrading` instantiates Mathlib's class for
`gl(p+q)` over `ℂ`; the analogue here would need the grading to decompose the **whole** real
algebra, and `suEven ⊔ suOdd` is `tracelessSkewMat`, not `⊤`. **No `ZMod 2`-indexed family is
built below and no instance is declared.**

**⚠ THE REASON WAS RIGHT AND THE CONCLUSION TOO NARROW, 2026-08-28 — `SuGradedLieAlgebra`.** The
grading does decompose a whole algebra: **not the matrices, but `tracelessSkewLie` itself**, which
`TracelessSkewLie` built as a `LieSubalgebra ℝ` and which is a Lie algebra in its own right. Pulled
back along the subtype inclusion the two pieces satisfy `sup_suPart = ⊤` and `inf_suPart = ⊥` —
exactly what fails in the matrices — so `GradedLieAlgebra (suPart p q)` holds at `ZMod 2`. **The
mathematics is entirely this file's**: `SetLike.GradedBracket` is the four rules above read through
`Submodule.mem_comap`, and `DirectSum.Decomposition` is `sup_eq`/`inf_eq_bot` through
`DirectSum.isInternal_submodule_iff_isCompl`. What changed is **where the grading lives**, not what
it says. The sentence above is kept as the record of the right reason for the wrong conclusion.

**No `LieSubmodule` for the odd piece.** `BlockOddModule` does that over `ℂ`; the real analogue is
not written here.

**No group, no compactness, no smooth structure**, and the name `su` is not used, for the reason
`F4_1e_SpectralTripleArithmetic` records and `TracelessSkewLie` follows.

**No physics.** That `centreOf p q (i·t)` "is" hypercharge or `B − L` is the reading
`PatiSalamOffDiagonal` fences; what is proved is an eigenvalue.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SuBlockGrading

open Matrix SlAbelianGeneral BlockOffDiagonal BlockGrading BlockLieMorphism
open TracelessSkewLie

variable {p q : ℕ}

/-! ## 1. The block subspaces over `ℝ` -/

/-- The two off-diagonal blocks, real-linearly. Same function as `BlockGrading.offBlocks`, a
different scalar ring, because the compact form is not a complex subspace
(`TracelessSkewLie.smul_I_notMem`). -/
noncomputable def offBlocksR : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ]
    (Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin p) ℂ) where
  toFun M := (M.toBlocks₁₂, M.toBlocks₂₁)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two diagonal blocks, real-linearly. -/
noncomputable def diagBlocksR : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℝ]
    (Matrix (Fin p) (Fin p) ℂ × Matrix (Fin q) (Fin q) ℂ) where
  toFun M := (M.toBlocks₁₁, M.toBlocks₂₂)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def evenPartR (p q : ℕ) : Submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  LinearMap.ker (offBlocksR (p := p) (q := q))

noncomputable def oddPartR (p q : ℕ) : Submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  LinearMap.ker (diagBlocksR (p := p) (q := q))

/-- **THE SAME CONDITION AS OVER `ℂ`**, so every bracket rule of `BlockGrading` is available. -/
theorem mem_evenPartR_iff (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M ∈ evenPartR p q ↔ M ∈ evenPart p q := by
  rw [mem_evenPart_iff]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst (LinearMap.mem_ker.mp h), congrArg Prod.snd (LinearMap.mem_ker.mp h)⟩
  · rintro ⟨h1, h2⟩
    exact LinearMap.mem_ker.mpr (Prod.ext h1 h2)

theorem mem_oddPartR_iff (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M ∈ oddPartR p q ↔ M ∈ oddPart p q := by
  rw [mem_oddPart_iff]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst (LinearMap.mem_ker.mp h), congrArg Prod.snd (LinearMap.mem_ker.mp h)⟩
  · rintro ⟨h1, h2⟩
    exact LinearMap.mem_ker.mpr (Prod.ext h1 h2)

/-! ## 2. The two graded pieces of the compact form -/

noncomputable def suEven (p q : ℕ) : Submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  evenPartR p q ⊓ tracelessSkewMat (Fin p ⊕ Fin q)

noncomputable def suOdd (p q : ℕ) : Submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  oddPartR p q ⊓ tracelessSkewMat (Fin p ⊕ Fin q)

/-- **THE TRACE CONDITION IS FREE ON THE ODD SIDE**, exactly as over `ℂ`: an off-diagonal matrix
has both diagonal blocks zero, so its trace is zero for nothing. -/
theorem suOdd_eq : suOdd p q = oddPartR p q ⊓ skewSub (Fin p ⊕ Fin q) := by
  refine le_antisymm (le_inf inf_le_left (le_trans inf_le_right inf_le_left)) ?_
  rintro M ⟨hodd, hskew⟩
  refine ⟨hodd, hskew, ?_⟩
  have : M ∈ tracelessSub (Fin p ⊕ Fin q) :=
    oddPart_le_tracelessSub ((mem_oddPartR_iff M).mp hodd)
  exact LinearMap.mem_ker.mp this

/-! ## 3. The four bracket rules, and the even piece as a Lie subalgebra -/

theorem lie_suEven_suEven {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ suEven p q) (hY : Y ∈ suEven p q) : ⁅X, Y⁆ ∈ suEven p q :=
  ⟨(mem_evenPartR_iff _).mpr
      (lie_evenPart_evenPart ((mem_evenPartR_iff X).mp hX.1) ((mem_evenPartR_iff Y).mp hY.1)),
   lie_mem_skewSub hX.2.1 hY.2.1,
   LinearMap.mem_ker.mp (lie_mem_tracelessSub _ (mem_tracelessSub_of_mem_skewTraceless hX.2)
      (mem_tracelessSub_of_mem_skewTraceless hY.2))⟩

theorem lie_suEven_suOdd {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ suEven p q) (hY : Y ∈ suOdd p q) : ⁅X, Y⁆ ∈ suOdd p q :=
  ⟨(mem_oddPartR_iff _).mpr
      (lie_evenPart_oddPart ((mem_evenPartR_iff X).mp hX.1) ((mem_oddPartR_iff Y).mp hY.1)),
   lie_mem_skewSub hX.2.1 hY.2.1,
   LinearMap.mem_ker.mp (lie_mem_tracelessSub _ (mem_tracelessSub_of_mem_skewTraceless hX.2)
      (mem_tracelessSub_of_mem_skewTraceless hY.2))⟩

theorem lie_suOdd_suEven {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ suOdd p q) (hY : Y ∈ suEven p q) : ⁅X, Y⁆ ∈ suOdd p q :=
  ⟨(mem_oddPartR_iff _).mpr
      (lie_oddPart_evenPart ((mem_oddPartR_iff X).mp hX.1) ((mem_evenPartR_iff Y).mp hY.1)),
   lie_mem_skewSub hX.2.1 hY.2.1,
   LinearMap.mem_ker.mp (lie_mem_tracelessSub _ (mem_tracelessSub_of_mem_skewTraceless hX.2)
      (mem_tracelessSub_of_mem_skewTraceless hY.2))⟩

/-- **THE RULE THAT MAKES IT A GRADING**: two odd elements bracket back into the even piece. -/
theorem lie_suOdd_suOdd {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ suOdd p q) (hY : Y ∈ suOdd p q) : ⁅X, Y⁆ ∈ suEven p q :=
  ⟨(mem_evenPartR_iff _).mpr
      (lie_oddPart_oddPart ((mem_oddPartR_iff X).mp hX.1) ((mem_oddPartR_iff Y).mp hY.1)),
   lie_mem_skewSub hX.2.1 hY.2.1,
   LinearMap.mem_ker.mp (lie_mem_tracelessSub _ (mem_tracelessSub_of_mem_skewTraceless hX.2)
      (mem_tracelessSub_of_mem_skewTraceless hY.2))⟩

/-- The even piece of the compact form, as a `LieSubalgebra ℝ`. -/
noncomputable def suEvenLie (p q : ℕ) : LieSubalgebra ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    where
  toSubmodule := suEven p q
  lie_mem' hx hy := lie_suEven_suEven hx hy

/-! ## 4. The two pieces are complementary inside the compact form -/

theorem sup_eq : suEven p q ⊔ suOdd p q = tracelessSkewMat (Fin p ⊕ Fin q) := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro M hM
  have hMs : Mᴴ = -M := hM.1
  have hMt : Matrix.trace M = 0 := hM.2
  have hent : ∀ i j, star (M j i) = -M i j := fun i j => by
    have h := congrFun (congrFun hMs i) j
    simpa [Matrix.conjTranspose_apply] using h
  have hdiagS : Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ ∈ skewSub (Fin p ⊕ Fin q) := by
    rw [mem_skewSub_iff]
    ext i j
    cases i <;> cases j <;>
      simp only [Matrix.conjTranspose_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.zero_apply,
        star_zero, neg_zero, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply] <;>
      try exact hent _ _
  have hdiagT : Matrix.trace (Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂) = 0 := by
    rw [BlockDiagonalSplit.trace_fromBlocks_diag, ← trace_eq_trace_blocks]
    exact hMt
  have hoffS : Matrix.fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 ∈ skewSub (Fin p ⊕ Fin q) := by
    rw [mem_skewSub_iff]
    ext i j
    cases i <;> cases j <;>
      simp only [Matrix.conjTranspose_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.zero_apply,
        star_zero, neg_zero, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply] <;>
      try exact hent _ _
  have hoffT : Matrix.trace (Matrix.fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0) = 0 :=
    offDiagOf_trace _ _
  rw [eq_diag_add_off M]
  exact Submodule.add_mem_sup
    ⟨(mem_evenPartR_iff _).mpr (fromBlocks_diag_mem _ _), hdiagS, hdiagT⟩
    ⟨(mem_oddPartR_iff _).mpr (fromBlocks_off_mem _ _), hoffS, hoffT⟩

theorem inf_eq_bot : suEven p q ⊓ suOdd p q = ⊥ := by
  rw [← le_bot_iff]
  intro M hM
  have h1 : M ∈ evenPart p q := (mem_evenPartR_iff M).mp hM.1.1
  have h2 : M ∈ oddPart p q := (mem_oddPartR_iff M).mp hM.2.1
  have h := (Submodule.disjoint_def.mp isCompl_evenPart_oddPart.disjoint) M h1 h2
  simpa using h

/-! ## 5. The grading element, and the `i` the physics reading puts in front of it -/

/-- **THE PURELY IMAGINARY GRADING ELEMENT IS SKEW-HERMITIAN**, so it lives in the compact form. -/
theorem centreOf_I_mem (t : ℝ) :
    centreOf p q (Complex.I * (t : ℂ)) ∈ skewSub (Fin p ⊕ Fin q) := by
  rw [mem_skewSub_iff, centreOf_eq]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, apply_ite (starRingEnd ℂ), Complex.conj_I,
      Complex.conj_ofReal, eq_comm, apply_ite (Neg.neg : ℂ → ℂ), neg_zero, neg_neg]

/-- **AND THE UN-`i`'d ONE IS NOT**, so the `i` is doing work rather than decorating. This is the
sentence `BlockLieMorphism` left as a remark. -/
theorem centreOf_one_notMem (hp : 0 < p) (hq : 0 < q) :
    centreOf p q 1 ∉ skewSub (Fin p ⊕ Fin q) := by
  intro h
  rw [mem_skewSub_iff] at h
  have hval := congrFun (congrFun h (Sum.inl ⟨0, hp⟩)) (Sum.inl ⟨0, hp⟩)
  simp only [Matrix.conjTranspose_apply, centreOf_eq, Matrix.fromBlocks_apply₁₁,
    Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hval
  have hstar : star ((q : ℂ)) = (q : ℂ) := by
    rw [RCLike.star_def, Complex.conj_natCast]
  rw [hstar] at hval
  have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (2 : ℂ) * (q : ℂ) = 0 := by linear_combination hval
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact two_ne_zero h'
  · exact hqne h'

/-- **ITS ACTION ON THE ODD PIECE IS MULTIPLICATION BY `±(p+q)·i·t`.** -/
theorem lie_centreOf_I_offDiagOf (t : ℝ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) :
    ⁅centreOf p q (Complex.I * (t : ℂ)), offDiagOf B C⁆
      = offDiagOf ((((p : ℂ) + q) * (Complex.I * (t : ℂ))) • B)
          ((-(((p : ℂ) + q) * (Complex.I * (t : ℂ)))) • C) :=
  lie_centreOf_offDiagOf _ B C

end SuBlockGrading
