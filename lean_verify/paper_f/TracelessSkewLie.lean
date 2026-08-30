import BlockOddModule
import SkewBlockOffDiagonal

/-!
# The traceless skew-Hermitian matrices are a Lie algebra over `ℝ`, which Mathlib does not have

Today's chain found that `SlAbelianGeneral.tracelessSub` **was** Mathlib's
`LieAlgebra.SpecialLinear.sl` all along (`BlockGrading.sl_toSubmodule`, by `rfl`), and
`ERRATUM 324` records the cost of six headers that said otherwise. The obvious next question is
whether the same is true of the compact form, which this estate has carried since
`TracelessSkewDimension` as *"the traceless skew-Hermitian matrices"* and has never called a Lie
algebra in any statement.

**It is not, and this time the absence is measured.** Mathlib's `skewAdjointLieSubalgebra` and
`skewAdjointMatricesLieSubalgebra` are about skew-adjointness for a **bilinear form**, not for the
star operation; searching the whole vendored tree for `skewAdjoint` in any line mentioning a Lie
notion returns **nothing outside those two files**, and `Matrix.specialUnitaryGroup` is a
`Submonoid` — a group, with no Lie algebra attached. So `su(n)` has to be built, and it is built
here.

## What is proved

> **`skewSub ι`** — the anti-Hermitian matrices as a `Submodule ℝ (Matrix ι ι ℂ)`. Mathlib's
> `skewAdjoint` is an `AddSubgroup` whose `Module ℝ` structure lives on the **subtype**, which is
> not what a `LieSubalgebra` takes.
>
> **`tracelessSkewMat ι := skewSub ι ⊓ Submodule.restrictScalars ℝ (tracelessSub ι)`**, so
> **`su(ι) ≤ sl(ι)` holds by construction** (`mem_tracelessSub_of_mem_skewTraceless`) rather than
> by an argument. **This line read `tracelessSkewMat_le_sl` until 2026-08-30 and that was never a
> declaration** (`ERRATUM 344`); the theorem it meant carries `su(ι) ≤ sl(ι)` as its own
> docstring headline, so the claim was checked and only the reference was not. The wrong
> spelling is kept beside the right one per `ERRATUM 94`.
>
> **`tracelessSkewLie ι`** — `su(ι)` as a `LieSubalgebra ℝ (Matrix ι ι ℂ)`: the commutator of two
> anti-Hermitian matrices is anti-Hermitian, and the trace half is Mathlib's, cited through
> `BlockGrading.lie_mem_tracelessSub`. **This is the estate's first statement that `su(n)` is a
> Lie algebra.**
>
> **`finrank_tracelessSkewMat = (card ι)² − 1`** — transported from
> `SkewBlockOffDiagonal.finrank_tracelessSkewSub` along `skewIncl`, which needs the one fact the
> two presentations differ by: a skew-Hermitian matrix has **purely imaginary trace**
> (`trace_re_eq_zero`), so vanishing of the imaginary part is vanishing of the trace.
>
> **`smul_I_notMem`** — **`su(ι)` is not a complex subspace**: multiplying a nonzero element by
> `i` leaves it. This is what makes it a real form rather than a subalgebra of `sl(ι, ℂ)` in the
> complex sense, and it is the statement that keeps `ERRATUM 316` — the record of confusing the
> two forms — from applying to this file.
>
> **`finrank_two_three_four`** — `3`, `8`, `15`, now as **dimensions of a Lie algebra**.

## The name

**This file does not use the name `su`, and that is a decision it is following rather than
making.** `F4_1e_SpectralTripleArithmetic` records it in as many words: *"that these subspaces ARE
the Lie algebras of SU(n) — tangent spaces at the identity of smooth groups — needs a smooth
structure that nothing here builds. The new definition is called `traceless`, not `su`, for that
reason."* Building the **algebraic** Lie algebra does not build the **group** link, so the reason
stands exactly as written and the declarations below are named for what they are. The prose says
`𝔰𝔲(n)` where that is what a reader expects; **no statement does**. Whether the estate should now
adopt the name is the author's call and is not taken here.

## What is NOT claimed

**NOTHING ABOUT MAXIMAL TORI, AND THE FENCE THAT NEEDS THEM STANDS.** `SlFourAbelian` and
`SlAbelianGeneral` both decline the same step:

> *"that `su(n)` has no abelian subspace above dimension `n − 1`, the statement that makes the
> rank argument work where it works, needs maximal-torus theory and is not proved and not begun."*

**Building the Lie algebra does not begin it.** No torus, no rank, no root system, no Cartan
subalgebra, and no abelian-subspace bound of any kind is proved here. Those two files' fences are
unchanged and are deliberately not annotated by this one: having the algebra is not having the
torus, and a dated note on them would suggest otherwise.

**No compactness.** `su(n)` is called the *compact form* in the literature; nothing here is a
topological statement, no group is built, and `Matrix.specialUnitaryGroup` is not mentioned in any
statement below.

**No semisimplicity, no Killing form, no `LieAlgebra.IsSemisimple`.**

**No complexification.** That `su(n) ⊕ i·su(n) = sl(n, ℂ)` as real spaces — the sentence that
would make "real form" a theorem rather than a word — is **not proved here**; `smul_I_notMem` is
the one-directional statement that `i` moves you out, and the decomposition is a different claim.

**⚠ AND IT IS PROVED THE SAME DAY, `TracelessRealSplit`.** `sup_eq` and `inf_eq_bot`: the traceless
matrices are the **internal real direct sum** of `tracelessSkewMat` and `HermitianNotLie
.tracelessHerm`, which is `i · tracelessSkewMat`. `finrank_traceZeroSub` reads `2(n² − 1)`, so
"real form" is now a dimension statement and not a word. **Still no tensor product is
constructed** and no isomorphism to `su(n) ⊗_ℝ ℂ` is exhibited — the decomposition is the
concrete content of the phrase, not the functor.

**No physics.**

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TracelessSkewLie

open Matrix SlAbelianGeneral

variable {ι : Type*} [Fintype ι]

/-! ## 1. The anti-Hermitian matrices as a real submodule -/

/-- The anti-Hermitian matrices, as a `Submodule ℝ` of the matrix algebra itself. Mathlib's
`skewAdjoint` is an `AddSubgroup` and carries its `Module ℝ` structure on the subtype; a
`LieSubalgebra` needs a submodule of the ambient algebra. -/
def skewSub (ι : Type*) [Fintype ι] : Submodule ℝ (Matrix ι ι ℂ) where
  carrier := {A | Aᴴ = -A}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.conjTranspose_add, hA, hB, neg_add]
  zero_mem' := by simp
  smul_mem' r A hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    rw [Matrix.conjTranspose_smul, hA, smul_neg]
    congr 1

theorem mem_skewSub_iff (A : Matrix ι ι ℂ) : A ∈ skewSub ι ↔ Aᴴ = -A := Iff.rfl

/-- **THE COMMUTATOR OF TWO ANTI-HERMITIAN MATRICES IS ANTI-HERMITIAN.** -/
theorem lie_mem_skewSub {A B : Matrix ι ι ℂ} (hA : A ∈ skewSub ι) (hB : B ∈ skewSub ι) :
    ⁅A, B⁆ ∈ skewSub ι := by
  rw [mem_skewSub_iff] at hA hB ⊢
  rw [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hA, hB, neg_mul_neg, neg_mul_neg]
  abel

/-! ## 2. A skew-Hermitian matrix has purely imaginary trace -/

theorem trace_re_eq_zero {A : Matrix ι ι ℂ} (hA : A ∈ skewSub ι) :
    (Matrix.trace A).re = 0 := by
  rw [mem_skewSub_iff] at hA
  have h : star (Matrix.trace A) = -Matrix.trace A := by
    rw [← Matrix.trace_conjTranspose, hA, Matrix.trace_neg]
  have hre : (Matrix.trace A).re = -(Matrix.trace A).re := by
    have := congrArg Complex.re h
    simpa using this
  linarith

theorem trace_eq_zero_of_im {A : Matrix ι ι ℂ} (hA : A ∈ skewSub ι)
    (him : (Matrix.trace A).im = 0) : Matrix.trace A = 0 := by
  refine Complex.ext ?_ ?_
  · simpa using trace_re_eq_zero hA
  · simpa using him

/-! ## 3. `su(ι)`, and it is a Lie subalgebra -/

/-- The traceless matrices as a **real** submodule. `SlAbelianGeneral.tracelessSub` is a
`Submodule ℂ`, and `su(ι)` is not a complex subspace (§5), so the meet below has to be taken over
`ℝ`. -/
def traceZeroSub (ι : Type*) [Fintype ι] : Submodule ℝ (Matrix ι ι ℂ) where
  carrier := {A | Matrix.trace A = 0}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.trace_add, hA, hB, add_zero]
  zero_mem' := by simp
  smul_mem' r A hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    rw [Matrix.trace_smul, hA, smul_zero]

/-- **`su(ι)`** — traceless and anti-Hermitian. -/
noncomputable def tracelessSkewMat (ι : Type*) [Fintype ι] : Submodule ℝ (Matrix ι ι ℂ) :=
  skewSub ι ⊓ traceZeroSub ι

theorem mem_tracelessSkewMat_iff (A : Matrix ι ι ℂ) :
    A ∈ tracelessSkewMat ι ↔ Aᴴ = -A ∧ Matrix.trace A = 0 := Iff.rfl

/-- **`su(ι) ≤ sl(ι)`**: every traceless anti-Hermitian matrix is traceless, which is what
`SlAbelianGeneral.tracelessSub` — Mathlib's `sl` by `BlockGrading.sl_toSubmodule` — asks for. The
inclusion is of **sets**: the two carry different scalars. -/
theorem mem_tracelessSub_of_mem_skewTraceless [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A ∈ tracelessSkewMat ι) : A ∈ tracelessSub ι :=
  LinearMap.mem_ker.mpr ((mem_tracelessSkewMat_iff A).mp hA).2

/-- **`su(ι)` AS A LIE SUBALGEBRA OVER `ℝ`.** The estate's first statement that the compact form
is a Lie algebra; the trace half is Mathlib's, cited and not reproved. -/
noncomputable def tracelessSkewLie (ι : Type*) [Fintype ι] [DecidableEq ι] :
    LieSubalgebra ℝ (Matrix ι ι ℂ) where
  toSubmodule := tracelessSkewMat ι
  lie_mem' {A B} hA hB := by
    have hA' := (mem_tracelessSkewMat_iff A).mp hA
    have hB' := (mem_tracelessSkewMat_iff B).mp hB
    refine (mem_tracelessSkewMat_iff _).mpr ⟨lie_mem_skewSub hA'.1 hB'.1, ?_⟩
    exact LinearMap.mem_ker.mp (BlockGrading.lie_mem_tracelessSub ι
      (LinearMap.mem_ker.mpr hA'.2) (LinearMap.mem_ker.mpr hB'.2))

theorem tracelessSkewLie_toSubmodule [DecidableEq ι] :
    (tracelessSkewLie ι).toSubmodule = tracelessSkewMat ι := rfl

/-! ## 4. Its dimension -/

/-- The inclusion of the skew-Hermitian subtype into the matrices, real-linearly. -/
def skewIncl (ι : Type*) [Fintype ι] : skewAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun A := (A : Matrix ι ι ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem skewIncl_injective (ι : Type*) [Fintype ι] : Function.Injective (skewIncl ι) :=
  fun _ _ h => Subtype.ext h

theorem map_tracelessSkewSub [DecidableEq ι] :
    Submodule.map (skewIncl ι) (SkewBlockOffDiagonal.tracelessSkewSub ι) = tracelessSkewMat ι := by
  ext A
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hskew : (X : Matrix ι ι ℂ) ∈ skewSub ι := by
      have := skewAdjoint.mem_iff.mp X.property
      rwa [Matrix.star_eq_conjTranspose] at this
    refine (mem_tracelessSkewMat_iff _).mpr ⟨hskew, trace_eq_zero_of_im hskew ?_⟩
    exact LinearMap.mem_ker.mp hX
  · intro hA
    obtain ⟨h1, h2⟩ := (mem_tracelessSkewMat_iff A).mp hA
    have hmem : A ∈ skewAdjoint (Matrix ι ι ℂ) :=
      skewAdjoint.mem_iff.mpr (by rwa [Matrix.star_eq_conjTranspose])
    refine ⟨⟨A, hmem⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
    have : Matrix.trace ((⟨A, hmem⟩ : skewAdjoint (Matrix ι ι ℂ)) :
        Matrix ι ι ℂ) = 0 := h2
    simp [SkewBlockOffDiagonal.traceImSub, this]

/-- **`dim_ℝ su(ι) = (card ι)² − 1`.** -/
theorem finrank_tracelessSkewMat (ι : Type*) [Fintype ι] [Nonempty ι] :
    Module.finrank ℝ (tracelessSkewMat ι) = Fintype.card ι ^ 2 - 1 := by
  classical
  rw [← map_tracelessSkewSub, ← (Submodule.equivMapOfInjective (skewIncl ι)
    (skewIncl_injective ι) (SkewBlockOffDiagonal.tracelessSkewSub ι)).finrank_eq]
  exact SkewBlockOffDiagonal.finrank_tracelessSkewSub ι

/-- `3`, `8`, `15` — now the dimensions of a Lie algebra. -/
theorem finrank_two_three_four :
    Module.finrank ℝ (tracelessSkewMat (Fin 2)) = 3
      ∧ Module.finrank ℝ (tracelessSkewMat (Fin 3)) = 8
      ∧ Module.finrank ℝ (tracelessSkewMat (Fin 4)) = 15 :=
  ⟨by rw [finrank_tracelessSkewMat]; simp,
   by rw [finrank_tracelessSkewMat]; simp,
   by rw [finrank_tracelessSkewMat]; simp⟩

/-! ## 5. It is a real form, not a complex subspace -/

/-- **MULTIPLYING BY `i` LEAVES `su(ι)`.** So `su(ι)` is not a complex subspace of the matrices,
which is the difference between it and `sl(ι, ℂ)` that `ERRATUM 316` exists to record. -/
theorem smul_I_notMem {A : Matrix ι ι ℂ} (hA : A ∈ skewSub ι) (hne : A ≠ 0) :
    Complex.I • A ∉ skewSub ι := by
  intro hIA
  rw [mem_skewSub_iff] at hA hIA
  have hfix : (Complex.I • A)ᴴ = Complex.I • A := by
    rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_I, hA, neg_smul_neg]
  have heq : Complex.I • A = -(Complex.I • A) := hfix.symm.trans hIA
  have hsum : Complex.I • A + Complex.I • A = 0 := by
    nth_rewrite 2 [heq]
    abel
  have h2 : (2 : ℂ) • (Complex.I • A) = 0 := by
    rw [two_smul]
    exact hsum
  have hI : Complex.I • A = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  exact hne ((smul_eq_zero.mp hI).resolve_left Complex.I_ne_zero)

end TracelessSkewLie
