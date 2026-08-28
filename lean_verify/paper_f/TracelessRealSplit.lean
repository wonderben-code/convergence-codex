import HermitianNotLie

/-!
# `sl(n,ℂ)` is `su(n) ⊕ i·su(n)` over `ℝ`, and so has twice the real dimension

`CascadeFoundation` says two things about the same object, four definitions apart:

> *"The traceless n×n complex matrices … This is `sl_n(ℂ)`, the complexification of `su(n)`."*
>
> *"`dim(sl₄(ℂ)) = 15`. **The Lie algebra of SU(4)**, the cascade gauge group."*

**The first is right and the second conflates a group with its complexification.** The Lie algebra
of `SU(4)` is `su(4)`, which is **real** of real dimension `15`; `sl₄(ℂ)` is the Lie algebra of
`SL(4,ℂ)`, of **complex** dimension `15` and **real dimension `30`**. The numeral `15` is a complex
dimension on one side of that sentence and a real dimension on the other, which is why the file can
contradict itself in four lines without anything noticing — `ERRATUM 325`'s pattern again, in a
second guise, in the base file the whole cascade cites.

This file proves the sentence that is right, which is what makes the sentence that is wrong
demonstrable.

## What is proved

> **`hermPart_mem` / `skewPart_mem`** — for a traceless `A`, both `½(A + Aᴴ)` and `½(A − Aᴴ)` are
> traceless, and Hermitian and anti-Hermitian respectively. The trace half needs
> `trace Aᴴ = conj (trace A)`.
>
> **`sup_eq`** — `tracelessHerm ι ⊔ tracelessSkewMat ι = traceZeroSub ι`, and **`inf_eq_bot`** —
> their intersection is `0`, since `Aᴴ = A` and `Aᴴ = −A` together force `A = 0`. So **the
> traceless matrices are the internal direct sum of the compact form and its `i`-multiple**, which
> is the concrete content of *"the complexification of `su(n)`"*.
>
> **`finrank_traceZeroSub = 2·((card ι)² − 1)`** — twice, not once.
>
> **`finrank_ne_tracelessSkewMat`** at `2 ≤ card ι` — **the two are not the same real space**, and
> the theorem says so by the only means that settles it: their real dimensions differ.
> **`finrank_four`** records `30` against `15` at `n = 4`, the case `CascadeFoundation`'s sentence
> is about.

## What is NOT claimed

**No complexification is constructed.** No tensor product `su(n) ⊗_ℝ ℂ` is built and no
isomorphism to one is exhibited; what is proved is the internal real direct sum, which is the
statement the docstring's phrase denotes concretely and **not** the same as building the functor.

**Nothing about `SU(n)` or `SL(n,ℂ)` as groups.** Neither is defined in this estate; the sentence
being corrected is about which algebra belongs to which group, and **this file settles only the
algebras**. That `su(n)` is the Lie algebra *of* `SU(n)` needs a smooth structure nothing here
builds — the reason `F4_1e_SpectralTripleArithmetic` records for not using the name `su`, followed
here as in `TracelessSkewLie` and `HermitianNotLie`.

**No Cartan decomposition and no symmetric space.** The splitting below is by Hermitian and
anti-Hermitian parts; **no involution is named, no `𝔨 ⊕ 𝔭` structure is claimed**, and the bracket
relations between the two summands are **not proved here** — `⁅p, p⁆ ⊆ k` and the rest are exactly
the statements this file does not make.

**Nothing in `CascadeFoundation` is withdrawn.** `traceless_dim_2`, `_3` and `_4` are true
statements about complex dimensions with untouched proofs; what is wrong there is one clause of
prose per docstring, corrected in place under `ERRATUM 94`.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TracelessRealSplit

open Matrix TracelessSkewLie HermitianNotLie

variable {ι : Type*} [Fintype ι]

/-! ## 1. The two halves of a traceless matrix -/

theorem trace_conjTranspose_eq_zero {A : Matrix ι ι ℂ} (h : Matrix.trace A = 0) :
    Matrix.trace Aᴴ = 0 := by
  rw [Matrix.trace_conjTranspose, h, star_zero]

theorem hermPart_mem {A : Matrix ι ι ℂ} (h : Matrix.trace A = 0) :
    ((2 : ℂ)⁻¹ • (A + Aᴴ)) ∈ tracelessHerm ι := by
  refine (mem_tracelessHerm_iff _).mpr ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    congr 1
    simp
  · rw [Matrix.trace_smul, Matrix.trace_add, h, trace_conjTranspose_eq_zero h, add_zero,
      smul_zero]

theorem skewPart_mem {A : Matrix ι ι ℂ} (h : Matrix.trace A = 0) :
    ((2 : ℂ)⁻¹ • (A - Aᴴ)) ∈ tracelessSkewMat ι := by
  refine (mem_tracelessSkewMat_iff _).mpr ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, ← neg_sub A Aᴴ, smul_neg]
    simp
  · rw [Matrix.trace_smul, Matrix.trace_sub, h, trace_conjTranspose_eq_zero h, sub_zero,
      smul_zero]

omit [Fintype ι] in
theorem eq_hermPart_add_skewPart (A : Matrix ι ι ℂ) :
    A = (2 : ℂ)⁻¹ • (A + Aᴴ) + (2 : ℂ)⁻¹ • (A - Aᴴ) := by
  rw [← smul_add]
  have h : A + Aᴴ + (A - Aᴴ) = (2 : ℂ) • A := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

/-! ## 2. The direct sum -/

/-- **THE TRACELESS MATRICES ARE THE REAL SUM OF THE TWO HALVES.** -/
theorem sup_eq : tracelessHerm ι ⊔ tracelessSkewMat ι = traceZeroSub ι := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro A hA
  have h : Matrix.trace A = 0 := hA
  rw [eq_hermPart_add_skewPart A]
  exact Submodule.add_mem_sup (hermPart_mem h) (skewPart_mem h)

/-- **AND THE SUM IS DIRECT**: Hermitian and anti-Hermitian at once forces zero. -/
theorem inf_eq_bot : tracelessHerm ι ⊓ tracelessSkewMat ι = ⊥ := by
  rw [← le_bot_iff]
  intro A hA
  have h1 : Aᴴ = A := ((mem_tracelessHerm_iff A).mp hA.1).1
  have h2 : Aᴴ = -A := ((mem_tracelessSkewMat_iff A).mp hA.2).1
  have hneg : A = -A := h1.symm.trans h2
  have h2' : (2 : ℂ) • A = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    abel
  have : A = 0 := (smul_eq_zero.mp h2').resolve_left two_ne_zero
  simpa using this

/-! ## 3. Twice, not once -/

theorem finrank_traceZeroSub [Nonempty ι] :
    Module.finrank ℝ (traceZeroSub ι) = 2 * (Fintype.card ι ^ 2 - 1) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (tracelessHerm ι) (tracelessSkewMat ι)
  rw [sup_eq, inf_eq_bot, finrank_bot, finrank_tracelessHerm, finrank_tracelessSkewMat] at h
  omega

/-- **THE TWO ARE NOT THE SAME REAL SPACE**, settled by the only thing that settles it. -/
theorem finrank_ne_tracelessSkewMat [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) :
    Module.finrank ℝ (traceZeroSub ι) ≠ Module.finrank ℝ (tracelessSkewMat ι) := by
  rw [finrank_traceZeroSub, finrank_tracelessSkewMat]
  have h : 4 ≤ Fintype.card ι ^ 2 := by nlinarith
  omega

/-- **`30` AGAINST `15`** — the case `CascadeFoundation`'s sentence is about. The `15` in
*"dim(sl₄(ℂ)) = 15, the Lie algebra of SU(4)"* is a **complex** dimension; the Lie algebra of
`SU(4)` has **real** dimension `15` and `sl₄(ℂ)` has real dimension `30`. -/
theorem finrank_four :
    Module.finrank ℝ (traceZeroSub (Fin 4)) = 30
      ∧ Module.finrank ℝ (tracelessSkewMat (Fin 4)) = 15 := by
  constructor
  · rw [finrank_traceZeroSub]
    simp
  · rw [finrank_tracelessSkewMat]
    simp

end TracelessRealSplit
