import LieAlgebraEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `sl₄(ℂ)` has a four-dimensional abelian subalgebra, so rank is not the obstruction

`SMEmbeddingHonest`'s "NOT proven here" paragraph gives two arguments for the full nonexistence
theorem and dismisses the second in one clause:

> The compact-forms rank argument (rank 4 > 3, maximal tori) is also valid FOR THE COMPACT FORMS,
> but **rank alone is NOT an obstruction inside `sl₄(ℂ)`, which contains 4-dimensional abelian
> subalgebras (an off-diagonal `2 × 2` block)**.

**That clause was prose, and it is the kind of prose this estate has been wrong about before**
(`ERRATUM 108` refuted a gap object nobody had tried to falsify). It is now a theorem, and it is
cheap: the witness the paragraph names works, and checking it takes four declarations.

## What is proved

> **`finrank_nilBlockRange = 4`** — the strictly-upper `2 × 2` block `[[0, B], [0, 0]]`, with `B`
> ranging over `M₂(ℂ)`, is a **four**-dimensional subspace of `TracelessMatrix 4`.
>
> **`nilBlock_mul_eq_zero`** — the product of any two of them is **zero**, so in particular they
> commute. `nilBlockRange_bracket_mem` records that the subspace is closed under the bracket: it is
> a subalgebra, not merely a subspace.
>
> **`finrank_cartanRange = 3`** — the diagonal traceless matrices, the Cartan, are **three**
> dimensional, and `cartanRange_bracket_mem` makes them abelian too.
>
> **`abelian_exceeds_cartan`** — `4 > 3`. **An abelian subalgebra of `sl₄(ℂ)` strictly larger than
> a Cartan subalgebra**, which is exactly what "rank is not an obstruction" means.

## What this does NOT prove, and the asymmetry is the whole point

**It does not say the embedding exists.** It removes one *proposed* obstruction and nothing more.
`SMEmbeddingHonest`'s actual refutation of its own maps stands untouched, and the nonexistence
theorem is still open — `ColourCommutant` closed one clause of the other argument and named the
step that remains.

**It says nothing about the compact form.** That `su(4)` has no abelian subspace of dimension above
`3` — the true statement, the one that makes the rank argument work for compact forms — is **not
proved here and nothing here begins it**: it needs maximal-torus theory. The contrast is the point,
and only one side of it is a theorem. `TracelessSkewDimension.traceless 4` is not mentioned below.

**"Subalgebra" is used in the weak sense** available to this estate: a subspace closed under
`X, Y ↦ X * Y − Y * X`. No `LieSubalgebra` instance is built and no Lie theory is invoked.

**⚠ "THE WEAK SENSE AVAILABLE TO THIS ESTATE" WAS WRONG, 2026-08-28.** The strong sense was in
Mathlib the whole time. `BlockGrading.sl_toSubmodule` is `rfl`: the ambient `tracelessSub ι` used
here **is** the carrier of `LieAlgebra.SpecialLinear.sl ι ℂ`, and `Ring.lie_def` makes
`X, Y ↦ X * Y − Y * X` **definitionally** Mathlib's bracket `⁅X, Y⁆`. A submodule closed under it
is a Lie subalgebra in content; what this file genuinely lacks is the packaged `LieSubalgebra`
**instance**, and nothing else. The sentence above is kept as the record of what was believed when
it was written (`ERRATUM 324`).

**⚠ THE DIMENSION RESTRICTION IS REMOVED 2026-08-28, and this file is kept as the `n = 4` case.**
`SlAbelianGeneral` proves the same thing over `Fin p ⊕ Fin q` for every `p, q ≥ 2`: the strictly
upper `p × q` block is a `p·q`-dimensional abelian subalgebra of `sl_{p+q}(ℂ)`, the Cartan is
`p + q − 1`, and `p + q − 1 < p·q`. **So "abelian dimension ≤ rank" fails in `sl_n(ℂ)` for every
`n ≥ 4`, by a margin of `(p−1)(q−1)`** — at `p = q` that is `n²/4` against `n − 1`, so the failure
is not marginal. `abelian_exceeds_cartan_four` there is this file's `4 > 3`, recorded rather than
reproved (`ERRATUM 313`); the two files build the same subspace over different index types and
neither is a duplicate of the other. **Nothing about the compact form moves in either file**, and
that asymmetry is now quantified on one side and still untouched on the other.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SlFourAbelian

open Matrix

/-! ## 1. The strictly-upper `2 × 2` block -/

/-- `B ↦ [[0, B], [0, 0]]`: rows `0, 1` against columns `2, 3`, everything else zero. -/
def nilBlockFn (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j =>
    if hi : i.val < 2 then
      if hj : 2 ≤ j.val then B ⟨i.val, hi⟩ ⟨j.val - 2, by omega⟩ else 0
    else 0

/-- **THE PRODUCT OF ANY TWO IS ZERO.** A nonzero entry of the first needs its column index `≥ 2`
and a nonzero entry of the second needs its row index `< 2`; the sum has no surviving term. -/
theorem nilBlock_mul_eq_zero (B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    nilBlockFn B * nilBlockFn B' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilBlockFn, Matrix.mul_apply, Fin.sum_univ_four]

theorem nilBlockFn_diag (B : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) : nilBlockFn B i i = 0 := by
  fin_cases i <;> simp [nilBlockFn]

theorem nilBlockFn_mem (B : Matrix (Fin 2) (Fin 2) ℂ) : nilBlockFn B ∈ TracelessMatrix 4 := by
  refine LinearMap.mem_ker.mpr ?_
  simp only [traceMap, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag]
  exact Finset.sum_eq_zero fun i _ => nilBlockFn_diag B i

/-- The block, as a linear map into `sl₄(ℂ)`. -/
noncomputable def nilBlockMap : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] TracelessMatrix 4 where
  toFun B := ⟨nilBlockFn B, nilBlockFn_mem B⟩
  map_add' B B' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilBlockFn]
  map_smul' c B := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilBlockFn]

theorem nilBlockMap_injective : Function.Injective nilBlockMap := by
  intro B B' h
  have hval : nilBlockFn B = nilBlockFn B' := congrArg Subtype.val h
  ext i j
  have hij := congrFun (congrFun hval ⟨i.val, by omega⟩) ⟨j.val + 2, by omega⟩
  have hi : (i : ℕ) ≤ 1 := by omega
  simpa [nilBlockFn, hi] using hij

/-- **THE WITNESS**, as a subspace. -/
noncomputable def nilBlockRange : Submodule ℂ (TracelessMatrix 4) := LinearMap.range nilBlockMap

theorem finrank_nilBlockRange : Module.finrank ℂ nilBlockRange = 4 := by
  rw [nilBlockRange, LinearMap.finrank_range_of_inj nilBlockMap_injective, Module.finrank_matrix]
  simp

/-- **AND IT IS A SUBALGEBRA**, in the weak sense this estate has: closed under the commutator,
because the commutator of any two of its elements is zero. -/
theorem nilBlockRange_bracket_mem {X Y : TracelessMatrix 4}
    (hX : X ∈ nilBlockRange) (hY : Y ∈ nilBlockRange) :
    (X : Matrix (Fin 4) (Fin 4) ℂ) * (Y : Matrix (Fin 4) (Fin 4) ℂ)
      - (Y : Matrix (Fin 4) (Fin 4) ℂ) * (X : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨B', rfl⟩ := hY
  have h1 : ((nilBlockMap B : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ) = nilBlockFn B := rfl
  have h2 : ((nilBlockMap B' : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ) = nilBlockFn B' := rfl
  rw [h1, h2, nilBlock_mul_eq_zero, nilBlock_mul_eq_zero, sub_zero]

/-! ## 2. The Cartan, for comparison -/

/-- `a ↦ diag(a₀, a₁, a₂, −(a₀ + a₁ + a₂))`: the diagonal traceless matrices. -/
def cartanFn (a : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a 0, a 1, a 2, -(a 0 + a 1 + a 2)]

theorem cartanFn_mem (a : Fin 3 → ℂ) : cartanFn a ∈ TracelessMatrix 4 := by
  refine LinearMap.mem_ker.mpr ?_
  simp only [traceMap, Matrix.traceLinearMap_apply, cartanFn, Matrix.trace_diagonal,
    Fin.sum_univ_four]
  simp

noncomputable def cartanMap : (Fin 3 → ℂ) →ₗ[ℂ] TracelessMatrix 4 where
  toFun a := ⟨cartanFn a, cartanFn_mem a⟩
  map_add' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cartanFn]
    ring
  map_smul' c a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cartanFn]
    ring

theorem cartanMap_injective : Function.Injective cartanMap := by
  intro a b h
  have hval : cartanFn a = cartanFn b := congrArg Subtype.val h
  funext i
  fin_cases i
  · simpa [cartanFn] using congrFun (congrFun hval 0) 0
  · simpa [cartanFn] using congrFun (congrFun hval 1) 1
  · simpa [cartanFn] using congrFun (congrFun hval 2) 2

noncomputable def cartanRange : Submodule ℂ (TracelessMatrix 4) := LinearMap.range cartanMap

/-- **THREE DIMENSIONS**, which is the rank of `sl₄(ℂ)`. -/
theorem finrank_cartanRange : Module.finrank ℂ cartanRange = 3 := by
  rw [cartanRange, LinearMap.finrank_range_of_inj cartanMap_injective, Module.finrank_pi_fintype ℂ]
  simp

theorem cartanRange_bracket_mem {X Y : TracelessMatrix 4}
    (hX : X ∈ cartanRange) (hY : Y ∈ cartanRange) :
    (X : Matrix (Fin 4) (Fin 4) ℂ) * (Y : Matrix (Fin 4) (Fin 4) ℂ)
      - (Y : Matrix (Fin 4) (Fin 4) ℂ) * (X : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  obtain ⟨a, rfl⟩ := hX
  obtain ⟨b, rfl⟩ := hY
  have h1 : ((cartanMap a : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ) = cartanFn a := rfl
  have h2 : ((cartanMap b : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ) = cartanFn b := rfl
  rw [h1, h2, cartanFn, cartanFn, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ## 3. Rank is not the obstruction -/

/-- **AN ABELIAN SUBALGEBRA STRICTLY LARGER THAN A CARTAN.** `4 > 3`, both exhibited, both abelian.
Inside `sl₄(ℂ)` the inequality "abelian dimension ≤ rank" is therefore **false**, and an argument
that an image is too big to be abelian cannot rest on rank alone.

**This says nothing about the compact form**, where the inequality does hold and the rank argument
is valid. That statement needs maximal-torus theory, is not proved here, and is not begun here. -/
theorem abelian_exceeds_cartan :
    Module.finrank ℂ cartanRange < Module.finrank ℂ nilBlockRange := by
  rw [finrank_cartanRange, finrank_nilBlockRange]
  norm_num

end SlFourAbelian
