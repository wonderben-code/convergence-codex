import SelfAdjointDimension
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# `dim_ℝ 𝔰𝔲(n) = n² − 1`, and a recorded obstruction that was the wrong obstruction

`F4_1e_SpectralTripleArithmetic` marks the `𝔰𝔲(n)` generator counts **OUT OF SCOPE** and says why:

> *"Mathlib has no `finrank skewAdjointMatricesLieSubalgebra` or `dim(su(n))` theorem. **The
> generator counts `n²−1` require Lie algebra structure not available.** We prove the ARITHMETIC
> identity and note the gap."*

So `dim_su2` there is `2 ^ 2 - 1 = 3` — a true statement about natural numbers, named after a Lie
algebra, with *"3 attempts exhausted"* recorded against the real one. **The first clause of that
diagnosis is right and the second is not.** Mathlib has no such theorem, but the count does **not**
require a Lie bracket: the traceless skew-Hermitian matrices are the kernel of one real-linear
functional on a space whose dimension `SelfAdjointDimension.finrank_skewAdjoint_matrix` now gives,
and rank–nullity does the rest.

> **`finrank_traceless_add`** — `finrank ℝ (traceless skew-Hermitian `n × n`) + 1 = n²`,
> for every `n ≥ 1`. Hence `3`, `8` and `15` at `n = 2, 3, 4`.

## What is proved and what is only named

**Proved:** a statement of linear algebra about a subspace of matrices. The functional is
`A ↦ im (tr A)`; it is real-linear because `trace` is additive and commutes with real scalars and
`Complex.im` is real-linear; it is onto because `i · 1` has trace `i·n`.

**NOT proved, and the name is where the temptation is.** That this subspace *is* the Lie algebra of
`SU(n)` — the tangent space at the identity of a smooth group — is a statement about a smooth
structure, and **nothing here builds one**. The definition below is called `traceless` rather than
`su` for exactly that reason. `F4_1e`'s third recorded gap, the dimension of `unitaryGroup` as a
manifold, is the same kind of statement and is equally untouched.

**Nor is the bracket used or supplied.** The subspace *is* closed under the commutator, and that is
a fact this file neither needs nor proves. What is refuted is only the recorded claim that the
**dimension** needs it.

**No published tag moves**, and no physics claim is made or moved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TracelessSkewDimension

open Complex

/-- **THE IMAGINARY PART OF THE TRACE, AS A REAL-LINEAR FUNCTIONAL ON THE SKEW-HERMITIAN
MATRICES.** A skew-Hermitian matrix has purely imaginary trace, so this loses nothing. -/
noncomputable def traceIm (n : ℕ) :
    skewAdjoint (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (A : Matrix (Fin n) (Fin n) ℂ)).im
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' c A := by
    simp only [RingHom.id_apply, skewAdjoint.val_smul, Matrix.trace_smul]
    exact Complex.smul_im c _

/-- **THE TRACELESS SKEW-HERMITIAN MATRICES.** Called `traceless` and not `su`: this is a subspace
of matrices, and nothing here says it is the tangent space of a smooth group. -/
noncomputable def traceless (n : ℕ) : Submodule ℝ (skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) :=
  LinearMap.ker (traceIm n)

/-- `i · 1` is skew-Hermitian. -/
theorem iOne_mem (n : ℕ) :
    (I • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := by
  rw [skewAdjoint.mem_iff, star_smul, star_def, conj_I, star_one, neg_smul]

/-- **THE FUNCTIONAL IS ONTO**, witnessed by `i · 1`, whose trace is `i·n`. -/
theorem traceIm_surjective (n : ℕ) (hn : 0 < n) : Function.Surjective (traceIm n) := by
  intro r
  have hw : traceIm n ⟨I • (1 : Matrix (Fin n) (Fin n) ℂ), iOne_mem n⟩ = (n : ℝ) := by
    simp [traceIm, Matrix.trace_smul, Matrix.trace_one]
  refine ⟨(r / n) • ⟨I • (1 : Matrix (Fin n) (Fin n) ℂ), iOne_mem n⟩, ?_⟩
  rw [map_smul, hw, smul_eq_mul, div_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr hn.ne'

instance finiteDimensional_skewAdjoint (n : ℕ) :
    FiniteDimensional ℝ (skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : Module.Finite ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) :=
    Module.Finite.of_injective
      (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)).subtype Subtype.val_injective
  exact Module.Finite.equiv
    (SelfAdjointDimension.skewAdjointEquivSelfAdjoint
      (A := Matrix (Fin n) (Fin n) ℂ)).symm

/-- **THE COUNT, WITHOUT A BRACKET.** Rank–nullity against `traceIm`, on a space whose dimension is
`SelfAdjointDimension.finrank_skewAdjoint_matrix`. Stated additively so no subtraction on `ℕ`
appears. -/
theorem finrank_traceless_add (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (traceless n) + 1 = n ^ 2 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (traceIm n)
  rw [SelfAdjointDimension.finrank_skewAdjoint_matrix n,
    LinearMap.range_eq_top.mpr (traceIm_surjective n hn), finrank_top,
    Module.finrank_self] at hrn
  rw [traceless]
  omega

/-- **`dim_ℝ 𝔰𝔲(2) = 3`** — the count `F4_1e.dim_su2` names and states as `2 ^ 2 - 1 = 3`. -/
theorem finrank_traceless_two : Module.finrank ℝ (traceless 2) = 3 := by
  have h := finrank_traceless_add 2 (by norm_num)
  norm_num at h
  omega

/-- **`dim_ℝ 𝔰𝔲(3) = 8`** — the Gell-Mann count. -/
theorem finrank_traceless_three : Module.finrank ℝ (traceless 3) = 8 := by
  have h := finrank_traceless_add 3 (by norm_num)
  norm_num at h
  omega

/-- **`dim_ℝ 𝔰𝔲(4) = 15`** — the cascade's gauge algebra, as a dimension rather than as an
arithmetic identity about `16 − 1`. -/
theorem finrank_traceless_four : Module.finrank ℝ (traceless 4) = 15 := by
  have h := finrank_traceless_add 4 (by norm_num)
  norm_num at h
  omega

/-- **AND THE TRACE DIRECTION IS THE WHOLE DIFFERENCE**, which is what
`F4_1e.su_generators` asserts arithmetically: `𝔲(n)` is `𝔰𝔲(n)` plus one dimension. -/
theorem finrank_traceless_add_one_eq_skewAdjoint (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (traceless n) + 1
      = Module.finrank ℝ (skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) := by
  rw [SelfAdjointDimension.finrank_skewAdjoint_matrix n]
  exact finrank_traceless_add n hn

/-! ## 2. Products, which is what a direct sum of these subspaces costs -/

instance finiteDimensional_traceless (n : ℕ) : FiniteDimensional ℝ (traceless n) :=
  FiniteDimensional.finiteDimensional_submodule _

/-- **THE `4 ⊕ 2 ⊕ 2` PATTERN: `15 + 3 + 3 = 21`, AS A DIMENSION.**
`F4_1e.pati_salam_generators` states `15 + 3 + 3 = 21` on naturals and records
*"requires direct sum of Lie algebra dimensions — 3 attempts exhausted"*. **A direct sum of finite
subspaces costs `Module.finrank_prod`**, which is in Mathlib, and the three summands' dimensions are
§1. No Lie structure is used.

**What this is a statement about**: the product of three subspaces of matrix spaces. Reading it as
*the Pati–Salam gauge algebra* is an identification this file does not make and does not need —
see §1's note on why the definition is called `traceless`. -/
theorem finrank_prod_4_2_2 :
    Module.finrank ℝ (traceless 4 × traceless 2 × traceless 2) = 21 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_traceless_four, finrank_traceless_two]

/-- **THE `3 ⊕ 2 ⊕ 1` PATTERN: `8 + 3 + 1 = 12`, AS A DIMENSION.**
`F4_1e.sm_generators` states `8 + 3 + 1 = 12` on naturals with the same recorded reason. The third
summand is `skewAdjoint (M₁(ℂ))`, whose dimension is `1² = 1` by
`SelfAdjointDimension.finrank_skewAdjoint_matrix`. -/
theorem finrank_prod_3_2_1 :
    Module.finrank ℝ
        (traceless 3 × traceless 2 × skewAdjoint (Matrix (Fin 1) (Fin 1) ℂ)) = 12 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_traceless_three, finrank_traceless_two,
    SelfAdjointDimension.finrank_skewAdjoint_matrix 1]
  norm_num

/-- **AND THE DIFFERENCE IS NINE**, which `F4_1e`'s next docstring reads as six leptoquarks plus
three right-handed weak bosons. **That reading is not proved here**: this is `21 − 12`, and nothing
in this file decomposes either space. -/
theorem finrank_prod_diff :
    Module.finrank ℝ (traceless 4 × traceless 2 × traceless 2)
      = Module.finrank ℝ
          (traceless 3 × traceless 2 × skewAdjoint (Matrix (Fin 1) (Fin 1) ℂ)) + 9 := by
  rw [finrank_prod_4_2_2, finrank_prod_3_2_1]

end TracelessSkewDimension
