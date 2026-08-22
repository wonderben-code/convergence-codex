import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# The real dimension of the self-adjoint part, and `dim_ℝ Herm_n(ℂ) = n²`

`F4_1l_GaussianPartition` records, in its own prose, a gap it then works around:

> *"Mathlib does NOT have finrank computations for: `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)` as a
> real vector space … Therefore the gauge orbit theorems below express the dimension arithmetic in
> terms of the FULL matrix space finrank, which Mathlib CAN verify."*

So `dim_U4` and `physical_dof` there are stated about `Module.finrank ℂ CascadeAlgebra` — a
**proxy** that happens to carry the same number — rather than about `Herm₄(ℂ)`, which is the space
the argument is about. This file supplies the missing fact.

> **`finrank_selfAdjoint_matrix`** —
> `Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) = n²`.

## The route, and it is short because Mathlib has the hard half

`realPart_add_I_smul_imaginaryPart` (root namespace — this header said
`Complex.realPart_add_I_smul_imaginaryPart`, which does not exist; `ERRATUM 224`, and the wrong
spelling is kept here rather than deleted) decomposes every element of a complex star module as
`ℜ a + I • ℑ a` with **both parts self-adjoint**, and `selfAdjoint.realPart_coe`,
`IsSelfAdjoint.imaginaryPart`, `realPart_I_smul` and `imaginaryPart_I_smul` are exactly the four
round-trip identities. So `(x, y) ↦ x + I • y` is a **linear equivalence**
`selfAdjoint A × selfAdjoint A ≃ₗ[ℝ] A`, hence `finrank ℝ A = 2 · finrank ℝ (selfAdjoint A)` — a
statement about **any** complex star module — and the matrix case is `Module.finrank_matrix` divided
by two. **No basis of Hermitian matrices is chosen anywhere**, which is what makes the general
statement come out at the same price as the `4 × 4` one.

## What this is not

**It is not a claim that the proxy statements in `F4_1l_GaussianPartition` were wrong.** They are
true and they were stated honestly, with the workaround named in a comment. What was missing was
the ability to say the same arithmetic about the *right space*, and that is what changes here.

**SUPERSEDED THE SAME DAY BY §3 OF THIS FILE, AND THE ROUTE IT NAMED WAS THE ROUTE.** This section
said:

> *"**Nothing about the gauge orbit is proved.** `skewAdjoint` — the Lie algebra `𝔲(n)` — is the
> second item on that file's missing list; it would follow from `skewAdjoint.negISMul` being an
> isomorphism, and it is recorded here as **NOT DONE** rather than claimed, because this file does
> not build it."*

§3 builds it: `skewAdjointEquivSelfAdjoint` is exactly `skewAdjoint.negISMul` upgraded, and
**`finrank_skewAdjoint_matrix` gives `dim_ℝ 𝔲(n) = n²`**. So the **second** of the three missing
facts is also supplied, and the prediction of the route was right — which is worth separating from
the fact that I recorded it as undone rather than doing it, since the whole cost was one section.

**The third item is untouched and stays untouched.** The dimension of `unitaryGroup (Fin n) ℂ` as a
**manifold** is a statement about a smooth structure, not about a module, and nothing here bears on
it. **Neither does anything here prove the gauge orbit's dimension**, which is what the arithmetic
in `F4_1l_GaussianPartition` consumes: `dim 𝔲(n) = n²` is the dimension of the *group acting*, and
the dimension of a generic *orbit* is `n² − n`, which needs a stabiliser computation this file does
not do.

**No published tag moves**, and no physics claim is made or moved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SelfAdjointDimension

open Complex ComplexStarModule

section StarModule

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- **A COMPLEX STAR MODULE IS TWO COPIES OF ITS SELF-ADJOINT PART.** The map is
`(x, y) ↦ x + I • y`; the inverse is `a ↦ (ℜ a, ℑ a)`, and both round trips are Mathlib
identities. -/
noncomputable def selfAdjointProdEquiv : (selfAdjoint A × selfAdjoint A) ≃ₗ[ℝ] A where
  toFun p := (p.1 : A) + I • (p.2 : A)
  invFun a := (ℜ a, ℑ a)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, selfAdjoint.val_smul, RingHom.id_apply, smul_add,
      smul_comm I c]
  left_inv p := by
    obtain ⟨x, y⟩ := p
    have hy : ℑ (y : A) = 0 := y.property.imaginaryPart
    have hx : ℑ (x : A) = 0 := x.property.imaginaryPart
    ext <;>
      simp [realPart_I_smul, imaginaryPart_I_smul, hx, hy]
  right_inv a := realPart_add_I_smul_imaginaryPart a

/-- **AND SO THE SELF-ADJOINT PART IS EXACTLY HALF THE REAL DIMENSION.** -/
theorem two_mul_finrank_selfAdjoint [FiniteDimensional ℝ A] :
    2 * Module.finrank ℝ (selfAdjoint A) = Module.finrank ℝ A := by
  haveI : Module.Finite ℝ (selfAdjoint A) :=
    Module.Finite.of_injective (selfAdjoint.submodule ℝ A).subtype Subtype.val_injective
  have h := (selfAdjointProdEquiv (A := A)).finrank_eq
  rw [Module.finrank_prod] at h
  omega

end StarModule

/-! ## The matrix case -/

/-- The complex `n × n` matrices have real dimension `2n²`. -/
theorem finrank_real_matrix (n : ℕ) :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix (R := ℝ) (M := ℂ) (Fin n) (Fin n), Complex.finrank_real_complex,
    Fintype.card_fin]
  ring

instance finiteDimensional_matrix (n : ℕ) :
    FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ) := by
  have : Module.Finite ℝ (Fin n → Fin n → ℂ) := inferInstance
  exact this

/-- **THE MISSING FACT, SUPPLIED.** `dim_ℝ Herm_n(ℂ) = n²` — the `n` real diagonal entries and the
`n(n−1)/2` complex entries above them, counted without ever choosing a basis. -/
theorem finrank_selfAdjoint_matrix (n : ℕ) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)) = n ^ 2 := by
  have h := two_mul_finrank_selfAdjoint (A := Matrix (Fin n) (Fin n) ℂ)
  rw [finrank_real_matrix n] at h
  omega

/-- **THE CASCADE INSTANCE.** `dim_ℝ Herm₄(ℂ) = 16`, stated about `Herm₄(ℂ)` itself rather than
about the full matrix algebra standing in for it. -/
theorem finrank_selfAdjoint_four :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ)) = 16 := by
  rw [finrank_selfAdjoint_matrix 4]
  norm_num

/-- And the two-by-two case, which `MinkowskiHerm2.pauliHerm` parametrises by hand: that
parametrisation is a bijection onto a space now known to be four-dimensional without reference to
the Pauli basis. -/
theorem finrank_selfAdjoint_two :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) = 4 := by
  rw [finrank_selfAdjoint_matrix 2]
  norm_num

/-! ## 3. The skew-adjoint part, which is the same size -/

section SkewAdjoint

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- **MULTIPLICATION BY `i` IS A LINEAR EQUIVALENCE FROM SKEW-ADJOINT TO SELF-ADJOINT.** Mathlib has
the map (`skewAdjoint.negISMul`) and one side of the round trip (`skewAdjoint.I_smul_neg_I`); this
supplies the other side and bundles them. -/
noncomputable def skewAdjointEquivSelfAdjoint : skewAdjoint A ≃ₗ[ℝ] selfAdjoint A where
  toFun := skewAdjoint.negISMul
  invFun x := ⟨I • (x : A), by
    rw [skewAdjoint.mem_iff, star_smul, star_def, conj_I, selfAdjoint.star_val_eq, neg_smul]⟩
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv a := by
    ext
    simpa using skewAdjoint.I_smul_neg_I a
  right_inv x := by
    ext
    simp [skewAdjoint.negISMul_apply_coe, smul_smul]

/-- **AND SO THE TWO HALVES HAVE THE SAME DIMENSION.** -/
theorem finrank_skewAdjoint_eq :
    Module.finrank ℝ (skewAdjoint A) = Module.finrank ℝ (selfAdjoint A) :=
  (skewAdjointEquivSelfAdjoint (A := A)).finrank_eq

end SkewAdjoint

/-- **THE SECOND MISSING FACT, SUPPLIED: `dim_ℝ 𝔲(n) = n²`.** The skew-Hermitian matrices are the
Lie algebra of the unitary group, and multiplication by `i` carries them bijectively onto the
Hermitian ones. -/
theorem finrank_skewAdjoint_matrix (n : ℕ) :
    Module.finrank ℝ (skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) = n ^ 2 := by
  rw [finrank_skewAdjoint_eq, finrank_selfAdjoint_matrix n]

/-- **`dim_ℝ 𝔲(4) = 16`**, which `F4_1l_GaussianPartition.dim_U4`'s docstring asserts in prose —
*"the Lie algebra `𝔲(4)` consists of skew-Hermitian `4 × 4` matrices; as a real vector space
`dim_ℝ(𝔲(4)) = n²`"* — and which is now a theorem about that space rather than a sentence about
it. -/
theorem finrank_skewAdjoint_four :
    Module.finrank ℝ (skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ)) = 16 := by
  rw [finrank_skewAdjoint_matrix 4]
  norm_num

/-- **AND THE TWO HALVES TOGETHER ARE THE WHOLE SPACE**, which is `two_mul_finrank_selfAdjoint` read
with §3: `n² + n² = 2n²`. Stated because the pair is what the decomposition means, and because it
is the shape a reader checking the arithmetic will want. -/
theorem finrank_selfAdjoint_add_skewAdjoint (n : ℕ) :
    Module.finrank ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ))
        + Module.finrank ℝ (skewAdjoint (Matrix (Fin n) (Fin n) ℂ))
      = Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) := by
  rw [finrank_selfAdjoint_matrix n, finrank_skewAdjoint_matrix n, finrank_real_matrix n]
  ring

end SelfAdjointDimension
