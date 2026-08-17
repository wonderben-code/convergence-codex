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

`Complex.realPart_add_I_smul_imaginaryPart` decomposes every element of a complex star module as
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

**Nothing about the gauge orbit is proved.** `skewAdjoint` — the Lie algebra `𝔲(n)` — is the second
item on that file's missing list; it would follow from `skewAdjoint.negISMul` being an isomorphism,
and it is recorded here as **NOT DONE** rather than claimed, because this file does not build it.
The third item, the dimension of `unitaryGroup` as a manifold, is a different kind of statement
about a different kind of object and is not touched.

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

end SelfAdjointDimension
