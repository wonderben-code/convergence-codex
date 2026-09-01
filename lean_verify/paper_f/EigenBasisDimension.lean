import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# A basis of eigenvectors makes an eigenspace's dimension a fibre count

`BoxLapMultiplicity` bounds the set of frequency vectors sharing a box eigenvalue and fences on
exactly one thing: *"it is a fibre count, not an eigenspace dimension … that the eigenspace is
spanned by the fibre's basis vectors is not proved here, and nothing here says a `finrank`."* This
file proves it, for an arbitrary matrix over an arbitrary field.

> **`ker_sub_smul_eq_span`** — if a basis `b` of `ι → K` satisfies `A *ᵥ b k = ν k • b k`, then the
> eigenspace of `A` at `μ` is **exactly** the span of the basis vectors whose eigenvalue is `μ`.
>
> **`finrank_ker_sub_smul`** — hence its dimension is `Nat.card {k // ν k = μ}`, the size of `ν`'s
> fibre over `μ`.

## What the estate already had, and why this is not it

`TorusRealMultiplicity.finrank_eigenspace_massive_real` is this statement **for the torus's massive
Laplacian**, and it is reached by a route that only that operator affords: diagonalise over `ℂ`
against the characters (`TorusMultiplicity.finrank_eigenspace_massive`), then transfer the kernel's
dimension back with `RealComplexKernel.finrank_eigenspace_cx`. **Nothing in it is available to a
real basis that is not a character family.** The box's modes are half-step cosines, they are already
real, and there is no complexification to undo — so the general statement is what that case needs,
and it is shorter than the special one.

**Mathlib does not have it either**, probed by concept rather than by one spelling on 1 September
2026 (`ERRATUM 384`'s rule): of the ten names pairing `eigenspace` with `finrank`, `rank`, `card`,
`basis` or `dim`, every one is about **generalised** eigenspaces and their stabilisation index
(`genEigenspace_le_genEigenspace_finrank`, `maxGenEigenspace_eq_genEigenspace_finrank`,
`finrank_genEigenspace_le`, …) or an upper bound (`LinearMap.finrank_eigenspace_le`). **None
computes an eigenspace's dimension from a basis of eigenvectors.**

## What this is NOT

**It assumes the eigenbasis.** Nothing here says one exists — that is the spectral theorem — and
the consumers supply their own.

**No multiplicity is computed.** This turns a fibre count into a dimension; **counting the fibre is
a separate question** and `BoxLapMultiplicity` shows on the box that the obvious group-theoretic
answer is not the whole one. Not costed here (`ERRATUM 194`, `ERRATUM 246`).

**It is not applied.** No graph, no box and no `massive` appears; wiring it to
`BoxLapBasis.boxLapBasis` is a further unit and is **not done here**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace EigenBasisDimension

open Finset Matrix

variable {ι K : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- **THE EIGENSPACE IS THE SPAN OF THE BASIS VECTORS WITH THAT EIGENVALUE.** -/
theorem ker_sub_smul_eq_span {A : Matrix ι ι K} (b : Module.Basis ι K (ι → K)) {ν : ι → K}
    (heig : ∀ k, A *ᵥ b k = ν k • b k) (μ : K) :
    LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)
      = Submodule.span K (Set.range fun k : {k // ν k = μ} => b k.val) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Matrix.toLin'_apply] at hx
    have hrepr : ∑ k, b.repr x k • b k = x := b.sum_repr x
    have hzero : ∑ k, ((ν k - μ) * b.repr x k) • b k = 0 := by
      have hA : A *ᵥ x = ∑ k, (ν k * b.repr x k) • b k := by
        conv_lhs => rw [← hrepr]
        rw [Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [Matrix.mulVec_smul, heig, smul_smul, mul_comm]
      have hμ : μ • x = ∑ k, (μ * b.repr x k) • b k := by
        conv_lhs => rw [← hrepr, Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _
      have hsplit : ∑ k, ((ν k - μ) * b.repr x k) • b k
          = (∑ k, (ν k * b.repr x k) • b k) - ∑ k, (μ * b.repr x k) • b k := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [← sub_smul, sub_mul]
      rw [hsplit, ← hA, ← hμ, hx]
    have hcoef : ∀ k, (ν k - μ) * b.repr x k = 0 :=
      Fintype.linearIndependent_iff.1 b.linearIndependent _ hzero
    have hout : ∀ k, ν k ≠ μ → b.repr x k = 0 := by
      intro k hk
      rcases mul_eq_zero.1 (hcoef k) with h | h
      · exact absurd (sub_eq_zero.1 h) hk
      · exact h
    rw [← hrepr]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : ν k = μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩)
    · rw [hout k hk, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Matrix.toLin'_apply, heig, hk, sub_self]

/-- **SO ITS DIMENSION IS THE SIZE OF THE FIBRE.** -/
theorem finrank_ker_sub_smul {A : Matrix ι ι K} (b : Module.Basis ι K (ι → K)) {ν : ι → K}
    (heig : ∀ k, A *ᵥ b k = ν k • b k) (μ : K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Nat.card {k // ν k = μ} := by
  classical
  rw [ker_sub_smul_eq_span b heig μ]
  have hli : LinearIndependent K fun k : {k // ν k = μ} => b k.val :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  rw [finrank_span_eq_card hli, Nat.card_eq_fintype_card]

end EigenBasisDimension
