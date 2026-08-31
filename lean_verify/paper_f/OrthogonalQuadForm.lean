import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# An orthogonal eigenbasis bounds a quadratic form

`BoxModeOrthogonal` closed by naming exactly one missing step: *"turning an orthogonal eigenbasis
into `x ⬝ᵥ A *ᵥ x ≤ ρ·(x ⬝ᵥ x)` needs the expansion of an arbitrary `x` in this basis and a
term-by-term comparison; that is a further unit."* This is that unit, and it is stated for an
arbitrary matrix so that nothing about graphs, boxes or cosines enters.

> **`dotProduct_expand`** — with the basis pairwise orthogonal, a pairing of two expansions
> collapses to a **single sum**: `(∑ f k • bₖ) ⬝ᵥ (∑ g l • b_l) = ∑ f k · g k · (bₖ ⬝ᵥ bₖ)`.
>
> **`quadForm_le_of_orthogonal_eigenbasis`** — hence if `A` is diagonalised by an orthogonal basis
> with eigenvalues `ν`, and `ν k ≤ c` for every `k`, then `x ⬝ᵥ A *ᵥ x ≤ c·(x ⬝ᵥ x)` **for every
> `x`**.

## Why it is a single sum and why that is the whole proof

Expand `x = ∑ₖ rₖ bₖ`. Then `A *ᵥ x = ∑ₖ (rₖ νₖ) bₖ`, because `A` is linear and each `bₖ` is an
eigenvector. Pairing the two expansions, orthogonality deletes every off-diagonal term, leaving
`∑ₖ νₖ rₖ² ‖bₖ‖²` against `∑ₖ rₖ² ‖bₖ‖²`; `rₖ² ≥ 0` and `‖bₖ‖² ≥ 0` make the comparison termwise.
**No spectral theorem is invoked and the basis is not normalised** — the square norms cancel out of
the comparison rather than being set to `1`, which is what lets a consumer use a basis it has
proved orthogonal without also computing its lengths.

## What this is NOT

**It assumes the orthogonality rather than deriving it.** Nothing here says an eigenbasis can be
chosen orthogonal; that is the spectral theorem, and the consumers of this lemma
(`SymmetricEigenOrthogonal`, `BoxModeOrthogonal`) prove orthogonality by hand for the family they
already have.

**It is one-sided.** `ν k ≤ c` gives an upper bound only; a lower bound is the same statement
applied to `−A`, which is **not** done here.

**No matrix inequality.** The conclusion is about the quadratic form at each `x`; converting it to
the Loewner order needs `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` and a symmetry hypothesis,
as in `LaplacianDegreeBound`, and is **not** done here. As of 31 Aug 2026 neither omission is
costed (`ERRATUM 194`, `ERRATUM 246`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace OrthogonalQuadForm

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/-! ## 1. Orthogonality collapses a double sum -/

/-- **THE OFF-DIAGONAL TERMS VANISH.** -/
theorem dotProduct_expand {b : ι → (ι → ℝ)} (horth : ∀ k l, k ≠ l → b k ⬝ᵥ b l = 0)
    (f g : ι → ℝ) :
    (∑ k, f k • b k) ⬝ᵥ (∑ l, g l • b l) = ∑ k, f k * g k * (b k ⬝ᵥ b k) := by
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_sum, Finset.sum_eq_single k]
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  · intro l _ hl
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, horth k l (Ne.symm hl)]
    ring
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ## 2. The bound -/

/-- **AN ORTHOGONAL EIGENBASIS BOUNDS THE QUADRATIC FORM BY THE LARGEST EIGENVALUE.** -/
theorem quadForm_le_of_orthogonal_eigenbasis {A : Matrix ι ι ℝ} (b : Module.Basis ι ℝ (ι → ℝ))
    {ν : ι → ℝ} (heig : ∀ k, A *ᵥ b k = ν k • b k)
    (horth : ∀ k l, k ≠ l → b k ⬝ᵥ b l = 0) (hnn : ∀ k, 0 ≤ b k ⬝ᵥ b k)
    {c : ℝ} (hc : ∀ k, ν k ≤ c) (x : ι → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ c * (x ⬝ᵥ x) := by
  obtain ⟨r, rfl⟩ : ∃ r : ι → ℝ, ∑ k, r k • b k = x :=
    ⟨fun k => b.repr x k, b.sum_repr x⟩
  have hAx : A *ᵥ (∑ k, r k • b k) = ∑ k, (r k * ν k) • b k := by
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mulVec_smul, heig, smul_smul]
  rw [hAx, dotProduct_expand horth, dotProduct_expand horth, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : 0 ≤ r k * r k * (b k ⬝ᵥ b k) := mul_nonneg (mul_self_nonneg _) (hnn k)
  nlinarith [h1, hc k]

end OrthogonalQuadForm
