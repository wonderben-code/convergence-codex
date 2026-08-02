/-
  CliffordIso: Cl₄(ℂ) ≅ M₄(ℂ) — the Isomorphism, Closing Gap N3
  ==============================================================

  SPINE link L8 and gap N3 (the ledgers live in the companion repository
  codex-internal): `F4_1e_CliffordMatrix` built the algebra homomorphism
  Cl₄(ℂ) →ₐ[ℂ] M₄(ℂ) via explicit gamma matrices and proved both sides
  have dimension 16 — but not that the map is an isomorphism. This file
  closes the gap.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `γ₁_mem` … `γ₄_mem` — the four gamma matrices lie in the range of
     `clifford4ToMatrix` (they are the images of the generators).
  2. `single_mem` — every standard basis matrix E i j lies in the range:
     each is an EXPLICIT (±1/4)-combination of at most four gamma
     products. The sixteen combinations were solved exactly (over ℚ) and
     each identity is verified entrywise in Lean. The gammas GENERATE.
  3. **`clifford4ToMatrix_surjective`** — surjectivity, by decomposing an
     arbitrary matrix over the standard basis (`Matrix.sum_sum_single`)
     inside the range subalgebra.
  4. **`clifford4ToMatrix_injective`** — injectivity, by the rank
     argument: the domain and codomain both have finrank 16
     (`clifford4_finrank`, `matrix4_finrank`, both proven upstream), a
     surjection forces the kernel's finrank to zero.
  5. **`cliffordMatrixEquiv : CliffordAlgebra Q₄ ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ`**
     — THE ISOMORPHISM, via `AlgEquiv.ofBijective`; and
     `cliffordMatrixEquiv_ι` — it acts on generators as the gammas, so it
     is the SAME map, not a repackaged abstract equivalence.

  NOT proven here (unchanged from SPINE):

  * The REAL classification Cl(1,3;ℝ) ≅ M₂(ℍ) — this file is complex
    coefficients throughout, where signature is invisible (Q₄ has
    diagonal coefficients (+1,+1,−1,−1) — now the THEOREM `Q₄_apply`;
    over ℂ no signature invariant separates nondegenerate forms, and no
    form-equivalence claim is formalised here). The real story is
    WALLS.md W7.
  * Nothing about the cascade, spinors, or physics: this is the L8
    algebra statement and only that.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import F4_1e_CliffordMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Matrix CliffordAlgebra

noncomputable section

namespace CliffordIso

/-! ## 1. The generators lie in the range -/

theorem γ₁_mem : γ₁ ∈ clifford4ToMatrix.range := by
  refine ⟨ι Q₄ ((1, 0), (0, 0)), ?_⟩
  change clifford4ToMatrix (ι Q₄ ((1, 0), (0, 0))) = γ₁
  rw [clifford4ToMatrix_ι]
  simp [clifford4Map]

theorem γ₂_mem : γ₂ ∈ clifford4ToMatrix.range := by
  refine ⟨ι Q₄ ((0, 1), (0, 0)), ?_⟩
  change clifford4ToMatrix (ι Q₄ ((0, 1), (0, 0))) = γ₂
  rw [clifford4ToMatrix_ι]
  simp [clifford4Map]

theorem γ₃_mem : γ₃ ∈ clifford4ToMatrix.range := by
  refine ⟨ι Q₄ ((0, 0), (1, 0)), ?_⟩
  change clifford4ToMatrix (ι Q₄ ((0, 0), (1, 0))) = γ₃
  rw [clifford4ToMatrix_ι]
  simp [clifford4Map]

theorem γ₄_mem : γ₄ ∈ clifford4ToMatrix.range := by
  refine ⟨ι Q₄ ((0, 0), (0, 1)), ?_⟩
  change clifford4ToMatrix (ι Q₄ ((0, 0), (0, 1))) = γ₄
  rw [clifford4ToMatrix_ι]
  simp [clifford4Map]

/-! ## 2. The gammas generate: every standard basis matrix is an explicit
(±1/4)-combination of gamma products, verified entrywise -/

private theorem m12 : γ₁ * γ₂ ∈ clifford4ToMatrix.range := mul_mem γ₁_mem γ₂_mem
private theorem m13 : γ₁ * γ₃ ∈ clifford4ToMatrix.range := mul_mem γ₁_mem γ₃_mem
private theorem m14 : γ₁ * γ₄ ∈ clifford4ToMatrix.range := mul_mem γ₁_mem γ₄_mem
private theorem m23 : γ₂ * γ₃ ∈ clifford4ToMatrix.range := mul_mem γ₂_mem γ₃_mem
private theorem m24 : γ₂ * γ₄ ∈ clifford4ToMatrix.range := mul_mem γ₂_mem γ₄_mem
private theorem m34 : γ₃ * γ₄ ∈ clifford4ToMatrix.range := mul_mem γ₃_mem γ₄_mem
private theorem m123 : γ₁ * γ₂ * γ₃ ∈ clifford4ToMatrix.range := mul_mem m12 γ₃_mem
private theorem m124 : γ₁ * γ₂ * γ₄ ∈ clifford4ToMatrix.range := mul_mem m12 γ₄_mem
private theorem m134 : γ₁ * γ₃ * γ₄ ∈ clifford4ToMatrix.range := mul_mem m13 γ₄_mem
private theorem m234 : γ₂ * γ₃ * γ₄ ∈ clifford4ToMatrix.range := mul_mem m23 γ₄_mem
private theorem m1234 : γ₁ * γ₂ * γ₃ * γ₄ ∈ clifford4ToMatrix.range := mul_mem m123 γ₄_mem

/- The sixteen identities share one uniform simp set; per-goal minimal sets
would obscure the uniformity, so the unused-argument linter is silenced for
this block only. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private theorem E00_mem :
    Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (1 + γ₁ - γ₂ * γ₃ - γ₁ * γ₂ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (sub_mem (add_mem (one_mem _) (γ₁_mem)) (m23)) (m123)) _

private theorem E01_mem :
    Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (-(γ₂ * γ₄) - γ₃ * γ₄ - γ₁ * γ₂ * γ₄ - γ₁ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (sub_mem (sub_mem (neg_mem (m24)) (m34)) (m124)) (m134)) _

private theorem E02_mem :
    Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ + γ₃ + γ₁ * γ₂ + γ₁ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (add_mem (add_mem (γ₂_mem) (γ₃_mem)) (m12)) (m13)) _

private theorem E03_mem :
    Matrix.single (0 : Fin 4) (3 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (3 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₄ + γ₁ * γ₄ - γ₂ * γ₃ * γ₄ - γ₁ * γ₂ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (sub_mem (add_mem (γ₄_mem) (m14)) (m234)) (m1234)) _

private theorem E10_mem :
    Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (-(γ₂ * γ₄) + γ₃ * γ₄ - γ₁ * γ₂ * γ₄ + γ₁ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (sub_mem (add_mem (neg_mem (m24)) (m34)) (m124)) (m134)) _

private theorem E11_mem :
    Matrix.single (1 : Fin 4) (1 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (1 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (1 + γ₁ + γ₂ * γ₃ + γ₁ * γ₂ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (add_mem (add_mem (one_mem _) (γ₁_mem)) (m23)) (m123)) _

private theorem E12_mem :
    Matrix.single (1 : Fin 4) (2 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (2 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₄ + γ₁ * γ₄ + γ₂ * γ₃ * γ₄ + γ₁ * γ₂ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (add_mem (add_mem (γ₄_mem) (m14)) (m234)) (m1234)) _

private theorem E13_mem :
    Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ - γ₃ + γ₁ * γ₂ - γ₁ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (add_mem (sub_mem (γ₂_mem) (γ₃_mem)) (m12)) (m13)) _

private theorem E20_mem :
    Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ - γ₃ - γ₁ * γ₂ + γ₁ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (sub_mem (sub_mem (γ₂_mem) (γ₃_mem)) (m12)) (m13)) _

private theorem E21_mem :
    Matrix.single (2 : Fin 4) (1 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (1 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (-γ₄ + γ₁ * γ₄ - γ₂ * γ₃ * γ₄ + γ₁ * γ₂ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (sub_mem (add_mem (neg_mem (γ₄_mem)) (m14)) (m234)) (m1234)) _

private theorem E22_mem :
    Matrix.single (2 : Fin 4) (2 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (2 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (1 - γ₁ + γ₂ * γ₃ - γ₁ * γ₂ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (add_mem (sub_mem (one_mem _) (γ₁_mem)) (m23)) (m123)) _

private theorem E23_mem :
    Matrix.single (2 : Fin 4) (3 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (3 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ * γ₄ - γ₃ * γ₄ - γ₁ * γ₂ * γ₄ + γ₁ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (sub_mem (sub_mem (m24) (m34)) (m124)) (m134)) _

private theorem E30_mem :
    Matrix.single (3 : Fin 4) (0 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (0 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (-γ₄ + γ₁ * γ₄ + γ₂ * γ₃ * γ₄ - γ₁ * γ₂ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (add_mem (add_mem (neg_mem (γ₄_mem)) (m14)) (m234)) (m1234)) _

private theorem E31_mem :
    Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ + γ₃ - γ₁ * γ₂ - γ₁ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (sub_mem (add_mem (γ₂_mem) (γ₃_mem)) (m12)) (m13)) _

private theorem E32_mem :
    Matrix.single (3 : Fin 4) (2 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (2 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (γ₂ * γ₄ + γ₃ * γ₄ - γ₁ * γ₂ * γ₄ - γ₁ * γ₃ * γ₄) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃, γ₄,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (sub_mem (add_mem (m24) (m34)) (m124)) (m134)) _

private theorem E33_mem :
    Matrix.single (3 : Fin 4) (3 : Fin 4) (1 : ℂ) ∈ clifford4ToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (3 : Fin 4) (1 : ℂ)
      = (1/4 : ℂ) • (1 - γ₁ - γ₂ * γ₃ + γ₁ * γ₂ * γ₃) by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [γ₁, γ₂, γ₃,
        Matrix.mul_apply, Fin.sum_univ_four, Matrix.single,
        Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (sub_mem (sub_mem (one_mem _) (γ₁_mem)) (m23)) (m123)) _

set_option linter.unusedSimpArgs true
set_option linter.unnecessarySeqFocus true

/-- Every standard basis matrix lies in the range of the representation:
    the sixteen exact (±1/4)-combinations, dispatched. -/
theorem single_mem (i j : Fin 4) :
    Matrix.single i j (1 : ℂ) ∈ clifford4ToMatrix.range := by
  fin_cases i <;> fin_cases j
  exacts [E00_mem, E01_mem, E02_mem, E03_mem, E10_mem, E11_mem, E12_mem,
    E13_mem, E20_mem, E21_mem, E22_mem, E23_mem, E30_mem, E31_mem, E32_mem,
    E33_mem]

/-! ## 3. Surjectivity and injectivity -/

/-- **The gammas generate M₄(ℂ)**: the representation is surjective. -/
theorem clifford4ToMatrix_surjective :
    Function.Surjective clifford4ToMatrix := by
  intro A
  have hA : A = ∑ i, ∑ j, Matrix.single i j (A i j) :=
    (Matrix.sum_sum_single fun i j => A i j).symm
  have hmem : A ∈ clifford4ToMatrix.range := by
    rw [hA]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hs : Matrix.single i j (A i j)
        = (A i j) • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs]
    exact Subalgebra.smul_mem _ (single_mem i j) _
  exact hmem

/-- **Injectivity by rank**: both sides have finrank 16 and the map is
    surjective, so the kernel has finrank zero. -/
theorem clifford4ToMatrix_injective :
    Function.Injective clifford4ToMatrix := by
  haveI : FiniteDimensional ℂ (CliffordAlgebra Q₄) :=
    FiniteDimensional.of_finrank_pos (by rw [clifford4_finrank]; norm_num)
  have hrk := LinearMap.finrank_range_add_finrank_ker
    clifford4ToMatrix.toLinearMap
  have hr : LinearMap.range clifford4ToMatrix.toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact clifford4ToMatrix_surjective
  rw [hr, finrank_top, matrix4_finrank, clifford4_finrank] at hrk
  have hk : Module.finrank ℂ
      (LinearMap.ker clifford4ToMatrix.toLinearMap) = 0 := by omega
  have hbot : LinearMap.ker clifford4ToMatrix.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hk
  exact LinearMap.ker_eq_bot.mp hbot

/-! ## 4. THE ISOMORPHISM -/

/-- **Cl₄(ℂ) ≅ M₄(ℂ)** — SPINE gap N3, closed: the gamma representation
    is an isomorphism of ℂ-algebras. -/
def cliffordMatrixEquiv :
    CliffordAlgebra Q₄ ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  AlgEquiv.ofBijective clifford4ToMatrix
    ⟨clifford4ToMatrix_injective, clifford4ToMatrix_surjective⟩

/-- The isomorphism IS the gamma representation: it sends the generators
    to the gamma matrices (not a repackaged abstract equivalence). -/
theorem cliffordMatrixEquiv_ι (v : (ℂ × ℂ) × (ℂ × ℂ)) :
    cliffordMatrixEquiv (ι Q₄ v) = clifford4Map v :=
  clifford4ToMatrix_ι v

/-! ## The form made explicit, and the generators tracked one by one
(review round 7: prose became theorems) -/

/-- The quadratic form, evaluated: diagonal coefficients (+1,+1,−1,−1).
    What the header's signature remark means, as a statement. -/
theorem Q₄_apply (a b c d : ℂ) :
    Q₄ ((a, b), (c, d)) = a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2 := by
  simp [Q₄, CliffordAlgebraQuaternion.Q_apply]
  ring

/-- The equiv sends the first generator to γ₁ — public, concrete. -/
theorem cliffordMatrixEquiv_e₁ :
    cliffordMatrixEquiv (ι Q₄ ((1, 0), (0, 0))) = γ₁ := by
  rw [cliffordMatrixEquiv_ι]
  simp [clifford4Map]

theorem cliffordMatrixEquiv_e₂ :
    cliffordMatrixEquiv (ι Q₄ ((0, 1), (0, 0))) = γ₂ := by
  rw [cliffordMatrixEquiv_ι]
  simp [clifford4Map]

theorem cliffordMatrixEquiv_e₃ :
    cliffordMatrixEquiv (ι Q₄ ((0, 0), (1, 0))) = γ₃ := by
  rw [cliffordMatrixEquiv_ι]
  simp [clifford4Map]

theorem cliffordMatrixEquiv_e₄ :
    cliffordMatrixEquiv (ι Q₄ ((0, 0), (0, 1))) = γ₄ := by
  rw [cliffordMatrixEquiv_ι]
  simp [clifford4Map]

end CliffordIso
