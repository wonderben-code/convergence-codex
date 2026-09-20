/-
  JSelectsDirac.lean — the other half of the witness file's sentence: on the regular bimodule of
  `M₂(ℂ)`, an operator satisfies the order-one condition AND commutes with the real structure
  `Jprod` iff it is `π(A) + π°(A⋆)` for some `A` — in Kronecker form `D = A ⊗ 1 + 1 ⊗ Ā`, exactly
  as `RealSpectralWitness.lean`'s docstring on `Dsym` asserted by hand. The witness's `Dccm` is the
  instance `A = σ₃`.

  SPINE L6 / `WALLS` §W9 rung 2, second half (§W9.9) — order-one together with `J`, on the
  estate's witness class. Hardening unit 169, 2026-09-20.

  WHY. Unit 168 proved the order-one half: on the regular bimodule every order-one operator is
  `C ⊗ 1 + 1 ⊗ B`. The `Dsym` docstring's derivation continues *"and `JDJ = D`"* to reach
  `D = A ⊗ 1 + 1 ⊗ Ā`, and stops there with no theorem. This file supplies it. `Jprod` is
  *conjugate, then exchange the two Kronecker factors* (`OppositeFromRealStructure`), so
  `J D J = D` reads, on the matrix `M` of `D`, `(M.submatrix σ σ).map conj = M`
  (`jInv_iff_matrix`, off `conjPerm_conj`). For `M = C ⊗ 1 + 1 ⊗ B` the left side is
  `1 ⊗ C̄ + B̄ ⊗ 1` (`swapConj_kron_sum`), so the condition is `(C − B̄) ⊗ 1 = 1 ⊗ (C̄ − B)`; a
  matrix of the form `X ⊗ 1` that is also of the form `1 ⊗ Y` is a scalar in both slots
  (`kron_one_eq_one_kron`), the scalar is real because conjugating one equation gives the other,
  and absorbing half of it into `C` gives `D = A ⊗ 1 + 1 ⊗ Ā` with `A = C − (c/2)·1`. In the
  estate's own maps that is `D = piW A + piOpW (op (star A))`: left multiplication by `A`, right
  multiplication by `A⋆`. The converse is a two-line check. So on this space the KO-6 sign
  `ε′ = +1` together with order-one determines the Dirac operator up to one matrix `A`, and `A`
  is free.

  WHAT IS PROVED.
  * `submatrix_prodComm_kron` — exchanging the index factors exchanges the Kronecker factors;
    `map_conj_kron` — entrywise conjugation distributes over `⊗ₖ`; **`kron_one_eq_one_kron`** —
    `X ⊗ 1 = 1 ⊗ Y` forces `X = c·1 = Y`, over any commutative ring with non-empty index types.
  * **`jInv_iff_matrix`** — `Jprod`-invariance of `matAlg Slots M` iff
    `(M.submatrix prodSwap prodSwap).map conj = M`; `submatrix_prodSwap_kron`, `swapConj_kron_sum`
    (`C ⊗ 1 + 1 ⊗ B ↦ 1 ⊗ C̄ + B̄ ⊗ 1`), `kron_sub'`, `transpose_conjTranspose` (`(A⋆)ᵀ = Ā`).
  * **`orderOne_jInv_iff`** — order-one ∧ `Jprod`-invariant ⟺
    `∃ A, D = piW A + piOpW (op (star A))`.
  * `pauli3_star`, **`Dccm_eq_piW_add_piOpW_star`**, `Dccm_orderOne_jInv` — the witness is the
    instance `A = σ₃`, and both its conditions are read off the theorem.

  WHAT IS **NOT** PROVED, said exactly.
  * The grading. CCM also asks `Dγ = −γD`; the docstring says this cuts `A` to a two-dimensional
    real space spanned by `i·1` (which gives `D = 0`) and `σ₃`. Not here.
  * The fibre of `A ↦ piW A + piOpW (op (star A))`: adding `i t·1` (`t` real) to `A` does not
    change `D`, and that this is the whole fibre is not stated.
  * `n = 2` only, because `Jprod`, `piW`, `piOpW` are defined on `Hw` only; the Kronecker lemmas are
    general. Anything off the regular bimodule — CCM's `A_F` on `H_F` — as in unit 168.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import OrderOneRegularBimodule

open Matrix
open scoped Kronecker

namespace JSelectsDirac

variable {m n : Type*}

/-! ## 1. Three Kronecker lemmas, over any commutative ring -/

/-- Exchanging the Kronecker factors is the `prodComm` submatrix. -/
theorem submatrix_prodComm_kron {R : Type*} [CommRing R] (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊗ₖ B).submatrix (Equiv.prodComm n m) (Equiv.prodComm n m) = B ⊗ₖ A := by
  ext ⟨p, i⟩ ⟨q, k⟩
  simp [kroneckerMap_apply, mul_comm]

/-- Entrywise conjugation distributes over the Kronecker product. -/
theorem map_conj_kron (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (A ⊗ₖ B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) ⊗ₖ B.map (starRingEnd ℂ) := by
  ext ⟨i, p⟩ ⟨k, q⟩
  simp [kroneckerMap_apply]

/-- `X ⊗ 1 = 1 ⊗ Y` forces both to be the same scalar. -/
theorem kron_one_eq_one_kron {R : Type*} [CommRing R] [DecidableEq m] [DecidableEq n]
    [Nonempty m] [Nonempty n] (X : Matrix m m R) (Y : Matrix n n R)
    (h : X ⊗ₖ (1 : Matrix n n R) = (1 : Matrix m m R) ⊗ₖ Y) :
    ∃ c : R, X = c • (1 : Matrix m m R) ∧ Y = c • (1 : Matrix n n R) := by
  obtain ⟨i₀⟩ := ‹Nonempty m›
  obtain ⟨p₀⟩ := ‹Nonempty n›
  have e : ∀ i k p q,
      X i k * (if p = q then (1 : R) else 0) = (if i = k then (1 : R) else 0) * Y p q := by
    intro i k p q
    have := congrFun (congrFun h (i, p)) (k, q)
    simpa [kroneckerMap_apply, Matrix.one_apply] using this
  refine ⟨X i₀ i₀, ?_, ?_⟩
  · ext i k
    by_cases hik : i = k
    · subst hik
      have h1 := e i i p₀ p₀
      have h2 := e i₀ i₀ p₀ p₀
      simp at h1 h2
      simp [h1, h2]
    · have h1 := e i k p₀ p₀
      simp [hik] at h1
      simp [hik, h1]
  · ext p q
    by_cases hpq : p = q
    · subst hpq
      have h1 := e i₀ i₀ p p
      simp at h1
      simp [h1]
    · have h1 := e i₀ i₀ p q
      simp [hpq] at h1
      simp [hpq, ← h1]


/-! ## The estate's witness: `Jprod`-invariance as a matrix identity, and the combined theorem -/

open OrderOneNontrivial OppositeFromRealStructure RealSpectralWitness OrderOneRegularBimodule
  ConjugatePermutation EvenGradingObstruction MulOpposite SpectralTripleBimodule

/-- `Jprod`-invariance of `matAlg Slots M` is the matrix identity
`(M.submatrix σ σ).map conj = M`. -/
theorem jInv_iff_matrix (M : Matrix Slots Slots ℂ) :
    (∀ v : Hw, Jprod (matAlg Slots M (Jprod v)) = matAlg Slots M v) ↔
      (M.submatrix prodSwap prodSwap).map (starRingEnd ℂ) = M := by
  constructor
  · intro h
    apply matAlg_injective Slots
    refine LinearMap.ext fun v => ?_
    have := h v
    rw [matAlg_apply, matAlg_apply, Jprod, conjPerm_conj prodSwap prodSwap_involutive] at this
    rw [matAlg_apply, matAlg_apply]
    exact this
  · intro h v
    rw [matAlg_apply, matAlg_apply, Jprod, conjPerm_conj prodSwap prodSwap_involutive, h]

theorem submatrix_prodSwap_kron (C B : Matrix (Fin 2) (Fin 2) ℂ) :
    (C ⊗ₖ B).submatrix prodSwap prodSwap = B ⊗ₖ C :=
  submatrix_prodComm_kron C B

/-- Exchange-then-conjugate of `C ⊗ 1 + 1 ⊗ B` is `1 ⊗ C̄ + B̄ ⊗ 1`. -/
theorem swapConj_kron_sum (C B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B).submatrix
        prodSwap prodSwap).map (starRingEnd ℂ)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ C.map (starRingEnd ℂ)
        + B.map (starRingEnd ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext ⟨p, i⟩ ⟨q, k⟩
  simp [prodSwap, kroneckerMap_apply, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

theorem kron_sub' (A : Matrix (Fin 2) (Fin 2) ℂ) (B₁ B₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (B₁ - B₂) = A ⊗ₖ B₁ - A ⊗ₖ B₂ := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [kroneckerMap_apply, mul_sub]

/-- `(Aᴴ)ᵀ = Ā` entrywise. -/
theorem transpose_conjTranspose (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (star A)ᵀ = A.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- **THE DOCSTRING'S SENTENCE, AS A THEOREM.** On `Hw`, an operator satisfies order-one AND is
`Jprod`-invariant iff it is `π(A) + π°(A⋆)` for some `A` — `D = A ⊗ 1 + 1 ⊗ Ā`. -/
theorem orderOne_jInv_iff (D : Module.End ℂ Hw) :
    ((∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        ⁅⁅D, piW a⁆, piOpW b⁆ = 0) ∧ (∀ v : Hw, Jprod (D (Jprod v)) = D v)) ↔
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ, D = piW A + piOpW (op (star A)) := by
  constructor
  · rintro ⟨h1, hJ⟩
    obtain ⟨C, B, hD⟩ := (orderOne_Hw_iff D).mp h1
    -- the matrix of D
    have hM : D = matAlg Slots (C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ) := by
      rw [hD, map_add]; rfl
    rw [hM] at hJ
    have hmat := (jInv_iff_matrix _).mp hJ
    rw [swapConj_kron_sum] at hmat
    -- hmat : 1 ⊗ C̄ + B̄ᵀ ⊗ 1 = C ⊗ 1 + 1 ⊗ Bᵀ
    have hsep : (C - (Bᵀ).map (starRingEnd ℂ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (C.map (starRingEnd ℂ) - Bᵀ) := by
      rw [sub_kronecker', kron_sub']
      have := hmat
      -- rearrange: 1⊗C̄ + B̄ᵀ⊗1 = C⊗1 + 1⊗Bᵀ  ⟹  C⊗1 − B̄ᵀ⊗1 = 1⊗C̄ − 1⊗Bᵀ
      calc C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) - (Bᵀ).map (starRingEnd ℂ) ⊗ₖ 1
          = (C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ)
            - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ + (Bᵀ).map (starRingEnd ℂ) ⊗ₖ 1) := by abel
        _ = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ C.map (starRingEnd ℂ)
              + (Bᵀ).map (starRingEnd ℂ) ⊗ₖ 1)
            - ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ + (Bᵀ).map (starRingEnd ℂ) ⊗ₖ 1) := by rw [this]
        _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ C.map (starRingEnd ℂ)
              - (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ := by abel
    obtain ⟨c, hc1, hc2⟩ := kron_one_eq_one_kron _ _ hsep
    -- `c` is real: conjugate `hc1` and compare with `hc2` at the `(0, 0)` entry
    have hcr : (starRingEnd ℂ) c = c := by
      have h1 := congrFun (congrFun hc1 0) 0
      have h2 := congrFun (congrFun hc2 0) 0
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1 h2
      have h3 := congrArg (starRingEnd ℂ) h1
      simp only [map_sub, Complex.conj_conj] at h3
      rw [h2] at h3
      exact h3.symm
    have hBt : Bᵀ = C.map (starRingEnd ℂ) - c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← hc2]; abel
    refine ⟨C - (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
    rw [hD]
    change matAlg Slots (kronLeft (Fin 2) (Fin 2) C)
        + matAlg Slots (kronRight (Fin 2) (Fin 2) (op B))
      = matAlg Slots (kronLeft (Fin 2) (Fin 2) (C - (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        + matAlg Slots (kronRight (Fin 2) (Fin 2)
            (op (star (C - (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))))
    rw [← map_add, ← map_add]
    congr 1
    rw [kronLeft_apply, kronRight_apply, kronLeft_apply, kronRight_apply, unop_op, unop_op,
      transpose_conjTranspose, hBt]
    have hmap : (C - (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map (starRingEnd ℂ)
        = C.map (starRingEnd ℂ) - (c / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      simp [Matrix.one_apply, apply_ite (starRingEnd ℂ), hcr, map_div₀, map_ofNat]
    rw [hmap, sub_kronecker', kron_sub', kron_sub', smul_kronecker, kronecker_smul, kronecker_smul]
    module
  · rintro ⟨A, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (orderOne_Hw_iff _).mpr ⟨A, star A, rfl⟩
    · have hM : piW A + piOpW (op (star A)) = matAlg Slots (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)) := by
        change matAlg Slots (kronLeft (Fin 2) (Fin 2) A)
          + matAlg Slots (kronRight (Fin 2) (Fin 2) (op (star A))) = _
        rw [← map_add]; congr 1
      rw [hM]
      apply (jInv_iff_matrix _).mpr
      rw [swapConj_kron_sum, Matrix.map_map]
      have hcc : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := by
        funext z; simp
      rw [hcc, Matrix.map_id]
      abel

/-- `σ₃` is Hermitian. -/
theorem pauli3_star : star pauli3 = pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli3]

/-- **The witness is the instance `A = σ₃`**: `Dccm = π(σ₃) + π°(σ₃⋆)`. -/
theorem Dccm_eq_piW_add_piOpW_star : Dccm = piW pauli3 + piOpW (op (star pauli3)) := by
  rw [pauli3_star]; exact Dccm_eq_piW_add_piOpW

/-- So `Dccm` satisfies both conditions — read off the theorem rather than checked by hand. -/
theorem Dccm_orderOne_jInv :
    (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        ⁅⁅Dccm, piW a⁆, piOpW b⁆ = 0) ∧ (∀ v : Hw, Jprod (Dccm (Jprod v)) = Dccm v) :=
  (orderOne_jInv_iff Dccm).mpr ⟨pauli3, Dccm_eq_piW_add_piOpW_star⟩

end JSelectsDirac

