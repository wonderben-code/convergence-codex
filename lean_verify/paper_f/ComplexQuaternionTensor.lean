import CliffordRealSmallBases

/-!
# `ℂ ⊗[ℝ] ℍ ≅ M₂(ℂ)`

**The one identity between *determined* and *named*.** `WALLS §W7.2` amendment 11 records that
every real Clifford algebra with `p + q ≤ 80` is determined by a chain of this estate's theorems,
and that turning "determined" into a named matrix algebra needs the `A ⊗ ℍ` outputs of
`clifford_step_neg` simplified. `ℝ ⊗ ℍ`, `ℍ ⊗ ℍ` (`QuaternionTensor.equivM4`), `Mₙ(A) ⊗ ℍ`
(`CliffordPeriodicityEight.matrixTensorRight`) and `(A × B) ⊗ ℍ`
(`Algebra.TensorProduct.prodRight` with `comm`) were all available. **This was the one that was
not.**

> **`equivM2C`** — `ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₂(ℂ)`.

## The map, and why it is shorter than `QuaternionTensor`

`ℍ` embeds in `M₂(ℂ)` by `q = z + wj ↦ !![z, w; −conj w, conj z]`, and `ℂ` sits inside `M₂(ℂ)` as
the scalars, which are central. So the map out of the **ordinary** tensor product needs no
commuting pair to be constructed by hand — `Algebra.commutes` supplies it — and the embedding
itself is `QuaternionAlgebra.Basis.liftHom` applied to three explicit matrices satisfying the
four quaternion relations.

Surjectivity is four coefficients read off a `2 × 2` matrix rather than a spanning argument: the
images of `1, i, j, k` are a `ℂ`-basis of `M₂(ℂ)`, and the preimage of `M` is written down
directly. Injectivity is free at `finrank ℝ = 8` on both sides.

## The obstacle was an instance, not the mathematics, and it is worth recording

`ℂ ⊗[ℝ] X` **has no `Semiring` instance in this estate's import closure, for any `X`.** The reason
is measured rather than guessed: `#synth Module ℝ ℂ` returns
`instInnerProductSpaceRealComplex.toModule`, so the tensor product elaborates carrying the
normed-space module structure, while `Algebra.TensorProduct.instSemiring` is stated for
`Algebra.toModule`. The two are defeq and neither is wrong; they are not *syntactically* the same,
and instance search does not unfold. `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]` is unaffected, which is why
`QuaternionTensor` never met this.

The fix is one `local instance` line pinning `Module ℝ ℂ` to `Algebra.toModule`. It is `local`, so
nothing downstream inherits it; inside this file it means lemmas stated against `ℂ`'s *normed*
structure must be applied with `exact` rather than `rw`, which is why `finrank_ct` below routes
`Complex.finrank_real_complex` through a `have`.
-/

namespace ComplexQuaternionTensor

open scoped TensorProduct Quaternion

noncomputable section

/-- **The instance the file exists around.** `Module ℝ ℂ` otherwise resolves to
`instInnerProductSpaceRealComplex.toModule`, and `ℂ ⊗[ℝ] X` then has no `Semiring`. `local`, so it
does not escape this file. -/
local instance instModuleRealComplexAlgebra : Module ℝ ℂ := Algebra.toModule

/-- The image of `i`. -/
def matI : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- The image of `j`. -/
def matJ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The image of `k`. -/
def matK : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-- The three matrices satisfy the quaternion relations, so they present `ℍ`. -/
def quatBasisM2C : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (-1 : ℝ) 0 (-1) where
  i := matI
  j := matJ
  k := matK
  i_mul_i := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;>
      simp [matI]
  j_mul_j := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;>
      simp [matJ]
  i_mul_j := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;>
      simp [matI, matJ, matK]
  j_mul_i := by
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;>
      simp [matI, matJ, matK]

/-- `ℍ → M₂(ℂ)`. -/
def rho : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := quatBasisM2C.liftHom

/-- `ℂ → M₂(ℂ)`, the scalars, as an `ℝ`-algebra map. -/
def cMap : ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Algebra.ofId ℂ (Matrix (Fin 2) (Fin 2) ℂ)).restrictScalars ℝ

/-- The scalars are central: no commuting pair has to be built by hand. -/
theorem commute_cMap_rho (z : ℂ) (q : ℍ[ℝ]) : Commute (cMap z) (rho q) :=
  Algebra.commutes z (rho q)

/-- `ℂ ⊗ ℍ → M₂(ℂ)`, out of the ORDINARY tensor product. -/
def T : ℂ ⊗[ℝ] ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  Algebra.TensorProduct.lift cMap rho commute_cMap_rho

@[simp] theorem T_tmul (z : ℂ) (q : ℍ[ℝ]) : T (z ⊗ₜ[ℝ] q) = z • rho q := by
  simp [T, Algebra.TensorProduct.lift_tmul, cMap, Algebra.ofId, Algebra.smul_def]

/-- The three imaginary units, named so the surjectivity witness typechecks as one expression. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The second imaginary unit. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- The third imaginary unit. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem rho_apply (q : ℍ[ℝ]) : rho q = quatBasisM2C.lift q := rfl

@[simp] theorem rho_i : rho qi = matI := by
  rw [rho_apply]; simp [QuaternionAlgebra.Basis.lift, quatBasisM2C, qi]

@[simp] theorem rho_j : rho qj = matJ := by
  rw [rho_apply]; simp [QuaternionAlgebra.Basis.lift, quatBasisM2C, qj]

@[simp] theorem rho_k : rho qk = matK := by
  rw [rho_apply]; simp [QuaternionAlgebra.Basis.lift, quatBasisM2C, qk]

/-- **Surjectivity: four coefficients, read off the matrix.** -/
theorem T_surjective : Function.Surjective T := by
  intro M
  refine ⟨(((M 0 0 + M 1 1) / 2) ⊗ₜ[ℝ] (1 : ℍ[ℝ])
      + ((M 1 1 - M 0 0) * Complex.I / 2) ⊗ₜ[ℝ] qi
      + ((M 0 1 - M 1 0) / 2) ⊗ₜ[ℝ] qj
      + (-(M 0 1 + M 1 0) * Complex.I / 2) ⊗ₜ[ℝ] qk : ℂ ⊗[ℝ] ℍ[ℝ]), ?_⟩
  simp only [map_add, T_tmul, map_one, rho_i, rho_j, rho_k]
  refine Matrix.ext fun a b => ?_
  fin_cases a <;> fin_cases b <;>
    simp [matI, matJ, matK, Complex.ext_iff] <;> ring_nf
  all_goals simp

theorem finrank_ct : Module.finrank ℝ (ℂ ⊗[ℝ] ℍ[ℝ]) = 8 := by
  have h : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [Module.finrank_tensorProduct, h, Quaternion.finrank_eq_four]

theorem finrank_m2c : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℂ) = 8 := by
  have h : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have := Module.finrank_mul_finrank ℝ ℂ (Matrix (Fin 2) (Fin 2) ℂ)
  rw [h, Module.finrank_matrix] at this
  simpa using this.symm

theorem T_injective : Function.Injective T :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := ℂ ⊗[ℝ] ℍ[ℝ]) (V₂ := Matrix (Fin 2) (Fin 2) ℂ)
    (by rw [finrank_ct, finrank_m2c])).2 T_surjective

/-- **`ℂ ⊗[ℝ] ℍ ≃ₐ[ℝ] M₂(ℂ)`.** Absent from Mathlib and from this estate until now. -/
def equivM2C : ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  AlgEquiv.ofBijective T ⟨T_injective, T_surjective⟩

end

end ComplexQuaternionTensor
