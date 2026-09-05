import FieldHouseholder

/-!
# One symmetry of the field per eigenvector of the propagator

`FieldHouseholder` reflected through the all-ones line and got a symmetry of the Gaussian field on
every graph. **Nothing in that argument was about the all-ones vector** except that it is an
eigenvector of `green`: a symmetric operator preserves an eigenvector's line and its orthogonal
complement, and the reflection swapping their roles therefore commutes with it.

**So there is one such reflection per eigenvector**, and this file states that. `PROOF_STRATEGY` §7
rule 3, and the restriction removed is *which* eigenvector.

## What is proved

**`eigenRefl v = (2/⟪v,v⟫) · vvᵀ − 1`** — the Householder reflection along `v`: it fixes `v` and
negates `v`'s orthogonal complement. **`eigenRefl_isSymm`** and **`eigenRefl_mul_self`** (`= 1` at
every `v ≠ 0`, so it is an involution and an isometry, through
`FieldHouseholder.reflIsometry`).

**`eigenRefl_mul_green_comm`** — **if `v` is an eigenvector of `green` then `eigenRefl v` commutes
with it.** Both products collapse to `μ · vvᵀ`, one using `green *ᵥ v = μ • v` and the other the
same fact through `green_isSymm`.

**`gaussianField_map_eigenRefl`** — hence the field is invariant under it, at every finite graph and
every `m ≠ 0`.

**`house_eq_eigenRefl_one`** — and the previous unit's reflection is this one at the all-ones
vector, so the general statement genuinely covers it rather than sitting beside it.

## What is NOT here

**No count of the eigenvectors, and so no count of the symmetries.** The family is indexed by
eigenvectors of `green`, and this file exhibits no eigenvector but the all-ones one — every other
instance needs a spectral input this file does not supply. **What that means concretely**: on a
graph whose spectrum this estate computes (`CycleLaplacianSpectrum`, `BoxLapSpectrum`,
`TorusLapSpectrum`), each eigenvector gives a reflection; nothing here does that instantiation.
**Not attempted, and no cost claimed** (`ERRATUM 246`).

**Still no description of the commutant.** Reflections along eigenvectors do not exhaust the
orthogonal maps commuting with a symmetric operator — the rotations inside a degenerate eigenspace
are the obvious others, and they remain unbuilt.
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 459`):
`FieldCommutantSpectral.mul_green_comm_iff` describes it — a matrix commutes with `green` **iff**
it carries every eigenvector to an eigenvector at the same eigenvalue — and
`FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` makes that a description of
the symmetries of the measure and not of a subset of them. What is still missing is the
`∏ᵢ O(dᵢ)` packaging, not a characterisation.

**Nothing about `v = 0`**, where `⟪v,v⟫ = 0` and the definition divides by it.

**Not OS3 and not any OS axiom.** A wider shadow is not a smaller gap.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldEigenReflection

open Matrix GraphLaplacian FieldIsometryInvariance FieldCommutant FieldHouseholder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The reflection along a vector -/

/-- **THE HOUSEHOLDER REFLECTION ALONG `v`**: it fixes `v` and negates `v`'s orthogonal
complement. -/
noncomputable def eigenRefl (v : V → ℝ) : Matrix V V ℝ :=
  (2 / (v ⬝ᵥ v)) • Matrix.vecMulVec v v - 1

omit [DecidableEq V] in
theorem vecMulVec_mul_self (v : V → ℝ) :
    Matrix.vecMulVec v v * Matrix.vecMulVec v v = (v ⬝ᵥ v) • Matrix.vecMulVec v v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem eigenRefl_isSymm (v : V → ℝ) : (eigenRefl v).IsSymm := by
  rw [eigenRefl]
  refine Matrix.IsSymm.sub ?_ Matrix.isSymm_one
  refine Matrix.IsSymm.smul ?_ _
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_comm]

theorem eigenRefl_mul_self {v : V → ℝ} (hv : v ⬝ᵥ v ≠ 0) : eigenRefl v * eigenRefl v = 1 := by
  have hkey : (2 / (v ⬝ᵥ v)) * (2 / (v ⬝ᵥ v)) * (v ⬝ᵥ v) = 2 * (2 / (v ⬝ᵥ v)) := by
    field_simp
  rw [eigenRefl, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_self, Matrix.one_mul, Matrix.mul_one, smul_smul, smul_smul, hkey]
  simp only [Matrix.one_mul]
  module

/-! ## 2. It commutes with the propagator at an eigenvector -/

theorem green_mul_vecMulVec {v : V → ℝ} {μ : ℝ} (hev : green G m *ᵥ v = μ • v) :
    green G m * Matrix.vecMulVec v v = μ • Matrix.vecMulVec v v := by
  ext i j
  have hi : ∑ x, green G m i x * v x = μ * v i := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hev i
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ x, green G m i x * (v x * v j)
      = (∑ x, green G m i x * v x) * v j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = μ * (v i * v j) := by rw [hi]; ring

theorem vecMulVec_mul_green (hm : m ≠ 0) {v : V → ℝ} {μ : ℝ} (hev : green G m *ᵥ v = μ • v) :
    Matrix.vecMulVec v v * green G m = μ • Matrix.vecMulVec v v := by
  have h := green_mul_vecMulVec (G := G) (m := m) hev
  have hg : (green G m).IsSymm := green_isSymm G hm
  have hJ : (Matrix.vecMulVec v v).IsSymm := by
    ext i j; simp [Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_comm]
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, hJ, hg, Matrix.transpose_smul, hJ] at this

/-- **THE REFLECTION ALONG AN EIGENVECTOR COMMUTES WITH THE PROPAGATOR.** -/
theorem eigenRefl_mul_green_comm (hm : m ≠ 0) {v : V → ℝ} {μ : ℝ}
    (hev : green G m *ᵥ v = μ • v) :
    eigenRefl v * green G m = green G m * eigenRefl v := by
  rw [eigenRefl, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    green_mul_vecMulVec hev, vecMulVec_mul_green hm hev, Matrix.one_mul, Matrix.mul_one]

/-- **AND SO THE GAUSSIAN FIELD IS INVARIANT UNDER IT.** -/
theorem gaussianField_map_eigenRefl (hm : m ≠ 0) {v : V → ℝ} {μ : ℝ}
    (hv : v ⬝ᵥ v ≠ 0) (hev : green G m *ᵥ v = μ • v) :
    MeasureTheory.Measure.map (reflIsometry (eigenRefl_isSymm v) (eigenRefl_mul_self hv))
        (gaussianField G m)
      = gaussianField G m :=
  gaussianField_map_reflIsometry hm _ _ (eigenRefl_mul_green_comm hm hev)

/-! ## 3. The previous unit is the instance at the all-ones vector -/

/-- **`FieldHouseholder.house` IS THIS REFLECTION AT THE ALL-ONES VECTOR**, so the general
statement covers it rather than sitting beside it. -/
theorem house_eq_eigenRefl_one : house V = eigenRefl (fun _ : V => (1 : ℝ)) := by
  have hdot : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = (Fintype.card V : ℝ) := by
    simp [dotProduct, Finset.card_univ]
  rw [house, eigenRefl, hdot]
  congr 1
  congr 1
  ext i j
  simp [GreenExpansion.allOnes, Matrix.vecMulVec_apply]

end FieldEigenReflection
