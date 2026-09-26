/-
  SelfAdjointDiracCount.lean — the self-adjoint Dirac operators the three conditions allow,
  counted and classified. Unit 236 showed that on `ℂ² ⊗ (ℂ² ⊗ ℂ^μ)` — `M₂(ℂ)` acting on itself,
  every vector carrying a generation label from `μ` — an operator satisfies order-one, commutes
  with the real structure `J`, anticommutes with the grading and is self-adjoint iff it is
  `Dsym ⊗ R` with `R` real symmetric. Here those operators are counted: a real vector space of
  dimension `n(n+1)/2`, `n` the number of generations — six at three, against nine without
  self-adjointness, and one at one, unit 170's one real scale. And they are classified: an
  orthogonal change of basis of the generations commutes with both actions, the grading and `J`,
  and carries `Dsym ⊗ R` to `Dsym ⊗ U R Uᵀ`; every self-adjoint solution is such a change of
  basis applied to `Dsym ⊗ diag(λ₁, …, λₙ)`, and two are related by one iff their generation
  matrices have the same eigenvalues, with multiplicity. And the tensor-sum shape is decided
  exactly: `Dsym ⊗ R` is `C ⊗ 1 + 1 ⊗ B`, in either grouping, iff `R` is a multiple of the
  identity — among the self-adjoint solutions, iff the generations neither mix nor differ.

  SPINE L6 / `WALLS` §W9 rung 2, second half — unit 236's count completed with self-adjointness,
  and what is left of it once the changes of basis that fix everything else are divided out; SPINE
  L19 / `ASSUMPTIONS_LEDGER` 12 — the tensor-sum premise of unit 172's factorisation, not forced at
  a multiplicity of two (units 232, 234, 236), now decided for every solution of this model; and
  `PROPOSED_TAG_CHANGES` entry 5, whose 26 September addition gives six real numbers at three
  generations and says no theorem in the estate counts them. Hardening unit 241, 26 September
  2026.

  WHY. Unit 236 (`GammaFixesDiracGenerations`) counted the operators the three conditions allow,
  `(card μ)²` (`finrank_range_DsymGenL`), and characterised the self-adjoint ones
  (`gen_fixes_dirac_selfAdjoint`), and its NOT list says *"The dimension of the self-adjoint
  solutions: they are `Dsym ⊗ R` with `R` real symmetric, and no theorem counts those; the estate
  counts only the complex symmetric matrices (`TransposeDimension.finrank_symSub_fin`)."* And a
  count of operators is not a count of what tells them apart: two Dirac operators related by a
  unitary that commutes with the algebra, `J` and the grading are the same finite geometry in
  other coordinates, so the question is also what is left once those changes of basis are
  divided out.

  WHAT IS PROVED.
  (1) `symMat K μ`: the symmetric matrices over any field `K`. **`symEquiv`**: a linear
      equivalence with the functions on unordered pairs, `Sym2 μ → K` (`toSym2`, through
      `Sym2.lift`, and `ofSym2`); **`finrank_symMat_choose`**: dimension `(card μ + 1).choose 2`;
      **`finrank_symMat`**: `card μ * (card μ + 1) / 2`. **`symMat_complex_eq_symSub`**: over
      `ℂ` it is `TransposeSplit.symSub`, so `finrank_symSub_choose_via_sym2` is
      `TransposeDimension.finrank_symSub_choose` by another route.
  (2) `selfAdjSolutions μ`: the image of `symMat ℝ μ` under unit 236's `DsymGenL`.
      **`mem_selfAdjSolutions_iff`**: it is exactly the set of self-adjoint operators meeting the
      three conditions. **`finrank_selfAdjSolutions`**: a real space of dimension
      `card μ * (card μ + 1) / 2`; **`finrank_selfAdjSolutions_three`**: `6` at three
      generations; `finrank_selfAdjSolutions_one`: `1` at one.
  (3) `slotGen M N`: `M` on the two slots and `N` on the generation (`slotGen_apply`,
      `slotGen_mul`, `conjTranspose_slotGen`, `slotGen_one_one`); `DsymGen_eq_slotGen`,
      `gammaGen_eq_slotGen`, `left_eq_slotGen`, `right_eq_slotGen`. `genRot U`: a real matrix `U`
      on the generation label and the identity on the slots. **`genRot_comm_left`**,
      **`genRot_comm_right`**, **`genRot_comm_gammaGen`**, **`exchConjGen_genRot`**: it commutes
      with the left action `a ⊗ 1`, the right action `1 ⊗ (b ⊗ 1)`, the grading and `J`
      (`genRot_comm_slotGen`); `conjTranspose_genRot`, `map_ofReal_mul`, `genRot_mul`;
      **`genRot_unitary`**: for `U Uᵀ = 1` it is unitary.
  (4) **`genRot_conj_DsymGen`**: `W (Dsym ⊗ R) Wᴴ = Dsym ⊗ (U R Uᵀ)` for `W = genRot U`;
      **`genRot_conj_mem`**: so conjugation by `genRot U` maps self-adjoint solutions to
      self-adjoint solutions, for every real `U`. `isHermitian_of_isSymm`, `spectral_real`:
      Mathlib's spectral theorem for a real symmetric `R`, as `R = V diag(λ) Vᵀ` with `V Vᵀ = 1`.
      **`exists_genRot_diagonal`** and **`mem_selfAdjSolutions_iff_genRot`**: the self-adjoint
      solutions are exactly the operators `W (Dsym ⊗ diag(λ)) Wᴴ` with `W = genRot V`, `V`
      orthogonal and `λ` real — `λ` the eigenvalues of `R`. **`genRot_equiv_iff_charpoly`**: for
      `R`, `R'` symmetric, `Dsym ⊗ R'` is `W (Dsym ⊗ R) Wᴴ` with `W = genRot U` for some `U` with
      `U Uᵀ = 1` iff `R` and `R'` have the same characteristic polynomial.
  (5) `DsymGen_apply`: the entries of `Dsym ⊗ R`. **`DsymGen_kronSum_iff`** and
      **`DsymGen_genPartSum_iff`**: `Dsym ⊗ R` is `C ⊗ 1 + 1 ⊗ B`, and is `genPart C + 1 ⊗ (B ⊗ 1)`,
      for some `C`, `B`, iff `R = r • 1`; **`DsymGen_real_kronSum_iff`**: for `R` real, iff `R` is a
      real multiple of the identity. Unit 236's `exists_gen_fixes_dirac_not_kronSum` is the case
      `R = diag(1, 0)`.

  NOT PROVED, said exactly.
  • What the numbers are physically. Nothing here identifies `R` or its eigenvalues with Yukawa
    matrices or masses; CCM's Yukawa matrices are complex, and whether a larger model leaves a
    complex matrix is not asked. The count and the classification are of this model's `D` —
    `M₂(ℂ)` with unit 170's grading — not of the Standard Model's parameters; and the `n`
    eigenvalues are not the cutoff's three moments (`DecayingCutoff`), which are numbers about
    the cutoff function, not about `D`.
  • Other changes of basis: a complex unitary on the generations, or one that also moves the
    slots, is not considered, and that the `genRot U` with `U` orthogonal are all the unitaries
    commuting with both actions, the grading and `J` is not proved.
  • The trace of the exponential: for a solution that is not a tensor sum only the shape is
    decided, as in units 232, 234 and 236; whether the trace factorises for it is not computed.
  • Products, `ℍ` and CCM's `A_F` with a generation index; any other grading; the spectrum of
    `Dsym ⊗ diag(λ)` as a set of numbers; the cutoff, the cascade's `D` (the watchlist item *the
    cascade's `D` AS A TENSOR SUM*, `L40927` today), the factor list or a tag: rung 2 is not
    climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `genRot_unitary` takes `U Uᵀ = 1`;
  `genRot_equiv_iff_charpoly` takes `R` and `R'` symmetric; `isHermitian_of_isSymm` takes `R`
  symmetric; `spectral_real` takes `R` Hermitian; `genRot_conj_mem` and `exists_genRot_diagonal`
  take membership in `selfAdjSolutions`; everything else takes elements of its types and nothing
  else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 44 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. The nearest statements are
  `TransposeDimension.finrank_symSub_choose` and `finrank_symSub_fin` — the same count over `ℂ`,
  by the complement with the antisymmetric matrices — of which (1) is the version over any field;
  unit 236's `finrank_range_DsymGenL` and `gen_fixes_dirac_selfAdjoint`, of which (2) is the
  self-adjoint count and the subspace form; Mathlib's `Matrix.IsHermitian.spectral_theorem` and
  `eigenvalues_eq_eigenvalues_iff`, which (4) applies on the generation label; and unit 236's
  `exists_gen_fixes_dirac_not_kronSum` and unit 232's `orderOne_iff_kronSum_of_unique`, of which
  (5) decides the general case: one generation is always scalar, `diag(1, 0)` never.

  `#print axioms` on all 44 declarations below: `[propext, Classical.choice, Quot.sound]`.
-/

import GammaFixesDiracGenerations
import TransposeDimension
import Mathlib.Data.Sym.Card
import Mathlib.Analysis.Matrix.Spectrum

open Matrix
open scoped Kronecker

namespace SelfAdjointDiracCount

/-! ## 1. The symmetric matrices over any field, counted through unordered pairs -/

section Symmetric

variable (K : Type*) [Field K] (μ : Type*)

/-- The symmetric matrices `Rᵀ = R`, as a subspace. -/
def symMat : Submodule K (Matrix μ μ K) where
  carrier := {R | R.IsSymm}
  add_mem' ha hb := ha.add hb
  zero_mem' := isSymm_zero
  smul_mem' c _ h := h.smul c

variable {K μ} in
theorem mem_symMat {R : Matrix μ μ K} : R ∈ symMat K μ ↔ R.IsSymm := Iff.rfl

/-- A symmetric matrix read as a function on unordered pairs `s(i, j)`. -/
def toSym2 : symMat K μ →ₗ[K] (Sym2 μ → K) where
  toFun R := Sym2.lift ⟨fun i j => (R : Matrix μ μ K) i j, fun i j => (R.2.apply i j).symm⟩
  map_add' R S := by
    funext s
    induction s using Sym2.ind with
    | h i j => simp
  map_smul' c R := by
    funext s
    induction s using Sym2.ind with
    | h i j => simp

/-- A function on unordered pairs read as a symmetric matrix. -/
def ofSym2 (f : Sym2 μ → K) : symMat K μ :=
  ⟨Matrix.of fun i j => f s(i, j), by
    rw [mem_symMat, IsSymm.ext_iff]
    intro i j
    simp only [Matrix.of_apply]
    exact congrArg f Sym2.eq_swap⟩

/-- **The symmetric matrices are the functions on unordered pairs.** -/
def symEquiv : symMat K μ ≃ₗ[K] (Sym2 μ → K) where
  __ := toSym2 K μ
  invFun := ofSym2 K μ
  left_inv R := by
    ext i j
    rfl
  right_inv f := by
    funext s
    induction s using Sym2.ind with
    | h i j => rfl

/-- **THE COUNT**: `n × n` symmetric matrices over any field form a space of dimension
`(n + 1).choose 2`. -/
theorem finrank_symMat_choose [Fintype μ] :
    Module.finrank K (symMat K μ) = (Fintype.card μ + 1).choose 2 := by
  classical
  rw [(symEquiv K μ).finrank_eq, Module.finrank_fintype_fun_eq_card, Sym2.card]

/-- The same as `n(n+1)/2`. -/
theorem finrank_symMat [Fintype μ] : Module.finrank K (symMat K μ) =
    Fintype.card μ * (Fintype.card μ + 1) / 2 := by
  rw [finrank_symMat_choose, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/-- **Over `ℂ` it is `TransposeSplit.symSub`**, whose dimension `TransposeDimension` computed by
the complement with the antisymmetric matrices; `finrank_symMat_choose` at `K = ℂ` is that count
by another route. -/
theorem symMat_complex_eq_symSub [Fintype μ] : symMat ℂ μ = TransposeSplit.symSub μ := rfl

theorem finrank_symSub_choose_via_sym2 [Fintype μ] :
    Module.finrank ℂ (TransposeSplit.symSub μ) = (Fintype.card μ + 1).choose 2 := by
  rw [← symMat_complex_eq_symSub, finrank_symMat_choose]

end Symmetric

/-! ## 2. The self-adjoint Dirac operators the three conditions allow, counted -/

section SelfAdjoint

open GammaFixesDiracGenerations OrderOneRealGenerations

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The operators `Dsym ⊗ R` with `R` real symmetric: the image of `symMat ℝ μ` under unit 236's
`DsymGenL`. -/
noncomputable def selfAdjSolutions (μ : Type*) [Fintype μ] [DecidableEq μ] :
    Submodule ℝ (Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :=
  (symMat ℝ μ).map (DsymGenL μ)

/-- **They are exactly the self-adjoint operators the three conditions allow.** -/
theorem mem_selfAdjSolutions_iff (D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    D ∈ selfAdjSolutions μ ↔
      ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D ∧
        D * gammaGen μ = -(gammaGen μ * D)) ∧ D.IsHermitian := by
  rw [gen_fixes_dirac_selfAdjoint, selfAdjSolutions, Submodule.mem_map]
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, rfl⟩

/-- **THE SELF-ADJOINT COUNT.** The self-adjoint operators the three conditions allow form a real
vector space of dimension `n(n+1)/2`, `n` the number of generations. -/
theorem finrank_selfAdjSolutions :
    Module.finrank ℝ (selfAdjSolutions μ) = Fintype.card μ * (Fintype.card μ + 1) / 2 := by
  rw [selfAdjSolutions,
    ← (Submodule.equivMapOfInjective (DsymGenL μ) DsymGenL_injective (symMat ℝ μ)).finrank_eq,
    finrank_symMat]

/-- At three generations: six real numbers, against nine without self-adjointness
(`finrank_range_DsymGenL`). -/
theorem finrank_selfAdjSolutions_three : Module.finrank ℝ (selfAdjSolutions (Fin 3)) = 6 := by
  rw [finrank_selfAdjSolutions, Fintype.card_fin]

/-- At one generation: unit 170's one real scale. -/
theorem finrank_selfAdjSolutions_one : Module.finrank ℝ (selfAdjSolutions (Fin 1)) = 1 := by
  rw [finrank_selfAdjSolutions, Fintype.card_fin]

end SelfAdjoint


/-! ## 3. Rotations of the generations, and what is left after them -/

section Rotation

open GammaFixesDiracGenerations OrderOneRealGenerations RealSpectralWitness OrderOneNontrivial

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- `M` on the two slots and `N` on the generation: `M ⊗ N` with the indices regrouped. -/
def slotGen (M : Matrix Slots Slots ℂ) (N : Matrix μ μ ℂ) :
    Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ :=
  (M ⊗ₖ N).submatrix (Equiv.prodAssoc (Fin 2) (Fin 2) μ).symm
    (Equiv.prodAssoc (Fin 2) (Fin 2) μ).symm

omit [Fintype μ] [DecidableEq μ] in
theorem slotGen_apply (M : Matrix Slots Slots ℂ) (N : Matrix μ μ ℂ) (a b : Fin 2 × (Fin 2 × μ)) :
    slotGen M N a b = M (a.1, a.2.1) (b.1, b.2.1) * N a.2.2 b.2.2 := rfl

omit [DecidableEq μ] in
theorem slotGen_mul (M M' : Matrix Slots Slots ℂ) (N N' : Matrix μ μ ℂ) :
    slotGen M N * slotGen M' N' = slotGen (M * M') (N * N') := by
  rw [slotGen, slotGen, submatrix_mul_equiv, ← mul_kronecker_mul]
  rfl

omit [Fintype μ] [DecidableEq μ] in
theorem conjTranspose_slotGen (M : Matrix Slots Slots ℂ) (N : Matrix μ μ ℂ) :
    (slotGen M N)ᴴ = slotGen Mᴴ Nᴴ := by
  rw [slotGen, conjTranspose_submatrix, conjTranspose_kronecker]
  rfl

omit [Fintype μ] in
theorem slotGen_one_one : slotGen (1 : Matrix Slots Slots ℂ) (1 : Matrix μ μ ℂ) = 1 := by
  rw [slotGen, one_kronecker_one, submatrix_one_equiv]

omit [Fintype μ] [DecidableEq μ] in
theorem DsymGen_eq_slotGen (R : Matrix μ μ ℂ) : DsymGen R = slotGen Dsym R := rfl

omit [Fintype μ] in
theorem gammaGen_eq_slotGen : gammaGen μ = slotGen gammaMat 1 := by
  ext a b
  simp only [gammaGen, slotGen_apply, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype μ] in
theorem left_eq_slotGen (a : Matrix (Fin 2) (Fin 2) ℂ) :
    a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) = slotGen (a ⊗ₖ 1) 1 := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [slotGen_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype μ] in
theorem right_eq_slotGen (b : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)) = slotGen (1 ⊗ₖ b) 1 := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [slotGen_apply, kroneckerMap_apply, Matrix.one_apply]
  ring

/-- **A rotation of the generations**: a real matrix `U` on the generation label, the identity on
the two slots. -/
def genRot (U : Matrix μ μ ℝ) : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ :=
  slotGen 1 (U.map ((↑) : ℝ → ℂ))

theorem genRot_comm_slotGen (U : Matrix μ μ ℝ) (M : Matrix Slots Slots ℂ) :
    genRot U * slotGen M 1 = slotGen M 1 * genRot U := by
  rw [genRot, slotGen_mul, slotGen_mul, one_mul, mul_one, mul_one, one_mul]

/-- It commutes with the left action `a ⊗ 1`. -/
theorem genRot_comm_left (U : Matrix μ μ ℝ) (a : Matrix (Fin 2) (Fin 2) ℂ) :
    genRot U * (a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)) =
      (a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)) * genRot U := by
  rw [left_eq_slotGen, genRot_comm_slotGen]

/-- It commutes with the right action `1 ⊗ (b ⊗ 1)`. -/
theorem genRot_comm_right (U : Matrix μ μ ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    genRot U * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))) =
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))) * genRot U := by
  rw [right_eq_slotGen, genRot_comm_slotGen]

/-- It commutes with the grading. -/
theorem genRot_comm_gammaGen (U : Matrix μ μ ℝ) :
    genRot U * gammaGen μ = gammaGen μ * genRot U := by
  rw [gammaGen_eq_slotGen, genRot_comm_slotGen]

omit [Fintype μ] [DecidableEq μ] in
/-- It commutes with the real structure: `J W J⁻¹ = W`. -/
theorem exchConjGen_genRot (U : Matrix μ μ ℝ) : exchConjGen (genRot U) = genRot U := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [exchConjGen, genRot, Matrix.map_apply, Matrix.submatrix_apply, slotGen_apply,
    Matrix.one_apply, genSwap, Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases h1 : x = y <;> by_cases h2 : p = q <;> simp [h1, h2, Complex.conj_ofReal]

omit [Fintype μ] [DecidableEq μ] in
theorem conjTranspose_genRot (U : Matrix μ μ ℝ) : (genRot U)ᴴ = genRot Uᵀ := by
  rw [genRot, genRot, conjTranspose_slotGen, conjTranspose_one]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]

omit [DecidableEq μ] in
theorem map_ofReal_mul (U V : Matrix μ μ ℝ) :
    (U * V).map ((↑) : ℝ → ℂ) = U.map ((↑) : ℝ → ℂ) * V.map ((↑) : ℝ → ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

omit [DecidableEq μ] in
theorem genRot_mul (U V : Matrix μ μ ℝ) : genRot U * genRot V = genRot (U * V) := by
  rw [genRot, genRot, genRot, slotGen_mul, one_mul, map_ofReal_mul]

/-- **For `U` orthogonal it is unitary.** -/
theorem genRot_unitary {U : Matrix μ μ ℝ} (hU : U * Uᵀ = 1) :
    genRot U * (genRot U)ᴴ = 1 ∧ (genRot U)ᴴ * genRot U = 1 := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  rw [conjTranspose_genRot, genRot_mul, genRot_mul, hU, hU', genRot, Matrix.map_one _ rfl rfl]
  exact ⟨slotGen_one_one, slotGen_one_one⟩

omit [DecidableEq μ] in
/-- **Conjugating `Dsym ⊗ R` by a rotation rotates `R`**: `W (Dsym ⊗ R) Wᴴ = Dsym ⊗ (U R Uᵀ)`. -/
theorem genRot_conj_DsymGen (U R : Matrix μ μ ℝ) :
    genRot U * DsymGen (R.map ((↑) : ℝ → ℂ)) * (genRot U)ᴴ =
      DsymGen ((U * R * Uᵀ).map ((↑) : ℝ → ℂ)) := by
  rw [conjTranspose_genRot, genRot, genRot, DsymGen_eq_slotGen, DsymGen_eq_slotGen, slotGen_mul,
    slotGen_mul, one_mul, mul_one, map_ofReal_mul, map_ofReal_mul]

/-- **ROTATIONS PRESERVE THE SELF-ADJOINT SOLUTIONS**, for any real `U`. -/
theorem genRot_conj_mem (U : Matrix μ μ ℝ)
    {D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ} (hD : D ∈ selfAdjSolutions μ) :
    genRot U * D * (genRot U)ᴴ ∈ selfAdjSolutions μ := by
  obtain ⟨R, hR, rfl⟩ := Submodule.mem_map.mp hD
  refine Submodule.mem_map.mpr ⟨U * R * Uᵀ, ?_, ?_⟩
  · rw [mem_symMat, Matrix.IsSymm, transpose_mul, transpose_mul, transpose_transpose, hR.eq,
      mul_assoc]
  · exact (genRot_conj_DsymGen U R).symm

omit [Fintype μ] [DecidableEq μ] in
/-- A real symmetric matrix is Hermitian. -/
theorem isHermitian_of_isSymm {R : Matrix μ μ ℝ} (hR : R.IsSymm) : R.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact hR

/-- The spectral theorem, in the form used here: `R = V diag(λ) Vᵀ` with `V Vᵀ = 1`. -/
theorem spectral_real {R : Matrix μ μ ℝ} (hH : R.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix μ μ ℝ) * (hH.eigenvectorUnitary : Matrix μ μ ℝ)ᵀ = 1 ∧
      R = (hH.eigenvectorUnitary : Matrix μ μ ℝ) * diagonal hH.eigenvalues *
        (hH.eigenvectorUnitary : Matrix μ μ ℝ)ᵀ := by
  have hs : star (hH.eigenvectorUnitary : Matrix μ μ ℝ) =
      (hH.eigenvectorUnitary : Matrix μ μ ℝ)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [hs]
    rfl

/-- **THE NORMAL FORM.** Every self-adjoint solution is, after a rotation of the generations,
`Dsym ⊗ diag(λ)` — with `λ` the eigenvalues of its generation matrix. -/
theorem exists_genRot_diagonal {D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ}
    (hD : D ∈ selfAdjSolutions μ) :
    ∃ V : Matrix μ μ ℝ, V * Vᵀ = 1 ∧ ∃ ev : μ → ℝ,
      D = genRot V * DsymGen ((diagonal ev).map ((↑) : ℝ → ℂ)) * (genRot V)ᴴ := by
  obtain ⟨R, hR, rfl⟩ := Submodule.mem_map.mp hD
  have hH : R.IsHermitian := isHermitian_of_isSymm hR
  obtain ⟨hV, hRV⟩ := spectral_real hH
  refine ⟨_, hV, hH.eigenvalues, ?_⟩
  rw [genRot_conj_DsymGen, ← hRV]
  rfl

/-- **AND CONVERSELY**: the self-adjoint solutions are exactly the operators
`W (Dsym ⊗ diag(λ)) Wᴴ` with `W` an orthogonal change of basis of the generations and `λ` real. -/
theorem mem_selfAdjSolutions_iff_genRot
    (D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    D ∈ selfAdjSolutions μ ↔ ∃ V : Matrix μ μ ℝ, V * Vᵀ = 1 ∧ ∃ ev : μ → ℝ,
      D = genRot V * DsymGen ((diagonal ev).map ((↑) : ℝ → ℂ)) * (genRot V)ᴴ := by
  refine ⟨exists_genRot_diagonal, ?_⟩
  rintro ⟨V, -, ev, rfl⟩
  exact genRot_conj_mem V (Submodule.mem_map.mpr ⟨diagonal ev, isSymm_diagonal ev, rfl⟩)

/-- **THE CLASSIFICATION.** Two self-adjoint solutions `Dsym ⊗ R`, `Dsym ⊗ R'` are related by a
rotation of the generations — a unitary commuting with both actions, the grading and `J` — iff `R`
and `R'` have the same characteristic polynomial, that is the same eigenvalues with multiplicity. -/
theorem genRot_equiv_iff_charpoly {R R' : Matrix μ μ ℝ} (hR : R.IsSymm) (hR' : R'.IsSymm) :
    (∃ U : Matrix μ μ ℝ, U * Uᵀ = 1 ∧
      DsymGen (R'.map ((↑) : ℝ → ℂ)) = genRot U * DsymGen (R.map ((↑) : ℝ → ℂ)) * (genRot U)ᴴ) ↔
      R.charpoly = R'.charpoly := by
  constructor
  · rintro ⟨U, hU, h⟩
    have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
    rw [genRot_conj_DsymGen] at h
    have h' : R' = U * R * Uᵀ := DsymGenL_injective h
    rw [h', Matrix.charpoly_mul_comm, ← mul_assoc, hU', one_mul]
  · intro h
    have hH : R.IsHermitian := isHermitian_of_isSymm hR
    have hH' : R'.IsHermitian := isHermitian_of_isSymm hR'
    have hev : hH.eigenvalues = hH'.eigenvalues := (hH.eigenvalues_eq_eigenvalues_iff hH').mpr h
    obtain ⟨hV, hRV⟩ := spectral_real hH
    obtain ⟨hV', hRV'⟩ := spectral_real hH'
    set V := (hH.eigenvectorUnitary : Matrix μ μ ℝ)
    set V' := (hH'.eigenvectorUnitary : Matrix μ μ ℝ)
    have hVt : Vᵀ * V = 1 := mul_eq_one_comm.mp hV
    refine ⟨V' * Vᵀ, ?_, ?_⟩
    · rw [transpose_mul, transpose_transpose, mul_assoc, ← mul_assoc Vᵀ, hVt, one_mul, hV']
    · rw [genRot_conj_DsymGen]
      congr 2
      rw [hRV', hRV, hev]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᵀ V, hVt, Matrix.one_mul, ← Matrix.mul_assoc Vᵀ V, hVt,
        Matrix.one_mul]

end Rotation


/-! ## 4. The tensor-sum shape, exactly: the generation matrix is scalar -/

section TensorSum

open GammaFixesDiracGenerations OrderOneCommutant RealSpectralWitness OrderOneNontrivial
open SpectralTripleBimodule (pauli3)

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] [DecidableEq μ] in
theorem DsymGen_apply (R : Matrix μ μ ℂ) (x y p q : Fin 2) (i j : μ) :
    DsymGen R (x, (p, i)) (y, (q, j)) =
      ((if x = y then 1 else 0) * pauli3 p q + pauli3 x y * (if p = q then 1 else 0)) * R i j := by
  simp only [DsymGen, Matrix.of_apply, Dsym, Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply]
  ring

omit [Fintype μ] in
/-- **`Dsym ⊗ R` IS A TENSOR SUM EXACTLY WHEN `R` IS SCALAR**, in the grouping `C ⊗ 1 + 1 ⊗ B`. -/
theorem DsymGen_kronSum_iff (R : Matrix μ μ ℂ) :
    (∃ (C : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ),
        DsymGen R =
          C ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) ↔
      ∃ r : ℂ, R = r • (1 : Matrix μ μ ℂ) := by
  constructor
  · rintro ⟨C, B, h⟩
    refine ⟨(C 0 0 - C 1 1) / 2, ?_⟩
    ext i j
    have h0 := congrFun (congrFun h (0, (0, i))) (0, (0, j))
    have h1 := congrFun (congrFun h (1, (0, i))) (1, (0, j))
    rw [DsymGen_apply] at h0 h1
    simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq, true_and,
      pauli3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, if_true] at h0 h1
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs at h0 h1 ⊢ with hij
    · linear_combination (h0 - h1) / 2
    · linear_combination (h0 - h1) / 2
  · rintro ⟨r, rfl⟩
    refine ⟨r • pauli3, (r • pauli3) ⊗ₖ (1 : Matrix μ μ ℂ), ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    rw [DsymGen_apply]
    simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul,
      Prod.mk.injEq]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*] <;> ring

omit [Fintype μ] in
/-- **AND IN THE OTHER GROUPING**: `Dsym ⊗ R` is `genPart C + 1 ⊗ (B ⊗ 1)` exactly when `R` is
scalar. -/
theorem DsymGen_genPartSum_iff (R : Matrix μ μ ℂ) :
    (∃ (C : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ),
        DsymGen R =
          genPart (κ := Fin 2) C + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ ℂ))) ↔
      ∃ r : ℂ, R = r • (1 : Matrix μ μ ℂ) := by
  constructor
  · rintro ⟨C, B, h⟩
    refine ⟨(B 0 0 - B 1 1) / 2, ?_⟩
    ext i j
    have h0 := congrFun (congrFun h (0, (0, i))) (0, (0, j))
    have h1 := congrFun (congrFun h (0, (1, i))) (0, (1, j))
    rw [DsymGen_apply] at h0 h1
    simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, genPart, Matrix.of_apply,
      pauli3, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, if_true] at h0 h1
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs at h0 h1 ⊢ with hij
    · linear_combination (h0 - h1) / 2
    · linear_combination (h0 - h1) / 2
  · rintro ⟨r, rfl⟩
    refine ⟨Matrix.of fun a b => r * pauli3 a.1 b.1 * (if a.2 = b.2 then 1 else 0), r • pauli3, ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    rw [DsymGen_apply]
    simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul,
      genPart, Matrix.of_apply]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*] <;> ring

omit [Fintype μ] in
/-- **FOR A REAL GENERATION MATRIX**: `Dsym ⊗ R` is a tensor sum iff `R` is a real multiple of the
identity. So among the self-adjoint solutions the tensor-sum shape holds exactly when the
generations neither mix nor differ. -/
theorem DsymGen_real_kronSum_iff (R : Matrix μ μ ℝ) :
    (∃ (C : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ),
        DsymGen (R.map ((↑) : ℝ → ℂ)) =
          C ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B) ↔
      ∃ r : ℝ, R = r • (1 : Matrix μ μ ℝ) := by
  rw [DsymGen_kronSum_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r.re, ?_⟩
    ext i j
    have := congrArg Complex.re (congrFun (congrFun hr i) j)
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.ofReal_re] at this
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs at this ⊢ <;> simpa using this
  · rintro ⟨r, rfl⟩
    refine ⟨(r : ℂ), ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp

end TensorSum

end SelfAdjointDiracCount
