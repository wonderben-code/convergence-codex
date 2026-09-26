/-
  GammaFixesDiracGenerations.lean — the grading with a generation index. On `ℂ² ⊗ (ℂ² ⊗ ℂ^μ)`
  — unit 170's space, `M₂(ℂ)` acting on itself, with every vector carrying a generation label
  from `μ` — an operator satisfies order-one, commutes with the real structure `J` and
  anticommutes with the grading `γ ⊗ 1` iff it is `Dsym ⊗ R` for a REAL matrix `R` on the
  generations. The operators the three conditions allow form a real vector space of dimension
  `(card μ)²` — one real number for each ordered pair of generations; at one generation, unit
  170's one real scale — and with self-adjointness `R` is exactly a real symmetric matrix. And
  the grading does not restore the tensor-sum shape: at two generations `Dsym ⊗ diag(1, 0)` meets
  all three conditions, is self-adjoint, and is a tensor sum in neither grouping.

  SPINE L6 / `WALLS` §W9 rung 2, second half — unit 170's grading carried to a space whose
  pieces repeat, after unit 234 carried `J` there; and SPINE L19 / `ASSUMPTIONS_LEDGER` 12 — the
  tensor-sum premise of unit 172's factorisation, not forced at a multiplicity of two by
  order-one (unit 232) or by order-one with `J` (unit 234), is not forced with the grading
  either. Hardening unit 236, 26 September 2026.

  WHY. Unit 234 (`OrderOneRealGenerations`) solved order-one with `J` and a generation index —
  `D = genPart A + 1 ⊗ Ā` — and its NOT list says *"The grading `γ` and the KO signs with a
  generation index, and what `Dγ = −γD` leaves of `A`."* Unit 170 (`GammaFixesDirac`) answered
  the question with no generations: on the regular bimodule of `M₂(ℂ)` the three conditions fix
  `D` up to one real scale. With generations the question becomes how much the conditions leave
  free on the generation label — where CCM's model puts its Yukawa matrices — and
  `PROPOSED_TAG_CHANGES` entry 5, the published *19 → 3*, turns on exactly that count. And
  whether the grading, the last of the three conditions, restores the tensor-sum shape that
  units 232 and 234 found not forced was open.

  WHAT IS PROVED (`μ` any finite type, over `ℂ`).
  (1) `genSlice M i j`: the `4 × 4` block of `M` between generations `i` and `j`;
      `genSlice_apply`, `ext_genSlice`. `gammaGen μ`: unit 170's `gammaMat` on the two `Fin 2`
      factors and the identity on the generation; **`gammaGen_sq`** (`γ² = 1`) and
      **`exchConjGen_gammaGen`** (`JγJ = −γ`, KO-6's `ε″ = −1`, as unit 170's
      `submatrix_prodSwap_gammaMat`). `genSlice_mul_gammaGen`, `genSlice_gammaGen_mul`,
      **`anticomm_gammaGen_iff`**: anticommuting with `gammaGen` is anticommuting with `gammaMat`
      slice by slice. `genBlock`, **`genSlice_genPart`**: the slice of unit 234's
      `genPart A + 1 ⊗ Ā` is unit 169's `A ⊗ 1 + 1 ⊗ Ā` for the block, so unit 170's
      `entries_of_anticomm` and `kron_eq_re_smul_Dsym` apply slice by slice.
  (2) `DsymGen R = Dsym ⊗ R` (`genSlice_DsymGen`); `diagGen`, `genBlock_diagGen`,
      `genPart_diagGen`, `DsymGen_anticomm`. **`gen_fixes_dirac`**: order-one against `M₂` on the
      left and `M₂ ⊗ 1` on the right, `exchConjGen D = D` and `D γ = −γ D` hold iff
      `D = Dsym ⊗ R` for a real `R` — block by block `A = diag(a, −ā)`, and `D` keeps only the
      real part of `a`: the imaginary part is unit 234's fibre `1 ⊗ G`.
  (3) `DsymGen_apply_zero`; `DsymGenL`, `R ↦ Dsym ⊗ R` as a real-linear map;
      **`DsymGenL_injective`**; **`gen_fixes_dirac_iff_mem_range`**; **`finrank_range_DsymGenL`**:
      the solutions form a real vector space of dimension `(card μ)²`.
  (4) **`DsymGen_isHermitian_iff`**: `Dsym ⊗ R` is self-adjoint iff `R` is symmetric;
      **`gen_fixes_dirac_selfAdjoint`**: the three conditions and self-adjointness hold iff
      `D = Dsym ⊗ R` with `R` real and symmetric. **`exists_gen_fixes_dirac_not_kronSum`**: at
      `μ = Fin 2`, `Dsym ⊗ diag(1, 0)` satisfies all three conditions and is self-adjoint, and it
      is neither `C ⊗ 1 + 1 ⊗ B` nor `genPart C + 1 ⊗ (B ⊗ 1)` for any `C`, `B`.
  (5) **`gen_fixes_dirac_op`**: the same as operators, with `J = conjPerm (genSwap (Fin 2) μ)`
      conjugate-linear and the grading `matAlg (gammaGen μ)`.

  NOT PROVED, said exactly.
  • Any other grading. The grading is unit 170's `gammaMat` with the identity on the generation,
    and the theorem is for THAT `γ`. It is not even: no KO-6 grading on unit 170's space
    commutes with the algebra (`EvenGradingObstruction.no_even_KO6_grading_on_Hw`,
    `gammaCcm_not_even`); whether that obstruction persists with generations, and what another
    admissible grading would leave, are not asked.
  • Products, `ℍ` and CCM's `A_F` with a generation index: the one factor `M₂(ℂ)` only.
  • What `R` is physically. Nothing here identifies it with Yukawa matrices, or reads a mass or a
    mixing angle off it; CCM's Yukawa matrices are complex, and whether a larger model leaves a
    complex matrix is not asked.
  • The dimension of the self-adjoint solutions: they are `Dsym ⊗ R` with `R` real symmetric,
    and no theorem counts those; the estate counts only the complex symmetric matrices
    (`TransposeDimension.finrank_symSub_fin`).
  • The spectrum of `Dsym ⊗ R` and the trace of its exponential: for the operator in (4) only the
    shape is shown not forced, as in units 232 and 234. Nothing about the cutoff, the cascade's
    `D` (`L40433`), the factor list, or a tag: rung 2 is not climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). None beyond the declarations' types: every
  statement takes elements of its types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 27 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. A first draft's `slice` is taken in Mathlib
  (`Finset.slice` and three others) and was renamed `genSlice`. The nearest statements are unit
  170's `anticomm_gammaCcm_iff`, `entries_of_anticomm`, `kron_eq_re_smul_Dsym` and
  `ccm_fixes_dirac`, whose versions with a generation index are `anticomm_gammaGen_iff`,
  `genSlice_genPart` (through which `entries_of_anticomm` is applied), `genPart_diagGen` and
  `gen_fixes_dirac`; and `RealSpectralWitness`'s `gammaMat_sq` and
  `submatrix_prodSwap_gammaMat`, whose versions are `gammaGen_sq` and `exchConjGen_gammaGen`; and
  unit 234's `exists_orderOne_jInv_not_kronSum`, of which `exists_gen_fixes_dirac_not_kronSum` is
  the version with the grading.

  `#print axioms` on all 27 declarations below: `[propext, Classical.choice, Quot.sound]`.
-/

import OrderOneRealGenerations
import GammaFixesDirac

open Matrix
open scoped Kronecker

namespace GammaFixesDiracGenerations

open OrderOneCommutant OrderOneRealGenerations RealSpectralWitness OrderOneNontrivial
  SpectralTripleBimodule GammaFixesDirac

/-! ## 1. Slices at a pair of generations -/

section Slices

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The `(i, j)` slice of a matrix on `Fin 2 × (Fin 2 × μ)`: the `4 × 4` matrix on `Slots` it
has between generation `i` and generation `j`. -/
def genSlice (M : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) (i j : μ) :
    Matrix Slots Slots ℂ :=
  Matrix.of fun a b => M (a.1, (a.2, i)) (b.1, (b.2, j))

omit [Fintype μ] [DecidableEq μ] in
theorem genSlice_apply (M : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) (i j : μ)
    (a b : Slots) : genSlice M i j a b = M (a.1, (a.2, i)) (b.1, (b.2, j)) := rfl

omit [Fintype μ] [DecidableEq μ] in
/-- A matrix is determined by its slices. -/
theorem ext_genSlice {M N : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ}
    (h : ∀ i j, genSlice M i j = genSlice N i j) : M = N := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  exact congrFun (congrFun (h i j) (x, p)) (y, q)

/-- **The grading with a generation index**: `gammaMat` on the two `Fin 2` factors, the identity
on the generation. -/
def gammaGen (μ : Type*) [DecidableEq μ] : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ :=
  Matrix.of fun a b => if a.2.2 = b.2.2 then gammaMat (a.1, a.2.1) (b.1, b.2.1) else 0

theorem genSlice_mul_gammaGen (M : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) (i j : μ) :
    genSlice (M * gammaGen μ) i j = genSlice M i j * gammaMat := by
  ext a b
  simp only [genSlice_apply, Matrix.mul_apply, gammaGen, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem genSlice_gammaGen_mul (M : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) (i j : μ) :
    genSlice (gammaGen μ * M) i j = gammaMat * genSlice M i j := by
  ext a b
  simp only [genSlice_apply, Matrix.mul_apply, gammaGen, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- The grading with a generation index is an involution, as `gammaMat` is (`gammaMat_sq`). -/
theorem gammaGen_sq : gammaGen μ * gammaGen μ = 1 := by
  refine ext_genSlice fun i j => ?_
  rw [genSlice_gammaGen_mul]
  ext a b
  simp only [Matrix.mul_apply, genSlice_apply, gammaGen, Matrix.of_apply, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij
    have := congrFun (congrFun gammaMat_sq a) b
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [if_true, and_true]
    rw [this]
    rcases a with ⟨x, p⟩
    rcases b with ⟨y, q⟩
    simp [Prod.ext_iff]
  · simp [hij]

omit [Fintype μ] in
/-- **KO-6 sign `ε″ = −1` with generations**: exchange-conjugation reverses the grading, as
`submatrix_prodSwap_gammaMat` does without them. -/
theorem exchConjGen_gammaGen : exchConjGen (gammaGen μ) = -gammaGen μ := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  have := congrFun (congrFun submatrix_prodSwap_gammaMat (x, p)) (y, q)
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.neg_apply] at this
  simp only [exchConjGen, genSwap, gammaGen, Matrix.map_apply, Matrix.submatrix_apply,
    Equiv.coe_fn_mk, Matrix.of_apply, Matrix.neg_apply]
  split_ifs
  · exact this
  · simp

/-- Anticommutation with the grading, slice by slice. -/
theorem anticomm_gammaGen_iff (M : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    M * gammaGen μ = -(gammaGen μ * M) ↔
      ∀ i j, genSlice M i j * gammaMat = -(gammaMat * genSlice M i j) := by
  constructor
  · intro h i j
    rw [← genSlice_mul_gammaGen, ← genSlice_gammaGen_mul, h]
    rfl
  · intro h
    refine ext_genSlice fun i j => ?_
    rw [genSlice_mul_gammaGen, h]
    rw [show genSlice (-(gammaGen μ * M)) i j = -genSlice (gammaGen μ * M) i j from rfl,
      genSlice_gammaGen_mul]

/-- The `(i, j)` generation block of a matrix on `Fin 2 × μ`. -/
def genBlock (A : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) (i j : μ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun x y => A (x, i) (y, j)

omit [Fintype μ] [DecidableEq μ] in
/-- The slice of unit 234's `genPart A + 1 ⊗ Ā` is unit 169's `A ⊗ 1 + 1 ⊗ Ā` for the block. -/
theorem genSlice_genPart (A : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) (i j : μ) :
    genSlice (genPart (κ := Fin 2) A +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)) i j =
      genBlock A i j ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (genBlock A i j).map (starRingEnd ℂ) := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [genSlice_apply, genBlock, genPart, Matrix.add_apply, Matrix.of_apply,
    kroneckerMap_apply, Matrix.one_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- **The Dirac operator with a generation matrix**: `Dsym` on the two `Fin 2` factors, `R` on the
generation. -/
def DsymGen (R : Matrix μ μ ℂ) : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ :=
  Matrix.of fun a b => Dsym (a.1, a.2.1) (b.1, b.2.1) * R a.2.2 b.2.2

omit [Fintype μ] [DecidableEq μ] in
theorem genSlice_DsymGen (R : Matrix μ μ ℂ) (i j : μ) :
    genSlice (DsymGen R) i j = R i j • Dsym := by
  ext a b
  simp [genSlice_apply, DsymGen, mul_comm]

end Slices

/-! ## 2. The three conditions with a generation index -/

section Main

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The block matrix `diag(R, −R)` on `Fin 2 × μ`, `R` real: the `A` whose `genPart A + 1 ⊗ Ā` is
`DsymGen R`. -/
def diagGen (R : Matrix μ μ ℝ) : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 then (if a.1 = 0 then (R a.2 b.2 : ℂ) else -(R a.2 b.2 : ℂ)) else 0

omit [Fintype μ] [DecidableEq μ] in
theorem genBlock_diagGen (R : Matrix μ μ ℝ) (i j : μ) :
    genBlock (diagGen R) i j 0 1 = 0 ∧ genBlock (diagGen R) i j 1 0 = 0 ∧
      genBlock (diagGen R) i j 1 1 = -(starRingEnd ℂ) (genBlock (diagGen R) i j 0 0) := by
  simp [genBlock, diagGen, Complex.conj_ofReal]

omit [Fintype μ] [DecidableEq μ] in
theorem genPart_diagGen (R : Matrix μ μ ℝ) :
    genPart (κ := Fin 2) (diagGen R) +
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (diagGen R).map (starRingEnd ℂ) =
      DsymGen (R.map ((↑) : ℝ → ℂ)) := by
  refine ext_genSlice fun i j => ?_
  obtain ⟨h01, h10, h11⟩ := genBlock_diagGen R i j
  rw [genSlice_genPart, kron_eq_re_smul_Dsym _ h01 h10 h11, genSlice_DsymGen]
  simp [genBlock, diagGen]

/-- `DsymGen R` anticommutes with the grading, for every `R`. -/
theorem DsymGen_anticomm (R : Matrix μ μ ℂ) :
    DsymGen R * gammaGen μ = -(gammaGen μ * DsymGen R) := by
  refine (anticomm_gammaGen_iff _).mpr fun i j => ?_
  rw [genSlice_DsymGen, smul_mul_assoc, Dsym_anticomm_gammaMat, mul_smul_comm, smul_neg]

/-- **ORDER-ONE, THE REAL STRUCTURE AND THE GRADING, WITH A GENERATION INDEX.** On
`ℂ² ⊗ (ℂ² ⊗ ℂ^μ)` — unit 170's space with every vector carrying a generation label — an
operator satisfies order-one against `M₂` on the left and `M₂ ⊗ 1` on the right, is invariant under
exchange-conjugation and anticommutes with `gammaMat ⊗ 1` iff it is `Dsym ⊗ R` for a REAL matrix
`R` on the generations. -/
theorem gen_fixes_dirac (D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D ∧
      D * gammaGen μ = -(gammaGen μ * D)) ↔
      ∃ R : Matrix μ μ ℝ, D = DsymGen (R.map ((↑) : ℝ → ℂ)) := by
  constructor
  · rintro ⟨h1, hJ, hγ⟩
    obtain ⟨A, rfl⟩ := (orderOne_exchConjGen_iff D).mp ⟨h1, hJ⟩
    have hs := (anticomm_gammaGen_iff _).mp hγ
    refine ⟨Matrix.of fun i j => (A (0, i) (0, j)).re, ext_genSlice fun i j => ?_⟩
    have hij := hs i j
    rw [genSlice_genPart] at hij
    obtain ⟨h01, h10, h11⟩ := entries_of_anticomm _ hij
    rw [genSlice_genPart, kron_eq_re_smul_Dsym _ h01 h10 h11, genSlice_DsymGen]
    rfl
  · rintro ⟨R, rfl⟩
    obtain ⟨h1, hJ⟩ := (orderOne_exchConjGen_iff _).mpr ⟨diagGen R, (genPart_diagGen R).symm⟩
    exact ⟨h1, hJ, DsymGen_anticomm _⟩

end Main

/-! ## 3. How many operators the three conditions leave: `(card μ)²` real dimensions -/

section Count

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] [DecidableEq μ] in
theorem DsymGen_apply_zero (R : Matrix μ μ ℂ) (i j : μ) :
    DsymGen R (0, (0, i)) (0, (0, j)) = 2 * R i j := by
  have h : Dsym (0, 0) (0, 0) = 2 := by
    simp [Dsym, pauli3, kroneckerMap_apply]
    norm_num
  simp only [DsymGen, Matrix.of_apply, h]

/-- `R ↦ DsymGen R` on real matrices, as a real-linear map. -/
def DsymGenL (μ : Type*) [Fintype μ] [DecidableEq μ] :
    Matrix μ μ ℝ →ₗ[ℝ] Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ where
  toFun R := DsymGen (R.map ((↑) : ℝ → ℂ))
  map_add' R S := by
    ext a b
    simp [DsymGen, mul_add]
  map_smul' c R := by
    ext a b
    simp only [DsymGen, Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, RingHom.id_apply,
      smul_eq_mul, Complex.ofReal_mul]
    change _ = (c : ℂ) * _
    ring

theorem DsymGenL_injective : Function.Injective (DsymGenL μ) := by
  intro R S h
  ext i j
  have := congrFun (congrFun h (0, (0, i))) (0, (0, j))
  simp only [DsymGenL, LinearMap.coe_mk, AddHom.coe_mk, DsymGen_apply_zero,
    Matrix.map_apply] at this
  exact_mod_cast (mul_right_injective₀ (two_ne_zero : (2 : ℂ) ≠ 0)) this

/-- The three conditions carve out exactly the range of `DsymGenL`. -/
theorem gen_fixes_dirac_iff_mem_range (D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D ∧
      D * gammaGen μ = -(gammaGen μ * D)) ↔ D ∈ LinearMap.range (DsymGenL μ) := by
  rw [gen_fixes_dirac, LinearMap.mem_range]
  exact exists_congr fun R => eq_comm

/-- **THE COUNT.** The operators the three conditions allow form a real vector space of dimension
`(card μ)²`: one real number per pair of generations. At one generation, unit 170's one real
scale. -/
theorem finrank_range_DsymGenL :
    Module.finrank ℝ (LinearMap.range (DsymGenL μ)) = Fintype.card μ ^ 2 := by
  rw [LinearMap.finrank_range_of_inj DsymGenL_injective, Module.finrank_matrix, Module.finrank_self]
  ring

end Count

/-! ## 4. Self-adjointness: `R` symmetric -/

section SelfAdjoint

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] [DecidableEq μ] in
theorem DsymGen_isHermitian_iff (R : Matrix μ μ ℝ) :
    (DsymGen (R.map ((↑) : ℝ → ℂ))).IsHermitian ↔ R.IsSymm := by
  have hD : ∀ a b, star (Dsym b a) = Dsym a b := fun a b => by
    have := congrFun (congrFun Dsym_star a) b
    rwa [Matrix.star_apply] at this
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (0, (0, i))) (0, (0, j))
    rw [Matrix.conjTranspose_apply, DsymGen_apply_zero, DsymGen_apply_zero] at this
    simp only [Matrix.map_apply, star_mul', Complex.star_def, Complex.conj_ofReal,
      map_ofNat] at this
    rw [Matrix.transpose_apply]
    exact_mod_cast (mul_right_injective₀ (two_ne_zero : (2 : ℂ) ≠ 0)) this
  · intro h
    ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [DsymGen, Matrix.of_apply, Matrix.map_apply, star_mul', hD]
    rw [Complex.star_def, Complex.conj_ofReal]
    congr 2
    exact (congrFun (congrFun h b.2.2) a.2.2).symm

/-- **WITH SELF-ADJOINTNESS**: the three conditions and `D = Dᴴ` hold iff `D = Dsym ⊗ R` for a
real SYMMETRIC `R`. -/
theorem gen_fixes_dirac_selfAdjoint (D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ) :
    (((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D ∧
      D * gammaGen μ = -(gammaGen μ * D)) ∧ D.IsHermitian) ↔
      ∃ R : Matrix μ μ ℝ, R.IsSymm ∧ D = DsymGen (R.map ((↑) : ℝ → ℂ)) := by
  rw [gen_fixes_dirac]
  constructor
  · rintro ⟨⟨R, rfl⟩, h⟩
    exact ⟨R, (DsymGen_isHermitian_iff R).mp h, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨⟨R, rfl⟩, (DsymGen_isHermitian_iff R).mpr hR⟩

/-- **THE GRADING DOES NOT RESTORE THE TENSOR-SUM SHAPE EITHER.** At `μ = Fin 2`,
`D = Dsym ⊗ diag(1, 0)` satisfies all three conditions and is self-adjoint, and it is neither
`C ⊗ 1 + 1 ⊗ B` nor `genPart C + 1 ⊗ (B ⊗ 1)` for any `C`, `B`. -/
theorem exists_gen_fixes_dirac_not_kronSum :
    ∃ D : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ, D.IsHermitian ∧
      ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ),
          ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)⁆,
            (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))⁆ = 0) ∧
        exchConjGen D = D ∧ D * gammaGen (Fin 2) = -(gammaGen (Fin 2) * D)) ∧
      (∀ (C : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
        D ≠ C ⊗ₖ 1 + 1 ⊗ₖ B) ∧
      (∀ (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ),
        D ≠ genPart C + 1 ⊗ₖ (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hR : (Matrix.diagonal ![(1 : ℝ), 0]).IsSymm := Matrix.isSymm_diagonal _
  have hD := (gen_fixes_dirac_selfAdjoint
    (DsymGen ((Matrix.diagonal ![(1 : ℝ), 0]).map ((↑) : ℝ → ℂ)))).mpr ⟨_, hR, rfl⟩
  have hd : ∀ x p i, DsymGen ((Matrix.diagonal ![(1 : ℝ), 0]).map ((↑) : ℝ → ℂ)) (x, (p, i))
      (x, (p, i)) = Dsym (x, p) (x, p) * (if i = 0 then 1 else 0) := by
    intro x p i
    fin_cases i <;> simp [DsymGen]
  have h00 : Dsym (0, 0) (0, 0) = 2 := by
    simp [Dsym, pauli3, kroneckerMap_apply]
    norm_num
  have h01 : Dsym (0, 1) (0, 1) = 0 := by simp [Dsym, pauli3, kroneckerMap_apply]
  have h10 : Dsym (1, 0) (1, 0) = 0 := by simp [Dsym, pauli3, kroneckerMap_apply]
  refine ⟨_, hD.2, hD.1, fun C B h => ?_, fun C B h => ?_⟩
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 0))
    have e2 := congrFun (congrFun h (1, (0, 0))) (1, (0, 0))
    have e3 := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
    have e4 := congrFun (congrFun h (1, (0, 1))) (1, (0, 1))
    rw [hd] at e1 e2 e3 e4
    simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply_eq, mul_one, one_mul,
      h00, h10, Fin.isValue, ↓reduceIte, one_ne_zero] at e1 e2 e3 e4
    have : (2 : ℂ) = 0 := by linear_combination e1 - e2 - e3 + e4
    exact two_ne_zero this
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 0))
    have e2 := congrFun (congrFun h (0, (1, 0))) (0, (1, 0))
    have e3 := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
    have e4 := congrFun (congrFun h (0, (1, 1))) (0, (1, 1))
    rw [hd] at e1 e2 e3 e4
    simp only [genPart, Matrix.add_apply, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply_eq,
      mul_one, one_mul, h00, h01, Fin.isValue, ↓reduceIte, one_ne_zero] at e1 e2 e3 e4
    have : (2 : ℂ) = 0 := by linear_combination e1 - e2 - e3 + e4
    exact two_ne_zero this

end SelfAdjoint

/-! ## 5. As operators on `ℂ^{Fin 2 × (Fin 2 × μ)}`, with the conjugate-linear `J` -/

section Operators

open ConjugatePermutation OppositeFromRealStructure OrderOneRegularBimodule

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- **THE THREE CONDITIONS WITH GENERATIONS, AS OPERATORS.** With `π(a) = a ⊗ 1`, the right action
`1 ⊗ (b ⊗ 1)`, `J = conjPerm (genSwap (Fin 2) μ)` and the grading `matAlg (gammaGen μ)`, an
operator satisfies order-one, commutes with `J` and anticommutes with the grading iff it is
`matAlg (Dsym ⊗ R)` for a real `R`. -/
theorem gen_fixes_dirac_op (D : Module.End ℂ (EuclideanSpace ℂ (Fin 2 × (Fin 2 × μ)))) :
    ((∀ a b : Matrix (Fin 2) (Fin 2) ℂ,
        ⁅⁅D, matAlg _ (a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ))⁆,
          matAlg _ ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))⁆ = 0) ∧
      (∀ v, conjPerm (genSwap (Fin 2) μ) (D (conjPerm (genSwap (Fin 2) μ) v)) = D v) ∧
      D * matAlg _ (gammaGen μ) = -(matAlg _ (gammaGen μ) * D)) ↔
    ∃ R : Matrix μ μ ℝ, D = matAlg _ (DsymGen (R.map ((↑) : ℝ → ℂ))) := by
  obtain ⟨M, rfl⟩ := matAlg_surjective' (Fin 2 × (Fin 2 × μ)) D
  have key : ∀ a b : Matrix (Fin 2) (Fin 2) ℂ,
      ⁅⁅matAlg _ M, matAlg _ (a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ))⁆,
          matAlg _ ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))⁆ = 0 ↔
        ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0 := by
    intro a b
    have e := map_lie_lie (matAlg (Fin 2 × (Fin 2 × μ))) M
      (a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ))
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))
    constructor
    · intro h
      exact matAlg_injective _ (by rw [map_zero]; exact e.trans h)
    · intro h
      exact e.symm.trans (by rw [h, map_zero])
  have hγ : matAlg _ M * matAlg _ (gammaGen μ) = -(matAlg _ (gammaGen μ) * matAlg _ M) ↔
      M * gammaGen μ = -(gammaGen μ * M) := by
    rw [← map_mul, ← map_mul, ← map_neg]
    exact (matAlg_injective _).eq_iff
  simp only [key, jInvGen_matAlg_iff, hγ]
  rw [gen_fixes_dirac]
  exact ⟨fun ⟨R, hR⟩ => ⟨R, by rw [hR]⟩, fun ⟨R, hR⟩ => ⟨R, matAlg_injective _ hR⟩⟩

end Operators

end GammaFixesDiracGenerations
