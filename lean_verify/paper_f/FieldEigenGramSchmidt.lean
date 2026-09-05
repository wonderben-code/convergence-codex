import FieldRotationInstance

/-!
# Independent is enough: the rotation needs no orthogonality hypothesis

Every step of the rotation chain assumes its two eigenvectors are **orthogonal**, and the only pair
the estate produces — a component's indicator and its complement's — is orthogonal by accident of
having disjoint supports. **An eigenspace of dimension two supplies two INDEPENDENT vectors, not two
orthogonal ones**, so the hypothesis as stated cannot be met from a dimension count, which is how
the connected case would have to be reached.

**One subtraction removes it.** For eigenvectors `u`, `v` at the same eigenvalue,
`v − (⟪u,v⟫/⟪u,u⟫)·u` is orthogonal to `u`, is still an eigenvector at that eigenvalue — every
combination of eigenvectors at one eigenvalue is one — and is non-zero exactly when `v` is not a
multiple of `u`.

`PROOF_STRATEGY` §7 rule 3, and the hypothesis removed is *orthogonal*, down to *independent*.

## What is proved

**`eigen_sub`** and **`eigen_smul_sub`** — eigenvectors at one eigenvalue are closed under the
combinations used below.

**`gramSchmidt`** — `v − (⟪u,v⟫/⟪u,u⟫)·u`, with **`dotProduct_gramSchmidt`** proving it orthogonal
to `u` and **`gramSchmidt_ne_zero`** proving it non-zero when `v ∉ span u`, stated concretely as
*`v ≠ c · u` for every `c`*.

**`gramSchmidt_eigen`** — and it is an eigenvector at the same eigenvalue.

**`exists_rotation_symmetry_of_independent_eigenpair`** — **so two INDEPENDENT eigenvectors at one
eigenvalue give a rotation symmetry of the Gaussian field at `m ≠ 0`**, with no orthogonality
assumed anywhere. **The mass hypothesis is part of the claim** — at `m = 0` the field is a point
mass, every isometry preserves it, and there is no eigenvector to rotate (`FieldMassNecessity`,
`ERRATUM 455`). `FieldRotationInstance.exists_rotation_symmetry_of_not_reachable` is the
disconnected instance and keeps its own proof (`ERRATUM 337`).

## What is NOT here

**Still nothing on a connected graph**, and the gap is now exactly one object: **a connected graph
whose propagator has an eigenvalue of multiplicity at least two, with two of its eigenvectors
exhibited.** `CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` says the connected cycle
has such an eigenvalue — **a dimension, not two vectors** — and turning a `finrank` of two into two
independent members is the step this file does not take. **Not attempted, no cost claimed**
(`ERRATUM 246`), and naming the step is not a claim that it is short (`ERRATUM 194`).

**No description of the commutant**, and no count of the rotations.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldEigenGramSchmidt

open Matrix GraphLaplacian FieldOrthIsometry FieldRotationInstance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Eigenvectors at one eigenvalue are closed under the combination -/

theorem eigen_sub {u v : V → ℝ} {μ : ℝ} (hu : green G m *ᵥ u = μ • u)
    (hv : green G m *ᵥ v = μ • v) : green G m *ᵥ (v - u) = μ • (v - u) := by
  rw [Matrix.mulVec_sub, hu, hv, smul_sub]

theorem eigen_smul_sub {u v : V → ℝ} {μ c : ℝ} (hu : green G m *ᵥ u = μ • u)
    (hv : green G m *ᵥ v = μ • v) : green G m *ᵥ (v - c • u) = μ • (v - c • u) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hu, hv, smul_sub, smul_comm]

/-! ## 2. The subtraction -/

/-- **`v` MADE ORTHOGONAL TO `u`.** -/
noncomputable def gramSchmidt (u v : V → ℝ) : V → ℝ := v - ((u ⬝ᵥ v) / (u ⬝ᵥ u)) • u

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem dotProduct_gramSchmidt {u : V → ℝ} (hu : u ⬝ᵥ u ≠ 0) (v : V → ℝ) :
    u ⬝ᵥ gramSchmidt u v = 0 := by
  rw [gramSchmidt, dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **AND IT IS NON-ZERO EXACTLY WHEN `v` IS NOT A MULTIPLE OF `u`.** -/
theorem gramSchmidt_ne_zero {u v : V → ℝ} (hind : ∀ c : ℝ, v ≠ c • u) :
    gramSchmidt u v ≠ 0 := by
  intro h
  exact hind ((u ⬝ᵥ v) / (u ⬝ᵥ u)) (by
    have := sub_eq_zero.mp h
    exact this)

theorem gramSchmidt_eigen {u v : V → ℝ} {μ : ℝ} (hu : green G m *ᵥ u = μ • u)
    (hv : green G m *ᵥ v = μ • v) :
    green G m *ᵥ gramSchmidt u v = μ • gramSchmidt u v :=
  eigen_smul_sub hu hv

/-! ## 3. So independence is enough -/

/-- **TWO INDEPENDENT EIGENVECTORS AT ONE EIGENVALUE GIVE A ROTATION SYMMETRY**, with no
orthogonality assumed. -/
theorem exists_rotation_symmetry_of_independent_eigenpair (hm : m ≠ 0) {u v : V → ℝ} {μ : ℝ}
    (hu0 : u ⬝ᵥ u ≠ 0) (hind : ∀ c : ℝ, v ≠ c • u)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix V V ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h) (gaussianField G m) = gaussianField G m := by
  set w : V → ℝ := gramSchmidt u v with hw
  have hw0 : w ⬝ᵥ w ≠ 0 := by
    intro hzero
    refine gramSchmidt_ne_zero hind ?_
    funext i
    have hnn := dotProduct_self_nonneg (V := V) w
    have hsum : ∑ j, w j * w j = 0 := by rw [← dotProduct]; exact hzero
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (w j)).mp hsum i
      (Finset.mem_univ i)
    simpa using mul_self_eq_zero.mp this
  obtain ⟨u', v', n, hn, hu'u', hv'v', hu'v', hu', hv'⟩ :=
    exists_equal_length_eigenpair (G := G) (m := m) hu0 hw0
      (dotProduct_gramSchmidt hu0 v) hu (gramSchmidt_eigen hu hv)
  have hv'u' : v' ⬝ᵥ u' = 0 := by rw [dotProduct_comm]; exact hu'v'
  refine ⟨FieldRotation.rotMatrix u' v' n c s,
    FieldRotation.rotMatrix_transpose_mul_self hn hu'u' hv'v' hu'v' hcs,
    FieldRotation.rotMatrix_ne_one hn hs hu'u' hv'v' hv'u', ?_⟩
  exact FieldRotation.gaussianField_map_rotMatrix hm hn hu'u' hv'v' hu'v' hcs hu' hv'

end FieldEigenGramSchmidt
