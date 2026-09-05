import FieldEigenGramSchmidt
import CycleMultiplicityCount

/-!
# A rotation of the field on a CONNECTED graph: the cycle

`FieldEigenGramSchmidt` reduced the rotation chain's needs to **two independent eigenvectors of
`green` at one eigenvalue**, and filed the remaining gap as one object: a connected graph with such
a pair. `CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` says the connected cycle has
the eigenvalue — **as a dimension over `ℝ`, not as two vectors.**

**A dimension of two is two vectors.** If every member of a subspace were a multiple of one of them,
the subspace would sit inside a line and have dimension at most one. That is the whole of the
missing step, and it is about subspaces rather than about characters — **neither route the
watchlist item named was needed.**

`PROOF_STRATEGY` §6 question 3: the previous unit was a `B` and this is the retry.

## What is proved

**`exists_independent_of_two_le_finrank`** — a subspace of dimension at least two contains `u ≠ 0`
and a `v` that is no multiple of it. Pure linear algebra: no graph, no matrix, no eigenvalue.

**`mem_eigenspace_iff_mulVec`** — membership of the kernel `CycleMultiplicityCount` uses is the
eigenvector equation, through `Matrix.toLin'_apply`.

**`exists_independent_eigenpair_cycle`** — so at an interior frequency the cycle has two independent
eigenvectors of `massive`, and hence of `green` at the reciprocal eigenvalue
(`FieldSignReflection.green_mulVec_of_massive_mulVec`, with `MassiveTorusSpectrum.sq_le_nuR` giving
the eigenvalue away from zero).

**`exists_rotation_symmetry_cycle`** — **the connected cycle carries a genuine rotation of the
Gaussian field, at `m ≠ 0`**: an orthogonal matrix, not the identity, commuting with the
propagator, whose isometry leaves the measure invariant. **The mass hypothesis is part of the
claim** — at `m = 0` the field is a point mass that every isometry preserves
(`FieldMassNecessity`, `ERRATUM 455`). **The first symmetry of this chain on a connected graph**,
and the first on a graph the OS programme is about.

## What is NOT here

**Not the torus in dimension `d > 1`.** The multiplicity count this uses is one-dimensional
(`CycleMultiplicityCount` is about `torusGraph 1 (N+3)`); the higher-dimensional fibres are
`TorusFibreOrbitPartition`'s orbits and **that composition is not made here. Not attempted, no cost
claimed** (`ERRATUM 246`).

**Not the box** — **SUPERSEDED 2026-09-05**, annotated where it stands rather than deleted
(`ERRATUM 94`), because it was true when written. The fence said the composition through
`BoxLapSpectrum` and `BoxEigenspaceDimension` "would be needed and is not made"; it is now made,
in `FieldBoxRotation.exists_rotation_symmetry_box`, and discharged at every `2 ≤ d` and every side
length `≥ 2` — the physical `d = 4` included — by `exists_rotation_symmetry_box_of_two_le`.

**No description of the commutant**, and no count of the rotations: every `(c, s)` on the unit
circle gives one and nothing here compares them.
⚠ **THE SECOND HALF IS SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`):
`FieldRotationCount` compares them and finds infinitely many. **The commutant is still not
described**, and that half stands.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense; a wider
finite-volume symmetry group is a wider shadow and not a smaller gap, which is what
`FieldAutInvariance`'s header says in capitals and what every file in this chain repeats.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldCycleRotation

open Matrix GraphLaplacian FieldOrthIsometry FieldEigenGramSchmidt

/-! ## 1. A dimension of two is two vectors -/

/-- **A SUBSPACE OF DIMENSION AT LEAST TWO CONTAINS TWO INDEPENDENT VECTORS.** If every member were
a multiple of one of them the subspace would sit inside a line. -/
theorem exists_independent_of_two_le_finrank {E : Type*} [AddCommGroup E] [Module ℝ E]
    {W : Submodule ℝ E} (h : 2 ≤ Module.finrank ℝ W) :
    ∃ u ∈ W, ∃ v ∈ W, u ≠ 0 ∧ ∀ c : ℝ, v ≠ c • u := by
  classical
  have hne : W ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    simp at h
  obtain ⟨u, huW, hu0⟩ := (Submodule.ne_bot_iff W).mp hne
  by_contra hcon
  push Not at hcon
  have hle : W ≤ Submodule.span ℝ {u} := by
    intro w hw
    obtain ⟨c, hc⟩ := hcon u huW w hw hu0
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hfin := Submodule.finrank_mono hle
  rw [finrank_span_singleton hu0] at hfin
  omega

/-! ## 2. The kernel is the eigenvector equation -/

theorem mem_eigenspace_iff_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (μ : ℝ) (x : n → ℝ) :
    x ∈ LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id) ↔ A *ᵥ x = μ • x := by
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/-! ## 3. The cycle -/

open SimpleGraph BoxGraph TorusReflection MassiveTorusSpectrum CycleMultiplicityCount
open FieldSignReflection

theorem dotProduct_self_ne_zero {n : Type*} [Fintype n] {x : n → ℝ} (hx : x ≠ 0) :
    x ⬝ᵥ x ≠ 0 := by
  intro hzero
  refine hx (funext fun i => ?_)
  have hsum : ∑ j, x j * x j = 0 := by rw [← dotProduct]; exact hzero
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (x j)).mp hsum i
    (Finset.mem_univ i)
  simpa using mul_self_eq_zero.mp this

/-- **TWO INDEPENDENT EIGENVECTORS OF THE PROPAGATOR ON THE CYCLE**, at an interior frequency. -/
theorem exists_independent_eigenpair_cycle (N : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    ∃ u v : Site 1 (N + 3) → ℝ, u ⬝ᵥ u ≠ 0 ∧ (∀ c : ℝ, v ≠ c • u) ∧
      green (torusGraph 1 (N + 3)) m *ᵥ u = (nuR N m k)⁻¹ • u ∧
      green (torusGraph 1 (N + 3)) m *ᵥ v = (nuR N m k)⁻¹ • v := by
  have h2 : 2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph 1 (N + 3)) m) - (nuR N m k) • LinearMap.id)) :=
    le_of_eq (finrank_eigenspace_interior_eq_two N m k hk0 hkhalf).symm
  obtain ⟨u, huW, v, hvW, hu0, hind⟩ := exists_independent_of_two_le_finrank h2
  have hnu : nuR N m k ≠ 0 := by
    have hle := sq_le_nuR N m k
    have hpos : (0 : ℝ) < m ^ 2 := by positivity
    linarith
  refine ⟨u, v, dotProduct_self_ne_zero hu0, hind, ?_, ?_⟩
  · exact green_mulVec_of_massive_mulVec hm hnu ((mem_eigenspace_iff_mulVec _ _ _).mp huW)
  · exact green_mulVec_of_massive_mulVec hm hnu ((mem_eigenspace_iff_mulVec _ _ _).mp hvW)

/-- **THE CONNECTED CYCLE CARRIES A GENUINE ROTATION OF THE GAUSSIAN FIELD.** -/
theorem exists_rotation_symmetry_cycle (N : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) :
    ∃ (R : Matrix (Site 1 (N + 3)) (Site 1 (N + 3)) ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h)
          (gaussianField (torusGraph 1 (N + 3)) m)
        = gaussianField (torusGraph 1 (N + 3)) m := by
  obtain ⟨u, v, hu0, hind, hu, hv⟩ := exists_independent_eigenpair_cycle N hm k hk0 hkhalf
  exact exists_rotation_symmetry_of_independent_eigenpair hm hu0 hind hu hv hcs hs


end FieldCycleRotation
