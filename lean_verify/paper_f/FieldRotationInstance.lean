import FieldRotation

/-!
# The rotation on a named class of graphs: the equal-length hypothesis, discharged

`FieldRotation` builds the rotation from two eigenvectors of `green` at one eigenvalue **of the same
squared length**, and carried that hypothesis rather than discharging it.
`FieldComponentEigen.exists_orthogonal_eigenpair_of_not_reachable` supplies a pair on any
disconnected graph — but the indicators of a component and its complement have squared lengths
`|A|` and `|V| − |A|`, **equal only when the graph splits exactly in half.** So the chain built a
rotation and had no graph to put it on.

**Rescaling fixes it**: `√⟪v,v⟫ · u` and `√⟪u,u⟫ · v` both have squared length `⟪u,u⟫⟪v,v⟫`, stay
orthogonal, and stay eigenvectors at the same eigenvalue, because scaling a vector does not change
either. `PROOF_STRATEGY` §6 question 3: the previous unit was a `B` and this is the retry.

## What is proved

**`dotProduct_self_nonneg`** and **`dotProduct_smul_self`** — a self-product is `≥ 0`, and scaling
multiplies it by the square.

**`eigen_smul`** — a scalar multiple of an eigenvector is an eigenvector at the same eigenvalue.

**`exists_equal_length_eigenpair`** — **the rescaling**: from any orthogonal non-zero eigenpair at a
common eigenvalue, an orthogonal eigenpair at that eigenvalue with **equal** squared lengths.

**`exists_rotation_symmetry_of_not_reachable`** — **so every disconnected graph carries a genuine
rotation of the Gaussian field, at `m ≠ 0`**: an orthogonal matrix, not the identity, commuting
with `green`, whose isometry leaves the measure invariant. **The mass hypothesis is part of the
claim, not boilerplate** — at `m = 0` the field is a point mass and every isometry preserves it,
on every graph (`FieldMassNecessity`, `ERRATUM 455`). That is the chain of 4–5 September
instantiated on a named class of graphs for the first time.

## What is NOT here

**Nothing on a connected graph**, which is the case the OS programme is about. There the eigenvalue
this construction uses has a one-dimensional eigenspace, and the degeneracies sit at eigenvalues
whose eigenvectors are the **complex** characters. Untouched, **not attempted, no cost claimed**
(`ERRATUM 246`).

**No description of the commutant.** A rotation and a family of reflections are members, not the
set.
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 459`):
`FieldCommutantSpectral.mul_green_comm_iff` describes it — a matrix commutes with `green` **iff**
it carries every eigenvector to an eigenvector at the same eigenvalue — and
`FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` makes that a description of
the symmetries of the measure and not of a subset of them. What is still missing is the
`∏ᵢ O(dᵢ)` packaging, not a characterisation.

**No count of the rotations.** Each `(c, s)` on the unit circle gives one and they are not compared
here; `FieldReflectionCount`'s separation argument is about reflections and does not apply.
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`): `FieldRotationCount.rotMatrix_inj`
compares them — `rotMatrix` sends `u` to `c • u + s • v`, so the angle is read back off the
matrix — and `infinite_symmetryMatrices_of_orthogonal_eigenpair` counts them as infinite.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldRotationInstance

open Matrix GraphLaplacian FieldOrthIsometry FieldRotation FieldComponentEigen

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Scaling -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem dotProduct_self_nonneg (u : V → ℝ) : 0 ≤ u ⬝ᵥ u := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg _

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem dotProduct_smul_self (c : ℝ) (u : V → ℝ) : (c • u) ⬝ᵥ (c • u) = c ^ 2 * (u ⬝ᵥ u) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem eigen_smul {u : V → ℝ} {μ c : ℝ} (h : green G m *ᵥ u = μ • u) :
    green G m *ᵥ (c • u) = μ • (c • u) := by
  rw [Matrix.mulVec_smul, h, smul_comm]

/-! ## 2. The rescaling -/

/-- **AN ORTHOGONAL EIGENPAIR CAN BE TAKEN OF EQUAL LENGTH.** `√⟪v,v⟫ · u` and `√⟪u,u⟫ · v` both
have squared length `⟪u,u⟫⟪v,v⟫`. -/
theorem exists_equal_length_eigenpair {u v : V → ℝ} {μ : ℝ}
    (hu0 : u ⬝ᵥ u ≠ 0) (hv0 : v ⬝ᵥ v ≠ 0) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    ∃ (u' v' : V → ℝ) (n : ℝ), n ≠ 0 ∧ u' ⬝ᵥ u' = n ∧ v' ⬝ᵥ v' = n ∧ u' ⬝ᵥ v' = 0 ∧
      green G m *ᵥ u' = μ • u' ∧ green G m *ᵥ v' = μ • v' := by
  have hua : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_nonneg u) (Ne.symm hu0)
  have hvb : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg v) (Ne.symm hv0)
  refine ⟨Real.sqrt (v ⬝ᵥ v) • u, Real.sqrt (u ⬝ᵥ u) • v, (u ⬝ᵥ u) * (v ⬝ᵥ v), by positivity,
    ?_, ?_, ?_, eigen_smul hu, eigen_smul hv⟩
  · rw [dotProduct_smul_self, Real.sq_sqrt hvb.le]
    ring
  · rw [dotProduct_smul_self, Real.sq_sqrt hua.le]
  · rw [smul_dotProduct, dotProduct_smul, huv, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero]

/-! ## 3. And so a disconnected graph carries a rotation -/

/-- **EVERY DISCONNECTED GRAPH CARRIES A GENUINE ROTATION OF THE GAUSSIAN FIELD**: an orthogonal
matrix, not the identity, commuting with the propagator, whose isometry leaves the measure
invariant. -/
theorem exists_rotation_symmetry_of_not_reachable (hm : m ≠ 0) {p q : V}
    (hpq : ¬ G.Reachable p q) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix V V ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h) (gaussianField G m) = gaussianField G m := by
  obtain ⟨u, v, hu0, hv0, huv, hu, hv⟩ :=
    exists_orthogonal_eigenpair_of_not_reachable (G := G) hm hpq
  obtain ⟨u', v', n, hn, hu'u', hv'v', hu'v', hu', hv'⟩ :=
    exists_equal_length_eigenpair (G := G) hu0 hv0 huv hu hv
  have hv'u' : v' ⬝ᵥ u' = 0 := by rw [dotProduct_comm]; exact hu'v'
  refine ⟨rotMatrix u' v' n c s, rotMatrix_transpose_mul_self hn hu'u' hv'v' hu'v' hcs,
    rotMatrix_ne_one hn hs hu'u' hv'v' hv'u', ?_⟩
  exact gaussianField_map_rotMatrix hm hn hu'u' hv'v' hu'v' hcs hu' hv'

end FieldRotationInstance
