import FieldComponentEigen

/-!
# The rotation, built: a symmetry of the field that is not a reflection

`FieldOrthIsometry` removed the packaging obstruction — a rotation is orthogonal and not symmetric,
which is why every earlier construction here could not have carried one. `FieldComponentEigen`
removed the other — two orthogonal eigenvectors of `green` at one eigenvalue, on any disconnected
graph. Both units said plainly that having the ingredients is not having the thing
(`ERRATUM 194`). **This file makes the thing.**

`PROOF_STRATEGY` §6 question 3: the previous unit was a `B` and this is the retry.

## The matrix, and why it is orthogonal

For `u, v` orthogonal with the **same** squared length `n ≠ 0`, and `c² + s² = 1`,

```
R = 1 + ((c−1)/n)·(uuᵀ + vvᵀ) + (s/n)·(vuᵀ − uvᵀ)
```

fixes everything perpendicular to both, and turns the plane they span: `R u = c·u + s·v` and
`R v = c·v − s·u`. Writing `A = uuᵀ`, `B = vvᵀ`, `C = vuᵀ`, `D = uvᵀ`, every product of two of them
is `n` times a third or zero — `Matrix.vecMulVec_mul_vecMulVec` reads each off the two inner
products — and `RᵀR` collapses to `1 + ((c² + s² − 1)/n)·(A + B)`. **The Pythagorean identity is
exactly what makes the correction vanish**, which is the whole content of the orthogonality proof.

## What is proved

**`rotMatrix`**, **`rotMatrix_mulVec_left`** and **`rotMatrix_mulVec_right`** — the matrix and its
action on the two axes.

**`rotMatrix_transpose_mul_self`** — `Rᵀ R = 1`, so `FieldOrthIsometry.orthIsometry` packages it.

**`rotMatrix_mul_green_comm`** — if `u` and `v` are eigenvectors of `green` at the **same**
eigenvalue then `R` commutes with it: each of `A`, `B`, `C`, `D` does, because `green` moves through
a rank-one matrix on either side and produces the same scalar.

**`gaussianField_map_rotMatrix`** — **so the Gaussian field is invariant under it**, at `m ≠ 0`.
**The mass hypothesis is stated here and in every summary below because it is what makes the
statement say anything**: `FieldMassNecessity` proves `gaussianField G 0` is a point mass at the
origin, which every linear isometry preserves on every graph (`ERRATUM 455`).

**`rotMatrix_ne_one`** — and at `s ≠ 0` it is not the identity, so this is a symmetry and not a
restatement of one.

## What is NOT here

**Not a symmetry outside the reflections on any NAMED graph.** `FieldComponentEigen`'s pair has
squared lengths `|A|` and `|V| − |A|`, which are equal only when the component splits the graph in
half; **the equal-length hypothesis is what this file assumes and it is not automatic.** Removing it
is a rescaling — replace `u, v` by `√⟪v,v⟫ · u` and `√⟪u,u⟫ · v`, which have common squared length
`⟪u,u⟫⟪v,v⟫` and are still eigenvectors — **and that step is not taken here.** It is one
`Real.sq_sqrt` and no new idea, which is said as a description of the step and **not** as a claim
about its difficulty (`ERRATUM 194`); no cost is claimed (`ERRATUM 246`).

> ⚠ **THE HYPOTHESIS IS DISCHARGED THE NEXT UNIT AND THIS PARAGRAPH IS KEPT AS WRITTEN**
> (`ERRATUM 94`, 2026-09-05). `FieldRotationInstance.exists_equal_length_eigenpair` rescales any
> orthogonal eigenpair to a common squared length, and
> `exists_rotation_symmetry_of_not_reachable` puts a genuine rotation on **every disconnected
> graph**. **The paragraph is right about this file** — the hypothesis is carried here — and right
> that the rescaling is the step; what it could not say is whether the step would land.

**Nothing on a connected graph**, for the reason `FieldComponentEigen` gives.

**No description of the commutant.** One rotation is not the set of them.
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 459`):
`FieldCommutantSpectral.mul_green_comm_iff` describes it — a matrix commutes with `green` **iff**
it carries every eigenvector to an eigenvector at the same eigenvalue — and
`FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` makes that a description of
the symmetries of the measure and not of a subset of them. What is still missing is the
`∏ᵢ O(dᵢ)` packaging, not a characterisation.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldRotation

open Matrix GraphLaplacian FieldOrthIsometry FieldCommutant

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The matrix -/

/-- **THE ROTATION BY `(c, s)` IN THE PLANE OF `u` AND `v`**, both of squared length `n`. -/
noncomputable def rotMatrix (u v : V → ℝ) (n c s : ℝ) : Matrix V V ℝ :=
  1 + ((c - 1) / n) • (Matrix.vecMulVec u u + Matrix.vecMulVec v v)
    + (s / n) • (Matrix.vecMulVec v u - Matrix.vecMulVec u v)

omit [Fintype V] [DecidableRel G.Adj] in
theorem rotMatrix_transpose (u v : V → ℝ) (n c s : ℝ) :
    (rotMatrix u v n c s)ᵀ
      = 1 + ((c - 1) / n) • (Matrix.vecMulVec u u + Matrix.vecMulVec v v)
        + (s / n) • (Matrix.vecMulVec u v - Matrix.vecMulVec v u) := by
  simp only [rotMatrix, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_vecMulVec]

/-! ## 2. It is orthogonal -/

omit [DecidableRel G.Adj] in
/-- **`Rᵀ R = 1`.** Every product of two rank-one blocks is `n` times a third or zero, and the
Pythagorean identity is exactly what makes the leftover correction vanish. -/
theorem rotMatrix_transpose_mul_self {u v : V → ℝ} {n c s : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotMatrix u v n c s)ᵀ * rotMatrix u v n c s = 1 := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hAA : Matrix.vecMulVec u u * Matrix.vecMulVec u u = n • Matrix.vecMulVec u u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huu, Matrix.vecMulVec_smul]
  have hAB : Matrix.vecMulVec u u * Matrix.vecMulVec v v = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huv, zero_smul, Matrix.vecMulVec_zero]
  have hAC : Matrix.vecMulVec u u * Matrix.vecMulVec v u = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huv, zero_smul, Matrix.vecMulVec_zero]
  have hAD : Matrix.vecMulVec u u * Matrix.vecMulVec u v = n • Matrix.vecMulVec u v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huu, Matrix.vecMulVec_smul]
  have hBA : Matrix.vecMulVec v v * Matrix.vecMulVec u u = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvu, zero_smul, Matrix.vecMulVec_zero]
  have hBB : Matrix.vecMulVec v v * Matrix.vecMulVec v v = n • Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, Matrix.vecMulVec_smul]
  have hBC : Matrix.vecMulVec v v * Matrix.vecMulVec v u = n • Matrix.vecMulVec v u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, Matrix.vecMulVec_smul]
  have hBD : Matrix.vecMulVec v v * Matrix.vecMulVec u v = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvu, zero_smul, Matrix.vecMulVec_zero]
  have hCA : Matrix.vecMulVec v u * Matrix.vecMulVec u u = n • Matrix.vecMulVec v u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huu, Matrix.vecMulVec_smul]
  have hCB : Matrix.vecMulVec v u * Matrix.vecMulVec v v = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huv, zero_smul, Matrix.vecMulVec_zero]
  have hCC : Matrix.vecMulVec v u * Matrix.vecMulVec v u = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huv, zero_smul, Matrix.vecMulVec_zero]
  have hCD : Matrix.vecMulVec v u * Matrix.vecMulVec u v = n • Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, huu, Matrix.vecMulVec_smul]
  have hDA : Matrix.vecMulVec u v * Matrix.vecMulVec u u = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvu, zero_smul, Matrix.vecMulVec_zero]
  have hDB : Matrix.vecMulVec u v * Matrix.vecMulVec v v = n • Matrix.vecMulVec u v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, Matrix.vecMulVec_smul]
  have hDC : Matrix.vecMulVec u v * Matrix.vecMulVec v u = n • Matrix.vecMulVec u u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, Matrix.vecMulVec_smul]
  have hDD : Matrix.vecMulVec u v * Matrix.vecMulVec u v = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvu, zero_smul, Matrix.vecMulVec_zero]
  have hcollect : (rotMatrix u v n c s)ᵀ * rotMatrix u v n c s
      = 1 + ((c - 1) / n * 2 + (c - 1) / n * ((c - 1) / n * n) + s / n * (s / n * n))
        • (Matrix.vecMulVec u u + Matrix.vecMulVec v v) := by
    simp only [rotMatrix, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.transpose_vecMulVec, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hAA, hAB, hAC, hAD, hBA, hBB, hBC, hBD, hCA, hCB, hCC, hCD, hDA, hDB, hDC,
      hDD]
    module
  have hkey : (c - 1) / n * 2 + (c - 1) / n * ((c - 1) / n * n) + s / n * (s / n * n) = 0 := by
    field_simp
    nlinarith [hcs]
  rw [hcollect, hkey, zero_smul, add_zero]

/-! ## 3. It turns the plane and fixes the rest -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem vecMulVec_mulVec_apply (a b x : V → ℝ) (i : V) :
    (Matrix.vecMulVec a b *ᵥ x) i = a i * (b ⬝ᵥ x) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableRel G.Adj] in
/-- **`R u = c·u + s·v`.** -/
theorem rotMatrix_mulVec_left {u v : V → ℝ} {n c s : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvu : v ⬝ᵥ u = 0) :
    rotMatrix u v n c s *ᵥ u = c • u + s • v := by
  funext i
  simp only [rotMatrix, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    vecMulVec_mulVec_apply, huu, hvu]
  field_simp
  ring

omit [DecidableRel G.Adj] in
/-- **`R v = c·v − s·u`.** -/
theorem rotMatrix_mulVec_right {u v : V → ℝ} {n c s : ℝ} (hn : n ≠ 0)
    (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) :
    rotMatrix u v n c s *ᵥ v = c • v - s • u := by
  funext i
  simp only [rotMatrix, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    vecMulVec_mulVec_apply, hvv, huv]
  field_simp
  ring

omit [DecidableRel G.Adj] in
/-- **AND IT IS NOT THE IDENTITY** when `s ≠ 0`, so this is a symmetry rather than a restatement of
one. -/
theorem rotMatrix_ne_one {u v : V → ℝ} {n c s : ℝ} (hn : n ≠ 0) (hs : s ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (hvu : v ⬝ᵥ u = 0) :
    rotMatrix u v n c s ≠ 1 := by
  intro hcontra
  have hu := rotMatrix_mulVec_left (u := u) (v := v) (c := c) (s := s) hn huu hvu
  rw [hcontra, Matrix.one_mulVec] at hu
  have hdot := congrArg (fun w : V → ℝ => v ⬝ᵥ w) hu
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hvu, hvv] at hdot
  exact hs (by
    rcases mul_eq_zero.mp (by linarith [hdot] : s * n = 0) with h | h
    · exact h
    · exact absurd h hn)

/-! ## 4. It commutes with the propagator at a shared eigenvalue -/

theorem green_mul_vecMulVec_eigen {u w : V → ℝ} {μ : ℝ} (hm : m ≠ 0)
    (hu : green G m *ᵥ u = μ • u) (hw : green G m *ᵥ w = μ • w) :
    green G m * Matrix.vecMulVec u w = Matrix.vecMulVec u w * green G m := by
  rw [Matrix.mul_vecMulVec, hu, Matrix.vecMulVec_mul]
  have : w ᵥ* green G m = μ • w := by
    rw [← Matrix.mulVec_transpose, (green_isSymm G hm)]
    exact hw
  rw [this]
  simp [Matrix.vecMulVec_smul]

/-- **THE ROTATION COMMUTES WITH THE PROPAGATOR** when `u` and `v` are eigenvectors at the same
eigenvalue. -/
theorem rotMatrix_mul_green_comm {u v : V → ℝ} {n c s μ : ℝ} (hm : m ≠ 0)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    rotMatrix u v n c s * green G m = green G m * rotMatrix u v n c s := by
  simp only [rotMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    ← green_mul_vecMulVec_eigen hm hu hu, ← green_mul_vecMulVec_eigen hm hv hv,
    ← green_mul_vecMulVec_eigen hm hv hu, ← green_mul_vecMulVec_eigen hm hu hv]

/-- **AND SO THE GAUSSIAN FIELD IS INVARIANT UNDER IT.** -/
theorem gaussianField_map_rotMatrix {u v : V → ℝ} {n c s μ : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) (hcs : c ^ 2 + s ^ 2 = 1)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    MeasureTheory.Measure.map
        (orthIsometry (rotMatrix_transpose_mul_self hn huu hvv huv hcs)) (gaussianField G m)
      = gaussianField G m :=
  gaussianField_map_orthIsometry hm _ (rotMatrix_mul_green_comm hm hu hv)


end FieldRotation
