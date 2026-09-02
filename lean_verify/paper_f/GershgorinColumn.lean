import GershgorinLocal

/-!
# The column half: Gershgorin down the columns, and the bound `PerronBound` could not sharpen

`GershgorinLocal` put Mathlib's circle theorem into this estate's idiom and sharpened
`PerronBound.abs_le_of_rowSum_le` — `|μ| ≤ C` for any `C` bounding the row sums — into
`le_rowSum_and_ge`, which keeps the diagonal entry the modulus had thrown away. **`PerronBound`'s
column bound was left exactly where it was**, and this file is that omission repaired.

**The ingredient the estate did not have is not Gershgorin. It is that a transpose has the same
eigenvalues.** `PerronBound.abs_le_of_colSum_le` avoids needing it by taking an eigenvector **of
the transpose** as its hypothesis, and its own docstring is careful to say that this is *not* a
statement about the eigenvalues of `A`; `abs_le_of_colSum_le_det` bridges that gap through the
determinant, one eigenvalue at a time. Stated once, as a fact about eigenvalues, it is reusable.

> **§1. Transpose.** `det_sub_smul_transpose` — `det (Aᵀ − μ·1) = det (A − μ·1)`, since
> `(A − μ·1)ᵀ = Aᵀ − μ·1` and `Matrix.det_transpose`. Hence **`exists_eigenvector_transpose`**: an
> eigenvector of `A` for `μ` yields one of `Aᵀ` for the same `μ`. **No symmetry, no diagonalisation
> and no characteristic polynomial** — `Matrix.exists_mulVec_eq_zero_iff` in both directions and one
> determinant identity between them.
>
> **§2. Localisation by columns.** `abs_sub_diag_le_colSum` — some column `k` has
> `|μ − A k k| ≤ ∑_{i ≠ k} |A i k|`. It is `GershgorinLocal.abs_sub_diag_le_rowSum` at `Aᵀ`, and
> the only content beyond §1 is that the off-diagonal row sum of `Aᵀ` at `k` **is** the off-diagonal
> column sum of `A` at `k`.
>
> **§3. The sharpening.** `le_colSum_and_ge` — for a non-negative matrix, some column bounds `μ`
> above by its column sum, which is `PerronBound.abs_le_of_colSum_le`'s conclusion, **and below by
> `2 A k k − (column sum k)`**, which that theorem cannot say. Exactly `le_rowSum_and_ge`'s
> statement with the transpose in front of it, and **its proof is that sentence**.

**WHAT THIS IS.** The column half of `GershgorinLocal`, and the eigenvalue-level transpose statement
that the estate had been routing around one determinant at a time.

**WHAT THIS IS NOT** (`ERRATUM 60`). **`PerronBound.abs_le_of_colSum_le` is not restated, deleted
or deprecated** — §3 is strictly stronger and that theorem is its corollary, so re-declaring it
would be a duplicate (`ERRATUM 176`). It is **not** a claim that `abs_le_of_colSum_le_det` is
redundant:
that theorem takes the eigenvalue as a root of the characteristic equation and needs no eigenvector
at all, which is a different and often more convenient hypothesis. And **no spectral gap follows**:
`GershgorinLocal`'s header says why, and a second family of discs does not make the first family
disjoint. `W4`'s `UniformSubTopRatio` is untouched, not attempted, not costed (`ERRATUM 194`,
`ERRATUM 246`). **No published tag moves and nothing in the earlier files is restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GershgorinColumn

open scoped Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-! ### §1. A transpose has the same eigenvalues

`DecidableEq` is a section variable only in §2, whose STATEMENT needs `Finset.erase`; `Matrix.det`
needs it too but only inside the proofs below, where `classical` supplies it (`ERRATUM 405`). -/

/-- `det (Aᵀ − μ·1) = det (A − μ·1)`: the subtraction and the scalar pass through the transpose,
and `Matrix.det_transpose` does the rest. -/
theorem det_sub_smul_transpose [DecidableEq n] (A : Matrix n n ℝ) (μ : ℝ) :
    (Aᵀ - μ • (1 : Matrix n n ℝ)).det = (A - μ • (1 : Matrix n n ℝ)).det := by
  have h : Aᵀ - μ • (1 : Matrix n n ℝ) = (A - μ • (1 : Matrix n n ℝ))ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [h, Matrix.det_transpose]

/-- **AN EIGENVECTOR OF `A` GIVES ONE OF `Aᵀ`, FOR THE SAME EIGENVALUE.** The statement
`PerronBound` routes around by hypothesis and `abs_le_of_colSum_le_det` bridges one eigenvalue at a
time. No symmetry and no characteristic polynomial. -/
theorem exists_eigenvector_transpose (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ∃ w : n → ℝ, w ≠ 0 ∧ Aᵀ *ᵥ w = μ • w := by
  classical
  have hzero : (A - μ • (1 : Matrix n n ℝ)) *ᵥ v = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv]
  have hdet : (A - μ • (1 : Matrix n n ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hzero⟩
  have hdetT : (Aᵀ - μ • (1 : Matrix n n ℝ)).det = 0 := by
    rw [det_sub_smul_transpose]; exact hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  refine ⟨w, hw0, ?_⟩
  have h2 : Aᵀ *ᵥ w - μ • w = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hw
    exact hw
  exact sub_eq_zero.mp h2

/-! ### §2. Localisation by columns -/

section Erase

variable [DecidableEq n]

/-- **GERSHGORIN DOWN THE COLUMNS.** Some column `k` has `μ` within its off-diagonal absolute
column sum of the diagonal entry. -/
theorem abs_sub_diag_le_colSum (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ∃ k, |μ - A k k| ≤ ∑ i ∈ Finset.univ.erase k, |A i k| := by
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_transpose hv hv0
  obtain ⟨k, hk⟩ := GershgorinLocal.abs_sub_diag_le_rowSum hw hw0
  exact ⟨k, by simpa using hk⟩

end Erase

/-! ### §3. The sharpening `PerronBound` could not state -/

/-- **THE COLUMN SHARPENING.** For a non-negative matrix, some column bounds `μ` above by its column
sum — `PerronBound.abs_le_of_colSum_le`'s conclusion — **and below by `2 A k k − (column sum k)`**,
which taking the modulus discarded. That theorem is this one's corollary and is **deliberately not
restated** (`ERRATUM 176`). -/
theorem le_colSum_and_ge (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ∃ k, 2 * A k k - (∑ i, A i k) ≤ μ ∧ μ ≤ ∑ i, A i k := by
  classical
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_transpose hv hv0
  obtain ⟨k, hlo, hhi⟩ := GershgorinLocal.le_rowSum_and_ge (fun i j => hA j i) hw hw0
  exact ⟨k, by simpa using hlo, by simpa using hhi⟩

end GershgorinColumn
