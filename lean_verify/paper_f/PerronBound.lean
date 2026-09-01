import IsingTransfer2D
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# An eigenvalue bound for nonnegative matrices, and it is not the Perron gap

`WALLS` §W4.0 §6 item 2 names exactly one missing theorem for the mass-gap wall:

> **Separation of its top eigenvalue.** Either Perron–Frobenius (absent from Mathlib; a
> contribution in its own right) or a direct estimate exploiting positivity of the entries.

and §5 inventories the absence rather than guessing at it — `PerronFrobenius` in no file,
`spectralRadius` in thirty statements all about Banach algebras and none mentioning `Matrix`.
**Probed again today and the boundary has not moved**: `gershgorin` and `Gershgorin` occur **0**
times in the pinned environment, and no constant relates an eigenvalue to a row or column sum.

**CORRECTED 2026-09-01 (`ERRATUM 412`), and the first half of that sentence is true while the
second is false.** `gershgorin` really is 0 in the name dump — **because Mathlib names the theorem
after its statement rather than after the person**. It is `eigenvalue_mem_ball`, in
`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`, for any `NormedField`: every eigenvalue lies within
`∑_{j ≠ k} ‖A k j‖` of some diagonal entry `A k k`. **That IS a constant relating an eigenvalue to a
row sum**, and over `ℝ` with non-negative entries one triangle inequality turns it into
`abs_le_of_rowSum_le`'s conclusion. No spelling of the eponym would have found it, which is
`ERRATUM 42`'s rule — probe by SHAPE, not by name — failing in the direction opposite to the one it
was written for.

**WHAT IS AND IS NOT WITHDRAWN.** The theorems below are unaffected: they are proved, they are
stated about `A *ᵥ v = μ • v` for real non-negative matrices, and **`abs_le_of_colSum_le` has no
Mathlib counterpart at all**. What is withdrawn is the claim of NOVELTY for the row-sum half.
Reproving it through `eigenvalue_mem_ball` is bounded work, is not done here, and is not costed
(`ERRATUM 194`, `ERRATUM 246`). The `PerronFrobenius` half of the paragraph above was re-probed the
same day by shape and **stands**: five case-insensitive `perron` matches, three of them the Perron
integral, one a `TODO`, and one a definitions file for irreducible non-negative matrices with no
theorem in it.

## What is proved here

> **`abs_le_of_rowSum_le`** — if `A` has nonnegative entries and `A *ᵥ v = μ • v` for some
> `v ≠ 0`, then `|μ| ≤ C` for **any** `C` bounding every row sum of `A`.
>
> **`abs_le_of_colSum_le`** — the same with columns, by transposing.
>
> **`abs_smul_abs_le_mulVec_abs`** — the entrywise inequality both rest on:
> `|μ| · |vᵢ| ≤ (A *ᵥ |v|)ᵢ`.

The last is the standard first move of every Perron argument, and it is stated separately because
it is what a later attempt at the gap would consume — the gap proof needs the *equality case* of
that inequality, and the inequality itself has to exist before its equality case can be discussed.

## **THIS IS NOT PERRON–FROBENIUS AND IT IS NOT A GAP**

A gap is a **strict** separation of the top eigenvalue from the rest. Everything here is a
**non-strict upper bound on every eigenvalue at once**, and it says nothing whatever about
whether the top one is simple, whether it is attained by a positive vector, or whether the second
is strictly below it. `WALLS` §W4.0 §6 item 2 is **not** closed by this file and the `W4` row does
not move.

**What has changed is smaller and is worth stating exactly.** §6 item 2 offered two routes —
Perron–Frobenius, or *"a direct estimate exploiting positivity of the entries"*. The second route
now has its first rung, and the rung is `Nonneg`-only: **nothing here uses strict positivity, and
nothing here uses symmetry.** That matters for where the difficulty is, because it means the whole
of the difficulty in the second route lies in the step that *does* need strict positivity — the
equality analysis — and none of it in the estimate that motivated the route's name.

## That the bound is sharp, and where it points

**`mulVec_one_of_rowSum_eq`** — when the row sums are all equal to `C`, the all-ones vector is an
eigenvector with eigenvalue `C`. So on a constant-row-sum matrix the bound is **attained and not
merely valid**, which is the only evidence available here that the constant is the right one rather
than a safe one. It also says exactly how much the bound can be worth: **it is sharp precisely
where it is least informative** — a matrix whose row sums are constant has its top eigenvalue
handed to it by the all-ones vector, with no Perron theory needed at all.

**`abs_le_rowSum_transfer2`** applies the bound to the object `WALLS` §W4.0 §6 asks about — the
**two-dimensional** transfer matrix `IsingTransfer2D.transfer2`, not the `2 × 2` chain — using the
strict positivity that file already proves. Its row sums are not constant and have no closed form
here, so this is a bound with an unevaluated constant: real, and not yet a number.
-/

namespace PerronBound

open Finset Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-! ## 1. The entrywise inequality -/

/-- **THE FIRST MOVE OF EVERY PERRON ARGUMENT.** If `A` has nonnegative entries and `v` is an
eigenvector for `μ`, then `|μ| · |v|` is dominated entrywise by `A *ᵥ |v|`. -/
theorem abs_smul_abs_le_mulVec_abs (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v) (i : n) :
    |μ| * |v i| ≤ (A *ᵥ fun j => |v j|) i := by
  have hexp : ∀ w : n → ℝ, (A *ᵥ w) i = ∑ j, A i j * w j := by
    intro w; simp [Matrix.mulVec, dotProduct]
  have hcalc : |μ| * |v i| = |∑ j, A i j * v j| := by
    rw [← abs_mul, ← hexp v, hv]; simp
  rw [hcalc, hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_mul, abs_of_nonneg (hA i j)]

/-! ## 2. The row-sum bound -/

/-- **EVERY REAL EIGENVALUE OF A NONNEGATIVE MATRIX IS BOUNDED BY ITS ROW SUMS.** No symmetry, no
strict positivity, no irreducibility. -/
theorem abs_le_of_rowSum_le [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hv0 : v ≠ 0) {C : ℝ} (hC : ∀ i, ∑ j, A i j ≤ C) : |μ| ≤ C := by
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) (fun i => |v i|) Finset.univ_nonempty
  have hmax' : ∀ i, |v i| ≤ |v i₀| := fun i => hmax i (Finset.mem_univ i)
  have hpos : 0 < |v i₀| := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
    exact lt_of_lt_of_le (abs_pos.mpr hj) (hmax' j)
  have hexp : (A *ᵥ fun j => |v j|) i₀ = ∑ j, A i₀ j * |v j| := by
    simp [Matrix.mulVec, dotProduct]
  have hstep : |μ| * |v i₀| ≤ C * |v i₀| := by
    refine (abs_smul_abs_le_mulVec_abs hA hv i₀).trans ?_
    rw [hexp]
    calc ∑ j, A i₀ j * |v j| ≤ ∑ j, A i₀ j * |v i₀| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax' j) (hA i₀ j)
      _ = (∑ j, A i₀ j) * |v i₀| := by rw [← Finset.sum_mul]
      _ ≤ C * |v i₀| := mul_le_mul_of_nonneg_right (hC i₀) (le_of_lt hpos)
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- **AND BY ITS COLUMN SUMS** — stated through an eigenvector **of the transpose**, which is what
the proof actually consumes. *That this bounds the eigenvalues of `A` itself is a separate step and
is `abs_le_of_colSum_le_det` below; saying it here would be a docstring claiming more than its
theorem.* -/
theorem abs_le_of_colSum_le [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {w : n → ℝ}
    (hw : Aᵀ *ᵥ w = μ • w) (hw0 : w ≠ 0) {C : ℝ} (hC : ∀ j, ∑ i, A i j ≤ C) : |μ| ≤ C :=
  abs_le_of_rowSum_le (fun i j => hA j i) hw hw0 (fun j => hC j)

/-! ## 2b. The same bounds for an eigenvalue given as a root of the characteristic equation

The two theorems above take an eigen**vector**. An eigenvalue is more usually handed over as a root
of `det (A − μ·1) = 0`, and the passage costs one Mathlib lemma each way. **Stating it is not
decoration**: it is what lets the column bound be a statement about the eigenvalues of `A`, which
`abs_le_of_colSum_le`'s own docstring is careful not to claim.
-/

section Det

variable [DecidableEq n]

/-- A root of the characteristic equation has an eigenvector, by
`Matrix.exists_mulVec_eq_zero_iff`. -/
theorem exists_eigenvector_of_det_eq_zero {μ : ℝ}
    (hμ : Matrix.det (A - μ • (1 : Matrix n n ℝ)) = 0) :
    ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  refine ⟨v, hv0, ?_⟩
  have h2 : A *ᵥ v - μ • v = 0 := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hv
  exact sub_eq_zero.mp h2

/-- **THE ROW BOUND FOR AN EIGENVALUE**, with no eigenvector supplied. -/
theorem abs_le_of_rowSum_le_det [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {μ : ℝ}
    (hμ : Matrix.det (A - μ • (1 : Matrix n n ℝ)) = 0) {C : ℝ} (hC : ∀ i, ∑ j, A i j ≤ C) :
    |μ| ≤ C := by
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_det_eq_zero hμ
  exact abs_le_of_rowSum_le hA hv hv0 hC

/-- **AND THE COLUMN BOUND, NOW ABOUT `A`'s OWN EIGENVALUES.** `Matrix.det_transpose` moves the
characteristic equation to `Aᵀ`, whose rows are `A`'s columns. -/
theorem abs_le_of_colSum_le_det [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {μ : ℝ}
    (hμ : Matrix.det (A - μ • (1 : Matrix n n ℝ)) = 0) {C : ℝ} (hC : ∀ j, ∑ i, A i j ≤ C) :
    |μ| ≤ C := by
  have hEq : (Aᵀ - μ • (1 : Matrix n n ℝ)) = (A - μ • (1 : Matrix n n ℝ))ᵀ := by
    simp [Matrix.transpose_sub, Matrix.transpose_smul]
  have hT : Matrix.det (Aᵀ - μ • (1 : Matrix n n ℝ)) = 0 := by
    rw [hEq, Matrix.det_transpose]; exact hμ
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_of_det_eq_zero hT
  exact abs_le_of_rowSum_le (fun i j => hA j i) hw hw0 (fun j => hC j)

end Det

/-! ## 3. Sharpness, and the wall's own matrix -/

/-- **CONSTANT ROW SUMS MAKE THE BOUND SHARP.** The all-ones vector is then an eigenvector with
eigenvalue the common row sum, so `abs_le_of_rowSum_le`'s `C` is attained. -/
theorem mulVec_one_of_rowSum_eq {C : ℝ} (hrow : ∀ i, ∑ j, A i j = C) :
    A *ᵥ (fun _ => (1 : ℝ)) = C • (fun _ => (1 : ℝ)) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [show (A *ᵥ fun _ => (1 : ℝ)) i = ∑ j, A i j * 1 by simp [Matrix.mulVec, dotProduct]]
  simpa using hrow i

omit [Fintype n] in
theorem one_fun_ne_zero [Nonempty n] : (fun _ => (1 : ℝ)) ≠ (0 : n → ℝ) := by
  intro h
  have := congrFun h (Classical.arbitrary n)
  norm_num at this

/-- **THE SHARP FORM.** With equal row sums the bound holds, and `C` is attained by a **nonzero**
eigenvector — which is why `one_fun_ne_zero` is proved above rather than left implicit: without it
the second component would be an eigenvector equation the zero vector also satisfies. -/
theorem abs_le_of_rowSum_eq [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {C : ℝ}
    (hrow : ∀ i, ∑ j, A i j = C) {μ : ℝ} {v : n → ℝ} (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    |μ| ≤ C ∧ ∃ u : n → ℝ, u ≠ 0 ∧ A *ᵥ u = C • u :=
  ⟨abs_le_of_rowSum_le hA hv hv0 (fun i => le_of_eq (hrow i)),
    ⟨fun _ => (1 : ℝ), one_fun_ne_zero, mulVec_one_of_rowSum_eq hrow⟩⟩

open IsingTransfer2D in
/-- **APPLIED TO THE MATRIX `WALLS` §W4.0 §6 IS ABOUT** — the two-dimensional transfer matrix, whose
strict entrywise positivity `IsingTransfer2D.transfer2_pos` already proves. The constant is left as
a hypothesis because `transfer2`'s row sums have no closed form in this estate: this is a real bound
with an unevaluated constant, and calling it anything more would be `ERRATUM 48`'s defect. -/
theorem abs_le_rowSum_transfer2 {β : ℝ} {m : ℕ} {μ : ℝ} {v : Col m → ℝ}
    (hv : transfer2 β m *ᵥ v = μ • v) (hv0 : v ≠ 0) {C : ℝ}
    (hC : ∀ σ, ∑ τ, transfer2 β m σ τ ≤ C) : |μ| ≤ C :=
  abs_le_of_rowSum_le (fun σ τ => le_of_lt (transfer2_pos β σ τ)) hv hv0 hC

end PerronBound
