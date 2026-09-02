import PerronBound
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Gershgorin, in this estate's idiom — and `PerronBound`'s row-sum bound as a corollary of it

`ERRATUM 412` found that Mathlib has Gershgorin's circle theorem, as `eigenvalue_mem_ball`, and
that four places in this estate said it does not — the eponym appears in **no** declaration name,
because Mathlib names theorems after their statements. That erratum named the follow-up and did not
do it: *"reproving `abs_le_of_rowSum_le` through `eigenvalue_mem_ball` is bounded work"*. **This
file does it, and takes the stronger statement while it is there.**

> **§1. The bridge.** `hasEigenvalue_of_mulVec` — a nonzero `v` with `A *ᵥ v = μ • v` gives
> `Module.End.HasEigenvalue (Matrix.toLin' A) μ`, which is the hypothesis Mathlib's theorem wants.
> **The estate had no such bridge**: every eigenvalue statement in `PerronBound`, `PerronSimple`
> and the transfer-matrix files is phrased with `mulVec` and none of them ever reached Mathlib's
> `Module.End` spectral vocabulary. Probed by grep, not recalled (`ERRATUM 396`).
>
> **§2. Localisation, which is what was actually missing.** `abs_sub_diag_le_rowSum` — some row
> index `k` has `|μ − A k k| ≤ ∑_{j ≠ k} |A k j|`, and `eigenvalue_mem_Icc` puts that in the form a
> gap argument reads: `A k k − R k ≤ μ ≤ A k k + R k`. **`PerronBound`'s bound is the modulus of
> this and throws the centre away.**
>
> **§3. The sharpening.** `le_rowSum_and_ge` — for a non-negative matrix, some row bounds `μ` above
> by its row sum, which is `PerronBound`'s conclusion, **and below by `2 A k k − (row sum k)`**,
> which `PerronBound` cannot say because the modulus threw the diagonal away. The estate's statement
> follows in one line and is **deliberately not restated** (`ERRATUM 176`).

**WHAT THIS IS.** The sharper statement the estate believed absent, in the vocabulary the estate
uses, plus the bridge that was genuinely missing.

**WHAT THIS IS NOT** (`ERRATUM 60`). **`PerronBound.abs_le_of_rowSum_le` is not deleted, not
deprecated and not restated.** It is proved and it is used; §3 is strictly stronger and the estate's
statement is its corollary, so re-declaring it here would be a duplicate (`ERRATUM 176`).
`abs_le_of_colSum_le` still has no Mathlib counterpart at all, re-probed by shape today.

**A first draft of §3 DID restate it**, with a header sentence justifying the duplicate on the
ground that this version needs `DecidableEq` and the estate's does not. **The linter refuted the
justification** — `unusedDecidableInType` reported the hypothesis absent from the type, so the two
statements were identical and one was redundant. `ERRATUM 408` is the entry about a duplicate
carrying a sentence explaining why it is fine; this is the same shape, caught by a linter instead of
by reading.

**And no spectral gap follows from this.** Gershgorin localises eigenvalues in discs; separating a
top eigenvalue needs those discs to be *disjoint*, which is a hypothesis about the matrix that no
estate transfer matrix has been shown to satisfy. `W4`'s `UniformSubTopRatio` is untouched, not
attempted, and not costed (`ERRATUM 194`, `ERRATUM 246`). **No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GershgorinLocal

open scoped Matrix

section Localisation

/-! `Matrix.toLin'` and `Finset.erase` both put `DecidableEq` in the STATEMENTS of §1 and §2,
so it is a section variable here and not in §3, where it appears only in a proof (`ERRATUM 405`). -/

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-! ### §1. From `mulVec` to `Module.End.HasEigenvalue` -/

/-- **The bridge the estate did not have.** Every eigenvalue statement in `PerronBound` and the
transfer-matrix files is phrased with `mulVec`; Mathlib's spectral API wants `Module.End`.

**GENERALISED OFF `ℝ`, 2026-09-02 (`ERRATUM 423`).** It was stated for a real matrix and **nothing
in its two-line proof is about `ℝ`** — `Module.End.mem_eigenspace_iff` and `Matrix.toLin'_apply`
hold over any field. The section's `ℝ` variables carried into a statement that never needed them,
which is `ERRATUM 274`'s shape at the level of a section header rather than a hypothesis. Every
existing use is at `K = ℝ` and is unaffected.

**AND IT HAS NO CONSUMER TODAY, WHICH IS SAID RATHER THAN GLOSSED.** Three files carry complex
`mulVec` eigenvector statements (`TorusMultiplicity`, `SignlessTorusReal`, `ColourEquivariance`,
grepped — `ERRATUM 396`). Two use no spectral API at all. The third uses `Module.End` and
`eigenspace` heavily but **never `HasEigenvalue`**: it computes with
`LinearMap.ker (toLin' A − μ • id)` and the plumbing it hand-rolls is `Matrix.toLin'_apply`, not
this bridge — and the `ker` form it does want is already general, as
`RealComplexKernel.mem_ker_sub_smul`, over any commutative ring. **So this is a hypothesis removed
because it was never used, not because anything is waiting on it**, and no cost or benefit beyond
that is claimed (`ERRATUM 194`, `ERRATUM 246`). -/
theorem hasEigenvalue_of_mulVec {K : Type*} [Field K] {B : Matrix n n K} {lam : K} {w : n → K}
    (hv : B *ᵥ w = lam • w) (hne : w ≠ 0) :
    Module.End.HasEigenvalue (Matrix.toLin' B) lam := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]

/-! ### §2. Localisation -/

/-- **GERSHGORIN, IN THIS ESTATE'S IDIOM.** Some row `k` has `μ` within its off-diagonal absolute
row sum of the diagonal entry `A k k`. -/
theorem abs_sub_diag_le_rowSum (hv : A *ᵥ v = μ • v) (hne : v ≠ 0) :
    ∃ k, |μ - A k k| ≤ ∑ j ∈ Finset.univ.erase k, |A k j| := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (hasEigenvalue_of_mulVec hv hne)
  refine ⟨k, ?_⟩
  simpa [Real.dist_eq, Real.norm_eq_abs] using hk

/-- The same fact as a two-sided bound, which is the form a gap argument reads. -/
theorem eigenvalue_mem_Icc (hv : A *ᵥ v = μ • v) (hne : v ≠ 0) :
    ∃ k, A k k - (∑ j ∈ Finset.univ.erase k, |A k j|) ≤ μ ∧
      μ ≤ A k k + ∑ j ∈ Finset.univ.erase k, |A k j| := by
  obtain ⟨k, hk⟩ := abs_sub_diag_le_rowSum hv hne
  have h := abs_le.mp hk
  exact ⟨k, by linarith [h.1], by linarith [h.2]⟩

end Localisation

/-! ### §3. What `PerronBound` could not say: the lower bound keeps the diagonal -/

section RowSum

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-- **THE SHARPENING, and it is the reason this file is not a restatement.** For a non-negative
matrix, some row `k` bounds `μ` above by its row sum — which is `PerronBound`'s conclusion — **and
below by `2 A k k − (row sum k)`**, which `PerronBound` cannot say because taking the modulus threw
the diagonal entry away. The two coincide only when `A k k = 0`.

`PerronBound.abs_le_of_rowSum_le` follows from this in one line — `μ ≤ S ≤ C` above, and
`μ ≥ 2 A k k − S ≥ −S ≥ −C` below, using `0 ≤ A k k` — **and is deliberately NOT restated here**,
because restating a proved theorem is a duplicate and `ERRATUM 176` is the entry about that. -/
theorem le_rowSum_and_ge (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v) (hne : v ≠ 0) :
    ∃ k, 2 * A k k - (∑ j, A k j) ≤ μ ∧ μ ≤ ∑ j, A k j := by
  classical
  obtain ⟨k, hk⟩ := abs_sub_diag_le_rowSum hv hne
  have habs : ∀ j, |A k j| = A k j := fun j => abs_of_nonneg (hA k j)
  have hsum : ∑ j ∈ Finset.univ.erase k, |A k j| = (∑ j, A k j) - A k k := by
    rw [Finset.sum_congr rfl fun j _ => habs j, Finset.sum_erase_eq_sub (Finset.mem_univ k)]
  rw [hsum] at hk
  have h := abs_le.mp hk
  exact ⟨k, by linarith [h.1], by linarith [h.2]⟩

end RowSum

end GershgorinLocal
