import OpNormTopEigenvalue

/-!
# The top eigenvalue is the largest value of the quadratic form — in the matrix currency

Both halves of this have been in the estate for days, in `EuclideanSpace` and `inner`:
`RayleighMatrix.quadForm_le_of_eigenvalues_le` bounds the form by an eigenvalue ceiling, and
`RayleighPow.eigenvalues_le_of_quadForm_le` bounds the eigenvalues by a form ceiling. **What was
missing is the join, in `dotProduct`, packaged as a greatest element.** Measured 2026-09-03 before
this file was written: `IsLUB` and `sSup` occurred **0 times** in `paper_f/`, and of the
`IsGreatest` statements involving a quadratic expression, three are today's — all about a set of
**eigenvalues**, not of form values — and the fourth is
`GreenDomainMonotone.isGreatest_dotProduct_inv_mulVec`, **a different variational principle**:
`x ⬝ᵥ A⁻¹ *ᵥ x` as the maximum of `2⟪x, z⟫ − zᵀAz` over `z`, which is the Legendre form and neither
implies nor is implied by the Rayleigh one. **The Rayleigh quotient's own greatest element was not
stated anywhere.**

```
IsGreatest {r | ∃ x ≠ 0, r · (x ⬝ᵥ x) = x ⬝ᵥ A *ᵥ x}  (⨆ j, eigenvalues j)
```

for any real symmetric `A` on a nonempty finite type — **no positivity**, where
`OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` needed `0 ≼ A` because it identifies the top
with the **norm**, and `‖A‖` is `|λ|`-blind.

## The form a wall wants

**`lt_top_iff_exists_quadForm_gt`** is the same statement as a witness test:

```
r < (⨆ j, eigenvalues j)   ↔   ∃ x ≠ 0,  r · (x ⬝ᵥ x) < x ⬝ᵥ A *ᵥ x
```

**Why that is written down here.** `WALLS.md` §W1.5 names W1's missing ingredient as a lower bound
on the cross form in terms of `c ⬝ᵥ c`, and `ReflectionFailureCriterion
.reflectedForm_neg_of_crossForm_gt` is the consumer: it fires exactly when some `c` has
`Δ²/(m²)³ · (c ⬝ᵥ c) < crossForm G m θ H (c · invDeg)`. Both sides of that are quadratic in `c`, so
the test is scale-invariant, and the biconditional above says such a `c` exists **iff one number
exceeds another**. **THAT APPLICATION IS NOT MADE HERE AND IS NOT COSTED** (`ERRATUM 246`,
`ERRATUM 194`): identifying the twisted cross form as `x ⬝ᵥ N *ᵥ x` for a matrix `N` supported on
`H × H` is a separate step, nothing here does it, and **no wall moves**. What this file provides is
the tool that step would consume, and the reason it is worth having is that a witness is cheaper
than an estimate — `LaplacianDeltaPlusOne` is the day's evidence for that.

## What is NOT here

**No second eigenvalue and no gap.** The greatest element of the Rayleigh set is identified; nothing
below says anything about the next one, and a spectral **gap** — which is what a decay argument
wants — is a statement about two eigenvalues.

**Not the least, and the absence is dated.** The mirror statement holds by the same argument at
`⨅` and is not written here. Probed 2026-09-03, every `IsLeast` about a spectrum in `paper_f/` read
at source: `MassiveSpectrumRange.isLeast_eigenvalue_massive`, `isLeast_eigenvalue_lapMatrix` and
`GreenSpectrumRange.isLeast_eigenvalue_green` are about **named operators**;
`MassiveTorusSpectrum` and `TorusSpectrumExtremes` are about the periodic lattice; and
`MassiveSpectrumRange.isLeast_eigenvalue_of_smul_one_le` is general but **takes the floor and an
eigenvector at it as hypotheses**, which is the opposite of a variational statement — it consumes
what `⨅` would produce. **As of 2026-09-03 none is the `⨅` analogue of §2**, and it is
not written because nothing consumes it rather than because it is hard.

**Nothing is superseded.** `RayleighPow` and `RayleighMatrix` keep their statements and their
consumers; this file **uses** the first through `OpNormTopEigenvalue` and does not restate either.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RayleighVariational

open Matrix Finset
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ}

/-- The greatest eigenvalue, as a plain real number. -/
noncomputable def topEigen [Nonempty V] (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

/-! ## 1. The two inequalities, in `dotProduct` -/

/-- **THE FORM IS BOUNDED BY THE TOP EIGENVALUE**, at every vector. -/
theorem quadForm_le_topEigen [Nonempty V] (hA : A.IsHermitian) (x : V → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ topEigen hA * (x ⬝ᵥ x) := by
  have hle : A ≤ topEigen hA • (1 : Matrix V V ℝ) :=
    OpNormTopEigenvalue.le_smul_one_of_eigenvalues_le hA
      (fun j => Finset.le_sup' _ (Finset.mem_univ j))
  have hps : (topEigen hA • (1 : Matrix V V ℝ) - A).PosSemidef := Matrix.le_iff.mp hle
  have hnn : 0 ≤ x ⬝ᵥ (topEigen hA • (1 : Matrix V V ℝ) - A) *ᵥ x := by
    simpa using hps.dotProduct_mulVec_nonneg x
  have hsplit : x ⬝ᵥ (topEigen hA • (1 : Matrix V V ℝ) - A) *ᵥ x
      = topEigen hA * (x ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  linarith [hsplit ▸ hnn]

/-- **AND IT IS ATTAINED**, at an eigenvector for the maximising index. -/
theorem exists_quadForm_eq_topEigen [Nonempty V] (hA : A.IsHermitian) :
    ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = topEigen hA * (x ⬝ᵥ x) := by
  obtain ⟨x, hx0, hx⟩ := OpNormTopEigenvalue.exists_eigenvector_sup' hA
  refine ⟨x, hx0, ?_⟩
  rw [hx, dotProduct_smul, smul_eq_mul, topEigen]

/-! ## 2. The join -/

/-- **THE TOP EIGENVALUE IS THE GREATEST RAYLEIGH VALUE**, for any real symmetric matrix on a
nonempty finite type — **no positivity**. -/
theorem isGreatest_rayleigh [Nonempty V] (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ r * (x ⬝ᵥ x) = x ⬝ᵥ A *ᵥ x} (topEigen hA) := by
  obtain ⟨x, hx0, hx⟩ := exists_quadForm_eq_topEigen hA
  refine ⟨⟨x, hx0, hx.symm⟩, ?_⟩
  rintro r ⟨y, hy0, hy⟩
  have hyy : 0 < y ⬝ᵥ y := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hy0 (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have h := quadForm_le_topEigen hA y
  rw [← hy] at h
  exact le_of_mul_le_mul_right (by linarith) hyy

/-! ## 3. The witness form, which is what a wall would consume -/

/-- **A NUMBER IS BELOW THE TOP EIGENVALUE EXACTLY WHEN SOME VECTOR BEATS IT.** The estimate
becomes a witness. -/
theorem lt_topEigen_iff_exists_quadForm_gt [Nonempty V] (hA : A.IsHermitian) (r : ℝ) :
    r < topEigen hA ↔ ∃ x : V → ℝ, x ≠ 0 ∧ r * (x ⬝ᵥ x) < x ⬝ᵥ A *ᵥ x := by
  constructor
  · intro hr
    obtain ⟨x, hx0, hx⟩ := exists_quadForm_eq_topEigen hA
    have hxx : 0 < x ⬝ᵥ x := by
      refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx0 (dotProduct_self_eq_zero.1 h0))
      rw [dotProduct]
      exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
    exact ⟨x, hx0, by rw [hx]; exact mul_lt_mul_of_pos_right hr hxx⟩
  · rintro ⟨x, hx0, hx⟩
    have hxx : 0 < x ⬝ᵥ x := by
      refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx0 (dotProduct_self_eq_zero.1 h0))
      rw [dotProduct]
      exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
    have h := quadForm_le_topEigen hA x
    exact lt_of_mul_lt_mul_right (by linarith) (le_of_lt hxx)

end RayleighVariational
