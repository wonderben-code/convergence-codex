import OpNormTopEigenvalue

/-!
# The massive Laplacian's spectrum lies in `[m², ‖massive G m‖]`, both ends attained

`OpNormTopEigenvalue` (the previous unit) gives the top: `‖massive G m‖` is the greatest
eigenvalue, at every finite nonempty graph. This file gives the bottom, and it is the free
constant:

```
IsLeast  {μ | ∃ x ≠ 0, massive G m *ᵥ x = μ • x}  (m²)
```

**at every finite nonempty graph, with no spectrum computed, no completeness and no eigenvalue
list.** Both inputs are old: `SimpleGraph.posSemidef_lapMatrix` (Mathlib) makes
`m² • 1 ≼ massive G m`, and `GreenExpansion.massive_mulVec_one` (2026-08-12) says the constant
field is an eigenvector there.

## What this changes about a sentence in this estate

`MassiveTorusSpectrum.isLeast_spectrum_real` is the estate's only least-eigenvalue statement for a
Laplacian, on the periodic lattice, and its docstring says:

> *"This is the statement completeness was needed for: exhibiting eigenvectors, however many, never
> bounds a spectrum from below — the bound quantifies over *all* eigenvalues, and that quantifier
> is `massive_eigenvalue_real_iff`'s forward direction."*

**The first clause is true and the necessity it implies is not.** Exhibiting eigenvectors really
does not bound a spectrum from below; but a **Loewner floor** does, and it quantifies over all
eigenvalues without naming any of them. That is `le_of_mulVec_smul_of_smul_one_le` below, three
lines, and it needs no character family, no `nuR`, and no `d`. **Nothing there is edited or
withdrawn** (`ERRATUM 94`, `ERRATUM 337`): `isLeast_spectrum_real` is a theorem about that family
under its own name, `spectrum_real_eq_range_nuR` — an equality of **sets** — genuinely does need
completeness, and the pointer added to that file says exactly this much and no more.

## What is proved

* **`le_of_mulVec_smul_of_smul_one_le`** — a Loewner floor is an eigenvalue floor, for any real
  matrix. The mirror of `GreenNormExact.abs_le_opNorm_of_mulVec_smul`, and like it, no symmetry.
* **`isLeast_eigenvalue_of_smul_one_le`** — with an eigenvector at the floor, the floor is the
  least eigenvalue.
* **`smul_one_le_massive`** — `m² • 1 ≼ massive G m`, off Mathlib's `posSemidef_lapMatrix`.
* **`isLeast_eigenvalue_massive`**, **`isLeast_eigenvalue_lapMatrix`** — the two instances. The
  second is the `m = 0` currency: **the least eigenvalue of the graph Laplacian is `0`**.
* **`massive_eigenvalue_mem_Icc`** — with the previous unit, every eigenvalue of `massive G m`
  lies in `Set.Icc (m ^ 2) ‖massive G m‖`, and **both endpoints are attained**. The unqualified
  name `eigenvalue_mem_Icc` is taken: `GershgorinLocal.eigenvalue_mem_Icc` (2026-09-01) is the
  **row-local** interval `A k k − R k ≤ μ ≤ A k k + R k` at some row `k`, which is a different
  statement about a different pair of endpoints. Flagged by `newnames_scan` before the commit and
  renamed rather than accepted.

## What this is NOT

**No multiplicity and no eigenvector identification.**
`TorusGroundState.eigenvector_at_least_is_const` identifies the whole eigenspace at `m²` on the
periodic lattice; nothing here says the constants are
the only eigenvectors at `m²`, and on a disconnected graph they are not.

**Not a spectrum computation.** The set `{μ | ∃ x ≠ 0, …}` is bounded here, not enumerated;
`MassiveTorusSpectrum.spectrum_real_eq_range_nuR` enumerates it on one family and is untouched.

**The Loewner floor is not the estate's only route to that lower bound, and the second one is
older than this file.** `GershgorinLocal.eigenvalue_mem_Icc` (2026-09-01) puts every eigenvalue
inside some row's disc, and on `massive G m` that row has centre `deg k + m²` and radius `deg k`,
so its left endpoint is `m²`. **That derivation is NOT formalised here and no cost is claimed for
it** (`ERRATUM 246`, `ERRATUM 194`); it is recorded because `ERRATUM 439` is about a sentence
asserting the lower bound needed completeness, and it turns out **two** independent routes in this
estate need none.

**No wall moves**, and no measure or field appears.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MassiveSpectrumRange

open Matrix Finset GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A Loewner floor is an eigenvalue floor -/

/-- **A LOEWNER FLOOR BOUNDS EVERY EIGENVALUE FROM BELOW**, with no symmetry hypothesis — the
mirror of `GreenNormExact.abs_le_opNorm_of_mulVec_smul`, which bounds them from above. -/
theorem le_of_mulVec_smul_of_smul_one_le {A : Matrix V V ℝ} {r μ : ℝ} {x : V → ℝ}
    (hr : r • (1 : Matrix V V ℝ) ≤ A) (hx : x ≠ 0) (h : A *ᵥ x = μ • x) : r ≤ μ := by
  have hps : (A - r • (1 : Matrix V V ℝ)).PosSemidef := Matrix.le_iff.mp hr
  have hnn : 0 ≤ x ⬝ᵥ (A - r • (1 : Matrix V V ℝ)) *ᵥ x := by
    simpa using hps.dotProduct_mulVec_nonneg x
  have hxx : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hsplit : x ⬝ᵥ (A - r • (1 : Matrix V V ℝ)) *ᵥ x = (μ - r) * (x ⬝ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, h, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsplit] at hnn
  nlinarith [hnn, hxx]

/-- **AND WITH AN EIGENVECTOR AT THE FLOOR, THE FLOOR IS THE LEAST EIGENVALUE.** -/
theorem isLeast_eigenvalue_of_smul_one_le {A : Matrix V V ℝ} {r : ℝ} {x : V → ℝ}
    (hr : r • (1 : Matrix V V ℝ) ≤ A) (hx : x ≠ 0) (h : A *ᵥ x = r • x) :
    IsLeast {μ : ℝ | ∃ y : V → ℝ, y ≠ 0 ∧ A *ᵥ y = μ • y} r :=
  ⟨⟨x, hx, h⟩, fun _ ⟨_, hy, hyv⟩ => le_of_mulVec_smul_of_smul_one_le hr hy hyv⟩

/-! ## 2. The graph Laplacian supplies both -/

/-- **`m² • 1 ≼ massive G m`**, because the difference is the Laplacian and Mathlib's
`posSemidef_lapMatrix` says that is positive semidefinite. -/
theorem smul_one_le_massive (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    (m ^ 2) • (1 : Matrix V V ℝ) ≤ massive G m := by
  refine Matrix.le_iff.mpr ?_
  have hsub : massive G m - (m ^ 2) • (1 : Matrix V V ℝ) = G.lapMatrix ℝ := by
    rw [GraphLaplacian.massive, Matrix.smul_one_eq_diagonal]
    abel
  rw [hsub]
  exact SimpleGraph.posSemidef_lapMatrix ℝ G

/-- **THE LEAST EIGENVALUE OF THE MASSIVE LAPLACIAN IS `m²`**, at every finite nonempty graph and
at every mass, with no spectrum computed. `MassiveTorusSpectrum.isLeast_spectrum_real` is this on
the periodic lattice, through the characters and their completeness. -/
theorem isLeast_eigenvalue_massive [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    IsLeast {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ massive G m *ᵥ x = μ • x} (m ^ 2) := by
  refine isLeast_eigenvalue_of_smul_one_le (x := fun _ => (1 : ℝ)) (smul_one_le_massive G m) ?_ ?_
  · intro h0
    obtain ⟨v⟩ := ‹Nonempty V›
    exact absurd (congrFun h0 v) (by norm_num)
  · rw [GreenExpansion.massive_mulVec_one]
    ext p
    simp

/-- **AND AT `m = 0`: THE LEAST EIGENVALUE OF THE GRAPH LAPLACIAN IS `0`.** -/
theorem isLeast_eigenvalue_lapMatrix [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsLeast {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ (G.lapMatrix ℝ) *ᵥ x = μ • x} 0 := by
  have h0 : massive G 0 = G.lapMatrix ℝ := by simp [GraphLaplacian.massive]
  have h := isLeast_eigenvalue_massive G 0
  rwa [h0, show ((0 : ℝ) ^ 2) = 0 from by norm_num] at h

/-! ## 3. The range, with the previous unit -/

/-- **EVERY EIGENVALUE OF `massive G m` LIES IN `[m², ‖massive G m‖]`, AND BOTH ENDS ARE
ATTAINED.** The upper end is `OpNormTopEigenvalue.isGreatest_eigenvalue_massive`. Not to be
confused with `GershgorinLocal.eigenvalue_mem_Icc`, which localises `μ` inside **one row's** disc
and whose endpoints move with the row. -/
theorem massive_eigenvalue_mem_Icc [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}
    (hm : m ≠ 0) {μ : ℝ} (hμ : μ ∈ {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ massive G m *ᵥ x = μ • x}) :
    μ ∈ Set.Icc (m ^ 2) ‖massive G m‖ :=
  ⟨(isLeast_eigenvalue_massive G m).2 hμ,
    (OpNormTopEigenvalue.isGreatest_eigenvalue_massive G hm).2 hμ⟩

end MassiveSpectrumRange
