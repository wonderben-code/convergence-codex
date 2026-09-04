import NonnegPerronNorm
import FrobeniusTopBound

/-!
# The adjacency spectrum bracketed, and a claim `NonnegPerronNorm` should not have made

`NonnegPerronNorm` (earlier today) proves `‖A‖ = topEigen` for a symmetric matrix with nonnegative
entries, and its header says the estate **did not prove** that a nonnegative matrix's Perron root
dominates every other eigenvalue in modulus. **That sentence is false and `ERRATUM 446` records
it.** `FrobeniusTopBound.abs_le_top_of_all` proves exactly that fact, and says so in a docstring
reading *"EVERY EIGENVALUE IS DOMINATED IN MODULUS BY THE TOP ONE, for a Hermitian matrix with
non-negative entries"*; `PerronGap.abs_le_top_of_eigenvector` is what it rests on, and **that proof
takes the absolute value of the eigenvector** — `PerronVector.absVec`, with
`PerronVector.normSq_absVec` for `⟪|v|,|v|⟫ = ⟪v,v⟫` — which is the idea `NonnegPerronNorm` and its
log entry presented as the new one.

**What was actually new this morning stands**: the identification with the OPERATOR NORM, in
`dotProduct` form, and the transfer of the adjacency floors onto the eigenvalue. The estate had the
eigenvalue statement and did not have `‖A‖ = topEigen`.

## What this file adds, which is the join neither side had

`FrobeniusTopBound.abs_le_top_of_all` is stated at a **designated maximising index** `p₀` supplied
as a hypothesis, and `RayleighVariational.topEigen` is a `Finset.sup'`. Nothing connected them.

**`abs_eigenvalues_le_topEigen`** states Perron's domination in the `topEigen` vocabulary the
operator-norm chain is written in: `|hA.eigenvalues j| ≤ topEigen hA`, for every Hermitian matrix
with nonnegative entries. `Finset.exists_mem_eq_sup'` supplies the index the older theorem asks for.

**And then the bracket closes on graphs.** With `NonnegPerronNorm.norm_adjMatrix_eq_topEigen` and
`SymmetricOpNorm.norm_adjMatrix_le`:

```
−Δ  ≤  eigenvalue j  ≤  Δ            every eigenvalue, every finite graph
√(deg v)  ≤  topEigen                every vertex
```

so **the whole adjacency spectrum sits in `[−Δ, Δ]` and its top is at least `√Δ`** — the day's
floors and ceilings assembled into one statement about the spectrum rather than about a norm.

## What is NOT here

**Still not Perron–Frobenius.** No simplicity, no positive eigenvector, no irreducibility. The
strict statements need **strictly** positive matrices (`PerronSimple`, `PerronVector`), which an
adjacency matrix is not, and the sub-top ratio the Ising item wants is untouched.

**Not a bipartite characterisation.** `−Δ ≤ λ` is proved; that equality at the bottom happens
exactly for bipartite graphs is classical and is **not attempted and not costed** (`ERRATUM 246`).

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense
(`ERRATUM 444`, `ERRATUM 445`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjSpectrumBracket

open Matrix Finset SimpleGraph RayleighVariational
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. Perron's domination, in the `topEigen` vocabulary -/

/-- **`|λ_j| ≤ topEigen` FOR EVERY HERMITIAN MATRIX WITH NONNEGATIVE ENTRIES.**
`FrobeniusTopBound.abs_le_top_of_all` is the same fact at a designated maximising index;
`Finset.exists_mem_eq_sup'` supplies that index from the `sup'` the operator-norm chain uses, which
is the join the two sides were missing. -/
theorem abs_eigenvalues_le_topEigen {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 ≤ A i j) (j : V) : |hA.eigenvalues j| ≤ topEigen hA := by
  obtain ⟨p₀, -, hp₀⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := V)) hA.eigenvalues
  have htop : ∀ k, hA.eigenvalues k ≤ hA.eigenvalues p₀ := by
    intro k
    rw [← hp₀]
    exact Finset.le_sup' _ (Finset.mem_univ k)
  have h := FrobeniusTopBound.abs_le_top_of_all hA hpos htop j
  rwa [← hp₀] at h

/-! ## 2. The graph bracket -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **EVERY ADJACENCY EIGENVALUE IS AT MOST `Δ` IN MODULUS**, hence the spectrum lies in `[−Δ, Δ]`.
Perron's domination puts every eigenvalue below the top; `NonnegPerronNorm` makes the top the norm;
`SymmetricOpNorm.norm_adjMatrix_le` puts the norm below `Δ`. -/
theorem abs_eigenvalues_adjMatrix_le {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (j : V) :
    |(NonnegPerronNorm.isHermitian_adjMatrix G).eigenvalues j| ≤ Δ := by
  refine le_trans (abs_eigenvalues_le_topEigen _ (NonnegPerronNorm.adjMatrix_entries_nonneg G) j) ?_
  rw [← NonnegPerronNorm.norm_adjMatrix_eq_topEigen]
  exact SymmetricOpNorm.norm_adjMatrix_le G hΔ

/-- **THE SPECTRUM IS BRACKETED FROM BOTH SIDES AT ONCE.** -/
theorem eigenvalues_adjMatrix_mem_Icc {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (j : V) :
    (NonnegPerronNorm.isHermitian_adjMatrix G).eigenvalues j ∈ Set.Icc (-Δ) Δ := by
  have h := abs_eigenvalues_adjMatrix_le G hΔ j
  exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩

/-- **AND THE TOP IS NOT SMALL**: `√(deg v) ≤ topEigen` at every vertex, so with §2 the whole
spectrum of a graph with maximum degree `Δ` lies in `[−Δ, Δ]` and reaches at least `√Δ`. -/
theorem sqrt_degree_le_topEigen_adjMatrix (v : V) :
    Real.sqrt (G.degree v) ≤ topEigen (NonnegPerronNorm.isHermitian_adjMatrix G) :=
  NonnegPerronNorm.sqrt_degree_le_topEigen G v

end AdjSpectrumBracket
