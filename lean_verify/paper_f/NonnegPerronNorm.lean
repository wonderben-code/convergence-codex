import AdjNormAverageDegree
import RayleighVariational

/-!
# For a nonnegative symmetric matrix the norm IS the top eigenvalue — Perron's domination, proved

`RayleighVariational.isGreatest_rayleigh` characterises `topEigen`, the **largest** eigenvalue.
`SymmetricOpNorm` and the whole adjacency chain bound `‖A‖`, the largest eigenvalue **in absolute
value**. For a matrix with nonnegative entries these coincide — a nonnegative matrix's Perron root
dominates every other eigenvalue in modulus — and **this estate did not prove it.**
`AdjNormAverageDegree`'s header fenced the gap this morning in as many words:

> *"the two coincide for a nonnegative matrix by Perron–Frobenius and **this estate does not prove
> that** — `OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` needs `0 ≤ A`, which an adjacency
> matrix is not. So every bound in this chain is a floor on the NORM, and reading it as a floor on
> the top eigenvalue borrows a fact from Perron–Frobenius that is not here."*

**The fence is removed by proof rather than by rewording**, which is what a fence naming a borrowed
fact is for.

```
‖A‖ = topEigen        every symmetric A with nonnegative entries
‖G.adjMatrix ℝ‖ = topEigen        every finite nonempty graph
```

## The argument, which needs no eigenvector and no positivity of `A` as an operator

`0 ≤ A` in the Loewner order — what `OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` wants — is a
statement about the **form**, and an adjacency matrix fails it. **§5 proves that rather than
asserting it**: `quadForm_edge_diff_eq_neg_two` evaluates the form at `e_u − e_v` across any edge
and gets exactly `−2`. What holds instead is nonnegativity of the **entries**, a different
hypothesis which happens to be enough.

**`topEigen ≤ ‖A‖` needs nothing at all**: `exists_quadForm_eq_topEigen` produces a vector where the
form attains `topEigen · ‖x‖²`, and one witness is a lower bound on the norm
(`LaplacianNormLowerBound.le_opNorm_of_le_quadForm`). This half is stated for **every** symmetric
matrix, because it is true of every symmetric matrix.

**`‖A‖ ≤ topEigen` is where the entries enter.** `quadForm_le_topEigen` already gives
`A ≼ topEigen • 1`. The other side, `−topEigen • 1 ≼ A`, is the whole content and it is three lines
of termwise comparison: `xᵀAx = ∑ᵢⱼ xᵢ Aᵢⱼ xⱼ ≥ −∑ᵢⱼ |xᵢ| Aᵢⱼ |xⱼ| = −|x|ᵀA|x| ≥ −topEigen·‖x‖²`,
using `Aᵢⱼ ≥ 0` at the first step and `quadForm_le_topEigen` **at `|x|`** at the last, with
`|x|ᵀ|x| = xᵀx`. Then `SymmetricOpNorm.l2_opNorm_le_of_abs_le` closes it.

**So the absolute value is taken on the VECTOR, not on the matrix**, and that is the trick: it turns
a statement about cancellation among signs into an instance of a bound the estate already had.

## What this buys, and it is not decoration

Every floor in the adjacency chain becomes a floor on the **top eigenvalue**, which is the quantity
the physics is about: `√(deg v) ≤ topEigen` (`AdjNormSqrtDegree`), `(∑ deg)/card V ≤ topEigen`
(`AdjNormAverageDegree`), `Δ = topEigen` on a regular graph (`AdjNormRegular`), `√n = topEigen` on
a star (`StarAdjNormExact`). None of those readings was available this morning without borrowing.

## What is NOT here

**Not the Perron–Frobenius theorem.** This is one clause of it — the spectral radius is attained at
the top of the spectrum rather than the bottom. It says **nothing** about simplicity of that
eigenvalue, nothing about positivity of its eigenvector, and nothing about irreducibility;
`PerronSimple` and `PerronVector` are where those live, for **strictly** positive matrices, and
neither applies to an adjacency matrix.

**Not a strict domination.** `‖A‖ = topEigen` does not say the second eigenvalue is strictly below,
which is exactly what `UNLOCK_WATCHLIST`'s Ising sub-top-ratio item needs and what this does not
supply.

**Not `‖A‖ = Δ ⟹ regular`.** The converse Perron statement is where `AdjNormRegular` left it.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense
(`ERRATUM 444`, `ERRATUM 445`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace NonnegPerronNorm

open Matrix Finset SimpleGraph RayleighVariational
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. The half that needs no hypothesis on the entries -/

/-- **`topEigen ≤ ‖A‖` FOR EVERY SYMMETRIC MATRIX.** One witness is a lower bound on the norm, and
`exists_quadForm_eq_topEigen` supplies the witness. -/
theorem topEigen_le_norm {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    topEigen hA ≤ ‖A‖ := by
  obtain ⟨x, hx0, hx⟩ := exists_quadForm_eq_topEigen hA
  have hT : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  exact LaplacianNormLowerBound.le_opNorm_of_le_quadForm hT hx0 (le_of_eq hx.symm)

/-! ## 2. The half where the entries enter -/

omit [DecidableEq V] [Nonempty V] in
/-- The absolute value taken on the vector, which is where the whole argument happens. -/
theorem dotProduct_abs_self (x : V → ℝ) :
    (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x := by
  rw [dotProduct, dotProduct]
  exact Finset.sum_congr rfl fun i _ => abs_mul_abs_self (x i)

omit [DecidableEq V] [Nonempty V] in
/-- **`−(xᵀAx) ≤ |x|ᵀA|x|` WHEN THE ENTRIES ARE NONNEGATIVE.** Termwise: `Aᵢⱼ ≥ 0` makes
`−(xᵢ Aᵢⱼ xⱼ) ≤ |xᵢ| Aᵢⱼ |xⱼ|` whatever the signs of `x`. -/
theorem neg_quadForm_le_quadForm_abs {A : Matrix V V ℝ} (hA : ∀ i j, 0 ≤ A i j) (x : V → ℝ) :
    -(x ⬝ᵥ A *ᵥ x) ≤ (fun i => |x i|) ⬝ᵥ A *ᵥ (fun i => |x i|) := by
  have hexp : ∀ y : V → ℝ, y ⬝ᵥ A *ᵥ y = ∑ i : V, ∑ j : V, y i * (A i j * y j) := by
    intro y
    rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [mulVec, dotProduct, Finset.mul_sum]
  rw [hexp, hexp, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hij := hA i j
  have h1 : -(x i * (A i j * x j)) ≤ |x i * (A i j * x j)| := neg_le_abs _
  have h2 : |x i * (A i j * x j)| = |x i| * (A i j * |x j|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hij]
  linarith [h1, h2.le, h2.ge]

/-- **`‖A‖ ≤ topEigen` WHEN THE ENTRIES ARE NONNEGATIVE.** `quadForm_le_topEigen` gives the upper
Loewner bound outright; the lower one is §2's termwise comparison read at `|x|`. -/
theorem norm_le_topEigen_of_nonneg {A : Matrix V V ℝ} (hsym : A.IsHermitian)
    (hA : ∀ i j, 0 ≤ A i j) : ‖A‖ ≤ topEigen hsym := by
  have hhi : A ≤ topEigen hsym • (1 : Matrix V V ℝ) := by
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      have hs : (A : Matrix V V ℝ).IsSymm := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
      refine Matrix.IsSymm.sub ?_ hs
      rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.isSymm_diagonal _
    · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
      have hconst : x ⬝ᵥ (topEigen hsym • (1 : Matrix V V ℝ)) *ᵥ x
          = topEigen hsym * (x ⬝ᵥ x) := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [hconst]
      exact quadForm_le_topEigen hsym x
  have hlo : -(topEigen hsym • (1 : Matrix V V ℝ)) ≤ A := by
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      refine Matrix.IsSymm.sub
        (by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym) ?_
      refine Matrix.IsSymm.neg ?_
      rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.isSymm_diagonal _
    · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, Matrix.neg_mulVec,
        dotProduct_neg]
      have hconst : x ⬝ᵥ (topEigen hsym • (1 : Matrix V V ℝ)) *ᵥ x
          = topEigen hsym * (x ⬝ᵥ x) := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [hconst]
      have h1 := neg_quadForm_le_quadForm_abs hA x
      have h2 := quadForm_le_topEigen hsym (fun i => |x i|)
      rw [dotProduct_abs_self] at h2
      linarith
  exact SymmetricOpNorm.l2_opNorm_le_of_abs_le hlo hhi

/-! ## 3. Perron's domination -/

/-- **`‖A‖ = topEigen` FOR EVERY SYMMETRIC MATRIX WITH NONNEGATIVE ENTRIES.** The spectral radius
is attained at the TOP of the spectrum, not the bottom — the clause of Perron–Frobenius the
adjacency chain has been borrowing, now proved from the entries rather than from operator
positivity, which an adjacency matrix does not have. -/
theorem norm_eq_topEigen_of_nonneg {A : Matrix V V ℝ} (hsym : A.IsHermitian)
    (hA : ∀ i j, 0 ≤ A i j) : ‖A‖ = topEigen hsym :=
  le_antisymm (norm_le_topEigen_of_nonneg hsym hA) (topEigen_le_norm hsym)

/-! ## 4. The graph corollary, which is what the chain wanted -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem isHermitian_adjMatrix : (G.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact G.isSymm_adjMatrix (α := ℝ)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem adjMatrix_entries_nonneg (i j : V) : 0 ≤ (G.adjMatrix ℝ) i j := by
  rw [SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

/-- **`‖G.adjMatrix ℝ‖ = topEigen`**, so every floor in the adjacency chain is a floor on the TOP
eigenvalue: `√(deg v)` (`AdjNormSqrtDegree`), the average degree (`AdjNormAverageDegree`), `Δ` on a
regular graph (`AdjNormRegular`) and `√n` on a star (`StarAdjNormExact`). None of those readings was
available without borrowing until this file. -/
theorem norm_adjMatrix_eq_topEigen :
    ‖G.adjMatrix ℝ‖ = topEigen (isHermitian_adjMatrix G) :=
  norm_eq_topEigen_of_nonneg _ (adjMatrix_entries_nonneg G)

/-- **The degree-root floor, read on the top eigenvalue.** -/
theorem sqrt_degree_le_topEigen (v : V) :
    Real.sqrt (G.degree v) ≤ topEigen (isHermitian_adjMatrix G) := by
  rw [← norm_adjMatrix_eq_topEigen]
  exact AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix v

/-- **The average-degree floor, read on the top eigenvalue.** -/
theorem avg_degree_le_topEigen :
    (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ)
      ≤ topEigen (isHermitian_adjMatrix G) := by
  rw [← norm_adjMatrix_eq_topEigen]
  exact AdjNormAverageDegree.avg_degree_le_norm_adjMatrix G

/-- **`topEigen = Δ` on a `Δ`-regular graph**, from `AdjNormRegular`. -/
theorem topEigen_eq_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    topEigen (isHermitian_adjMatrix G) = (Δ : ℝ) := by
  rw [← norm_adjMatrix_eq_topEigen]
  exact AdjNormRegular.norm_adjMatrix_eq_of_regular G hreg

/-! ## 5. And the motivating remark is a theorem rather than a remark -/

omit [Nonempty V] in
/-- **A NEGATIVE DIRECTION ACROSS EVERY EDGE, with the value named.** `e_u − e_v` sees only the
four entries at `{u,v}`: the diagonal ones vanish because a simple graph has no loops, and the two
off-diagonal ones are `1` and enter with a minus. -/
theorem quadForm_edge_diff_eq_neg_two {u v : V} (huv : G.Adj u v) :
    (Pi.single u (1 : ℝ) - Pi.single v 1) ⬝ᵥ
        (G.adjMatrix ℝ) *ᵥ (Pi.single u (1 : ℝ) - Pi.single v 1) = -2 := by
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    Matrix.mulVec_single, Matrix.mulVec_single]
  rw [single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  simp only [one_mul, MulOpposite.op_one, one_smul, Matrix.col_apply,
    SimpleGraph.adjMatrix_apply]
  rw [if_neg (G.irrefl (v := u)), if_neg (G.irrefl (v := v)), if_pos huv, if_pos huv.symm]
  ring

omit [Nonempty V] in
/-- **THAT IS EXACTLY THE REFUTATION OF `0 ≤ A` IN THE LOEWNER ORDER** — the hypothesis
`OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` needs and an adjacency matrix does not have,
since `−2 < 0`. **This is why §2 works from the ENTRIES instead**, and it is why the header's
motivating sentence is a theorem here rather than a remark. The value is named rather than merely
its sign, so a consumer needs no second argument. -/
theorem quadForm_edge_diff_neg {u v : V} (huv : G.Adj u v) :
    (Pi.single u (1 : ℝ) - Pi.single v 1) ⬝ᵥ
        (G.adjMatrix ℝ) *ᵥ (Pi.single u (1 : ℝ) - Pi.single v 1) < 0 := by
  rw [quadForm_edge_diff_eq_neg_two G huv]
  norm_num

end NonnegPerronNorm
