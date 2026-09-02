import PerronBound
import PerronVector
import IsingTransferMatrix

/-!
# A LOWER bound on an eigenvalue from the row sums, and the Perron eigenvalue identified by it

`PerronBound.abs_le_of_rowSum_le` bounds `|μ|` ABOVE by any `C` dominating the row sums, for any
eigenvector at all. **Nothing in this estate bounded an eigenvalue BELOW by the row sums**, and the
two Gershgorin files bound it below by `2·A k k − (row sum k)`, which is a different and generally
weaker number. This file supplies the missing side, under the one extra hypothesis that makes it
true: the eigenvector is **strictly positive**.

> **§1. The bound.** `exists_rowSum_le` — if `A ≥ 0`, `A *ᵥ v = μ • v` and `v > 0` entrywise, then
> some row sum is `≤ μ`. **The proof is the mirror of `abs_le_of_rowSum_le`'s and the mirror is
> where the positivity is spent**: that theorem maximises `|v|` and bounds `∑ A i₀ j |v j|` above by
> `(∑ A i₀ j)|v i₀|`; this one MINIMISES `v` itself and bounds `∑ A k j v j` below by
> `(∑ A k j) v k`, which needs the `v j` to be `≥ v k` as REAL NUMBERS and not as moduli.
> `le_of_rowSum_ge` is the usable form — `c ≤ μ` whenever `c` is under every row sum.
>
> **§2. Sandwich and sign.** `rowSum_sandwich` puts the two sides together, **reusing
> `abs_le_of_rowSum_le` rather than restating it** (`ERRATUM 176`); `inf_rowSum_le_and_le_sup` is
> it at the sharpest constants and is the classical statement — **`μ` lies between the smallest and
> the largest row sum**, with no witness to supply. `pos_of_rowSum_pos` — an eigenvalue with a
> positive eigenvector is positive as soon as the row sums are, with no strict positivity asked of
> `A`. `exists_colSum_le` is the same theorem at `Aᵀ`.
>
> **§3. At the estate's own matrices.** `top_eigenvalue_ge_of_rowSum` — for a Hermitian `A` with
> strictly positive entries, `PerronVector.exists_pos_top_eigenvector` supplies the positive
> eigenvector, so **the top eigenvalue is at least the smallest row sum**. `transfer_rowSum` and
> `transfer_gershgorin_lower` compute both bounds on the one-dimensional Ising transfer matrix —
> `lamPlus β` and `lamMinus β` exactly — so `transfer_pos_eigenvalue` can pin any eigenvalue with a
> strictly positive eigenvector at `2 cosh β`.
>
> **§4. The comparison with Gershgorin, done as a theorem and not asserted.**
> `gershgorin_lower_le_rowSum` — `2·A k k − (row sum k) ≤ ∑ j, A k j` for a nonnegative matrix, at
> every `k`, so **§1's lower bound is at the level of the larger of the two numbers**. It does not
> follow that §1's is larger AT THE SAME `k`: the two theorems produce their own indices and neither
> controls the other's, which is why the statement is about the numbers and not about `μ`.

**WHAT §3's SECOND THEOREM IS.** An identification of the Perron eigenvalue of `transfer β` that
**shares no step with `IsingTransferMatrix.eigenvalue_eq`**: that theorem eliminates between the two
coordinate equations and exhausts the spectrum; this one bounds from both sides and never looks at
`lamMinus`. It is weaker — it speaks only of eigenvalues with a strictly positive eigenvector — and
that is exactly why it is a check: two routes, one number.

**WHAT THIS IS NOT.** **No gap follows, and the example shows why.** For `transfer β` the Gershgorin
lower bound is `lamMinus β` and §1's is `lamPlus β` — `transfer_gershgorin_lower` and
`transfer_rowSum`, computed here and not asserted — so both are tight, on DIFFERENT
eigenvalues. Separating them
needs a lower bound on `λ₊` **with an upper bound on the others**, and the only upper bound here is
`max row sum = 2 cosh β`, which is `λ₊` itself. `W4`'s `UniformSubTopRatio` is untouched, not
attempted and not costed (`ERRATUM 194`, `ERRATUM 246`). **The positivity hypothesis is not
cosmetic**: `![1,-1]` is an eigenvector of `transfer β` for `2 sinh β`, and `2 sinh β < 2 cosh β`,
so §1 is false without it. Nothing earlier is restated, deleted or deprecated, and no published tag
moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PerronRowLower

open Finset Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-! ### §1. The bound -/

/-- **SOME ROW SUM IS AT MOST `μ`**, when the eigenvector is strictly positive. The mirror of
`PerronBound.abs_le_of_rowSum_le`, minimising `v` where that maximises `|v|`. -/
theorem exists_rowSum_le [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) : ∃ k, ∑ j, A k j ≤ μ := by
  obtain ⟨k, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset n) v Finset.univ_nonempty
  refine ⟨k, ?_⟩
  have hrow : μ * v k = ∑ j, A k j * v j := by
    have h := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hge : (∑ j, A k j) * v k ≤ ∑ j, A k j * v j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (hA k j)
  exact le_of_mul_le_mul_right (by rw [hrow]; exact hge) (hvpos k)

/-- **THE LOWER BOUND IN USABLE FORM**: any `c` under every row sum is under `μ`. -/
theorem le_of_rowSum_ge [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) {c : ℝ} (hc : ∀ i, c ≤ ∑ j, A i j) : c ≤ μ := by
  obtain ⟨k, hk⟩ := exists_rowSum_le hA hv hvpos
  exact (hc k).trans hk

/-! ### §2. Sandwich, sign, and the column form -/

/-- **BOTH SIDES AT ONCE.** The upper half is `PerronBound.abs_le_of_rowSum_le`, cited and not
restated (`ERRATUM 176`); only the lower half is new. -/
theorem rowSum_sandwich [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) {c C : ℝ} (hc : ∀ i, c ≤ ∑ j, A i j) (hC : ∀ i, ∑ j, A i j ≤ C) :
    c ≤ μ ∧ μ ≤ C := by
  refine ⟨le_of_rowSum_ge hA hv hvpos hc, ?_⟩
  have hvne : v ≠ 0 := by
    intro h
    exact absurd (hvpos (Classical.arbitrary n)) (by simp [h])
  exact (le_abs_self μ).trans (PerronBound.abs_le_of_rowSum_le hA hv hvne hC)

/-- **THE CLASSICAL FORM: `μ` LIES BETWEEN THE SMALLEST AND THE LARGEST ROW SUM**, with no witness
to supply. `rowSum_sandwich` at its sharpest `c` and `C`. -/
theorem inf_rowSum_le_and_le_sup [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) :
    (Finset.univ.inf' Finset.univ_nonempty fun i => ∑ j, A i j) ≤ μ ∧
      μ ≤ Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, A i j :=
  rowSum_sandwich hA hv hvpos
    (fun i => Finset.inf'_le (fun i => ∑ j, A i j) (Finset.mem_univ i))
    (fun i => Finset.le_sup' (fun i => ∑ j, A i j) (Finset.mem_univ i))

/-- **AN EIGENVALUE WITH A POSITIVE EIGENVECTOR IS POSITIVE** as soon as the row sums are, and `A`
itself is asked only to be nonnegative. -/
theorem pos_of_rowSum_pos [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hrow : ∀ i, 0 < ∑ j, A i j) : 0 < μ := by
  obtain ⟨k, hk⟩ := exists_rowSum_le hA hv hvpos
  exact lt_of_lt_of_le (hrow k) hk

/-- **THE COLUMN FORM**, which is §1 at the transpose and needs a positive eigenvector **of the
transpose** — `GershgorinColumn.exists_eigenvector_transpose` produces one for the same eigenvalue
but says nothing about its sign, so the hypothesis stays. -/
theorem exists_colSum_le [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {w : n → ℝ}
    (hw : Aᵀ *ᵥ w = μ • w) (hwpos : ∀ i, 0 < w i) : ∃ k, ∑ i, A i k ≤ μ :=
  exists_rowSum_le (fun i j => hA j i) hw hwpos

/-! ### §3. At the estate's own matrices -/

/-- **THE TOP EIGENVALUE OF A HERMITIAN POSITIVE MATRIX IS AT LEAST THE SMALLEST ROW SUM.**
`PerronVector.exists_pos_top_eigenvector` supplies the strictly positive eigenvector §1 needs. -/
theorem top_eigenvalue_ge_of_rowSum [Nonempty n] [DecidableEq n] (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 < A i j) {c : ℝ} (hc : ∀ i, c ≤ ∑ j, A i j) :
    ∃ M : ℝ, (∀ j, hA.eigenvalues j ≤ M) ∧ c ≤ M := by
  obtain ⟨M, u, hupos, hmax, -, heig⟩ := PerronVector.exists_pos_top_eigenvector hA hpos
  refine ⟨M, hmax, ?_⟩
  have hmv : A *ᵥ (WithLp.ofLp u) = M • (WithLp.ofLp u) := by
    have h := congrArg WithLp.ofLp heig
    simpa [RayleighMatrix.mv] using h
  exact le_of_rowSum_ge (fun i j => (hpos i j).le) hmv hupos hc

/-- **EVERY ROW OF THE ONE-DIMENSIONAL TRANSFER MATRIX SUMS TO `lamPlus β`**, which is why the two
bounds coincide on it. -/
theorem transfer_rowSum (β : ℝ) (i : Fin 2) :
    ∑ j, IsingTransferMatrix.transfer β i j = IsingTransferMatrix.lamPlus β := by
  fin_cases i <;> simp [IsingTransferMatrix.transfer, IsingTransferMatrix.lamPlus,
    Fin.sum_univ_two]
  ring

/-- **AND ITS GERSHGORIN LOWER BOUND IS `lamMinus β` EXACTLY**, on every row. So on this matrix
both lower bounds are attained and they are attained on DIFFERENT eigenvalues — the header's claim,
computed rather than asserted (`ERRATUM 194`). -/
theorem transfer_gershgorin_lower (β : ℝ) (i : Fin 2) :
    2 * IsingTransferMatrix.transfer β i i - (∑ j, IsingTransferMatrix.transfer β i j)
      = IsingTransferMatrix.lamMinus β := by
  rw [transfer_rowSum]
  fin_cases i <;> simp [IsingTransferMatrix.transfer, IsingTransferMatrix.lamPlus,
    IsingTransferMatrix.lamMinus] <;> ring

/-- **THE ONE-DIMENSIONAL ISING TRANSFER MATRIX: BOTH BOUNDS COINCIDE AND PIN THE EIGENVALUE.**
Any eigenvalue with a strictly positive eigenvector is `2 cosh β`. **The route shares no step with
`IsingTransferMatrix.eigenvalue_eq`**, which eliminates between the coordinate equations; this one
never mentions the other eigenvalue. -/
theorem transfer_pos_eigenvalue (β : ℝ) {μ : ℝ} {v : Fin 2 → ℝ}
    (hv : IsingTransferMatrix.transfer β *ᵥ v = μ • v) (hvpos : ∀ i, 0 < v i) :
    μ = 2 * Real.cosh β := by
  have hrow := transfer_rowSum β
  have hA : ∀ i j, 0 ≤ IsingTransferMatrix.transfer β i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [IsingTransferMatrix.transfer, (Real.exp_pos _).le]
  obtain ⟨hlo, hhi⟩ :=
    rowSum_sandwich hA hv hvpos (fun i => (hrow i).ge) (fun i => (hrow i).le)
  rw [le_antisymm hhi hlo, IsingTransferMatrix.lamPlus_eq_two_cosh]

/-! ### §4. How the two lower bounds compare -/

/-- **THE GERSHGORIN LOWER BOUND IS AT MOST THE ROW SUM**, whenever the diagonal entry is at most
the row sum — so §1's bound sits at the level of the larger number. It does NOT follow that §1's
bound is larger at the same index: each theorem chooses its own `k`, and neither controls the
other's. -/
theorem gershgorin_lower_le_rowSum (hA : ∀ i j, 0 ≤ A i j) (k : n) :
    2 * A k k - (∑ j, A k j) ≤ ∑ j, A k j := by
  have hk : A k k ≤ ∑ j, A k j :=
    Finset.single_le_sum (fun j _ => hA k j) (Finset.mem_univ k)
  linarith

end PerronRowLower
