import ReflectionFailureSharper

/-!
# An entry is below the operator norm, and `ERRATUM 427` run backwards over the rest of the chain

`ERRATUM 427` recorded that two units of 2026-09-02 restated `GreenLargeMass.lean` §General. Its own
rule — *before building on a file, read its header* — is a **forward** guard, and `ERRATUM 419` is
this project's record of what a forward-only guard misses. So the rule was run backwards over the
three earlier units of the same chain, and it found one more thing.

**WHAT THE BACKWARD RUN CLEARED.** `GreenLargeMass.lean` contains **no norm bar at all** — zero
occurrences of `‖` in 1424 lines, counted. So `PosSemidefNormBound`, `SymmetricOpNorm`,
`LaplacianOpNorm` and `SqrtGreenOpNorm` are not restatements of it: the operator-norm route is
genuinely absent there, and those four units' theorems stand as new.

**WHAT IT DID NOT CLEAR, AND IT IS A THIRD FRAMING OF THE SAME ERROR.**
`GreenLargeMass.generalRemainder_abs_le` bounds `green · A · Dinv · A · Dinv` — **the same matrix**
`NeumannTailBound` bounds — entrywise, **by the same constant `Δ²/(m²)³`**, at the same generality,
with no regularity. So:

* `NeumannTailBound`'s header presents W1's *"a bound on the Neumann tail of the Green function"* as
  an unmet ask and says *"This file bounds it"*. **The tail was already bounded**, in a different
  currency, by the same number.
* `LaplacianOpNorm`'s header calls that ask *"the live consumer"* and offers `norm_green_le` as
  *"the first factor"* of a bound nobody had. Same overstatement.

Both are kept as written with dated pointers (`ERRATUM 94`), and this file is the fold-back.

> **THE FOLD-BACK, AND IT GOES THE GOOD WAY.** `abs_apply_le_opNorm` : `|M x q| ≤ ‖M‖` for every
> real matrix and every entry — one column of `M` is `M *ᵥ e_q`, a single squared entry is below the
> sum of them, and `RemainderFormBound.dotProduct_mulVec_sq_le` bounds that sum by `‖M‖²`.
> **So an operator-norm bound implies the entrywise one with the same constant**, and
> `generalRemainder_abs_le_of_opNorm` derives `GreenLargeMass`'s entrywise bound from
> `NeumannTailBound`'s — not the reverse.

**AND THE SAME QUALIFICATION AS `ERRATUM 427`'s FOLD-BACK, FOR THE SAME REASON.** The operator-norm
route carries `[Nonempty V]`, which `generalRemainder_abs_le` does not: it comes from
`PosSemidefNormBound.l2_opNorm_le`, false on an empty vertex type (`ERRATUM 426`). **Neither
statement dominates the other outright**; on a graph with a vertex the operator-norm bound is the
stronger, and `GreenLargeMass`'s is the one to cite on an arbitrary finite type.

**W1 DOES NOT MOVE**, and this file adds nothing toward it: it is a relation between two bounds that
were both already proved, plus a correction to how two headers described the gap.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace EntrywiseFromOpNorm

open Matrix GraphLaplacian GreenExpansion
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. An entry is below the operator norm -/

/-- **`|M x q| ≤ ‖M‖`, FOR EVERY REAL MATRIX AND EVERY ENTRY.** Column `q` of `M` is `M *ᵥ e_q`; one
squared entry is below the sum of the squared entries, which
`RemainderFormBound.dotProduct_mulVec_sq_le` bounds by `‖M‖²` since `e_q ⬝ᵥ e_q = 1`. -/
theorem abs_apply_le_opNorm (M : Matrix V V ℝ) (x q : V) : |M x q| ≤ ‖M‖ := by
  classical
  set e : V → ℝ := Pi.single q 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hcol : M *ᵥ e = M.col q := by rw [he, Matrix.mulVec_single_one]
  have hsum := RemainderFormBound.dotProduct_mulVec_sq_le M e
  rw [hcol, hee, mul_one] at hsum
  have hexp : M.col q ⬝ᵥ M.col q = ∑ y, (M y q) ^ 2 := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun y _ => by rw [Matrix.col_apply]; ring
  rw [hexp] at hsum
  have hone : (M x q) ^ 2 ≤ ∑ y, (M y q) ^ 2 :=
    Finset.single_le_sum (fun y _ => sq_nonneg (M y q)) (Finset.mem_univ x)
  have hsq : (M x q) ^ 2 ≤ ‖M‖ ^ 2 := by linarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (norm_nonneg M))

/-! ## 2. `GreenLargeMass`'s entrywise tail bound, derived from the operator-norm one -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`GreenLargeMass.generalRemainder_abs_le`, FROM `NeumannTailBound.norm_neumann_tail_le`.** Same
matrix, same constant; the operator-norm bound is the stronger of the two on a nonempty vertex type,
and that hypothesis is the price (`ERRATUM 426`). -/
theorem generalRemainder_abs_le_of_opNorm [Nonempty V] {Δ : ℝ}
    (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ} (hm : m ≠ 0) (x q : V) :
    |(green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) x q|
      ≤ Δ ^ 2 / (m ^ 2) ^ 3 :=
  le_trans (abs_apply_le_opNorm _ x q) (NeumannTailBound.norm_neumann_tail_le G hΔ hm)

end EntrywiseFromOpNorm
