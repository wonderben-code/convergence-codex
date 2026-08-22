import IsingTransfer2D

/-!
# The two-point function of the two-dimensional strip, and the observable that did not exist

`WALLS` §W4 §6 item 3 — the identification of a spectral gap with correlation decay — is
discharged for the one-dimensional chain and was recorded as *"untouched"* at `d ≥ 2`. **That was
corrected on 2026-08-22 and the correction named what is actually missing**
(`ERRATUM 228`'s addendum): the trace half is had at `d = 2`
(`IsingTransferSym.partition2_eq_trace_sym`), and the decay half is blocked **not on an estimate
but on a definition** — no two-point function of the strip existed anywhere in this estate, so
there was nothing for a decay rate to be about. This file writes it, and the general theorem the
writing needed.

## What is proved

* **`TracePathSum.cyc_eq_walkProd`** — extracted from inside `sum_cyc_eq_trace`'s proof rather
  than copied out of it, since this file needs the same step (`ERRATUM 173`);
* **`sum_cyc_weighted`** — **the weighted cyclic trace identity**, for an arbitrary matrix over an
  arbitrary commutative ring: weighting each closed walk by a function of its starting point turns
  the trace into `tr (diagonal w · Mᴺ⁺¹)`. `sum_cyc_eq_trace` is the case `w = 1`. **Absent from
  Mathlib by name**, probed 2026-08-22 against the environment dump: `trace_pow_eq_sum`,
  `Matrix.trace_pow`, `prod_cycle`, `diagonal_mul_pow_trace`, `trace_diagonal_mul`,
  `Matrix.trace_diagonal_mul`, `Matrix.trace_mul_diagonal`, `sum_cyc_eq_trace` — **zero each**.
  `Matrix.trace_diagonal` exists and is `tr (diagonal d) = ∑ d i`, a different statement.
  **Absence by shape is inherited rather than re-probed**: this is a weighted refinement of
  `sum_cyc_eq_trace`, whose own absence-by-shape probe is recorded in `WALLS` §W4 §6 item 3, and
  a library that lacks the unweighted identity does not carry the weighted one;
* **`expect`** — the Gibbs expectation of a **column observable** on the periodic strip, and
  **`expect_eq_trace_div`**, which is that expectation as a ratio of traces;
* **`corr2`** — **the two-point function**: the expectation of `σ_i σ_{i'}` within a column, and
  **`corr2_eq_trace_div`**;
* **`corr2_self`** — `⟨σ_i σ_i⟩ = 1`, the sanity check that the normalisation is right, proved
  from `spin_sq` rather than asserted.

## What is NOT proved, named as a `def` in this estate's convention for a gap

**`SeparatedTransferFormula`** is the statement this file does not reach: the expectation of
`σ_{i}` at column `0` against `σ_{i}` at column `k` is
`tr (D · Tᵏ · D · Tᴹ⁺¹⁻ᵏ) / tr (Tᴹ⁺¹)`. Everything here is the `k = 0` case, where both weights sit
on the same column and collapse into one diagonal. **The separated case needs the cyclic product
split at two points rather than one**, which `cyc_eq_walkProd` does not do, and it is the rung
between this file and any decay statement.

**And a decay statement is further still.** Even with the separated formula, *decay* needs the
spectral gap fed into it, the strip is of **fixed width**, and every limit available here is in its
length. `WALLS` §W4's row does not move and the physical `d ≥ 2` mass gap remains open mathematics
with no formalisation route known to this project.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace IsingTwoPoint

open IsingTransfer2D TracePathSum Real

/-! ## 1. The weighted cyclic trace identity -/

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

/-- **THE WEIGHTED CYCLIC TRACE IDENTITY.** Weighting each closed walk by a function of its
starting point replaces `tr (Mᴺ⁺¹)` by `tr (diagonal w · Mᴺ⁺¹)`. `sum_cyc_eq_trace` is `w = 1`. -/
theorem sum_cyc_weighted (M : Matrix α α R) (N : ℕ) (w : α → R) :
    ∑ s : Fin (N + 1) → α, w (s 0) * ∏ i : Fin (N + 1), M (s i) (s (i + 1))
      = Matrix.trace (Matrix.diagonal w * M ^ (N + 1)) := by
  have hlhs : (∑ s : Fin (N + 1) → α, w (s 0) * ∏ i : Fin (N + 1), M (s i) (s (i + 1)))
      = ∑ s : Fin (N + 1) → α, w (s 0) * walkProd M (s 0) N (s 0) (Fin.tail s) :=
    Finset.sum_congr rfl fun s _ => by rw [cyc_eq_walkProd M N s]
  have hrhs : Matrix.trace (Matrix.diagonal w * M ^ (N + 1))
      = ∑ a, ∑ t : Fin N → α, w a * walkProd M a N a t := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [pow_succ_apply M N a a, Finset.mul_sum]
  rw [hlhs, hrhs]
  have hprod : (∑ p : α × (Fin N → α), w p.1 * walkProd M p.1 N p.1 p.2)
      = ∑ a, ∑ t : Fin N → α, w a * walkProd M a N a t := Fintype.sum_prod_type _
  rw [← hprod]
  refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (N + 1) => α).symm
    (fun s => w (s 0) * walkProd M (s 0) N (s 0) (Fin.tail s))
    (fun p => w p.1 * walkProd M p.1 N p.1 p.2) fun s => ?_
  simp [Fin.consEquiv]

/-! ## 2. The Gibbs expectation of a column observable -/

variable {n : ℕ}

/-- **THE GIBBS EXPECTATION OF A COLUMN OBSERVABLE** on the periodic `(n+1) × (M+1)` strip: the
observable is evaluated on column `0`, and the sum runs over all configurations. -/
noncomputable def expect (β : ℝ) (n M : ℕ) (w : Col n → ℝ) : ℝ :=
  (∑ s : Fin (M + 1) → Col n, w (s 0) * exp (β * energy M s)) / partition2 β n M

/-- **THE EXPECTATION IS A RATIO OF TRACES.** `partition2_eq_trace` gives the denominator and
`sum_cyc_weighted` the numerator, through the same factorisation of `exp (β · energy)` over
columns that `partition2_eq_trace` uses. -/
theorem expect_eq_trace_div (β : ℝ) (n M : ℕ) (w : Col n → ℝ) :
    expect β n M w
      = Matrix.trace (Matrix.diagonal w * transfer2 β n ^ (M + 1))
          / Matrix.trace (transfer2 β n ^ (M + 1)) := by
  have hfac : ∀ s : Fin (M + 1) → Col n,
      exp (β * energy M s) = ∏ j : Fin (M + 1), transfer2 β n (s j) (s (j + 1)) := by
    intro s
    simp only [energy, transfer2, Finset.mul_sum]
    exact Real.exp_sum _ _
  rw [expect, partition2_eq_trace,
    Finset.sum_congr rfl fun s _ => by rw [hfac s], sum_cyc_weighted]

/-! ## 3. The two-point function -/

/-- **THE TWO-POINT FUNCTION** of the strip: the expectation of the product of the spins at rows
`i` and `i'` of one column. -/
noncomputable def corr2 (β : ℝ) (n M : ℕ) (i i' : Fin (n + 1)) : ℝ :=
  expect β n M (fun σ => spin (σ i) * spin (σ i'))

theorem corr2_eq_trace_div (β : ℝ) (n M : ℕ) (i i' : Fin (n + 1)) :
    corr2 β n M i i'
      = Matrix.trace (Matrix.diagonal (fun σ : Col n => spin (σ i) * spin (σ i'))
            * transfer2 β n ^ (M + 1))
          / Matrix.trace (transfer2 β n ^ (M + 1)) :=
  expect_eq_trace_div β n M _

/-- **`⟨σ_i σ_i⟩ = 1`**, which is what a correctly normalised two-point function has to give, and
is proved from `spin_sq` rather than asserted. -/
theorem corr2_self (β : ℝ) (n M : ℕ) (i : Fin (n + 1)) : corr2 β n M i i = 1 := by
  have hz : partition2 β n M ≠ 0 := ne_of_gt (by
    simp only [partition2]
    exact Finset.sum_pos (fun s _ => exp_pos _)
      ⟨(fun _ _ => true : Fin (M + 1) → Col n), Finset.mem_univ _⟩)
  have hnum : (∑ s : Fin (M + 1) → Col n,
      spin (s 0 i) * spin (s 0 i) * exp (β * energy M s)) = partition2 β n M := by
    simp only [partition2]
    exact Finset.sum_congr rfl fun s _ => by rw [spin_sq, one_mul]
  simp only [corr2, expect]
  rw [hnum]
  exact div_self hz

/-! ## 4. The rung this file does not climb, named as a `def` -/

/-- **THE SEPARATED TRANSFER FORMULA, NAMED AND NOT PROVED.** The expectation of `σ_i` at column
`0` against `σ_i` at column `k` should be `tr (D · Tᵏ · D · Tᴹ⁺¹⁻ᵏ) / tr (Tᴹ⁺¹)`, where `D` is the
diagonal matrix of `spin (σ i)`. **Everything above is the `k = 0` case**, where the two weights sit
on one column and collapse into a single diagonal; the separated case needs the cyclic product
split at **two** points rather than one, which `TracePathSum.cyc_eq_walkProd` does not do.

**This is stated as a definition of the gap, not as a claim**, in the convention `S3bResidue`
records — and it is the rung between this file and any statement about decay. -/
def SeparatedTransferFormula (n : ℕ) : Prop :=
  ∀ (β : ℝ) (M k : ℕ) (_ : k ≤ M) (i : Fin (n + 1)),
    (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * spin (s ⟨k, by omega⟩ i)
        * exp (β * energy M s))
      = Matrix.trace (Matrix.diagonal (fun σ : Col n => spin (σ i)) * transfer2 β n ^ k
          * Matrix.diagonal (fun σ : Col n => spin (σ i)) * transfer2 β n ^ (M + 1 - k))

end IsingTwoPoint
