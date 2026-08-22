import IsingTransfer2D
import TracePathSeq

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
  from `spin_sq` rather than asserted;
* **`corr2Sep`** — **the two-point function ALONG the strip**, two spins in the same row `k`
  columns apart, and **`corr2Sep_eq_trace_div`**: the transfer matrix twice with the spin diagonal
  between the factors, which is the shape every transfer-matrix account of correlation decay starts
  from. `corr2` pairs spins across the strip, whose width is fixed; **this one is in the direction
  the limit is taken in**, and it is the observable a mass gap concerns. `corr2Sep_zero` is its
  normalisation check.

## What is still not here, and it is no longer an object

**A decay statement.** `corr2Sep_eq_trace_div` puts the observable in the form the classical
argument uses, and the classical argument then needs **the spectral gap of `transfer2` fed into
it** — `λ₂/λ₁` raised to the separation. `PerronGap` and `PerronSimple` supply a gap for a
**primitive** matrix at a **fixed** side length; the strip's width is fixed here too, and every
limit available is in its length. **So what stands between this file and a mass gap is not a
missing definition and not a missing identity: it is the uniformity in the width**, which is
`WALLS` §W4 §6 item 2's own closing sentence and is open mathematics.

## What is NOT proved, named as a `def` in this estate's convention for a gap

**`SeparatedTransferFormula`** is the statement this file does not reach: the expectation of
`σ_{i}` at column `0` against `σ_{i}` at column `k` is
`tr (D · Tᵏ · D · Tᴹ⁺¹⁻ᵏ) / tr (Tᴹ⁺¹)`. Everything here is the `k = 0` case, where both weights sit
on the same column and collapse into one diagonal. **The separated case needs the cyclic product
split at two points rather than one**, which `cyc_eq_walkProd` does not do, and it is the rung
between this file and any decay statement.

**⚠ SUPERSEDED THE SAME DAY — `separatedTransferFormula_holds` PROVES IT**, and the paragraph is
kept per `ERRATUM 94`. **The diagnosis above was wrong about what was needed.** The cyclic product
does not have to be split at two points: `TracePathSeq` generalises `TracePathSum` to a
**sequence** of matrices, one per step, and a weight at a fixed time is then a diagonal factor
folded into that step's matrix. `TracePathSeq.sum_cyc_two_weight` is the general statement and this
file's `k = 0` argument is unchanged. **What the paragraph got right is that it was a rung and not
a wall.** `PROOF_STRATEGY` §6's KEY GENERATOR rule — a unit that reaches a `B` retries `B → C`
immediately — is what produced it, in the unit after this one.

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
records — and it is the rung between this file and any statement about decay.

**⚠ NO LONGER A GAP — `separatedTransferFormula_holds` below proves it**, the same day, via
`TracePathSeq.sum_cyc_two_weight`. **The `def`'s name and statement are left exactly as they
were**: rewriting a target to match what got proved is the one move this campaign does not make,
and this `def` is now the thing that theorem concludes. The sentence *"needs the cyclic product
split at two points"* was the wrong diagnosis and is kept beside the correction (`ERRATUM 94`) —
what it needed was a sequence of matrices, not a second split. `ERRATUM 228`. -/
def SeparatedTransferFormula (n : ℕ) : Prop :=
  ∀ (β : ℝ) (M k : ℕ) (_ : k ≤ M) (i : Fin (n + 1)),
    (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * spin (s ⟨k, by omega⟩ i)
        * exp (β * energy M s))
      = Matrix.trace (Matrix.diagonal (fun σ : Col n => spin (σ i)) * transfer2 β n ^ k
          * Matrix.diagonal (fun σ : Col n => spin (σ i)) * transfer2 β n ^ (M + 1 - k))

/-! ## 5. The rung climbed, the same day

`TracePathSeq` generalises `TracePathSum` to a **sequence** of matrices, one per step; the
separated formula is then this file's `k = 0` argument with the second weight at a different time,
and needs no new combinatorics. -/

/-- **THE SEPARATED TRANSFER FORMULA, PROVED.** The `def` above named it; this discharges it.
The `k = 0` case is the one §3 already had — both weights on one column — and is closed here by
`spin_sq` through `Matrix.diagonal_mul_diagonal`; every `k ≥ 1` is
`TracePathSeq.sum_cyc_two_weight` at `w = v = spin ∘ (· i)`. -/
theorem separatedTransferFormula_holds (n : ℕ) : SeparatedTransferFormula n := by
  intro β M k hk i
  have hfac : ∀ (N : ℕ) (s : Fin (N + 1) → Col n),
      exp (β * energy N s) = ∏ j : Fin (N + 1), transfer2 β n (s j) (s (j + 1)) := by
    intro N s
    simp only [energy, transfer2, Finset.mul_sum]
    exact Real.exp_sum _ _
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hz : (⟨0, by omega⟩ : Fin (M + 1)) = 0 := rfl
    have hlhs : (∑ s : Fin (M + 1) → Col n,
        spin (s 0 i) * spin (s (⟨0, by omega⟩ : Fin (M + 1)) i) * exp (β * energy M s))
          = partition2 β n M := by
      simp only [partition2, hz]
      exact Finset.sum_congr rfl fun s _ => by rw [spin_sq, one_mul]
    have hd : Matrix.diagonal (fun σ : Col n => spin (σ i))
        * Matrix.diagonal (fun σ : Col n => spin (σ i)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have : (fun σ : Col n => spin (σ i) * spin (σ i)) = fun _ => (1 : ℝ) := by
        funext σ; exact spin_sq (σ i)
      rw [this, Matrix.diagonal_one]
    rw [hlhs, pow_zero, Matrix.mul_one, hd, Matrix.one_mul, Nat.sub_zero,
      partition2_eq_trace]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, M = k' + m + 1 := ⟨M - k' - 1, by omega⟩
    have hsub : k' + m + 1 + 1 - (k' + 1) = m + 1 := by omega
    rw [hsub, Finset.sum_congr rfl fun s _ => by rw [hfac (k' + m + 1) s]]
    exact TracePathSeq.sum_cyc_two_weight (transfer2 β n)
      (fun σ : Col n => spin (σ i)) (fun σ : Col n => spin (σ i)) k' m

/-! ## 6. The observable a decay statement would be about

`corr2` pairs two spins **within a column** — the direction across the strip, whose width is fixed.
The two-point function a mass gap concerns is the other one: two spins in the **same row**, `k`
columns apart, along the direction the limit is taken in. `separatedTransferFormula_holds` supplies
its numerator; this normalises it. -/

/-- **THE TWO-POINT FUNCTION ALONG THE STRIP**: the expectation of the product of the spins at
row `i` of column `0` and row `i` of column `k`. -/
noncomputable def corr2Sep (β : ℝ) (n M : ℕ) (k : Fin (M + 1)) (i : Fin (n + 1)) : ℝ :=
  (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * spin (s k i) * exp (β * energy M s))
    / partition2 β n M

/-- **AND IT IS A RATIO OF TRACES**, with the transfer matrix appearing twice and the spin
diagonal between the factors — the shape every transfer-matrix account of correlation decay
starts from. -/
theorem corr2Sep_eq_trace_div (β : ℝ) (n M : ℕ) (k : Fin (M + 1)) (i : Fin (n + 1)) :
    corr2Sep β n M k i
      = Matrix.trace (Matrix.diagonal (fun σ : Col n => spin (σ i)) * transfer2 β n ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Col n => spin (σ i))
            * transfer2 β n ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2 β n ^ (M + 1)) := by
  have hkM : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.isLt
  have hke : (⟨(k : ℕ), by omega⟩ : Fin (M + 1)) = k := Fin.ext rfl
  rw [corr2Sep, partition2_eq_trace]
  rw [show (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * spin (s k i) * exp (β * energy M s))
      = ∑ s : Fin (M + 1) → Col n,
          spin (s 0 i) * spin (s (⟨(k : ℕ), by omega⟩ : Fin (M + 1)) i) * exp (β * energy M s)
    from by rw [hke]]
  rw [separatedTransferFormula_holds n β M (k : ℕ) hkM i]

/-- **`⟨σ_{0,i} σ_{0,i}⟩ = 1`**, the normalisation check for the separated observable at zero
separation, proved from `spin_sq` rather than asserted. -/
theorem corr2Sep_zero (β : ℝ) (n M : ℕ) (i : Fin (n + 1)) :
    corr2Sep β n M 0 i = 1 := by
  have hz : partition2 β n M ≠ 0 := ne_of_gt (by
    simp only [partition2]
    exact Finset.sum_pos (fun s _ => exp_pos _)
      ⟨(fun _ _ => true : Fin (M + 1) → Col n), Finset.mem_univ _⟩)
  have hnum : (∑ s : Fin (M + 1) → Col n,
      spin (s 0 i) * spin (s 0 i) * exp (β * energy M s)) = partition2 β n M := by
    simp only [partition2]
    exact Finset.sum_congr rfl fun s _ => by rw [spin_sq, one_mul]
  simp only [corr2Sep]
  rw [hnum]
  exact div_self hz

end IsingTwoPoint
