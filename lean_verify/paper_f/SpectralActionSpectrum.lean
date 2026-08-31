/-
  SpectralActionSpectrum.lean — the spectral action's own values, written as power sums of the
  squared singular values, and the remaining gap restated over the numbers it actually concerns.

  WHY THIS FILE EXISTS, AND IT IS A CORRECTION. `UNLOCK_WATCHLIST`'s TRACE-TO-SPECTRUM BRIDGE
  carries a note dated 23 August 2026 saying of `TransferPowerSum`'s Hermitian power-sum theorem:
  *"`SpectralAction`'s theorems … are stated for `M : Matrix (Fin n) (Fin n) ℂ` with no Hermitian
  hypothesis, so the Hermitian case reaches none of them, and leg (i) is exactly as open as it
  was."* **Both halves are false** (`ERRATUM 253`).

  * §§9-10 do not trace `Dlin M`. They trace `(M · Mᴴ)^k` — `trace_Dlin_pow_two_mul` and
    `trace_pow_eq_spectralAction` say so in their statements — and `M · Mᴴ` is Hermitian for every
    `M` whatever. **`ERRATUM 180` had already corrected this exact dismissal on 16 August**, where
    it had been made with a different wrong reason (`Dlin M` is not self-adjoint). The 23 August
    note re-derived it.
  * Leg (i) was proved on **16 August** by `TracePowerSpectrum.trace_pow_eq_sum_roots_charpoly`,
    over any algebraically closed field, with no triangularisation — and the same watchlist block
    records that, in capitals, ninety lines below the note that denies it.

  WHAT IS PROVED HERE, WHICH IS THE FOLD-BACK. One `rw` composing two theorems that have sat in
  this estate unconnected since 16 August: **`spectralAction_monomial_eq_power_sum`** —

      `spectralAction (X^{2k}) 1 M = 4 · ∑ᵢ λᵢ^k`,   `λ` the eigenvalues of `M · Mᴴ`.

  The action's values at the even monomials ARE power sums of the squared singular values. That is
  the forward half of the bridge the watchlist item asks for, at the estate's own matrix.

  AND THE REMAINING GAP IS SHARPER THAN THE ITEM STATES IT. `eigenvalues_nonneg` records that these
  `λᵢ` are non-negative reals — `M · Mᴴ` is positive semidefinite. So legs (ii) and (iii), *"equal
  power sums imply the same multiset"*, are needed **over non-negative reals**, not over an
  algebraically closed field. That is a different and easier problem than the one the item names,
  and saying which problem is left is worth more than another attempt at it.

  WHAT THIS DOES NOT DO, AND THE ITEM DOES NOT CLOSE. It gives the forward direction only. Nothing
  here proves that equal moments force equal singular values, so `SpectralAction` §10's *"THE ONE
  STEP THAT IS NOT PROVED HERE"* paragraph stands exactly as written, `spectralAction_congr_tfae`
  is untouched, and no tag, docstring or claim anywhere in this estate moves. Legs (ii) and (iii)
  are not attempted and their cost is not claimed (`ERRATUM 246`).

  ^ **THREE OF THOSE FOUR CLAUSES HAVE BEEN FALSE SINCE 26 AUGUST 2026, AND THE PARAGRAPH IS KEPT
    AS WRITTEN** (`ERRATUM 94`, `ERRATUM 365`).
    **STILL TRUE**: *"Nothing HERE proves…"* — file-scoped, and this file still gives the forward
    direction only.
    **FALSE**: `SpectralActionDetermines.eigenvalues_multiset_eq_of_spectralAction_eq` proves that
    equal spectral actions at the even monomials force the same multiset of squared singular
    values — equal moments forcing equal singular values, which is the step this paragraph says
    nobody takes. That file also carries a theorem headed *"`spectralAction_congr_tfae` GAINS ITS
    FOURTH CLAUSE"*, so it is not untouched; and `SpectralAction` §10's paragraph was itself
    corrected the same day, so *"no docstring anywhere in this estate moves"* fails too.
    **This file mentions `SpectralActionDetermines` nowhere**, and the accept reading that vouched
    for this paragraph repeated its error rather than catching it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SpectralAction
import TracePowerSpectrum
import Mathlib.Analysis.Matrix.PosDef

namespace SpectralActionSpectrum

open Matrix

-- `Matrix.PosSemidef` is stated over an ordered star-ring, so the complex order must be in scope
-- for `M · Mᴴ` to be callable positive semidefinite at all. §1 uses no order and is unaffected.
open scoped ComplexOrder

variable {n : ℕ}

/-! ## 1. The composition -/

/-- **THE SPECTRAL ACTION AT AN EVEN MONOMIAL IS FOUR TIMES A POWER SUM OF THE SQUARED SINGULAR
VALUES OF `M`.** `SpectralAction.trace_pow_eq_spectralAction` (10 Aug) says the action at `X^{2k}`
and `Λ = 1` is `4 · Tr((M·Mᴴ)^k)`; `Matrix.trace_pow_mul_conjTranspose` (16 Aug) says that trace is
`∑ᵢ λᵢ^k` over the eigenvalues of `M·Mᴴ`. **The two have never been composed**, and the composition
is one rewrite. -/
theorem spectralAction_monomial_eq_power_sum (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M
      = 4 * ∑ i, (((Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i : ℂ)) ^ k := by
  rw [← SpectralAction.trace_pow_eq_spectralAction, Matrix.trace_pow_mul_conjTranspose]

/-! ## 2. Which numbers the remaining gap is about -/

/-- **AND THOSE EIGENVALUES ARE NON-NEGATIVE REALS.** `M · Mᴴ` is positive semidefinite for every
`M`, so the power sums above run over `[0, ∞)`. This is why the watchlist item's legs (ii) and
(iii) are a smaller problem than the item states: they are wanted over non-negative reals, not over
an algebraically closed field. -/
theorem eigenvalues_nonneg (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (0 : ℝ) ≤ (Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i :=
  (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg i

/-- The `k = 1` case, named because it is the one with a physical reading: the action at `X²` and
`Λ = 1` is four times the sum of the squared singular values — the Frobenius norm of the Yukawa
matrix, which is what `SpectralAction.trace_Dlin_sq` computes by a different route. -/
theorem spectralAction_sq_eq_power_sum (M : Matrix (Fin n) (Fin n) ℂ) :
    SpectralAction.spectralAction (Polynomial.X ^ 2) 1 M
      = 4 * ∑ i, (((Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i : ℂ)) := by
  have h := spectralAction_monomial_eq_power_sum M 1
  simpa using h

end SpectralActionSpectrum
