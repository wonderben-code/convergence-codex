import SqrtGreenBound
import BoxMassiveSharp

/-!
# The box's inverse-square-root estimate, with the sharp constant

`SqrtGreenBound.inv_sqrt_green_boxGraph_le` gives
`(CFC.sqrt (green (boxGraph d n) m))⁻¹ ≼ √(4d + m²) • 1` — *"the object `LatticeUniformStein`'s
fence names"* — and that `4d` is a **degree count**. `BoxMassiveSharp` produced the **provably
optimal** constant `d·(2 + 2cos(π/n)) + m²` for the same box, and `SqrtGreenBound` was generalised
the same day to accept any lower bound on `green` rather than only a degree one. This file joins
them.

> **`inv_sqrt_green_boxGraph_sharp`** —
> `(CFC.sqrt (green (boxGraph d n) m))⁻¹ ≼ √(d·(2 + 2cos(π/n)) + m²) • 1`.
>
> **`sqrt_sharp_lt`** — and that is **strictly smaller** than `√(4d + m²)` at every `d ≥ 1` and
> every side length, so the estimate genuinely improves rather than merely differs.

## What this is and is not

**The constant inside the square root is optimal; the estimate around it is not claimed to be.**
`BoxMassiveSharp.not_le_of_lt_sharp` shows no smaller `c` satisfies `massive ≼ c·1`, so the number
under the root cannot be lowered by this route. **It does not follow that the `√` bound itself is
attained**, and no such claim is made: three inequalities separate them — the operator monotonicity
of the square root, the inversion, and the passage from `green` to its root — and **none is shown
tight here** (`ERRATUM 194`, `ERRATUM 246`).

**`inv_sqrt_green_boxGraph_le` is untouched.** Its `√(4d + m²)` statement stands verbatim; this
adds a second, better bound beside it rather than editing it, so nothing that consumes the old
constant changes.

**No continuum limit.** `d·(2 + 2cos(π/n)) → 4d`, so the improvement vanishes as the box grows;
that limit is **not stated or proved here**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxSqrtGreenSharp

open Matrix SimpleGraph BoxGraph GraphLaplacian BoxMassiveSharp
open scoped MatrixOrder

variable {d m : ℕ}

/-- The sharp constant is positive, which every use of it needs. -/
theorem sharp_pos (d m : ℕ) {mass : ℝ} (hm : mass ≠ 0) : 0 < sharp d m mass := by
  have hcos : -1 ≤ Real.cos (Real.pi / ((m : ℝ) + 1)) := Real.neg_one_le_cos _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hm2 : (0 : ℝ) < mass ^ 2 := by positivity
  rw [sharp]
  nlinarith

/-- **THE BOX'S INVERSE-SQUARE-ROOT ESTIMATE, WITH THE OPTIMAL CONSTANT UNDER THE ROOT.** -/
theorem inv_sqrt_green_boxGraph_sharp (d m : ℕ) {mass : ℝ} (hm : mass ≠ 0) :
    (CFC.sqrt (green (boxGraph d (m + 1)) mass))⁻¹
      ≤ Real.sqrt (sharp d m mass) • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) :=
  SqrtGreenBound.inv_sqrt_green_le_of_le (boxGraph d (m + 1)) (sharp_pos d m hm) hm
    (smul_one_le_green_sharp d m hm)

/-- **AND IT IS STRICTLY BETTER THAN THE DEGREE-COUNT ESTIMATE.** -/
theorem sqrt_sharp_lt (d m : ℕ) (hd : 0 < d) {mass : ℝ} (hm : mass ≠ 0) :
    Real.sqrt (sharp d m mass) < Real.sqrt (4 * (d : ℝ) + mass ^ 2) := by
  refine Real.sqrt_lt_sqrt (le_of_lt (sharp_pos d m hm)) ?_
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcos := BoxSpectrumComplete.cos_base_lt_one m
  rw [sharp]
  nlinarith

end BoxSqrtGreenSharp
