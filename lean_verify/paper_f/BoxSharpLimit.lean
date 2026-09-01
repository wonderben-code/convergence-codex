import BoxMassiveSharp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The sharp constant tends to the degree bound, so the improvement is a small-volume effect

`BoxMassiveSharp` proved `massive (boxGraph d n) m ≼ (d·(2 + 2cos(π/n)) + m²)·1`, that no smaller
constant works, and that it is strictly below `LaplacianDegreeBound`'s `4d + m²` at every finite
side length. `UNLOCK_WATCHLIST`'s `STATUS (21)` item (c) then records what was **not** stated:
*"No continuum limit. `d·(2 + 2cos(π/n)) → 4d` is arithmetic about the answer and is not stated."*
This states it.

> **`tendsto_sharp`** — `sharp d n m → 4d + m²` as the side length grows.

## Why a limitation is worth proving rather than fencing

The constant `4d + m²` is exactly what a degree count gives, and the previous unit showed the true
value is always strictly smaller. **This says how much smaller: asymptotically, not at all.** The
gap `2d·(1 − cos(π/n))` is `O(d/n²)`, so the sharp constant is a **small-volume** improvement and
the degree bound is asymptotically right. A reader deciding whether to re-derive a downstream
estimate with the new constant needs that sentence to be a theorem, not a caveat — because the
answer it gives is *usually not worth it*, and a caveat can be read as hedging where a theorem
cannot.

## What this is NOT

**No rate is proved.** That the gap is `O(d/n²)` is stated in this prose as motivation and is **not
a theorem here**; only the limit is. As of 1 Sep 2026 no rate is costed (`ERRATUM 194`,
`ERRATUM 246`).

**^ THE RATE IS PROVED, SAME DAY, AND THIS SENTENCE IS KEPT** (`ERRATUM 94`).
`paper_f/BoxSharpRate.lean`: `sharp_gap_eq` gives the gap **exactly** as `2d·(1 − cos(π/(m+1)))`,
and `sharp_gap_le` bounds it by **`d·π²/(m+1)²`** — the `O(d/n²)` above, with the constant named
rather than an asymptotic symbol. The annotation is written **here**, in the file that declined
the rate, and not only in the file that proved it: the estate's standing defect is that
supersession is recorded forward and never backward (`ERRATUM 393`), and this file's own residue
sentence was one day old.
**WHAT IS STILL NOT PROVED, AND IT IS THE OTHER HALF**: no LOWER bound on the gap, so
*"the gap is `Θ(d/n²)`"* remains outside this estate. Not attempted, not costed.

**It is a limit of constants, not of operators.** Nothing here says anything converges in the
Loewner order, and no infinite-volume object appears — `UNLOCK_WATCHLIST`'s infinite-volume items
are untouched, and the estate has no operator on an infinite box.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxSharpLimit

open Filter Topology BoxMassiveSharp

/-- The angle `π/(n+1)` tends to `0`. -/
theorem tendsto_angle : Tendsto (fun m : ℕ => Real.pi / ((m : ℝ) + 1)) atTop (𝓝 0) := by
  refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- Hence its cosine tends to `1`. -/
theorem tendsto_cos_angle :
    Tendsto (fun m : ℕ => Real.cos (Real.pi / ((m : ℝ) + 1))) atTop (𝓝 1) := by
  have h := (Real.continuous_cos.tendsto 0).comp tendsto_angle
  rwa [Real.cos_zero] at h

/-- **THE SHARP CONSTANT TENDS TO THE DEGREE BOUND.** The improvement is a small-volume effect and
vanishes as the box grows. -/
theorem tendsto_sharp (d : ℕ) (mass : ℝ) :
    Tendsto (fun m : ℕ => sharp d m mass) atTop (𝓝 (4 * (d : ℝ) + mass ^ 2)) := by
  have h : Tendsto (fun m : ℕ => (d : ℝ) * (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) + mass ^ 2)
      atTop (𝓝 ((d : ℝ) * (2 + 2 * 1) + mass ^ 2)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_cos_angle)).const_mul
      (d : ℝ)).add tendsto_const_nhds
  have harith : (d : ℝ) * (2 + 2 * 1) + mass ^ 2 = 4 * (d : ℝ) + mass ^ 2 := by ring
  rw [harith] at h
  exact h

end BoxSharpLimit
