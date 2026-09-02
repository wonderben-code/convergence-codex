import BoxSharpLimit

/-!
# How fast the sharp constant approaches the degree bound: the rate, with its constant

`BoxSharpLimit` proved `sharp d m mass → 4d + mass²` and then said, in its own *"What this is
NOT"*, exactly what it had not done:

> *"**No rate is proved.** That the gap is `O(d/n²)` is stated in this prose as motivation and is
> **not a theorem here**; only the limit is. As of 1 Sep 2026 no rate is costed."*

This proves it, and with an explicit constant rather than an asymptotic symbol.

> **`sharp_gap_eq`** — the gap is exactly `2d·(1 − cos(π/(m+1)))`. An identity, no estimate.
>
> **`one_sub_cos_le_half_sq`** — `1 − cos θ ≤ θ²/2`, for **every** real `θ`, with no bound on `θ`.
>
> **`sharp_gap_le`** — hence `4d + mass² − sharp d m mass ≤ d·π²/(m+1)²`.
>
> **`sharp_ge`** — the same as a lower bound on the constant itself, which is the form a reader
> deciding whether to re-derive a downstream estimate actually wants.

## Why the general lemma is stated separately, and what was probed

`1 − cos θ ≤ θ²/2` is not in Mathlib. Probed under eight spellings before it was written
(`ERRATUM 384` — a single-spelling probe is not a measurement of absence): `one_sub_cos`,
`cos_le_one_sub`, `sub_cos_le`, `cos_ge_one_sub`, `one_sub_sq_div`, `cos_quadratic`, `cos_bound`,
`cos_le_sub`. The four hits on the first are `sin_eq_sqrt_one_sub_cos_sq` and its `abs` twin and two
`unitary` norm identities; `Real.cos_bound` is the **Taylor** bound `|cos x − (1 − x²/2)| ≤
|x|⁴·(5/96)` and carries the hypothesis `|x| ≤ 1`, so it does not give this and does not give it
globally. The proof here needs neither a Taylor expansion nor a range restriction:
`Real.sin_sq_eq_half_sub` at `θ/2` makes `1 − cos θ` equal to `2·sin(θ/2)²`, and
`Real.sin_sq_le_sq` bounds that by `2·(θ/2)²`. Two library lemmas and `ring`.

**⚠ THE FIRST SENTENCE OF THIS SECTION IS FALSE, AND IS KEPT AS WRITTEN** (`ERRATUM 94`, corrected
2026-09-02 by `ERRATUM 418`). **Mathlib has it**, as
**`Real.one_sub_sq_div_two_le_cos : 1 - x ^ 2 / 2 ≤ Real.cos x`** — rearranged, and with **no
hypothesis on `x` at all**, exactly the generality this section is proud of. **The fifth spelling in
the list above finds it.** `one_sub_sq_div` matches two names in this estate's own `env_names.txt`
dump and `Real.one_sub_sq_div_two_le_cos` is the FIRST line of that output. So the eight-spelling
probe this section cites `ERRATUM 384` for was not eight probes read: the paragraph reports the hits
on spelling one in detail and says nothing about spelling five, which is what an unread output looks
like (`ERRATUM 415`, `ERRATUM 157`). **The proof is now one `linarith` over Mathlib's theorem**, and
the estate's own eleven-line derivation through `Real.sin_sq_eq_half_sub` is withdrawn — it was
correct and it was redundant (`ERRATUM 413`'s shape). Nothing downstream changes: `sharp_gap_le` and
`sharp_gap_eq` are untouched and their statements are identical.

## What this is NOT

**It is not an improvement to any constant.** `BoxMassiveSharp.massive_le_smul_one_sharp` is
already optimal — `not_le_of_lt_sharp` says no smaller constant works — so nothing here can sharpen
it and nothing tries. This measures the size of a gap that was already known to be positive and
already known to vanish.

**It says nothing about the operators.** `BoxSharpLimit`'s own fence applies verbatim: this is a
statement about a sequence of real constants, no infinite-volume object appears, and nothing
converges in the Loewner order.

**No lower bound on the gap is proved.** `1 − cos θ ≥ θ²/2 − θ⁴/24` would give one and is not
stated, so *"the gap is `Θ(d/n²)`"* is **not** a theorem here — only the upper half is. Not
attempted, and no cost is claimed (`ERRATUM 194`, `ERRATUM 246`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxSharpRate

open BoxMassiveSharp

/-- **`1 − cos θ ≤ θ²/2`, for every real `θ`.** **THIS IS MATHLIB'S
`Real.one_sub_sq_div_two_le_cos` REARRANGED** — see the dated correction in §"Why the general lemma
is stated separately". The name is kept because `sharp_gap_le` below uses it in this orientation and
because deleting a name changes nothing about the mistake; the eleven-line proof it used to carry
is gone (`ERRATUM 418`). -/
theorem one_sub_cos_le_half_sq (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

/-- **The gap below the degree bound, exactly.** An identity; nothing is estimated here. -/
theorem sharp_gap_eq (d m : ℕ) (mass : ℝ) :
    4 * (d : ℝ) + mass ^ 2 - sharp d m mass
      = 2 * (d : ℝ) * (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) := by
  rw [sharp]; ring

/-- **The rate.** The sharp constant is below `LaplacianDegreeBound`'s `4d + mass²` by at most
`d·π²/(m+1)²` — the `O(d/n²)` that `BoxSharpLimit`'s prose asserted, as a theorem and with the
constant named. -/
theorem sharp_gap_le (d m : ℕ) (mass : ℝ) :
    4 * (d : ℝ) + mass ^ 2 - sharp d m mass
      ≤ (d : ℝ) * Real.pi ^ 2 / ((m : ℝ) + 1) ^ 2 := by
  rw [sharp_gap_eq]
  have h := one_sub_cos_le_half_sq (Real.pi / ((m : ℝ) + 1))
  calc 2 * (d : ℝ) * (1 - Real.cos (Real.pi / ((m : ℝ) + 1)))
      ≤ 2 * (d : ℝ) * ((Real.pi / ((m : ℝ) + 1)) ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (d : ℝ) * Real.pi ^ 2 / ((m : ℝ) + 1) ^ 2 := by
        rw [div_pow]; ring

/-- **The same, as a lower bound on the constant itself.** This is the form a reader deciding
whether to re-derive a downstream estimate with the sharp constant wants: at side length `m + 1`
the sharp constant is within `d·π²/(m+1)²` of the degree bound, so the improvement is worth having
only at small volume. -/
theorem sharp_ge (d m : ℕ) (mass : ℝ) :
    4 * (d : ℝ) + mass ^ 2 - (d : ℝ) * Real.pi ^ 2 / ((m : ℝ) + 1) ^ 2 ≤ sharp d m mass := by
  have h := sharp_gap_le d m mass
  linarith

end BoxSharpRate
