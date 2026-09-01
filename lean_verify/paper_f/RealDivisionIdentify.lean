import RealDivisionExactlyOne

/-!
# Which of the three: a decision procedure, from two invariants already in this estate

`RealDivisionExactlyOne` sharpened Frobenius to *exactly* one of `ℝ`, `ℂ`, `ℍ` and closed by naming
what it did not do: *"it says nothing about WHICH of the three a given `D` is — that is a
computation for each `D` and is not attempted here."* **This file does that computation once, in
general**, so no `D` ever needs it done by hand.

> **§1. By dimension.** `finrank_eq_one_iff`, `finrank_eq_two_iff`, `finrank_eq_four_iff` — each
> algebra is pinned by `Module.finrank ℝ D` alone. The forward directions are
> `RealDivisionSmallCases` and `RealDivisionQuaternionCase`; the converses are
> `LinearEquiv.finrank_eq` and `Module.finrank_self` / `Complex.finrank_real_complex` /
> `Quaternion.finrank_eq_four`, so **each is one rewrite**.
>
> **§2. By a ring invariant, with no dimension anywhere.** `complex_iff_hasCentralSqrtNegOne` —
> `D` is `ℂ` **exactly when it contains a central `z` with `z * z = -1`**. Forward is
> `RealDivisionExactlyOne.hasCentralSqrtNegOne_complex` transported; backward is the trichotomy
> plus the fact that `ℝ` and `ℍ` have real centre, so neither can host such a `z`. **This is the
> useful half**: it decides the `ℂ` column of an algebra whose dimension is unknown, which is the
> situation `RealDivisionTrichotomy`'s invariants were designed for and the situation a
> classification argument is actually in.
>
> **§3. The remaining pair, and only one side needs the exclusion.** `real_iff_not_and` — once the
> `ℂ` column is excluded, `ℝ` is decided by `finrank ≠ 4`, **without computing the dimension
> exactly**. Its `ℍ` companion was written and deleted: `finrank = 4` already excludes both others,
> so the hypothesis was unused and the statement was `finrank_eq_four_iff` in a hat. **Nothing
> ring-theoretic separates `ℝ` from `ℍ`** — both have real centre, and `RealDivisionTrichotomy`'s
> account says so at length — which is the classical asymmetry and not a gap here.

**WHAT THIS IS.** Frobenius as a decision procedure. Given a finite-dimensional real division
algebra, one number or one ring-theoretic test names it.

**WHAT THIS IS NOT** (`ERRATUM 60`). It computes nothing for any particular algebra: it says which
test to run, not what the test returns for, say, a Clifford algebra. Deciding `HasCentralSqrtNegOne`
or `finrank` for a concrete `D` is that `D`'s problem, is not attempted here, and is not costed
(`ERRATUM 194`, `ERRATUM 246`). **No published tag moves and nothing in the earlier files is
restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionIdentify

open scoped Quaternion
open RealDivisionTrichotomy RealDivisionExactlyOne

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-! ### §1. By dimension -/

/-- `D` is `ℝ` exactly when it is one-dimensional. -/
theorem finrank_eq_one_iff : Nonempty (ℝ ≃ₐ[ℝ] D) ↔ Module.finrank ℝ D = 1 := by
  constructor
  · rintro ⟨f⟩
    rw [← f.toLinearEquiv.finrank_eq]
    exact Module.finrank_self ℝ
  · exact RealDivisionSmallCases.algEquiv_real

/-- `D` is `ℂ` exactly when it is two-dimensional. -/
theorem finrank_eq_two_iff : Nonempty (ℂ ≃ₐ[ℝ] D) ↔ Module.finrank ℝ D = 2 := by
  constructor
  · rintro ⟨f⟩
    rw [← f.toLinearEquiv.finrank_eq]
    exact Complex.finrank_real_complex
  · exact RealDivisionSmallCases.algEquiv_complex

/-- `D` is `ℍ` exactly when it is four-dimensional. -/
theorem finrank_eq_four_iff : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) ↔ Module.finrank ℝ D = 4 := by
  constructor
  · rintro ⟨f⟩
    rw [← f.toLinearEquiv.finrank_eq]
    exact Quaternion.finrank_eq_four
  · exact RealDivisionQuaternionCase.algEquiv_quaternion

/-! ### §2. The `ℂ` column, with no dimension anywhere -/

/-- **THE USEFUL HALF.** `D` is `ℂ` exactly when it contains a central square root of `-1`. No
dimension appears on either side, so this decides the `ℂ` column of an algebra whose dimension is
unknown. -/
theorem complex_iff_hasCentralSqrtNegOne :
    Nonempty (ℂ ≃ₐ[ℝ] D) ↔ HasCentralSqrtNegOne D := by
  constructor
  · rintro ⟨f⟩
    exact HasCentralSqrtNegOne.of_ringEquiv f.toRingEquiv hasCentralSqrtNegOne_complex
  · intro hz
    rcases exactly_one_of_three (D := D) with ⟨⟨f⟩, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, ⟨f⟩⟩
    · exact absurd (HasCentralSqrtNegOne.of_ringEquiv f.symm.toRingEquiv hz)
        (not_hasCentralSqrtNegOne centreIsReal_real)
    · exact h
    · exact absurd (HasCentralSqrtNegOne.of_ringEquiv f.symm.toRingEquiv hz)
        (not_hasCentralSqrtNegOne centreIsReal_quaternion)

/-! ### §3. The pair no ring invariant separates -/

/-- Once the `ℂ` column is excluded, `ℝ` is the one-dimensional case. -/
theorem real_iff_not_and (h : ¬ HasCentralSqrtNegOne D) :
    Nonempty (ℝ ≃ₐ[ℝ] D) ↔ Module.finrank ℝ D ≠ 4 := by
  have hc : ¬ Nonempty (ℂ ≃ₐ[ℝ] D) := fun hn => h (complex_iff_hasCentralSqrtNegOne.mp hn)
  constructor
  · intro hr
    rw [finrank_eq_one_iff.mp hr]; norm_num
  · intro h4
    rcases RealDivisionQuaternionCase.frobenius (D := D) with hr | hcx | hq
    · exact hr
    · exact absurd hcx hc
    · exact absurd (finrank_eq_four_iff.mp hq) h4

/-! **AND THE `ℍ` SIDE NEEDS NO EXCLUSION AT ALL.** A companion
`quaternion_iff_not_and (h : ¬ HasCentralSqrtNegOne D)` was written here and **deleted**: its proof
was `finrank_eq_four_iff` verbatim, so `h` went unused and the `unused variable` linter said so. The
statement was `finrank_eq_four_iff` with a hypothesis added that no step needed — a duplicate
wearing a hypothesis (`ERRATUM 274`, `ERRATUM 278`, and `ERRATUM 176` for the duplicate).
**The asymmetry it was trying to express is real and is the opposite way round**: `ℝ` genuinely
needs the `ℂ` column excluded before `finrank ≠ 4` decides it, and `ℍ` does not, because
`finrank = 4` already excludes both others on its own. -/

end RealDivisionIdentify
