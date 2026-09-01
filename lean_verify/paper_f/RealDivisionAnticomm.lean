import RealDivisionPureSpace

/-!
# A fourth anticommuting direction is zero

`RealDivisionPureSpace` named leg (c)'s three steps and said which one decides the theorem: that
the pure part cannot have dimension four or more. **This file is that step's algebraic heart**, and
it needs no linear algebra at all.

> **`commute_mul_of_anticomm`** — if `l` anticommutes with `i` and with `j` then it **commutes**
> with `i * j`. Two sign flips make a sign.
>
> **`eq_zero_of_anticomm_three`** — so if `l` also **anti**commutes with `i * j`, then `l = 0`:
> commuting and anticommuting together give `2·(ij)l = 0`, and `2` is invertible because `D` is an
> `ℝ`-algebra.
>
> **`anticomm_mul_left`**, **`anticomm_mul_right`** — and `i * j` really is a fourth direction of
> the same kind: it anticommutes with `i` and with `j` whenever they anticommute with each other.

Together: **`i`, `j`, `i * j` are pairwise anticommuting, and nothing anticommutes with all three
except `0`.** That is why the answer is three and not four.

## What this is not

**It is not `dim V ≤ 3`.** That statement needs the dictionary between *orthogonal* and
*anticommuting* for the form of `RealDivisionPureForm`, and then a basis argument: a fourth basis
vector orthogonal to `i`, `j`, `ij` would anticommute with all three and so be `0`, contradicting
independence. **Neither the dictionary nor the basis argument is here**, and no cost is claimed for
either (`ERRATUM 194`, `ERRATUM 246`).

**A duplicate was written and deleted before this file ever built.** The draft carried
`eq_zero_of_anticomm_triple`, whose statement and hypotheses are `eq_zero_of_anticomm_three`'s
exactly and whose proof was a call to it — the "same proof twice" defect `ERRATUM 373` records, in
its cheapest form, caught by reading my own file rather than by a checker.

**Nothing here mentions purity**, and that is deliberate rather than an oversight: every statement
is about anticommutation in a division ring, which is the generality the argument actually has.
`i * j ≠ 0` is a hypothesis rather than a conclusion, because it is `mul_ne_zero` and belongs to
the caller.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionAnticomm

/-! ## The ring identities

**Three of the four theorems below need only a ring**, and they are in a section that says so.
`ERRATUM 405`, written one unit ago, records that four consecutive files of this chain carried a
section hypothesis their theorems did not need, and prescribes exactly this split. **I did not
apply it when writing this file** and the linter caught a fifth instance; see that erratum's
addendum. The split is here now. -/
section RingOnly

variable {D : Type*} [Ring D]

/-- **Two sign flips make a sign.** Anticommuting with `i` and with `j` means commuting with the
product. -/
theorem commute_mul_of_anticomm {i j l : D} (hi : l * i + i * l = 0) (hj : l * j + j * l = 0) :
    l * (i * j) = (i * j) * l := by
  have h1 : l * i = -(i * l) := by linear_combination (norm := noncomm_ring) hi
  have h2 : l * j = -(j * l) := by linear_combination (norm := noncomm_ring) hj
  calc l * (i * j) = (l * i) * j := by noncomm_ring
    _ = (-(i * l)) * j := by rw [h1]
    _ = -(i * (l * j)) := by noncomm_ring
    _ = -(i * -(j * l)) := by rw [h2]
    _ = (i * j) * l := by noncomm_ring

end RingOnly

/-! ## The obstruction, which is the one statement needing an `ℝ`-algebra -/
section DivisionAlgebra

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-- **The obstruction.** Commuting and anticommuting with the same nonzero element forces `l = 0`.
`2` is invertible because `D` is an `ℝ`-algebra, which is the only place that hypothesis is used in
this file. -/
theorem eq_zero_of_anticomm_three {i j l : D} (hij : i * j ≠ 0)
    (hi : l * i + i * l = 0) (hj : l * j + j * l = 0)
    (hk : l * (i * j) + (i * j) * l = 0) : l = 0 := by
  have hc : l * (i * j) = (i * j) * l := commute_mul_of_anticomm hi hj
  have hdouble : (i * j) * l + (i * j) * l = 0 := by rw [hc] at hk; exact hk
  have hsmul : (2 : ℝ) • ((i * j) * l) = 0 := by rw [two_smul]; exact hdouble
  have hzero : (i * j) * l = 0 := by
    have := congrArg (fun x : D => (2⁻¹ : ℝ) • x) hsmul
    simpa [smul_smul] using this
  exact (mul_eq_zero.mp hzero).resolve_left hij

end DivisionAlgebra

section RingOnlyTwo

variable {D : Type*} [Ring D]

/-- `i * j` anticommutes with `i`. -/
theorem anticomm_mul_left {i j : D} (h : i * j + j * i = 0) :
    (i * j) * i + i * (i * j) = 0 := by
  have hji : j * i = -(i * j) := by linear_combination (norm := noncomm_ring) h
  calc (i * j) * i + i * (i * j) = i * (j * i) + i * (i * j) := by noncomm_ring
    _ = i * -(i * j) + i * (i * j) := by rw [hji]
    _ = 0 := by noncomm_ring

/-- And with `j`. -/
theorem anticomm_mul_right {i j : D} (h : i * j + j * i = 0) :
    (i * j) * j + j * (i * j) = 0 := by
  have hji : j * i = -(i * j) := by linear_combination (norm := noncomm_ring) h
  calc (i * j) * j + j * (i * j) = (i * j) * j + (j * i) * j := by noncomm_ring
    _ = (i * j) * j + (-(i * j)) * j := by rw [hji]
    _ = 0 := by noncomm_ring

end RingOnlyTwo

end RealDivisionAnticomm
