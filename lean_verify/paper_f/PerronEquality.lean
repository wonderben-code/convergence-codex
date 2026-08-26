import PerronBound

/-!
# The equality case `PerronBound` localised, and the two halves it settles

`PerronBound` proved `|μ|·|vᵢ| ≤ (A *ᵥ |v|)ᵢ` for a **nonnegative** matrix, and recorded the
finding that mattered more than the theorem: **neither strict positivity nor symmetry is used**,
so the whole difficulty of `WALLS` §W4.0 §6 item 2's second route sits in the **equality case** of
that inequality — where strict positivity first has to earn its keep.

This file is that equality case, and it settles two halves of it.

> **`nonneg_or_nonpos_of_abs_sum_eq`** — equality in the triangle inequality with **strictly
> positive weights** forces the summands to share a sign. Stated for a bare weighted sum, because
> that is what it is about; **absent from Mathlib**, which has `Finset.abs_sum_le_sum_abs` and no
> equality companion (`Finset.abs_sum_eq_sum_abs`, `abs_sum_eq_iff`: 0 each).
>
> **^ THE ABSENCE CLAIM STANDS AND ITS SEARCH DID NOT (`ERRATUM 281`).** Both probe strings
> above assume the Mathlib name contains `sum`, and the nearest neighbour does not:
> **`abs_add_eq_add_abs_iff` — `|a + b| = |a| + |b| ↔ (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)`** —
> which is this theorem's conclusion, *forces a common sign*, in Mathlib, for two terms. So
> Mathlib does have the equality case; what it does not have is the **weighted** version over a
> **`Fintype`**, and that is what is proved here. Enumerating `Finset.*abs` gives five names --
> `abs_sum_le_sum_abs`, `abs_sum_of_nonneg`, `abs_sum_of_nonneg'`, `abs_prod`, `abs_expect_le` --
> and none is an equality case, so the `Finset`-level claim is confirmed by a probe that assumes
> nothing about the name. The two-term lemma is not a route to this one: an induction over it
> would have to carry the weights and the sign of the partial sums, which is the content of the
> proof below.
>
> **`sign_constant_of_mulVec_abs_eq`** — so an eigenvector achieving equality at **one** index of
> a strictly positive matrix is sign-constant.
>
> **`eigenvalue_ne_zero_of_mulVec_abs_eq`** and **`ne_zero_of_mulVec_abs_eq`** — and if it
> achieves equality at **every** index, then the eigenvalue is **nonzero** and the vector has
> **no zero entry**. *The nonzero-eigenvalue clause was a hypothesis in the first draft; the
> unused-variable linter caught that the proof never used it, and it turned out to be implied
> rather than merely unused. It is proved rather than deleted.*

## **THIS IS STILL NOT PERRON–FROBENIUS, AND THE TWO MISSING HALVES ARE NAMED**

What a gap proof needs from the equality case is that **the top eigenvector achieves equality**,
and then that the top eigenvalue is **simple**. Neither is here:

1. **That equality holds at all** is a hypothesis of every theorem below, never a conclusion. It
   would come from the variational characterisation — a maximiser of `⟨v, Av⟩/⟨v,v⟩` has `|v|` as
   a maximiser too, so the inequality closes — and this estate has **no** Rayleigh-quotient
   statement for matrices. Mathlib's `ContinuousLinearMap.rayleighQuotient` (16 names) is about
   operators on a Hilbert space and is not applied to `Matrix` anywhere in the estate.
2. **Simplicity** — that no second independent eigenvector shares the top eigenvalue — does not
   follow from anything here. Two sign-constant nowhere-zero vectors can still be independent;
   ruling that out is the step that uses positivity a second time, and it is untouched.

So `WALLS` §W4.0 §6 item 2 is **open**, the `W4` row does not move, and what has changed is that
the route's remaining length is now two named steps rather than one unexamined one.
-/

namespace PerronEquality

open Finset Matrix

/-! ## 1. Equality in the triangle inequality, with strictly positive weights -/

/-- **EQUALITY FORCES A COMMON SIGN.** If every weight is strictly positive and
`|∑ wⱼvⱼ| = ∑ wⱼ|vⱼ|`, then the `vⱼ` are all `≥ 0` or all `≤ 0`.

Absent from Mathlib: `Finset.abs_sum_le_sum_abs` has no equality companion. -/
theorem nonneg_or_nonpos_of_abs_sum_eq {n : Type*} [Fintype n] (w v : n → ℝ)
    (hw : ∀ j, 0 < w j) (h : |∑ j, w j * v j| = ∑ j, w j * |v j|) :
    (∀ j, 0 ≤ v j) ∨ (∀ j, v j ≤ 0) := by
  have key : ∀ u : n → ℝ, (∑ j, w j * u j) = ∑ j, w j * |u j| → ∀ j, 0 ≤ u j := by
    intro u hu j
    have hle : ∀ k ∈ (univ : Finset n), w k * u k ≤ w k * |u k| := fun k _ =>
      mul_le_mul_of_nonneg_left (le_abs_self _) (le_of_lt (hw k))
    have := (Finset.sum_eq_sum_iff_of_le hle).mp hu j (mem_univ j)
    have huj : u j = |u j| := mul_left_cancel₀ (ne_of_gt (hw j)) this
    rw [huj]; exact abs_nonneg _
  rcases abs_cases (∑ j, w j * v j) with ⟨hpos, -⟩ | ⟨hneg, -⟩
  · left
    exact key v (by rw [← hpos, h])
  · right
    intro j
    have hneg' : ∑ j, w j * (-v j) = ∑ j, w j * |(-v j)| := by
      have e1 : ∑ j, w j * (-v j) = -∑ j, w j * v j := by simp [mul_neg]
      have e2 : ∑ j, w j * |(-v j)| = ∑ j, w j * |v j| :=
        Finset.sum_congr rfl fun j _ => by rw [abs_neg]
      rw [e1, e2, ← hneg, h]
    have := key (fun j => -v j) hneg' j
    linarith

/-! ## 2. What that says about an eigenvector -/

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}

/-- **AN EIGENVECTOR ACHIEVING EQUALITY AT ONE INDEX OF A STRICTLY POSITIVE MATRIX IS
SIGN-CONSTANT.** This is the step `PerronBound`'s finding said the whole route rests on. -/
theorem sign_constant_of_mulVec_abs_eq (hA : ∀ i j, 0 < A i j) (hv : A *ᵥ v = μ • v) {i : n}
    (heq : |μ| * |v i| = (A *ᵥ fun j => |v j|) i) :
    (∀ j, 0 ≤ v j) ∨ (∀ j, v j ≤ 0) := by
  refine nonneg_or_nonpos_of_abs_sum_eq (fun j => A i j) v (fun j => hA i j) ?_
  have hrow : ∀ w : n → ℝ, (A *ᵥ w) i = ∑ j, A i j * w j := by
    intro w; simp [Matrix.mulVec, dotProduct]
  have hleft : |∑ j, A i j * v j| = |μ| * |v i| := by
    rw [← hrow v, hv, ← abs_mul]
    simp
  rw [hleft, heq, hrow]

/-- The image of `|v|` under a strictly positive matrix is strictly positive at every index,
whenever `v ≠ 0`. -/
theorem mulVec_abs_pos (hA : ∀ i j, 0 < A i j) (hv0 : v ≠ 0) (i : n) :
    0 < (A *ᵥ fun j => |v j|) i := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv0
  have hrow : (A *ᵥ fun j => |v j|) i = ∑ j, A i j * |v j| := by
    simp [Matrix.mulVec, dotProduct]
  rw [hrow]
  refine Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hA i j)) (abs_nonneg _))
    ⟨k, mem_univ k, mul_pos (hA i k) (abs_pos.mpr hk)⟩

/-- **EQUALITY AT EVERY INDEX ALREADY FORCES THE EIGENVALUE TO BE NONZERO.**

*A first draft of this file carried `μ ≠ 0` as a hypothesis of the theorem below, and the unused-
variable linter caught that the proof never used it. It is not merely unused — it is **implied**,
and the honest fold-back is to prove it rather than to delete it quietly.* -/
theorem eigenvalue_ne_zero_of_mulVec_abs_eq (hA : ∀ i j, 0 < A i j) (hv0 : v ≠ 0)
    (heq : ∀ i, |μ| * |v i| = (A *ᵥ fun j => |v j|) i) : μ ≠ 0 := by
  obtain ⟨k, -⟩ := Function.ne_iff.mp hv0
  have hpos : 0 < |μ| * |v k| := by rw [heq k]; exact mulVec_abs_pos hA hv0 k
  intro hzero
  rw [hzero] at hpos
  simp at hpos

/-- **AND IT LEAVES NO ZERO ENTRY.** No hypothesis on `μ`: the previous theorem supplies it. -/
theorem ne_zero_of_mulVec_abs_eq (hA : ∀ i j, 0 < A i j) (hv0 : v ≠ 0)
    (heq : ∀ i, |μ| * |v i| = (A *ᵥ fun j => |v j|) i) (i : n) : v i ≠ 0 := by
  have hpos : 0 < |μ| * |v i| := by rw [heq i]; exact mulVec_abs_pos hA hv0 i
  intro hzero
  rw [hzero] at hpos
  simp at hpos

end PerronEquality
