import RicciFlatSharp
import LovelockOrthogonality

/-!
# The form is positive definite, and now something needs it to be

`LovelockOrthogonality` built the full contraction `ip R S = ∑_{abcd} R_{abcd} S_{abcd}`, proved
the three summands mutually orthogonal against it, and then said plainly what it had not done:

> no positive-definiteness, no completeness. It is a symmetric bilinear form, and **positivity is
> not proved because nothing below needs it**.

**That was true when it was written, and it is the right way to leave a gap: named, with the
reason.** This file is here because the reason expired. `WeylNonzeroGeneral` and `RicciFlatSharp`
produce a curvature tensor whose Weyl summand is non-zero at every `n ≥ 4`, and "non-zero" becomes
a statement about *length* — that the decomposition has a Weyl direction of positive size, not
merely a non-zero entry — exactly when the form is known positive definite.

## What is proved

* **`ip_self_pos`** — one non-zero entry makes `ip R R` strictly positive. The proof is
  `Finset.single_le_sum` four times: the sum of squares dominates any one of them;
* `ip_self_nonneg`, and **`eq_zero_of_ip_self_eq_zero`** — so `ip` is positive definite and the
  word *orthogonality* in the file above now carries its usual meaning;
* **`ip_weylPart_pos`** — the consumer. At `n ≥ 4` the Weyl summand of `knSquare (twoProj i j)`
  has **strictly positive squared length**;
* **`ip_weylPart_le_self`** — and Pythagoras (`ip_self_eq`) then gives the ordinary consequence:
  each summand's squared length is at most the whole tensor's.

## What this does not do

**It is not an inner-product-space instance**, and `LovelockOrthogonality`'s other disclaimer
stands: no `InnerProductSpace`, no completeness, no norm. Bundling would mean choosing a carrier
for four-index arrays that nothing in the estate consumes — `LovelockReduction` §1's reason again.
What is proved is the two properties, on the bare form.

**And it says nothing about `KillsWeyl`.** It sharpens *how* non-trivial the Weyl summand is, from
"has a non-zero entry" to "has positive length". The statement about what an equivariant `T` does
to it is untouched, and the watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockInnerPositive

open AlgebraicCurvature LovelockProjections LovelockOrthogonality WeylNonzeroGeneral Finset

variable {n : ℕ}

/-! ## 1. Positive definiteness -/

theorem ip_self_nonneg (R : Fin n → Fin n → Fin n → Fin n → ℝ) : 0 ≤ ip R R := by
  simp only [ip]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- **ONE NON-ZERO ENTRY IS ENOUGH.** A sum of squares dominates any one of its terms, four times
over. -/
theorem ip_self_pos {R : Fin n → Fin n → Fin n → Fin n → ℝ} {a b c d : Fin n}
    (h : R a b c d ≠ 0) : 0 < ip R R := by
  have hterm : (0 : ℝ) < R a b c d * R a b c d := mul_self_pos.mpr h
  have h4 : R a b c d * R a b c d ≤ ∑ d', R a b c d' * R a b c d' :=
    Finset.single_le_sum (fun _ _ => mul_self_nonneg _) (Finset.mem_univ d)
  have h3 : (∑ d', R a b c d' * R a b c d')
      ≤ ∑ c', ∑ d', R a b c' d' * R a b c' d' :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ c)
  have h2 : (∑ c', ∑ d', R a b c' d' * R a b c' d')
      ≤ ∑ b', ∑ c', ∑ d', R a b' c' d' * R a b' c' d' :=
    Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ b)
  have h1 : (∑ b', ∑ c', ∑ d', R a b' c' d' * R a b' c' d')
      ≤ ∑ a', ∑ b', ∑ c', ∑ d', R a' b' c' d' * R a' b' c' d' :=
    Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
      (Finset.mem_univ a)
  have hip : ip R R = ∑ a', ∑ b', ∑ c', ∑ d', R a' b' c' d' * R a' b' c' d' := rfl
  rw [hip]
  linarith

/-- **AND THEREFORE THE FORM IS POSITIVE DEFINITE.** -/
theorem eq_zero_of_ip_self_eq_zero {R : Fin n → Fin n → Fin n → Fin n → ℝ} (h : ip R R = 0) :
    R = fun _ _ _ _ => (0 : ℝ) := by
  funext a b c d
  by_contra hne
  have := ip_self_pos (R := R) (a := a) (b := b) (c := c) (d := d) hne
  linarith

/-! ## 2. The consumer that made it worth proving -/

/-- **THE WEYL SUMMAND HAS POSITIVE LENGTH IN EVERY DIMENSION FROM FOUR UP.** -/
theorem ip_weylPart_pos (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    0 < ip (weylPart (knSquare (twoProj i j))) (weylPart (knSquare (twoProj i j))) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  refine ip_self_pos (a := i) (b := j) (c := j) (d := i) ?_
  rw [weylPart_twoProj_entry hn0 hn1 hn2 hij]
  have hne : (n : ℝ) - 3 ≠ 0 := by linarith
  exact div_ne_zero hne hn1

/-- **AND PYTHAGORAS THEN BOUNDS EACH SUMMAND BY THE WHOLE.** The ordinary consequence of an
orthogonal decomposition, unavailable until the form was known non-negative. -/
theorem ip_weylPart_le_self (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    ip (weylPart R) (weylPart R) ≤ ip R R := by
  have hpy := ip_self_eq hn0 hn1 hn2 hR
  have h1 := ip_self_nonneg (ricciPart R)
  have h2 := ip_self_nonneg (scalPart R)
  linarith

end LovelockInnerPositive
