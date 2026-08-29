import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# `n = 4` is minimal, it is **not** unique, and the difference is the whole point

`SPINE.md` link **L6** rates the `n = 4` selection **MISSING** at the headline and **PARTIAL** at
the arithmetic core, and says exactly what the arithmetic core needs:

> *"Genuine proof requires: (a) the honest minimality theorem (∀ even m ≥ 2 with m²−1 ≥ 12,
> 4 ≤ m) — easy, queued as integrity fix; (b) actual CCM classification from spectral-triple
> axioms — serious NCG formalisation, far."*

**This file is (a), and only (a).** It was called easy on 29 July and was still unwritten on
2026-08-29; what `CascadeUniqueness` has instead is `cascade_unique_all_even`, whose conclusion
`n = 4` is reached **from a hypothesis `n ≤ 4`** — so the file assumes an upper bound and
concludes the number it assumed. `n_4_is_smallest` beside it is two numeral facts, `¬(12 ≤ 3)`
and `12 ≤ 15`, and quantifies over nothing.

## What is proved

> **`four_le_of_criterion`** — the honest minimality theorem, in the words the spine asked for:
> every positive even `m` with `12 ≤ m² − 1` satisfies `4 ≤ m`. **No upper bound is assumed.**
>
> **`four_isLeast`** — the same bundled as `IsLeast`, which is the statement *"4 is the smallest
> solution"* rather than a pair of facts about 4 and about everything else.
>
> **`six_mem_criterion`** and **`not_forall_eq_four`** — **and `4` is NOT the only solution.**
> `6` is positive, even, and `6² − 1 = 35 ≥ 12`. So the criterion does not force `n = 4`, and
> `CascadeUniqueness.cascade_unique_all_even`'s `n ≤ 4` hypothesis **cannot be dropped** — which
> is worth knowing, because the obvious reading of a theorem named *"unique"* is that it can.
>
> **`criterion_eq_even_ge_four`** — the criterion is *exactly* "even and at least 4", so the
> solution set is `{4, 6, 8, …}` and nothing about it singles out `4` beyond being least.

## What is NOT claimed

**This is arithmetic and it is not the selection.** Part (b) of L6 — that the spectral-triple
axioms force the algebra class — **is untouched, and it is the headline**. Nothing below mentions
a spectral triple, an algebra, or Connes' axioms; the criterion `12 ≤ n² − 1` is taken as given
rather than derived, and where it comes from is exactly what L6 rates MISSING.

**Minimality is not uniqueness and this file proves they differ.** Any reading of `n = 4` as
*forced* by this criterion is refuted below by `6`. What is forced is `4 ≤ n`.

**Nothing in `CascadeUniqueness` is withdrawn.** `cascade_unique_all_even` is true as stated,
with its hypothesis; `not_forall_eq_four` shows the hypothesis is doing real work rather than
being an artefact.

**No wall moves. No published tag moves. No rating moves** — L6's `MISSING` is the author's and
this file closes one named sub-item of it, which is not the same thing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CascadeMinimality

/-- The numerical criterion `SPINE` L6 states: positive, even, and `12 ≤ n² − 1`. -/
def Criterion (n : ℕ) : Prop := 0 < n ∧ n % 2 = 0 ∧ 12 ≤ n * n - 1

/-- **THE HONEST MINIMALITY THEOREM**, with no upper bound assumed. -/
theorem four_le_of_criterion {m : ℕ} (h : Criterion m) : 4 ≤ m := by
  obtain ⟨hpos, heven, h12⟩ := h
  by_contra hlt
  have hlt' : m < 4 := Nat.lt_of_not_le hlt
  interval_cases m <;> omega

theorem four_mem_criterion : Criterion 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **`4` IS THE LEAST SOLUTION**, as one statement rather than two. -/
theorem four_isLeast : IsLeast {n : ℕ | Criterion n} 4 :=
  ⟨four_mem_criterion, fun _ hb => four_le_of_criterion hb⟩

/-! ## And it is not the only one -/

theorem six_mem_criterion : Criterion 6 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **THE CRITERION DOES NOT FORCE `n = 4`.** So the `n ≤ 4` hypothesis in
`CascadeUniqueness.cascade_unique_all_even` cannot be dropped. -/
theorem not_forall_eq_four : ¬ ∀ n : ℕ, Criterion n → n = 4 := by
  intro h
  have := h 6 six_mem_criterion
  omega

/-- The criterion is **exactly** "even and at least `4`": the solution set is `{4, 6, 8, …}`, and
nothing in it distinguishes `4` except being least. -/
theorem criterion_eq_even_ge_four (n : ℕ) : Criterion n ↔ (n % 2 = 0 ∧ 4 ≤ n) := by
  constructor
  · intro h
    exact ⟨h.2.1, four_le_of_criterion h⟩
  · rintro ⟨heven, h4⟩
    refine ⟨by omega, heven, ?_⟩
    have : 4 * 4 ≤ n * n := Nat.mul_le_mul h4 h4
    omega

end CascadeMinimality
