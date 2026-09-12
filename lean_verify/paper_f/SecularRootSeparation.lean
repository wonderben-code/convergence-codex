import SecularRootLocation

/-!
# Two solutions of the secular equation are separated by a pole

**THE PREVIOUS UNIT USED ONE SIGN AND ONLY ABOVE THE POLES.** It located a root of
`∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1` above `poleMax` by observing that there every term is negative and every
term increases. **The increase does not need the negativity.** Each term rises across any interval
its own pole avoids: below the pole the denominator is negative and shrinking in size, above it the
denominator is positive and shrinking, and in both cases the fraction rises. So the sum rises across
**any** pole-free interval and cannot equal `−1` twice in one.

## What is proved

**`div_lt_div_of_pos_denom`, `term_lt_term`** — the two sign cases, the first from Mathlib and the
second from the previous unit's negative-denominator lemma.
**`secularSum_lt_of_no_pole_between`** — the sum is strictly increasing across any interval
containing no pole. This **generalises the previous unit's `secularSum_strictMono`**, which is the
case where every pole lies below the interval; that statement is deliberately **not** re-derived
from this one, because it is what `secular_root_unique` there consumes and re-pointing it would be
churn buying nothing.

**`exists_pole_between_secular_roots`** — hence **between any two roots there is a pole**, and
**`secular_root_unique_of_no_pole`** — hence a pole-free interval holds at most one.

## What is NOT here

* **NO COUNT OF THE ROOTS, AND THAT IS EXACTLY WHAT THE PREVIOUS UNIT NAMED AS NEXT.** *At most one
  per gap* is half of *exactly one per gap*. The other half needs a value at each end of a gap —
  the previous unit's explicit-bracket argument run at a pole from both sides, where the terms
  belonging to that pole blow up and the rest stay bounded — **and** it needs the distinct pole
  values put in order, which is `Finset` work nobody here has done. Not attempted (`ERRATUM 246`);
  having half is not a claim that the other half is short (`ERRATUM 194`).
* **NO FINITENESS OF THE ROOT SET.** *Separated by a pole* bounds the number of roots only once one
  knows the gaps are finite in number and how they are arranged. Neither is proved here, so **no
  numerical bound on the count follows from this file alone**.
* **NOTHING NEW ABOUT MULTIPLICITY.** Each root off the part values is already a **simple**
  eigenvalue of `Q` — `UnbalancedMultipartiteSecularEquation.finrank_ker_secularMap_eq_one` with
  `finrank_signless_eigenspace_of_ne`, neither of which needs a pole to be avoided by an interval.
  Nothing here adds to that and nothing here restates it.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` instances;
`Nonempty ι` and `∀ i, Nonempty (V i)` on the two statements about the sum, the second because a
part of size zero contributes an identically-zero term and breaks the strict inequality; the
separation statement inherits both. **No `DecidableEq` is used, no mass, no propagator, and no
metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootSeparation

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootLocation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. A term increases across any interval its own pole avoids -/

theorem div_lt_div_of_pos_denom {n d₁ d₂ : ℝ} (hn : 0 < n) (h₂ : 0 < d₂) (h : d₂ < d₁) :
    n / d₁ < n / d₂ :=
  div_lt_div_of_pos_left hn h₂ h

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem term_lt_term {μ₁ μ₂ : ℝ} (hμ : μ₁ < μ₂) (i : ι) (hn : 0 < (Fintype.card (V i) : ℝ))
    (hpole : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) < μ₁
      ∨ μ₂ < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) :
    (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ₁)
      < (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ₂) := by
  rcases hpole with h | h
  · exact div_lt_div_of_neg_denom hn (by linarith) (by linarith) (by linarith)
  · exact div_lt_div_of_pos_denom hn (by linarith) (by linarith)

/-! ## 2. So the sum increases across any interval with no pole in it -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_lt_of_no_pole_between (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    {μ₁ μ₂ : ℝ} (hμ : μ₁ < μ₂)
    (hpole : ∀ i : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) < μ₁
      ∨ μ₂ < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) :
    secularSum (V := V) μ₁ < secularSum (V := V) μ₂ := by
  rw [secularSum, secularSum]
  refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr hι) fun i _ => ?_
  refine term_lt_term hμ i ?_ (hpole i)
  exact_mod_cast Fintype.card_pos_iff.mpr (hne i)

/-! ## 3. Hence two roots are separated by a pole -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **BETWEEN TWO SOLUTIONS OF THE SECULAR EQUATION THERE IS A POLE.** -/
theorem exists_pole_between_secular_roots (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    {μ₁ μ₂ : ℝ} (hμ : μ₁ < μ₂) (hs₁ : secularSum (V := V) μ₁ = -1)
    (hs₂ : secularSum (V := V) μ₂ = -1) :
    ∃ i : ι, μ₁ ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
      ∧ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) ≤ μ₂ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hpole : ∀ i : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) < μ₁
      ∨ μ₂ < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) := by
    intro i
    rcases lt_or_ge ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) μ₁ with h | h
    · exact Or.inl h
    · exact Or.inr (hcon i h)
  have := secularSum_lt_of_no_pole_between hne hι hμ hpole
  rw [hs₁, hs₂] at this
  exact lt_irrefl _ this

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **AND SO A POLE-FREE INTERVAL HOLDS AT MOST ONE ROOT.** -/
theorem secular_root_unique_of_no_pole (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    {a b μ₁ μ₂ : ℝ}
    (hpole : ∀ i : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) < a
      ∨ b < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
    (h₁ : a ≤ μ₁) (h₁' : μ₁ ≤ b) (h₂ : a ≤ μ₂) (h₂' : μ₂ ≤ b)
    (hs₁ : secularSum (V := V) μ₁ = -1) (hs₂ : secularSum (V := V) μ₂ = -1) :
    μ₁ = μ₂ := by
  rcases lt_trichotomy μ₁ μ₂ with h | h | h
  · obtain ⟨i, hi1, hi2⟩ := exists_pole_between_secular_roots hne hι h hs₁ hs₂
    rcases hpole i with hp | hp
    · linarith
    · linarith
  · exact h
  · obtain ⟨i, hi1, hi2⟩ := exists_pole_between_secular_roots hne hι h hs₂ hs₁
    rcases hpole i with hp | hp
    · linarith
    · linarith

end SecularRootSeparation
