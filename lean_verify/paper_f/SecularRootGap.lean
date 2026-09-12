import SecularRootBounds

/-!
# Exactly one secular root in every gap between poles

**THIS IS THE PRICE THE LAST TWO UNITS DECLINED TO PAY, PAID.** Entry 165 proved that two solutions
of `∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1` are separated by a pole — *at most one per gap* — and said the other
half needs a value at each end of a gap. Entry 166 said the same. **Here are those values.** They
are explicit, as at the top end: no limit is taken and no filter appears.

## The two brackets, and why they are explicit

`gapStep p q n := n(q − p) / (2((q − p) + 2N))`. Just inside the left end of a gap, at `p + δ` with
`δ = gapStep p q nᵢ₀` for a part whose pole is `p`, that part's term is exactly
`−(2 + 4N/(q − p))`; every other term is at most `2nₖ/(q − p)`, because a pole at or below `p` makes
its term negative and a pole at or above `q` leaves a denominator of at least `(q − p)/2`. The two
add to at most `−2`. Just inside the right end the same computation runs with the signs reversed and
gives at least `2`. **Between them the equation must hold**, and entry 165 says it holds once.

## What is proved

**`gapStep`, `gapStep_pos`, `gapStep_lt_half`, `div_gapStep`** — the offset, its two size facts, and
the value `n / gapStep = 2 + 4N/(q − p)` that makes the arithmetic come out.
**`term_le_of_outside`, `term_ge_of_outside`** — a term whose pole lies outside the gap is bounded
by `± 2nₖ/(q − p)` anywhere inside it, in both sign cases.
**`secularSum_lt_neg_one_near_left`, `secularSum_gt_neg_one_near_right`** — so the sum is below `−1`
just inside the left end and above `−1` just inside the right.
**`continuousOn_secularSum_gap`** — and it is continuous in between, no pole being there.

**`existsUnique_secular_root_in_gap`** — **exactly one solution in `(p, q)`**, for any two poles
`p < q` with no pole strictly between them. **`exists_signless_eigenvector_in_gap`** — and it is an
eigenvalue of `Q`.

Checked by hand: at `K₄` minus an edge the poles are `2, 2, 0`, the one gap is `(0, 2)`, and the one
root there is `3 − √5 ≈ 0.76`; at the three-vertex path the poles are `1, −1`, the gap is `(−1, 1)`,
and the root is `0`. At the equipartite family every pole is equal, there is no gap, and the
statement is vacuous — correctly, since that family has only the one root above the poles.

## What is NOT here

* **THE COUNT ITSELF IS STILL NOT STATED, AND NOW ONLY BOOKKEEPING IS MISSING.** With entry 164
  (one root above the largest pole), entry 166 (none below the smallest) and this (one per gap), the
  number of roots **is** determined — it is the number of distinct values among the `N − 2nᵢ`.
  Saying so in Lean means enumerating the distinct poles in order and pairing consecutive ones,
  which is `Finset` work and is **not done here**. The mathematics is finished; the statement is
  not.
  Not attempted (`ERRATUM 246`), and "only bookkeeping" is a description of the remaining work and
  not a claim that it is quick (`ERRATUM 194`).
* **NO MULTIPLICITY CLAIM BEYOND THE EARLIER ONE.** Each of these roots is a **simple** eigenvalue
  already, by entry 157; nothing here restates that and nothing here adds to it.
* **NOTHING ABOUT THE PART VALUES `N − nᵢ`**, which are eigenvalues by an entirely different route
  and may lie anywhere relative to these gaps.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `p < q`; **witnesses** `i₀` and `j₀` whose poles are `p` and `q`, which is what makes `p`
and `q` poles rather than arbitrary reals; the separation hypothesis that no pole lies strictly
between them; and `∀ i, Nonempty (V i)` throughout, a part of size zero contributing a term that is
identically zero. `Nonempty ι` is **not** taken — it follows from `i₀`. **No mass, no propagator,
and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootGap

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootLocation SecularRootSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The offset used at both ends of a gap: explicit, so no limit is taken anywhere. -/
noncomputable def gapStep (p q : ℝ) (n : ℝ) : ℝ :=
  n * (q - p) / (2 * ((q - p) + 2 * (Fintype.card (Σ i, V i) : ℝ)))

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem gapStep_pos {p q n : ℝ} (hpq : p < q) (hn : 0 < n) :
    0 < gapStep (V := V) p q n := by
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  exact div_pos (mul_pos hn (by linarith)) (by linarith)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem gapStep_lt_half {p q n : ℝ} (hpq : p < q) (hn : 0 < n)
    (hnN : n ≤ (Fintype.card (Σ i, V i) : ℝ)) :
    gapStep (V := V) p q n < (q - p) / 2 := by
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  rw [gapStep, div_lt_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem gapStep_spec {p q n : ℝ} (hpq : p < q) :
    2 * gapStep (V := V) p q n * ((q - p) + 2 * (Fintype.card (Σ i, V i) : ℝ))
      = n * (q - p) := by
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  have hden : (q - p) + 2 * (Fintype.card (Σ i, V i) : ℝ) ≠ 0 := by
    intro h; linarith
  rw [gapStep]
  field_simp

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem div_gapStep {p q n : ℝ} (hpq : p < q) (hn : 0 < n) :
    n / gapStep (V := V) p q n
      = 2 + 4 * (Fintype.card (Σ i, V i) : ℝ) / (q - p) := by
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  have hden : (q - p) + 2 * (Fintype.card (Σ i, V i) : ℝ) ≠ 0 := by intro h; linarith
  have hqp : q - p ≠ 0 := by intro h; linarith
  have hn' : n ≠ 0 := ne_of_gt hn
  rw [gapStep]
  field_simp
  ring

/-! ## 2. A uniform bound on the terms whose pole is outside the gap -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem term_le_of_outside {p q μ : ℝ} (hp : p < μ) (hhalf : μ - p < (q - p) / 2)
    (k : ι)
    (hsep : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ)
      ≤ 2 * (Fintype.card (V k) : ℝ) / (q - p) := by
  have hnk : (0 : ℝ) ≤ Fintype.card (V k) := Nat.cast_nonneg _
  have hrhs : 0 ≤ 2 * (Fintype.card (V k) : ℝ) / (q - p) :=
    div_nonneg (by linarith) (by linarith)
  rcases hsep with h | h
  · exact le_trans (div_nonpos_of_nonneg_of_nonpos hnk (by linarith)) hrhs
  · have hpos : (0 : ℝ) < (q - p) / 2 := by linarith
    have hle : (q - p) / 2 ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ := by
      linarith
    have := div_le_div_of_nonneg_left hnk hpos hle
    calc (Fintype.card (V k) : ℝ)
          / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ)
        ≤ (Fintype.card (V k) : ℝ) / ((q - p) / 2) := this
      _ = 2 * (Fintype.card (V k) : ℝ) / (q - p) := by
          rw [div_div_eq_mul_div]; ring_nf

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem term_ge_of_outside {p q μ : ℝ} (hq : μ < q) (hhalf : q - μ < (q - p) / 2)
    (k : ι)
    (hsep : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    -(2 * (Fintype.card (V k) : ℝ) / (q - p))
      ≤ (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) := by
  have hnk : (0 : ℝ) ≤ Fintype.card (V k) := Nat.cast_nonneg _
  rcases hsep with h | h
  · have hpos : (0 : ℝ) < (q - p) / 2 := by linarith
    have hle : (q - p) / 2 ≤ μ - ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) := by
      linarith
    have hstep := div_le_div_of_nonneg_left hnk hpos hle
    have heq : (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ)
        = -((Fintype.card (V k) : ℝ)
          / (μ - ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)))) := by
      rw [← div_neg]; ring_nf
    have h2 : (Fintype.card (V k) : ℝ) / ((q - p) / 2)
        = 2 * (Fintype.card (V k) : ℝ) / (q - p) := by
      rw [div_div_eq_mul_div]; ring_nf
    rw [heq, neg_le_neg_iff, ← h2]
    exact hstep
  · have hpos : (0 : ℝ) < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ := by
      linarith
    have : (0 : ℝ) ≤ (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) :=
      div_nonneg hnk (le_of_lt hpos)
    have hrhs : 0 ≤ 2 * (Fintype.card (V k) : ℝ) / (q - p) :=
      div_nonneg (by linarith) (by linarith)
    linarith

/-! ## 3. The two brackets, at explicit points inside the gap -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_lt_neg_one_near_left {p q : ℝ} (hpq : p < q) {i₀ : ι}
    (hn0 : (0 : ℝ) < Fintype.card (V i₀))
    (hi₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀) = p)
    (hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    secularSum (V := V) (p + gapStep (V := V) p q (Fintype.card (V i₀))) < -1 := by
  classical
  have hn0N : (Fintype.card (V i₀) : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) := by
    exact_mod_cast card_part_le (V := V) i₀
  have hδ : 0 < gapStep (V := V) p q (Fintype.card (V i₀)) := gapStep_pos hpq hn0
  have hδh : gapStep (V := V) p q (Fintype.card (V i₀)) < (q - p) / 2 :=
    gapStep_lt_half hpq hn0 hn0N
  have hNq : (0 : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) / (q - p) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hterm : (Fintype.card (V i₀) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀)
        - (p + gapStep (V := V) p q (Fintype.card (V i₀))))
      = -(2 + 4 * (Fintype.card (Σ i, V i) : ℝ) / (q - p)) := by
    rw [hi₀, show p - (p + gapStep (V := V) p q (Fintype.card (V i₀)))
      = -gapStep (V := V) p q (Fintype.card (V i₀)) from by ring, div_neg,
      div_gapStep hpq hn0]
  have hrest : ∑ k ∈ Finset.univ.erase i₀, (Fintype.card (V k) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
        - (p + gapStep (V := V) p q (Fintype.card (V i₀))))
      ≤ 2 * (Fintype.card (Σ i, V i) : ℝ) / (q - p) := by
    have hb : ∀ k ∈ Finset.univ.erase i₀, (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
          - (p + gapStep (V := V) p q (Fintype.card (V i₀))))
        ≤ 2 * (Fintype.card (V k) : ℝ) / (q - p) :=
      fun k _ => term_le_of_outside (by linarith) (by linarith) k (hsep k)
    calc ∑ k ∈ Finset.univ.erase i₀, (Fintype.card (V k) : ℝ)
            / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
              - (p + gapStep (V := V) p q (Fintype.card (V i₀))))
        ≤ ∑ k ∈ Finset.univ.erase i₀, 2 * (Fintype.card (V k) : ℝ) / (q - p) :=
          Finset.sum_le_sum hb
      _ ≤ ∑ k : ι, 2 * (Fintype.card (V k) : ℝ) / (q - p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun k _ _ => div_nonneg (by positivity) (by linarith))
      _ = 2 * (Fintype.card (Σ i, V i) : ℝ) / (q - p) := by
          rw [← Finset.sum_div, ← Finset.mul_sum, sum_card_part]
  rw [secularSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hterm,
    show (4 : ℝ) * (Fintype.card (Σ i, V i) : ℝ) / (q - p)
      = 4 * ((Fintype.card (Σ i, V i) : ℝ) / (q - p)) from by ring]
  rw [show (2 : ℝ) * (Fintype.card (Σ i, V i) : ℝ) / (q - p)
      = 2 * ((Fintype.card (Σ i, V i) : ℝ) / (q - p)) from by ring] at hrest
  linarith

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_gt_neg_one_near_right {p q : ℝ} (hpq : p < q) {j₀ : ι}
    (hn0 : (0 : ℝ) < Fintype.card (V j₀))
    (hj₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j₀) = q)
    (hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    -1 < secularSum (V := V) (q - gapStep (V := V) p q (Fintype.card (V j₀))) := by
  classical
  have hn0N : (Fintype.card (V j₀) : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) := by
    exact_mod_cast card_part_le (V := V) j₀
  have hδ : 0 < gapStep (V := V) p q (Fintype.card (V j₀)) := gapStep_pos hpq hn0
  have hδh : gapStep (V := V) p q (Fintype.card (V j₀)) < (q - p) / 2 :=
    gapStep_lt_half hpq hn0 hn0N
  have hNq : (0 : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) / (q - p) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hterm : (Fintype.card (V j₀) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j₀)
        - (q - gapStep (V := V) p q (Fintype.card (V j₀))))
      = 2 + 4 * (Fintype.card (Σ i, V i) : ℝ) / (q - p) := by
    rw [hj₀, show q - (q - gapStep (V := V) p q (Fintype.card (V j₀)))
      = gapStep (V := V) p q (Fintype.card (V j₀)) from by ring, div_gapStep hpq hn0]
  have hrest : -(2 * (Fintype.card (Σ i, V i) : ℝ) / (q - p))
      ≤ ∑ k ∈ Finset.univ.erase j₀, (Fintype.card (V k) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
          - (q - gapStep (V := V) p q (Fintype.card (V j₀)))) := by
    have hb : ∀ k ∈ Finset.univ.erase j₀, -(2 * (Fintype.card (V k) : ℝ) / (q - p))
        ≤ (Fintype.card (V k) : ℝ)
          / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
            - (q - gapStep (V := V) p q (Fintype.card (V j₀)))) :=
      fun k _ => term_ge_of_outside (by linarith) (by linarith) k (hsep k)
    calc -(2 * (Fintype.card (Σ i, V i) : ℝ) / (q - p))
        = ∑ k : ι, -(2 * (Fintype.card (V k) : ℝ) / (q - p)) := by
          rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum, sum_card_part]
      _ ≤ ∑ k ∈ Finset.univ.erase j₀, -(2 * (Fintype.card (V k) : ℝ) / (q - p)) := by
          have hj : -(2 * (Fintype.card (V j₀) : ℝ) / (q - p)) ≤ 0 :=
            neg_nonpos.mpr (div_nonneg (by positivity) (by linarith))
          rw [← Finset.add_sum_erase _ (fun k : ι => -(2 * (Fintype.card (V k) : ℝ) / (q - p)))
            (Finset.mem_univ j₀)]
          linarith
      _ ≤ _ := Finset.sum_le_sum hb
  rw [secularSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hterm,
    show (4 : ℝ) * (Fintype.card (Σ i, V i) : ℝ) / (q - p)
      = 4 * ((Fintype.card (Σ i, V i) : ℝ) / (q - p)) from by ring]
  rw [show (2 : ℝ) * (Fintype.card (Σ i, V i) : ℝ) / (q - p)
      = 2 * ((Fintype.card (Σ i, V i) : ℝ) / (q - p)) from by ring] at hrest
  linarith

/-! ## 4. Continuity across the gap, and the root -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem continuousOn_secularSum_gap {p q a b : ℝ} (ha : p < a) (hb : b < q)
    (hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    ContinuousOn (secularSum (V := V)) (Set.Icc a b) := by
  unfold secularSum
  refine continuousOn_finset_sum _ fun k _ => ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
  rcases hsep k with h | h
  · exact ne_of_lt (by have := hx.1; linarith)
  · exact ne_of_gt (by have := hx.2; linarith)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **EXACTLY ONE SOLUTION OF THE SECULAR EQUATION IN EVERY GAP BETWEEN CONSECUTIVE POLES.** -/
theorem existsUnique_secular_root_in_gap (hne : ∀ i, Nonempty (V i)) {p q : ℝ} (hpq : p < q)
    {i₀ j₀ : ι}
    (hi₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀) = p)
    (hj₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j₀) = q)
    (hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    ∃! μ : ℝ, μ ∈ Set.Ioo p q ∧ secularSum (V := V) μ = -1 := by
  have hι : Nonempty ι := ⟨i₀⟩
  have hni : (0 : ℝ) < Fintype.card (V i₀) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (hne i₀)
  have hnj : (0 : ℝ) < Fintype.card (V j₀) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (hne j₀)
  have hniN : (Fintype.card (V i₀) : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) := by
    exact_mod_cast card_part_le (V := V) i₀
  have hnjN : (Fintype.card (V j₀) : ℝ) ≤ (Fintype.card (Σ i, V i) : ℝ) := by
    exact_mod_cast card_part_le (V := V) j₀
  have hδ : 0 < gapStep (V := V) p q (Fintype.card (V i₀)) := gapStep_pos hpq hni
  have hε : 0 < gapStep (V := V) p q (Fintype.card (V j₀)) := gapStep_pos hpq hnj
  have hδh : gapStep (V := V) p q (Fintype.card (V i₀)) < (q - p) / 2 :=
    gapStep_lt_half hpq hni hniN
  have hεh : gapStep (V := V) p q (Fintype.card (V j₀)) < (q - p) / 2 :=
    gapStep_lt_half hpq hnj hnjN
  have hab : p + gapStep (V := V) p q (Fintype.card (V i₀))
      ≤ q - gapStep (V := V) p q (Fintype.card (V j₀)) := by linarith
  have hmem : (-1 : ℝ) ∈ Set.Icc
      (secularSum (V := V) (p + gapStep (V := V) p q (Fintype.card (V i₀))))
      (secularSum (V := V) (q - gapStep (V := V) p q (Fintype.card (V j₀)))) :=
    ⟨le_of_lt (secularSum_lt_neg_one_near_left hpq hni hi₀ hsep),
      le_of_lt (secularSum_gt_neg_one_near_right hpq hnj hj₀ hsep)⟩
  obtain ⟨μ, hμmem, hμ⟩ := intermediate_value_Icc hab
    (continuousOn_secularSum_gap (V := V) (by linarith) (by linarith) hsep) hmem
  refine ⟨μ, ⟨⟨by linarith [hμmem.1], by linarith [hμmem.2]⟩, hμ⟩, ?_⟩
  rintro ν ⟨⟨hν1, hν2⟩, hνs⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · obtain ⟨k, hk1, hk2⟩ := exists_pole_between_secular_roots hne hι h hνs hμ
    rcases hsep k with hs | hs
    · linarith
    · linarith [hμmem.2]
  · obtain ⟨k, hk1, hk2⟩ := exists_pole_between_secular_roots hne hι h hμ hνs
    rcases hsep k with hs | hs
    · linarith [hμmem.1]
    · linarith

/-- **AND SO AN EIGENVALUE OF `Q` IN EVERY GAP.** -/
theorem exists_signless_eigenvector_in_gap (hne : ∀ i, Nonempty (V i)) {p q : ℝ} (hpq : p < q)
    {i₀ j₀ : ι}
    (hi₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀) = p)
    (hj₀ : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j₀) = q)
    (hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
      ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) :
    ∃ μ ∈ Set.Ioo p q, ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x := by
  obtain ⟨μ, ⟨hμmem, hμ⟩, -⟩ := existsUnique_secular_root_in_gap hne hpq hi₀ hj₀ hsep
  have hd : ∀ k : ι, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) ≠ 0 := by
    intro k
    rcases hsep k with h | h
    · exact ne_of_lt (by have := hμmem.1; linarith)
    · exact ne_of_gt (by have := hμmem.2; linarith)
  obtain ⟨x, hx, hxp⟩ :=
    exists_eigenvector_of_mem_ker_secular hne (mem_ker_secularVec (V := V) hd hμ)
  exact ⟨μ, hμmem, x, fun h0 => secularVec_ne_zero hne i₀ hd (by rw [← hxp, h0, map_zero]), hx⟩

end SecularRootGap
