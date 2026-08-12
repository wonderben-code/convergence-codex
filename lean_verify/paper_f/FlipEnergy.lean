import BoxDegree
import PlusClassVanishes

/-!
# Flipping a set of spins costs a bounded amount of energy

The next rung of the chain `FieldThreshold` left written down — the energy comparison its sharper
estimate would consume:

> **`isingH_flipOn_le`** — for every set `S` of sites and every configuration,
> `isingH n (flipOn S σ) ≤ isingH n σ + 16·|S|`.

**`FieldThreshold`'s header called this comparison's degree bound a thing "the estate has none"
of, and that was false.** `PlusClassVanishes` has had `card_adj_le_four`, `card_adj_le_four'`
**and** the single-site comparison `isingH_flipAt_le` — same constant — all along; `ERRATUM 131`
records the truncated probe that missed them. So this file is a **generalisation of a result the
estate already had**, from one site to an arbitrary set, and it consumes that file's degree
bounds rather than re-proving them.

## Where the constant comes from, and it is not tuned

A bond `(p, q)` changes its contribution **only when exactly one of `p`, `q` is flipped** — flip
both and the two sign changes cancel, flip neither and nothing happens. When it does change, it
changes by at most `2`, because each contribution is a product of two spins and so lies in
`[−1, 1]`.

So the whole cost is `2` per *ordered* adjacent pair meeting `S`, and there are at most
`2 · 4 · |S|` such pairs: at most `4` neighbours per site
(`PlusClassVanishes.card_adj_le_four`, and `card_adj_le_four'` for the other order), counted once
with the flipped site first and once with it second. Hence `16·|S|`. **The `16` is `2 × 2 × 4` and
every factor is a step of the argument**, not a constant chosen to make something work: `2` for
the sign change, `2` for the two orders, `4` for the degree.

*Where the bound is loose, and where it is not.* At `|S| = 1` the constant agrees exactly with
`PlusClassVanishes.isingH_flipAt_le`, which the estate proved independently — that is a check on
the constant, not a claim that it is attained, and **whether `16` is attained is not verified
here**. For larger `S` the bound is visibly generous: a bond with **both** endpoints in `S` costs
nothing and is charged twice, and `4` is the interior degree while boundary sites have fewer.

**This generalises `PlusClassVanishes.isingH_flipAt_le`, which the estate has had all along** —
the same bound, the same constant `16`, for a **single** site. `flipOn_singleton` proves the
one-element case of `flipOn` *is* that file's `flipAt`, so "generalises" is checked rather than
claimed. The two degree bounds this proof consumes, `card_adj_le_four` and `card_adj_le_four'`,
are also that file's; an earlier draft of this one re-proved the second under a new name and it
has been deleted (`ERRATUM 131`).

## What this does NOT do

**It does not sharpen the field threshold.** `FieldThreshold.magnetisation_threshold` is unchanged
and still quadratic in the side. The remaining legs of that estimate — stratifying the off-`+` sum
by the number of wrong boundary spins, the injectivity of the flip map on each stratum, and the
binomial sum — are **not attempted here**, and each is a real step rather than bookkeeping.

**And even completed it would not close the uniformity gap**, which `FieldThreshold` already says:
the sharpened threshold would grow like `log n`, and `log n → ∞` too.
-/

namespace FlipEnergy

open IsingFiniteVolume PlusClassVanishes

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The flip, and the two facts about spins the estimate uses -/

/-- Flip the spins on `S`, leave the rest alone. -/
def flipOn (S : Finset (Site n)) (σ : Config n) : Config n :=
  fun p => if p ∈ S then !(σ p) else σ p

theorem spin_mul_le_one (a b : Bool) : spin a * spin b ≤ 1 := by
  cases a <;> cases b <;> norm_num [spin]

theorem neg_one_le_spin_mul (a b : Bool) : (-1 : ℝ) ≤ spin a * spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- **THE SINGLE-SITE FLIP IS THE ONE-ELEMENT CASE**, which is what makes this file a
generalisation of `PlusClassVanishes.isingH_flipAt_le` rather than a parallel construction. Proved
rather than asserted, on the `knSquare_delta` pattern. -/
theorem flipOn_singleton (σ : Config n) (x : Site n) : flipOn {x} σ = flipAt σ x := by
  funext p
  by_cases h : p = x <;> simp [flipOn, flipAt, h]

/-! ## 2. One bond at a time -/

/-- **THE COST OF ONE ORDERED BOND.** Zero unless the bond meets `S`; at most `2` when it does,
because both contributions lie in `[−1, 1]`. The right-hand side charges `2` for each endpoint in
`S` separately — deliberately, since that is what makes the double sum split. -/
theorem bond_diff_le (S : Finset (Site n)) (σ : Config n) (p q : Site n) :
    ((if adj p q then spin (σ p) * spin (σ q) else 0)
      - (if adj p q then spin (flipOn S σ p) * spin (flipOn S σ q) else 0))
      ≤ (if adj p q ∧ p ∈ S then (2 : ℝ) else 0)
        + (if adj p q ∧ q ∈ S then (2 : ℝ) else 0) := by
  classical
  by_cases hpq : adj p q
  · have h1 := spin_mul_le_one (σ p) (σ q)
    have h2 := neg_one_le_spin_mul (flipOn S σ p) (flipOn S σ q)
    by_cases hp : p ∈ S
    · have hnn : (0 : ℝ) ≤ if adj p q ∧ q ∈ S then (2 : ℝ) else 0 := by split <;> norm_num
      rw [if_pos hpq, if_pos hpq, if_pos ⟨hpq, hp⟩]
      linarith
    · by_cases hq : q ∈ S
      · have hz : (if adj p q ∧ p ∈ S then (2 : ℝ) else 0) = 0 := by
          rw [if_neg (by simp [hp])]
        rw [if_pos hpq, if_pos hpq, hz, if_pos ⟨hpq, hq⟩]
        linarith
      · have e1 : flipOn S σ p = σ p := by simp [flipOn, hp]
        have e2 : flipOn S σ q = σ q := by simp [flipOn, hq]
        rw [e1, e2, if_pos hpq]
        simp [hp, hq]
  · simp [hpq]

/-! ## 3. Each of the two orders costs at most `8|S|` -/

theorem row_bound (S : Finset (Site n)) (p : Site n) :
    ∑ q : Site n, (if adj p q ∧ p ∈ S then (2 : ℝ) else 0)
      ≤ if p ∈ S then (8 : ℝ) else 0 := by
  classical
  by_cases hp : p ∈ S
  · rw [if_pos hp]
    have hcong : ∀ q : Site n, (if adj p q ∧ p ∈ S then (2 : ℝ) else 0)
        = (if adj p q then (2 : ℝ) else 0) := fun q => by simp [hp]
    rw [Finset.sum_congr rfl fun q _ => hcong q, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have hc : (((Finset.univ : Finset (Site n)).filter (fun q => adj p q)).card : ℝ) ≤ 4 := by
      exact_mod_cast card_adj_le_four p
    linarith
  · simp [hp]

theorem col_bound (S : Finset (Site n)) (q : Site n) :
    ∑ p : Site n, (if adj p q ∧ q ∈ S then (2 : ℝ) else 0)
      ≤ if q ∈ S then (8 : ℝ) else 0 := by
  classical
  by_cases hq : q ∈ S
  · rw [if_pos hq]
    have hcong : ∀ p : Site n, (if adj p q ∧ q ∈ S then (2 : ℝ) else 0)
        = (if adj p q then (2 : ℝ) else 0) := fun p => by simp [hq]
    rw [Finset.sum_congr rfl fun p _ => hcong p, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    have hc : (((Finset.univ : Finset (Site n)).filter (fun p => adj p q)).card : ℝ) ≤ 4 := by
      exact_mod_cast card_adj_le_four' q
    linarith
  · simp [hq]

theorem sum_indicator (S : Finset (Site n)) (c : ℝ) :
    ∑ p : Site n, (if p ∈ S then c else 0) = (S.card : ℝ) * c := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-! ## 4. The comparison -/

/-- **FLIPPING `S` COSTS AT MOST `16|S|` IN ENERGY.** No hypothesis on `S`, on `σ`, or on `n`. -/
theorem isingH_flipOn_le (S : Finset (Site n)) (σ : Config n) :
    isingH n (flipOn S σ) ≤ isingH n σ + 16 * (S.card : ℝ) := by
  classical
  have key : isingH n (flipOn S σ) - isingH n σ
      = ∑ p : Site n, ∑ q : Site n,
        ((if adj p q then spin (σ p) * spin (σ q) else 0)
          - (if adj p q then spin (flipOn S σ p) * spin (flipOn S σ q) else 0)) := by
    simp only [isingH, Finset.sum_sub_distrib]
    ring
  have hle : ∑ p : Site n, ∑ q : Site n,
        ((if adj p q then spin (σ p) * spin (σ q) else 0)
          - (if adj p q then spin (flipOn S σ p) * spin (flipOn S σ q) else 0))
      ≤ 16 * (S.card : ℝ) := by
    have step1 : ∑ p : Site n, ∑ q : Site n,
        ((if adj p q then spin (σ p) * spin (σ q) else 0)
          - (if adj p q then spin (flipOn S σ p) * spin (flipOn S σ q) else 0))
        ≤ ∑ p : Site n, ∑ q : Site n,
            ((if adj p q ∧ p ∈ S then (2 : ℝ) else 0)
              + (if adj p q ∧ q ∈ S then (2 : ℝ) else 0)) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => bond_diff_le S σ p q
    refine step1.trans ?_
    have hsplit : ∑ p : Site n, ∑ q : Site n,
        ((if adj p q ∧ p ∈ S then (2 : ℝ) else 0)
          + (if adj p q ∧ q ∈ S then (2 : ℝ) else 0))
        = (∑ p : Site n, ∑ q : Site n, (if adj p q ∧ p ∈ S then (2 : ℝ) else 0))
          + ∑ p : Site n, ∑ q : Site n, (if adj p q ∧ q ∈ S then (2 : ℝ) else 0) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit]
    have hrow : (∑ p : Site n, ∑ q : Site n, (if adj p q ∧ p ∈ S then (2 : ℝ) else 0))
        ≤ 8 * (S.card : ℝ) := by
      refine (Finset.sum_le_sum fun p _ => row_bound S p).trans ?_
      rw [sum_indicator]
      ring_nf
      exact le_refl _
    have hcol : (∑ p : Site n, ∑ q : Site n, (if adj p q ∧ q ∈ S then (2 : ℝ) else 0))
        ≤ 8 * (S.card : ℝ) := by
      rw [Finset.sum_comm]
      refine (Finset.sum_le_sum fun q _ => col_bound S q).trans ?_
      rw [sum_indicator]
      ring_nf
      exact le_refl _
    linarith
  linarith [key ▸ hle]

end FlipEnergy
