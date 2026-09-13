import BoxLapLowWeight

/-!
# At side length three the count is solved, in every dimension

The signless frontier item's live clause is **the box's fibre count at `d ≥ 2`**, and four units
have now circled it: the two ends, the gap, and every level below `2(1 + cos(π/n))`. All four
avoided the difficulty rather than met it, and each said so. **This unit meets it, at one side
length, and there it goes away completely.**

## Why side length three and not another

The eigenvalue is `∑ᵢ (2 − 2cos(kᵢπ/n))` and the count is hard because those cosines are
transcendental and their sums collide unpredictably. **At `n = 3` they are not transcendental.**
The three available terms are

```
2 − 2cos 0 = 0,   2 − 2cos(π/3) = 1,   2 − 2cos(2π/3) = 3
```

— `0`, `1` and `3`, because `cos(π/3)` and `cos(2π/3)` are `±½`. So every eigenvalue is a natural
number and the collision question becomes **`a + 3b = a' + 3b'` in `ℕ`**, which is not a question
about cosines at all.

## What is proved

**`term_three_zero`, `term_three_one`, `term_three_two`** — the three values, `0`, `1`, `3`.

**`boxLapEig_three_eq`** — hence, for any frequency vector on the box of side three,

```
boxLapEig d 3 k = (#{i : kᵢ = 1}) + 3 · (#{i : kᵢ = 2})
```

**as a natural number cast into `ℝ`**, with no cosine left in it.

**`finrank_three_box`** — **THE FILE'S THEOREM.** The eigenspace at a natural number `v` has
dimension `Nat.card {k : Site d 3 // #{i : kᵢ = 1} + 3 · #{i : kᵢ = 2} = v}` — **a decidable
condition on a finite type**, so the multiplicity is computable for every dimension and every
value. **That is what solving the count means here**: the clause is open because the fibre was cut
out by an equation among cosines, and at this side length it is cut out by an equation in `ℕ`.

**`finrank_three_box_not_nat`** — and at a value that is **not** a natural number the eigenspace is
`0`, so the two theorems together describe every real `μ`.

**`finrank_three_dim_three_at_three`** — the worked instance, and it is the collision from the
previous unit seen as a number: in dimension three the multiplicity of `3` is **`4`**, made of the
one vector `(1,1,1)` and the three vectors with a single `2`. **Two shapes, one eigenvalue,
multiplicity four**, computed by `decide` rather than argued.

## What is NOT here

* **NO CLOSED FORM, as of 2026-09-13.** The multiplicity is `∑_{a + 3b = v} C(d,a)·C(d−a,b)` —
  checked by machine for `d ≤ 4` and **not proved**. What is proved, **as of 2026-09-13**, is that
  the fibre is a decidable finite set; turning that into a binomial sum is a separate combinatorial
  argument and **is not attempted** (`ERRATUM 246`).
* **NO OTHER SIDE LENGTH.** `n = 3` works because `cos(π/3) = ½`. The next rational cosine is at
  `n = 2`, where the spectrum is `{0, 2}` and the question is trivial, and at `n = 4`
  `cos(π/4) = √2/2` is irrational — **so this is not the first case of a pattern, it is the one
  side length above two where the arithmetic degenerates.** Nothing here suggests a method for
  `n ≥ 4`.
* **SO THE CLAUSE DOES NOT CLOSE.** It is answered at one side length in every dimension, which is
  more than the previous four units did and much less than the clause asks.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a dimension `d` and, for the main theorem, a
natural number `v`. No side length — it is fixed at three — and no positivity.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BoxLapSideThree

open Real Finset BoxGraph BoxLapSpectrum

/-! ## 1. The three terms are `0`, `1`, `3` -/

theorem term_three_zero : 2 - 2 * Real.cos (((0 : ℕ) : ℝ) * Real.pi / ((2 : ℕ) + 1)) = 0 := by
  norm_num

theorem term_three_one : 2 - 2 * Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((2 : ℕ) + 1)) = 1 := by
  have h : ((1 : ℕ) : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1) = Real.pi / 3 := by push_cast; ring
  rw [h, Real.cos_pi_div_three]
  norm_num

theorem term_three_two : 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((2 : ℕ) + 1)) = 3 := by
  have h : ((2 : ℕ) : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1) = 2 * (Real.pi / 3) := by push_cast; ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num

/-! ## 2. So the eigenvalue is a natural number, spelled out -/

/-- The two counts: how many coordinates carry frequency `1`, and how many carry `2`.

**THE NAME IS LONG BECAUSE THE SHORT ONE IS TAKEN**: `HermitePiCoeff.wt` is a Hermite-coefficient
weight and has nothing to do with this. Renamed rather than accepted, which is
`LaplacianSignlessKernel.compRep`'s precedent and this campaign's habit. -/
def boxWeightThree (d : ℕ) (k : Fin d → ℕ) : ℕ :=
  (Finset.univ.filter (fun i => k i = 1)).card
    + 3 * (Finset.univ.filter (fun i => k i = 2)).card

/-- **NO COSINE LEFT.** -/
theorem boxLapEig_three_eq {d : ℕ} {k : Fin d → ℕ} (hk : ∀ i, k i ≤ 2) :
    boxLapEig d (2 + 1) k = (boxWeightThree d k : ℝ) := by
  classical
  rw [boxLapEig_eq]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => k i = 1)]
  have hone : ∑ l ∈ Finset.univ.filter (fun i => k i = 1),
      (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1)))
      = ((Finset.univ.filter (fun i => k i = 1)).card : ℝ) := by
    rw [Finset.sum_congr rfl fun l hl => by
      rw [(Finset.mem_filter.mp hl).2, term_three_one], Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrest : ∑ l ∈ Finset.univ.filter (fun i => ¬ k i = 1),
      (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1)))
      = 3 * ((Finset.univ.filter (fun i => k i = 2)).card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun i => ¬ k i = 1)) (fun i => k i = 2)]
    have htwo : ∑ l ∈ (Finset.univ.filter (fun i => ¬ k i = 1)).filter (fun i => k i = 2),
        (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1)))
        = 3 * (((Finset.univ.filter (fun i => ¬ k i = 1)).filter
            (fun i => k i = 2)).card : ℝ) := by
      rw [Finset.sum_congr rfl fun l hl => by
        rw [(Finset.mem_filter.mp hl).2, term_three_two], Finset.sum_const, nsmul_eq_mul]
      ring
    have hzero : ∑ l ∈ (Finset.univ.filter (fun i => ¬ k i = 1)).filter (fun i => ¬ k i = 2),
        (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1))) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
      have h2 := (Finset.mem_filter.mp hl).2
      have : k l = 0 := by have := hk l; omega
      rw [this, term_three_zero]
    have hfilt : (Finset.univ.filter (fun i => ¬ k i = 1)).filter (fun i => k i = 2)
        = Finset.univ.filter (fun i => k i = 2) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by omega, h⟩
    rw [htwo, hzero, add_zero, hfilt]
  rw [hone, hrest, boxWeightThree]
  push_cast
  ring

/-! ## 3. So the count is a decidable question about natural numbers -/

/-- **THE FILE'S THEOREM.** At side length three the fibre is cut out by an equation in `ℕ`. -/
theorem finrank_three_box (d v : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (2 + 1)).lapMatrix ℝ) - ((v : ℕ) : ℝ) • LinearMap.id))
      = Nat.card {k : Site d (2 + 1) // boxWeightThree d (fun i => (k i : ℕ)) = v} := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d 2 ((v : ℕ) : ℝ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [boxLapEig_three_eq (fun i => Nat.lt_succ_iff.mp (k i).isLt)]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- **AND OFF THE NATURAL NUMBERS THERE IS NOTHING**, so the two together describe every real. -/
theorem finrank_three_box_not_nat (d : ℕ) {μ : ℝ} (hμ : ∀ v : ℕ, μ ≠ (v : ℝ)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (2 + 1)).lapMatrix ℝ) - μ • LinearMap.id)) = 0 := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d 2 μ, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨k, hk⟩ => ?_⟩
  rw [boxLapEig_three_eq (fun i => Nat.lt_succ_iff.mp (k i).isLt)] at hk
  exact hμ (boxWeightThree d fun i => (k i : ℕ)) hk.symm

/-- **THE WORKED INSTANCE, AND IT IS THE PREVIOUS UNIT'S COLLISION AS A NUMBER.** In dimension
three the multiplicity of `3` is `4`: the single vector `(1,1,1)` and the three vectors carrying one
frequency `2`. -/
theorem finrank_three_dim_three_at_three :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph 3 (2 + 1)).lapMatrix ℝ) - ((3 : ℕ) : ℝ) • LinearMap.id)) = 4 := by
  rw [finrank_three_box 3 3, Nat.card_eq_fintype_card]
  decide

end BoxLapSideThree
