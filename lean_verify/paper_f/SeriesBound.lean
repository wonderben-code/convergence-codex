import SideLength

/-!
# The Peierls sum is small at low temperature, uniformly in the box

`SideLength.peierls_closed_form` bounds the down-weight fraction by

`∑_{3 ≤ L ≤ card (Plaq n)} (2L + 3) ^ 2 * 4 ^ L * exp (-4βL)`

and `ERRATUM 85` records what that bound was worth before the sum was made to start at
three: nothing, since its `L = 0` term is `9` at every `β`. Starting at three makes
"small for large `β`" *possible*. **This file makes it true.**

## The two steps, and the constant

The summand is `(2L + 3) ^ 2 * s ^ L` with `s = 4 exp (-4β)`. Two facts finish it:

* **`sq_le_pow_two`** — `(2L + 3) ^ 2 ≤ 11 * 2 ^ L` for `L ≥ 3`. Induction; the step is
  `(2L + 5) ^ 2 ≤ 2 (2L + 3) ^ 2`, which is `0 ≤ 4L² + 4L - 7`.
* the geometric tail — with `t = 2s ≤ 1/2`, `∑_{L ∈ Ico 3 M} t ^ L = t ^ 3 ∑_k t ^ k ≤ 2 t ^ 3`,
  using `sum_geometric_two_le` rather than a general geometric formula, because
  restricting to `t ≤ 1/2` is free here and makes the bound a numeral.

So the whole sum is at most `22 * (8 exp (-4β)) ^ 3`, **with no dependence on the size of
the box**. That uniformity is the point: a Peierls estimate that degraded with `n` would
say nothing about the infinite-volume model, and this one does not.

## What it gives, and what it still does not

**`peierls_small`** — for every `ε > 0`, at every low enough temperature, **for every box
and every interior site**, the weight of the `+`-boundary configurations with that site down
is less than `ε` times the partition function.

**It is still not the conditional probability.** The numerator is restricted to `+` boundary
and the denominator is the whole partition function, exactly as `PeierlsCover` and
`SideLength` record; conditioning needs `ContourSubtract`'s injection redone inside the `+`
class.

**And the distance to `IsingBoundaryField.MagnetisationBound` is more than that one step**,
which is worth stating because it would be easy to write otherwise. That `def` is about a
*different measure*: `isingMeasure n h β`, built from `isingHB n h` — the Hamiltonian with a
**boundary field** `h` — over **all** configurations. This file bounds a weight ratio for
`isingH` restricted to `+`-**boundary configurations**. Those are two set-ups, related in the
literature by a limit in `h` that is **not** formalised here — and **corrected 2026-08-10
(ERRATUM 86): this header first named that limit `h → 0⁺`, which is the standard route for a
*bulk* field and was asserted without checking it is the right one for a *boundary* field.**
A finite boundary field does not force the boundary; it favours it. What separates the two
set-ups is that unexamined comparison, not a limit this estate can name. Beyond conditioning,
a magnetisation bound would also need the estimate at **every** site rather than every
interior site, and the passage from a weight ratio to the integral `∫ magnetisation`. **Four
things, not one**, and `MagnetisationBound` is untouched.

**And a caution about reading the theorem.** `∀ᶠ β in atTop` says "for all large enough
`β`", with the threshold *not* exhibited. The proof is by a limit, so a reader wanting an
explicit temperature will not find one here; `sum_le_cube` is the explicit inequality behind
it and does carry a usable threshold (`8 exp (-4β) ≤ 1/2`).
-/

namespace SeriesBound

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField DualObstruction PlaquetteLattice
open SideLength PeierlsCover Filter

set_option linter.style.openClassical false
open scoped Classical

/-! ## 1. The polynomial is dominated by a power of two -/

/-- **`(2L + 3) ^ 2 ≤ 11 * 2 ^ L` from `L = 3` on.** The step is
`(2L + 5) ^ 2 ≤ 2 * (2L + 3) ^ 2`, which is `0 ≤ 4L² + 4L - 7`, true from `L = 1`. -/
theorem sq_le_pow_two : ∀ L, 3 ≤ L → (2 * L + 3) ^ 2 ≤ 11 * 2 ^ L := by
  intro L
  induction L with
  | zero => omega
  | succ L ih =>
    intro h
    rcases Nat.lt_or_ge L 3 with hL | hL
    · interval_cases L <;> simp_all
    · have hstep : (2 * (L + 1) + 3) ^ 2 ≤ 2 * (2 * L + 3) ^ 2 := by nlinarith
      calc (2 * (L + 1) + 3) ^ 2 ≤ 2 * (2 * L + 3) ^ 2 := hstep
        _ ≤ 2 * (11 * 2 ^ L) := by
            exact Nat.mul_le_mul_left 2 (ih hL)
        _ = 11 * 2 ^ (L + 1) := by ring

/-! ## 2. The geometric tail, at ratio at most one half -/

/-- `∑_{L ∈ Ico 3 M} t ^ L ≤ 2 * t ^ 3` for `0 ≤ t ≤ 1/2`. The `t ^ 3` is what makes the
bound small; the `2` is `sum_geometric_two_le`. -/
theorem geom_Ico_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (M : ℕ) :
    ∑ L ∈ Finset.Ico 3 M, t ^ L ≤ 2 * t ^ 3 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hpow : ∀ k ∈ Finset.range (M - 3), t ^ (3 + k) = t ^ 3 * t ^ k := fun k _ => pow_add t 3 k
  rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht0 3)
  calc ∑ k ∈ Finset.range (M - 3), t ^ k
      ≤ ∑ k ∈ Finset.range (M - 3), (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ ht0 ht k
    _ ≤ 2 := sum_geometric_two_le _

/-! ## 3. The closed form is at most a cube -/

/-- **The Peierls sum is at most `22 * (8 exp (-4β)) ^ 3`**, with **no dependence on the
size of the box**. The hypothesis `8 exp (-4β) ≤ 1/2` is an explicit low-temperature
threshold. -/
theorem sum_le_cube (β : ℝ) (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) (M : ℕ) :
    ∑ L ∈ Finset.Ico 3 M, ((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) ≤
      22 * (8 * Real.exp (-(4 * β))) ^ 3 := by
  set q : ℝ := Real.exp (-(4 * β)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hterm : ∀ L ∈ Finset.Ico 3 M,
      ((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) ≤
        11 * (8 * q) ^ L := by
    intro L hL
    have hL3 : 3 ≤ L := (Finset.mem_Ico.mp hL).1
    have hexp : Real.exp (-(4 * β) * (L : ℝ)) = q ^ L := by
      rw [hq, ← Real.exp_nat_mul]
      ring_nf
    have hcast : (((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) : ℝ)
        = ((2 * L + 3) ^ 2 : ℕ) * (4 : ℝ) ^ L := by
      push_cast
      ring
    rw [hexp, hcast]
    have hpoly : (((2 * L + 3) ^ 2 : ℕ) : ℝ) ≤ 11 * 2 ^ L := by
      exact_mod_cast Nat.cast_le.mpr (sq_le_pow_two L hL3)
    calc (((2 * L + 3) ^ 2 : ℕ) : ℝ) * (4 : ℝ) ^ L * q ^ L
        ≤ (11 * 2 ^ L) * (4 : ℝ) ^ L * q ^ L := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly ?_) ?_
          · positivity
          · positivity
      _ = 11 * (8 * q) ^ L := by
          rw [mul_pow]
          have : (8 : ℝ) ^ L = 2 ^ L * 4 ^ L := by
            rw [← mul_pow]; norm_num
          rw [this]; ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hle := geom_Ico_le (8 * q) (by positivity) hβ M
  calc 11 * ∑ L ∈ Finset.Ico 3 M, (8 * q) ^ L ≤ 11 * (2 * (8 * q) ^ 3) := by
        exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 22 * (8 * q) ^ 3 := by ring

/-! ## 4. So it is eventually smaller than any `ε` -/

theorem tendsto_bound : Tendsto (fun β : ℝ => 22 * (8 * Real.exp (-(4 * β))) ^ 3) atTop
    (nhds 0) := by
  have hexp : Tendsto (fun β : ℝ => Real.exp (-(4 * β))) atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop (by norm_num))
  have := ((hexp.const_mul (8 : ℝ)).pow 3).const_mul (22 : ℝ)
  simpa using this

theorem eventually_threshold : ∀ᶠ β : ℝ in atTop, 8 * Real.exp (-(4 * β)) ≤ 1 / 2 := by
  have hexp : Tendsto (fun β : ℝ => 8 * Real.exp (-(4 * β))) atTop (nhds 0) := by
    have h : Tendsto (fun β : ℝ => Real.exp (-(4 * β))) atTop (nhds 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.const_mul_atTop (by norm_num))
    simpa using h.const_mul (8 : ℝ)
  exact hexp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

/-- **THE PEIERLS ESTIMATE, SMALL AT LOW TEMPERATURE AND UNIFORMLY IN THE BOX.** For every
`ε > 0`, at every low enough temperature, **for every box and every interior site**, the
weight of the `+`-boundary configurations with that site down is less than `ε` times the
partition function.

The uniformity in `n` is the content: `sum_le_cube`'s bound does not mention the box, so one
threshold works for every box at once. **It remains a statement about the `+`-boundary
weight over the full partition function, not a conditional probability** — see `SideLength`
and `PeierlsCover` — and it is **not** a step away from
`IsingBoundaryField.MagnetisationBound`, which is stated for the boundary-**field** measure
over all configurations; the header lists the four things that separate them.
`MagnetisationBound` is untouched. -/
theorem peierls_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ), 0 < n → ∀ x : Site n,
      x.1.val + 1 < n → x.2.val + 1 < n →
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
            (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
          (∑ σ : Config n, Real.exp (-β * isingH n σ)) < ε := by
  filter_upwards [eventually_threshold, tendsto_bound.eventually (gt_mem_nhds hε)]
    with β hthr hsmall n hn x hi hj
  exact lt_of_le_of_lt
    (le_trans (peierls_closed_form hn β hi hj) (sum_le_cube β hthr _)) hsmall

end SeriesBound
