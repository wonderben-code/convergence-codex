import ExplicitThreshold

/-!
# How low can this Peierls chain's temperature go?

`ExplicitThreshold` delivers `⅔ n²` at `β ≥ 1` with the eight-contour count and at
`β ≥ 11/12` with the six-contour count, and its header asks **"How good is `1`?"**. It answers
by comparing `1` against the hypothesis `8 e^{-4β} ≤ 1/2` — "the closed form cannot be used at
all unless" that holds — and against Onsager.

**That comparison is against a necessary condition which is not the binding one, and the effect
is that the file understates its own number.** `8 e^{-4β} ≤ 1/2` is what `cond_le` needs in
order to *state* its estimate; `beta_gt_of_thr_eight` below proves it forces no more than
`β > 69/100`. What the estimate needs in order to *deliver* `⅔ n²` is `2ε ≤ 1/3` with
`ε = 22 (8 e^{-4β})³`, and `beta_gt_of_eight_bound` proves *that* forces `β > 11/12`. So `1` is
not within about half of what binds; it is within `9%` of it, and the honest answer to "how good
is `1`?" is better than the one the header gives.

## What is proved

* `beta_gt_of_eight_bound` — if `2 · 22 (8 e^{-4β})³ ≤ 1/3`, then `β > 11/12`; and
  `eight_route_needs_beta` says the same thing about the chain's own conclusion: if
  `magnetisation_ge_of`'s lower bound is to reach `⅔ n²` in any nonempty box, then `β > 11/12`.
* `six_bound_at_eleven_twelfths` — the six-count estimate *does* meet its requirement at
  `β = 11/12`, by `ExplicitThreshold.eps_le_of_eleven_twelfths`.
* `six_buys_the_temperature` — together: at `β = 11/12` the six-count route reaches `⅔ n²` and
  the eight-count route provably cannot. `ExplicitThreshold` §3b called this "the first
  statement in the estate that the sharper count buys outright rather than merely improves" and
  supported it with arithmetic done outside Lean. Here it is a theorem.
* `beta_gt_of_six_bound`, `six_route_needs_beta` — the six-count route cannot reach `⅔ n²` at
  or below `β = 9/10`. So `11/12` is within `1.9%` of everything that route can give.
* `thr_holds_but_conclusion_fails` — `β = 3/4` satisfies `cond_le`'s hypothesis and is far
  below the ceiling, so the two constraints are separated by an exhibited `β`, not by an
  estimate of the gap between them.

## Two numbers quoted from outside Lean

`ERRATUM 46` is about numbers quoted in the estate's voice, so these are labelled. The exact
ceilings are `ln(67584)/12 ≈ 0.92676` for the eight-count route and `ln(57024)/12 ≈ 0.91260`
for the six-count route; `11/12 ≈ 0.91667`. **This is arithmetic done outside Lean.** What is
proved below are the clean rational bounds `11/12`, `9/10` and `69/100`, which is what the
estate can check.

## What is NOT proved

Every statement here is about **the estimate**, not about the model. Nothing here says the
magnetisation is small below `9/10` — Onsager says it is not. A ceiling on a Peierls bound is a
fact about the bound. The correct reading is: *further work on the temperature in this chain
must change the estimate, because the estimate as it stands is spent.*

`ExplicitThreshold`'s statements are untouched.
-/

namespace ExplicitThresholdCeiling

/-! ## 1. From the chain's conclusion to a lower bound on an exponential

Both routes bottom out in the same shape: a constant times `e^{-12β}` is at most `1/3`. The
constant is `2 · 22 · 512 = 22528` for the eight-count route and `2 · 44 · 216 = 19008` for the
six-count one, and in each case three times the constant is the number `e^{12β}` must clear. -/

/-- `e^t` is at least `C` as soon as `e^{-t}` is at most `1/C`. The inversion is the only
content; it is separated out because every ceiling below uses it. -/
theorem exp_ge_of_exp_neg_le {t C : ℝ} (hC : 0 < C)
    (h : Real.exp (-t) ≤ 1 / C) : C ≤ Real.exp t := by
  have hx : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have hprod : 0 ≤ (1 / C - Real.exp (-t)) * Real.exp t :=
    mul_nonneg (by linarith) hx.le
  have hexp : (1 / C - Real.exp (-t)) * Real.exp t = Real.exp t / C - 1 := by
    field_simp
    nlinarith [h1]
  rw [hexp] at hprod
  have hstep : C * 1 ≤ C * (Real.exp t / C) := by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Real.exp t / C) hC.le
    linarith
  rw [mul_div_cancel₀ _ hC.ne'] at hstep
  linarith

/-- **THE REQUIREMENT THE `⅔ n²` CONCLUSION IMPOSES.** `magnetisation_ge_of` and
`magnetisation_ge_of_six` both conclude `(1 - 2ε) n² ≤ ⟨magnetisation⟩`. For that to be worth
`⅔ n²` in a box with at least one site, `2ε ≤ 1/3` — no weaker inequality will do. This is why
the ceilings below are about `2ε ≤ 1/3` and not about `cond_le`'s hypothesis. -/
theorem bound_of_two_thirds {ε x : ℝ} (hx : 0 < x)
    (h : 2 / 3 * x ≤ (1 - 2 * ε) * x) : 2 * ε ≤ 1 / 3 := by
  nlinarith

/-- A nonempty box has positive area, so `bound_of_two_thirds` applies to it. -/
theorem box_area_pos {n : ℕ} (hn : 0 < n) : (0 : ℝ) < (n : ℝ) * n := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-! ## 2. The eight-count route: nothing at or below `11/12`

`e^{11} ≈ 59874`, and the eight-count route needs `e^{12β} ≥ 67584`. That gap is the whole
proof: `11` is a whole number, so `Real.exp_one_lt_d9` settles it in one power. -/

/-- `e^{11} < 67584`, from `Real.exp_one_lt_d9` and an eleventh power. The companion of
`ExplicitThreshold.exp_eleven_gt`, in the other direction. -/
theorem exp_eleven_lt : Real.exp 11 < (67584 : ℝ) := by
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 1 ^ 11 = Real.exp 11 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc Real.exp 11 = Real.exp 1 ^ 11 := hpow.symm
    _ ≤ (2.7183 : ℝ) ^ 11 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 11
    _ < 67584 := by norm_num

/-- **THE EIGHT-COUNT ESTIMATE CANNOT MEET ITS REQUIREMENT AT OR BELOW `β = 11/12`.**

A statement about the estimate: the route is spent below `11/12`, not the model disordered
there. -/
theorem beta_gt_of_eight_bound {β : ℝ}
    (h : 2 * (22 * (8 * Real.exp (-(4 * β))) ^ 3) ≤ 1 / 3) : 11 / 12 < β := by
  have hcube : (8 * Real.exp (-(4 * β))) ^ 3 = 512 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  rw [hcube] at h
  have hE : Real.exp (-(12 * β)) ≤ 1 / 67584 := by linarith
  have hEE : (67584 : ℝ) ≤ Real.exp (12 * β) := exp_ge_of_exp_neg_le (by norm_num) hE
  have hlt : Real.exp 11 < Real.exp (12 * β) := lt_of_lt_of_le exp_eleven_lt hEE
  have h12 : (11 : ℝ) < 12 * β := Real.exp_lt_exp.mp hlt
  linarith

/-- **AND SO, ABOUT THE CHAIN'S OWN CONCLUSION.** If the bound `magnetisation_ge_of` proves is
to be worth `⅔ n²` in any box with at least one site, then `β > 11/12`. -/
theorem eight_route_needs_beta {n : ℕ} {β : ℝ} (hn : 0 < n)
    (h : 2 / 3 * ((n : ℝ) * n) ≤
      (1 - 2 * (22 * (8 * Real.exp (-(4 * β))) ^ 3)) * ((n : ℝ) * n)) :
    11 / 12 < β :=
  beta_gt_of_eight_bound (bound_of_two_thirds (box_area_pos hn) h)

/-! ## 3. The six-count route: nothing at or below `9/10`

Here `12β` is not a whole number at `9/10`, so a fifth power does what the eleventh power did
above: `e^{54/5}` is compared with `57024` by comparing `e^{54}` with `57024⁵`. This is the
non-integer exponential estimate that `magnetisation_ge_of_six`'s docstring said "is not done
here" — done, though for the ceiling rather than for a lower threshold. -/

/-- `e^{54} < 57024⁵`, from `Real.exp_one_lt_d9` and a fifty-fourth power. -/
theorem exp_fiftyfour_lt : Real.exp 54 < (57024 : ℝ) ^ 5 := by
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 1 ^ 54 = Real.exp 54 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc Real.exp 54 = Real.exp 1 ^ 54 := hpow.symm
    _ ≤ (2.7183 : ℝ) ^ 54 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 54
    _ < (57024 : ℝ) ^ 5 := by norm_num

/-- `e^{54/5} < 57024`, by taking fifth powers. -/
theorem exp_fiftyfour_fifths_lt : Real.exp (54 / 5 : ℝ) < 57024 := by
  have h5 : Real.exp (54 / 5 : ℝ) ^ 5 = Real.exp 54 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlt : Real.exp (54 / 5 : ℝ) ^ 5 < (57024 : ℝ) ^ 5 := by
    rw [h5]
    exact exp_fiftyfour_lt
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) hlt

/-- **THE SIX-COUNT ESTIMATE CANNOT MEET ITS REQUIREMENT AT OR BELOW `β = 9/10`.** Same reading
as `beta_gt_of_eight_bound`, with `ε = 44 (6 e^{-4β})³`.

Since `ExplicitThreshold.magnetisation_two_thirds_six` delivers at `11/12`, the temperature in
that chain is inside `1.9%` of everything the chain has. -/
theorem beta_gt_of_six_bound {β : ℝ}
    (h : 2 * (44 * (6 * Real.exp (-(4 * β))) ^ 3) ≤ 1 / 3) : 9 / 10 < β := by
  have hcube : (6 * Real.exp (-(4 * β))) ^ 3 = 216 * Real.exp (-(12 * β)) := by
    rw [mul_pow, ExplicitThreshold.exp_cube]
    norm_num
  rw [hcube] at h
  have hE : Real.exp (-(12 * β)) ≤ 1 / 57024 := by linarith
  have hEE : (57024 : ℝ) ≤ Real.exp (12 * β) := exp_ge_of_exp_neg_le (by norm_num) hE
  have hlt : Real.exp (54 / 5 : ℝ) < Real.exp (12 * β) :=
    lt_of_lt_of_le exp_fiftyfour_fifths_lt hEE
  have h12 : (54 / 5 : ℝ) < 12 * β := Real.exp_lt_exp.mp hlt
  linarith

/-- **AND SO, ABOUT THE CHAIN'S OWN CONCLUSION.** If the bound `magnetisation_ge_of_six` proves
is to be worth `⅔ n²` in any box with at least one site, then `β > 9/10`. -/
theorem six_route_needs_beta {n : ℕ} {β : ℝ} (hn : 0 < n)
    (h : 2 / 3 * ((n : ℝ) * n) ≤
      (1 - 2 * (44 * (6 * Real.exp (-(4 * β))) ^ 3)) * ((n : ℝ) * n)) :
    9 / 10 < β :=
  beta_gt_of_six_bound (bound_of_two_thirds (box_area_pos hn) h)

/-! ## 4. The two routes separate exactly at `11/12` -/

/-- The six-count estimate meets its own requirement at `β ≥ 11/12`: this is
`ExplicitThreshold.eps_le_of_eleven_twelfths` with the doubling carried through,
`2 · 9504/59000 = 19008/59000 < 1/3`. -/
theorem six_bound_at_eleven_twelfths {β : ℝ} (hβ : 11 / 12 ≤ β) :
    2 * (44 * (6 * Real.exp (-(4 * β))) ^ 3) ≤ 1 / 3 := by
  have h := ExplicitThreshold.eps_le_of_eleven_twelfths hβ
  linarith

/-- **THE SHARPER CONTOUR COUNT BUYS THE TEMPERATURE OUTRIGHT.** At `β = 11/12` the six-count
estimate meets the requirement that yields `⅔ n²`, and the eight-count estimate does not — and
not merely "does not, as proved here": it *cannot*, since meeting it would force `β > 11/12`.

`ExplicitThreshold` §3b asserted this from arithmetic done outside Lean. Here it is a theorem,
and the ceiling is what makes the second half of it a `¬` rather than a failed attempt. -/
theorem six_buys_the_temperature :
    (2 * (44 * (6 * Real.exp (-(4 * (11 / 12 : ℝ)))) ^ 3) ≤ 1 / 3) ∧
      ¬ (2 * (22 * (8 * Real.exp (-(4 * (11 / 12 : ℝ)))) ^ 3) ≤ 1 / 3) := by
  refine ⟨six_bound_at_eleven_twelfths le_rfl, fun h => ?_⟩
  have := beta_gt_of_eight_bound h
  linarith

/-! ## 5. The condition the header names is not the condition that binds

`8 e^{-4β} ≤ 1/2` — the hypothesis of `cond_le`, and the one `ExplicitThreshold`'s header
compares `1` against — forces only `β > 69/100`, and is already satisfied at `β = 3/4`, where
`beta_gt_of_eight_bound` puts the conclusion out of reach. One exhibited `β` separates the two
conditions. -/

/-- `e³ > 16`, from `Real.exp_one_gt_d9` and a cube. -/
theorem exp_three_gt : (16 : ℝ) < Real.exp 3 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : Real.exp 1 ^ 3 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc (16 : ℝ) < (2.718 : ℝ) ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
    _ = Real.exp 3 := hpow

/-- **`cond_le`'S HYPOTHESIS HOLDS AT `β = 3/4`.** -/
theorem thr_eight_at_three_quarters :
    8 * Real.exp (-(4 * (3 / 4 : ℝ))) ≤ 1 / 2 := by
  have harg : -(4 * (3 / 4 : ℝ)) = -(3 : ℝ) := by norm_num
  rw [harg, Real.exp_neg, inv_eq_one_div]
  have hle : (1 : ℝ) / Real.exp 3 ≤ 1 / 16 :=
    le_of_lt (one_div_lt_one_div_of_lt (by norm_num) exp_three_gt)
  linarith

/-- `e^{69} < 16^{25}`, from `Real.exp_one_lt_d9` and a sixty-ninth power. -/
theorem exp_sixtynine_lt : Real.exp 69 < (16 : ℝ) ^ 25 := by
  have he : Real.exp 1 < (2.7183 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 1 ^ 69 = Real.exp 69 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc Real.exp 69 = Real.exp 1 ^ 69 := hpow.symm
    _ ≤ (2.7183 : ℝ) ^ 69 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 69
    _ < (16 : ℝ) ^ 25 := by norm_num

/-- `e^{69/25} < 16`, by taking twenty-fifth powers. -/
theorem exp_sixtynine_twentyfifths_lt : Real.exp (69 / 25 : ℝ) < 16 := by
  have h25 : Real.exp (69 / 25 : ℝ) ^ 25 = Real.exp 69 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hlt : Real.exp (69 / 25 : ℝ) ^ 25 < (16 : ℝ) ^ 25 := by
    rw [h25]
    exact exp_sixtynine_lt
  exact lt_of_pow_lt_pow_left₀ 25 (by norm_num) hlt

/-- **AND `cond_le`'S HYPOTHESIS FORCES ONLY `β > 69/100`.** This is the number the header
compares `1` against. It is a genuine necessary condition and it is far from the binding one. -/
theorem beta_gt_of_thr_eight {β : ℝ} (h : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    69 / 100 < β := by
  have hE : Real.exp (-(4 * β)) ≤ 1 / 16 := by linarith
  have hEE : (16 : ℝ) ≤ Real.exp (4 * β) := exp_ge_of_exp_neg_le (by norm_num) hE
  have hlt : Real.exp (69 / 25 : ℝ) < Real.exp (4 * β) :=
    lt_of_lt_of_le exp_sixtynine_twentyfifths_lt hEE
  have h4 : (69 / 25 : ℝ) < 4 * β := Real.exp_lt_exp.mp hlt
  linarith

/-- **THE SEPARATION, EXHIBITED.** At `β = 3/4` the estimate can be *stated* and cannot be
*used*. So the honest answer to `ExplicitThreshold`'s question "How good is `1`?" is not `1`
against `69/100` but `1` against a proved ceiling above `11/12`. -/
theorem thr_holds_but_conclusion_fails :
    (8 * Real.exp (-(4 * (3 / 4 : ℝ))) ≤ 1 / 2) ∧
      ¬ (2 * (22 * (8 * Real.exp (-(4 * (3 / 4 : ℝ)))) ^ 3) ≤ 1 / 3) := by
  refine ⟨thr_eight_at_three_quarters, fun h => ?_⟩
  have := beta_gt_of_eight_bound h
  linarith

end ExplicitThresholdCeiling
