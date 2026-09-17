/-
  WheelHubCollision: where the hub's lower root sits, how fast it converges — and the coincidence
  three units called a question, which at the smallest wheel actually happens

  WHY THIS FILE EXISTS. Units 89 and 90 both closed on the same sentence: the wheel's
  multiplicity table needs `hubRootMinus` shown distinct from every rim value `3 + 2cos(2πk/N)`,
  and that is a coincidence question between a root of `λ² = (N+5)λ − 4N` and a cosine, of the
  species this estate records as library-blocked at `L102`. **BOTH SENTENCES WERE WRITTEN WITHOUT
  ANYONE EVALUATING THE SMALLEST CASE.** At `N = 3` the wheel is `K₄`, the discriminant is `16`,
  and the lower root is `2` — which is exactly `3 + 2cos(2π/3)`. **The collision is not
  hypothetical: it occurs, at the first wheel there is.** So the table cannot be had by proving
  non-collision, because non-collision is false; it has to be stated under the hypothesis, or
  case-split. That is `ERRATUM 622`, and this file is the proof that goes with it.

  **CHECKED AGAINST THE ESTATE BEFORE BEING WRITTEN.** The index (14492 statements, 1110 modules)
  holds five statements naming `hubRootMinus` — its definition, `hubRootMinus_lt_hubRootPlus`,
  `hubRoot_hubRootMinus`, `one_le_finrank_coneEig_hubRootMinus` and unit 86's
  `hubRootMinus_lt_two_mul_add_one` — and four naming `hubDisc`: `hubDisc_pos`,
  `sq_sqrt_hubDisc`, `sq_lt_hubDisc` and `sq_lt_hubDisc'`. **Not one of them is a numeric bound, a
  rate, or an evaluation at a named `n`**, and the sharpest of them, `< 2d + 1`, is exactly one
  too weak to place the root inside the rim's range rather than at its top end.

  WHAT IS PROVED.

  * **`sub_lt_sqrt_hubDisc`** — the one inequality the general section rests on: the discriminant's
    square root clears `n − 2d + 1`. Everything in `Range` is this fact read twice.
  * **`hubRootMinus_lt_two_mul`** — **sharper by one than the estate's bound**: the lower root is
    below `2d`, not merely below `2d + 1`.
  * **`hubRootMinus_pos`, `one_lt_hubRootMinus`, `hubRootMinus_mem_Ioo`** — and above `1` once
    `n > 2d`, so it lies in the OPEN `(1, 2d)` while the rim fills `[1, 2d + 1]`. **Strictly
    interior, away from both ends — so no comparison of sizes can separate the two families**,
    which is what makes the remaining question arithmetic rather than analytic. At `n = 2d` with
    `d = 1` the root is exactly `1`, so that hypothesis is not decoration.
  * **`two_mul_sub_hubRootMinus_lt`** — **THE RATE**: `2d − hubRootMinus < 2d/(n − 2d + 1)`. For a
    fixed degree the lower root accumulates on `2d`, and `2d` is an interior point of the rim's
    range, not an endpoint.
  * **`hubRootMinus_lt_four`, `four_sub_hubRootMinus_lt`, `rim_value_mem_Icc`,
    `hubRootMinus_mem_Ioo_four`** — the wheel's form of all of that, at `d = 2`: the root is in
    `(1, 4)`, the rim fills `[1, 5]`, and `4 − hubRootMinus < 4/(n − 3)`.
  * **`hubDisc_three_two`, `sqrt_hubDisc_three_two`, `hubRootMinus_three_two`,
    `cos_two_pi_div_three`, `hubRootMinus_eq_rim_three`** — **THE COLLISION.** `hubDisc 3 2 = 16`
    is a perfect square, so the lower root is the rational `2`, and `2 = 3 + 2cos(2π/3)`.
  * **`finrank_coneEig_hubRootMinus_three`** — **AND THE MULTIPLICITY, COMPUTED EXACTLY: `3`.**
    The first exact non-trivial multiplicity this chain has produced. Upper bound: unit 89's
    pigeonhole against unit 86's simple top. Lower bound: unit 83's hub vector plus unit 88's
    pair of rim vectors, which land in the SAME eigenspace precisely because of the collision.
    **Away from a collision the pattern gives `1`**, so this is the case that shows the table is
    not one formula.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING SAYS `N = 3` IS THE ONLY COLLISION.** One instance is exhibited; no theorem here
    excludes another, and deciding it in general is still the `L102` species — a quadratic
    irrational against a value of `2cos` at a rational multiple of `π`. **Not attempted and no
    cost offered** (`ERRATUM 194`, `ERRATUM 246`). A floating-point scan is recorded on
    `UNLOCK_WATCHLIST` and is labelled there as floating point.
  * **THE WHEEL'S TABLE IS STILL NOT ASSEMBLED.** This file supplies two of its ingredients — the
    rim's range, and the fact that the hypothesis it needs is a real hypothesis rather than a
    theorem waiting to be proved — and assembles nothing.
  * **THE RATE IS NOT A LIMIT.** `two_mul_sub_hubRootMinus_lt` is an inequality at each `n`; no
    `Filter.Tendsto`, no `atTop`, and no statement in Mathlib's limit language appears here.
  * **NOTHING ABOUT ANY OTHER `d`-REGULAR GRAPH.** The `Range` section is general in `n` and `d`,
    but `Exact` is about `cycleGraph 3` and nothing else; the general cone is untouched.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  THE HYPOTHESES, READ OFF THE BINDERS. `0 < d` is taken by every general bound and is necessary:
  at `d = 0` the lower root is `0 = 2d` and `hubRootMinus_lt_two_mul` would be false.
  `2 * d ≤ n` is taken only by the rate, where it keeps the denominator positive, and `2 * d < n`
  only by `one_lt_hubRootMinus`, where `n = 2d, d = 1` is a genuine counterexample. The `Exact`
  section takes no hypothesis at all: it is a statement about one graph.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import ConeDimensionSum
import WheelMultiplicity

namespace WheelHubCollision

open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen
open WheelSpectrum WheelMultiplicity ConeDimensionSum

/-! ## Where the hub's lower root sits -/

section Range

variable (n d : ℕ)

/-- The one inequality the section rests on: the square root of the discriminant clears
`n - 2d + 1`. Both of the bounds below are this fact read twice. -/
theorem sub_lt_sqrt_hubDisc (hd : 0 < d) :
    (n : ℝ) - 2 * d + 1 < Real.sqrt (hubDisc n d) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  refine Real.lt_sqrt_of_sq_lt ?_
  change _ < ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ))
  nlinarith [hd']

/-- **SHARPER BY ONE THAN THE ESTATE'S BOUND.** `hubRootMinus_lt_two_mul_add_one` puts the lower
root below `2d + 1`; it is in fact below `2d`. -/
theorem hubRootMinus_lt_two_mul (hd : 0 < d) : hubRootMinus n d < 2 * d := by
  have h := sub_lt_sqrt_hubDisc n d hd
  rw [hubRootMinus]
  linarith

/-- And it is positive, so it sits strictly inside the rim's range `[d + 1 - d, d + 1 + d]`. -/
theorem hubRootMinus_pos (hn : 0 < n) (hd : 0 < d) : 0 < hubRootMinus n d := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hlt : Real.sqrt (hubDisc n d) < (n : ℝ) + 2 * d + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    change ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ)) < _
    nlinarith [hn', hd']
  rw [hubRootMinus]
  linarith

/-- **THE RATE.** The lower root approaches `2d` from below like `2d/n`, so for a fixed degree it
accumulates on `2d` — which is an interior point of the rim's range, not an endpoint. -/
theorem two_mul_sub_hubRootMinus_lt (hd : 0 < d) (hn : 2 * d ≤ n) :
    2 * (d : ℝ) - hubRootMinus n d < 2 * d / ((n : ℝ) - 2 * d + 1) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hn' : 2 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : (0 : ℝ) < (n : ℝ) - 2 * d + 1 := by linarith
  have hsa := sub_lt_sqrt_hubDisc n d hd
  have hs2 := sq_sqrt_hubDisc n d
  rw [lt_div_iff₀ ha, hubRootMinus]
  nlinarith [hs2, ha, mul_pos (sub_pos.2 hsa) (sub_pos.2 hsa)]

/-- And it clears `1`, the rim's other end, as soon as `n > 2d`. (At `n = 2d` and `d = 1` it is
exactly `1`, so the hypothesis is not decoration.) -/
theorem one_lt_hubRootMinus (hd : 0 < d) (hn : 2 * d < n) : 1 < hubRootMinus n d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : 2 * (d : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlt : Real.sqrt (hubDisc n d) < (n : ℝ) + 2 * d - 1 := by
    rw [Real.sqrt_lt' (by linarith)]
    change ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ)) < _
    nlinarith [mul_pos (sub_pos.2 hn') (by linarith : (0 : ℝ) < 2 * (d : ℝ) - 1)]
  rw [hubRootMinus]
  linarith

/-- **SO IT SITS STRICTLY INSIDE.** The rim's values fill `[d + 1 - d, d + 1 + d] = [1, 2d + 1]`,
and the lower root is in the open `(1, 2d)` — away from both ends. **No comparison of sizes can
separate it from the rim**, which is why the question unit 89 named is arithmetic and not
analytic. -/
theorem hubRootMinus_mem_Ioo (hd : 0 < d) (hn : 2 * d < n) :
    hubRootMinus n d ∈ Set.Ioo (1 : ℝ) (2 * d) :=
  ⟨one_lt_hubRootMinus n d hd hn, hubRootMinus_lt_two_mul n d hd⟩

end Range

/-! ## The wheel: the lower root converges to four -/

section Wheel

/-- At `d = 2` the bound reads `< 4`, at every `n`. -/
theorem hubRootMinus_lt_four (n : ℕ) : hubRootMinus n 2 < 4 := by
  have h := hubRootMinus_lt_two_mul n 2 (by norm_num)
  norm_num at h
  exact h

/-- **AND IT CONVERGES TO `4`.** The rim values are `3 + 2cos(2πk/n)`, so they live in `[1, 5]`
and `4` is interior to that range: the lower root accumulates on the rim from inside. -/
theorem four_sub_hubRootMinus_lt (n : ℕ) (hn : 4 ≤ n) :
    4 - hubRootMinus n 2 < 4 / ((n : ℝ) - 3) := by
  have h := two_mul_sub_hubRootMinus_lt n 2 (by norm_num) (by omega)
  rw [show (n : ℝ) - 2 * ((2 : ℕ) : ℝ) + 1 = (n : ℝ) - 3 by push_cast; ring] at h
  norm_num at h
  exact h

/-- The rim's range, at `d = 2`: every rim value is in `[1, 5]`. -/
theorem rim_value_mem_Icc (x : ℝ) : 3 + 2 * Real.cos x ∈ Set.Icc (1 : ℝ) 5 :=
  ⟨by nlinarith [Real.neg_one_le_cos x], by nlinarith [Real.cos_le_one x]⟩

/-- **THE WHEEL'S FORM OF THE SAME SENTENCE.** The hub's lower root is in `(1, 4)` and the rim
fills `[1, 5]`: strictly interior, and accumulating on the interior point `4`. -/
theorem hubRootMinus_mem_Ioo_four (n : ℕ) (hn : 4 < n) :
    hubRootMinus n 2 ∈ Set.Ioo (1 : ℝ) 4 :=
  ⟨one_lt_hubRootMinus n 2 (by norm_num) (by omega), hubRootMinus_lt_four n⟩

end Wheel

/-! ## The collision, at the smallest wheel -/

section Three

theorem hubDisc_three_two : hubDisc 3 2 = 16 := by
  unfold hubDisc
  norm_num

theorem sqrt_hubDisc_three_two : Real.sqrt (hubDisc 3 2) = 4 := by
  rw [hubDisc_three_two, show (16 : ℝ) = 4 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem hubRootMinus_three_two : hubRootMinus 3 2 = 2 := by
  rw [hubRootMinus, sqrt_hubDisc_three_two]
  norm_num

/-- `cos(2π/3) = -1/2`, off `Real.cos_pi_sub` and `Real.cos_pi_div_three`. -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi * 1 / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi * 1 / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

/-- **THE COINCIDENCE UNIT 89 CALLED A QUESTION ACTUALLY HAPPENS.** At the smallest wheel -- `W₃`,
which is `K₄` -- the hub's lower root IS a rim value. -/
theorem hubRootMinus_eq_rim_three :
    hubRootMinus 3 2 = 3 + 2 * Real.cos (2 * Real.pi * 1 / 3) := by
  rw [hubRootMinus_three_two, cos_two_pi_div_three]
  norm_num

end Three

/-! ## And so the multiplicity at `N = 3` is computed exactly -/

section Exact

/-- The angle at `k = 1` on the three-cycle, with the `Fin` coercion discharged once. -/
theorem angle_one_three :
    2 * Real.pi * (((1 : Fin (0 + 3)) : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 3)
      = 2 * Real.pi * 1 / 3 := by
  norm_num

theorem sin_angle_one_three_ne_zero : Real.sin (2 * Real.pi * 1 / 3) ≠ 0 := by
  have h0 : (0 : ℝ) < 2 * Real.pi * 1 / 3 := by have := Real.pi_pos; linarith
  have h1 : 2 * Real.pi * 1 / 3 < Real.pi := by have := Real.pi_pos; linarith
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h0 h1)

/-- **THE FIRST EXACTLY COMPUTED NON-TRIVIAL MULTIPLICITY IN THIS CHAIN**, and it is `3`, where
the pattern that holds away from a collision would give `1`. The upper bound is unit 89's
pigeonhole, the lower bound is unit 88's pair of rim vectors plus unit 83's hub vector, and what
makes them meet is `hubRootMinus_eq_rim_three`. -/
theorem finrank_coneEig_hubRootMinus_three :
    Module.finrank ℝ (coneEig (cycleGraph 3) (hubRootMinus 3 2)) = 3 := by
  have hc : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hhub : HubRoot (Fintype.card (Fin 3)) 2 (hubRootMinus 3 2) := by
    rw [hc]; exact hubRoot_hubRootMinus 3 2
  have h1 := finrank_coneEig_of_hubRoot (cycleGraph 3) (cycle_reg 0) hhub
  have hval : 2 * Real.cos (2 * Real.pi * (((1 : Fin (0 + 3)) : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 3))
      = hubRootMinus 3 2 - ((2 : ℕ) : ℝ) - 1 := by
    rw [angle_one_three, cos_two_pi_div_three, hubRootMinus_three_two]
    norm_num
  have h2 := two_le_finrank_rimEig 0 1 (by decide)
    (by rw [angle_one_three]; exact sin_angle_one_three_ne_zero)
  rw [hval] at h2
  -- `two_le_finrank_rimEig` says `cycleGraph (0 + 3)` where `h1` says `cycleGraph 3`; they are
  -- the same graph, and `omega` reads the two spellings as two atoms unless they are made one.
  have h2' : 2 ≤ Module.finrank ℝ
      (rimEig (cycleGraph 3) (hubRootMinus 3 2 - ((2 : ℕ) : ℝ) - 1)) := h2
  have htop := ConeTopEigen.finrank_coneEig_hubRootPlus (cycleGraph 3) (cycle_reg 0)
  have hne : hubRootPlus (Fintype.card (Fin 3)) 2 ≠ hubRootMinus 3 2 := by
    rw [hc]; exact (hubRootMinus_lt_hubRootPlus 3 2).ne'
  have h3 := sum_finrank_coneEig_le (cycleGraph 3)
    {hubRootPlus (Fintype.card (Fin 3)) 2, hubRootMinus 3 2}
  rw [Finset.sum_pair hne, htop, hc] at h3
  omega

end Exact

end WheelHubCollision
