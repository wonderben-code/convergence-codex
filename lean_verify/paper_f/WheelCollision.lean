/-
  WheelCollision: the wheel's hub root NEVER meets its rim, except at the triangle — so unit 92's
  non-collision hypothesis is a theorem, and the wheel's multiplicity table is unconditional

  **WHY THIS FILE EXISTS.** `WheelTable`'s multiplicity table carries
  `hcol : hubRootMinus (n+3) 2 ∉ rimSet n` as a HYPOTHESIS in eleven declarations, because unit 92
  could not decide when the hub's lower root meets a rim value. `RE-SWEEP #62` recorded the
  question as blocked on the degree of `ℚ(cos 2π/N)` over `ℚ`, which the pinned Mathlib does not
  have; `ERRATUM 632` showed that blocker is **sufficient and not necessary**, and named a route
  through a degree Mathlib *does* have. This file runs that route to the end.

  **THE ONE IDEA.** `ConeMultiplicityExact.HubRoot n d lam` is `lam² = (n + 2d + 1)·lam − 2d·n`, so
  at `d = 2` the hub quadratic has **integer** coefficients. A rim value is `3 + 2cos(2πk/N)`, so a
  collision makes `s = 2cos(2πk/N)` satisfy the integer quadratic `s² + (1−N)s + (N−6) = 0`; and
  `s = w + w⁻¹` for `w = ζ_N^k`, so clearing `w` gives a monic integer **quartic** annihilating
  `w`. A root of unity's minimal polynomial over `ℚ` is a cyclotomic polynomial of degree `φ(m)`,
  so `φ(m) ≤ 4` — and unit 107 rung one's `TotientSmall.totient_le_four_iff` reduces `m` to nine
  values. Each of the nine is then decided by arithmetic on `N`.

  **THE ANSWER, AND IT IS SHARP.** Eight of the nine orders are impossible. Five die on the real
  quadratic alone (`m = 1, 2, 6` and `m = 8, 12`, whose `s²` is `2` and `3`); `m = 4` forces
  `N = 6` and dies on `orderOf w ∣ N`, since `4 ∤ 6`; `m = 5` and `m = 10` force `N² = 15N − 25`
  and `N² = N + 11`, neither of which has a natural root. **Order three survives and forces
  `N = 3`** — which is exactly the collision unit 91 found by hand, at the triangle, where the
  wheel is `K₄`. So `hubRootMinus_notMem_rimSet_of_ne_zero` needs `n ≠ 0` and **the hypothesis
  cannot be weakened**, because `WheelHubCollision.hubRootMinus_eq_rim_three` proves the collision
  at `n = 0`, and `hubRootMinus_notMem_rimSet_iff` at the foot of this file states the side
  condition as an iff.

  **THE INDEX, WHICH IS WHERE `ERRATUM 632` WENT WRONG.** `hubDisc`'s first argument is the base
  graph's size; `WheelTable`'s `n` is the shifted index, with side `N = n + 3`. `ERRATUM 632` wrote
  the quadratic in the former and the rim in the latter and reported the answer as `n = 3`. The
  side is 3, so the shifted index is **0**. `ERRATUM 633` records that, and also that the
  erratum's reachability test divided into `n + 3 = 9` where it should have divided into the side
  6 — a step whose verdict survives, since `4` divides neither.

  **WHAT IS KEPT.** `WheelTable`'s eleven `hcol` declarations stay exactly as they are
  (`ERRATUM 94`): at `n = 0` the hypothesis is false and their conclusions fail, so the
  hypothesised form is the general statement, not a superseded one. The five restatements at the
  foot of this file are the table with `hcol` replaced by `n ≠ 0`.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TotientSmall
import WheelTable
import WheelSecondEigen
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace WheelCollision

open Finset ConeMultiplicityExact Real
open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity WheelSpectrum WheelMultiplicity WheelTable
open ConeTopEigen

/-! ## the real-side algebra: the hub quadratic in integer form -/

/-- **THE HUB QUADRATIC AT `d = 2` HAS INTEGER COEFFICIENTS.** Unfolding
`ConeMultiplicityExact.HubRoot` at `d = 2` and nothing else. -/
theorem hub_quadratic_two (N : ℕ) :
    (hubRootMinus N 2) ^ 2 = ((N : ℝ) + 5) * hubRootMinus N 2 - 4 * (N : ℝ) := by
  have h := hubRoot_def.1 (hubRoot_hubRootMinus N 2)
  norm_num at h
  linarith [h]

/-- **THE SUBSTITUTION.** If the hub's lower root is `3 + s` then `s` satisfies the integer
quadratic `s² + (1−N)s + (N−6) = 0`. Pure algebra on the previous lemma. -/
theorem shifted_quadratic {N : ℕ} {s : ℝ} (h : hubRootMinus N 2 = 3 + s) :
    s ^ 2 + (1 - (N : ℝ)) * s + ((N : ℝ) - 6) = 0 := by
  have hq := hub_quadratic_two N
  rw [h] at hq
  nlinarith [hq]

/-! ## the root of unity, and the monic integer quartic it satisfies

`CycleLaplacianSpectrum.zeta N = exp(2πi/N)`. A rim value at index `k` is `3 + 2cos(2πk/N)`, and
`2cos(2πk/N)` is exactly `w + w⁻¹` for `w = zeta N ^ k`. That identity is the whole bridge from the
real quadratic to the algebraic one, and it lives in `CycleLaplacianSpectrum` rather than here —
unit 108 moved it there when it turned out to be the estate's third copy (`ERRATUM 636`). -/

/-- The form the bridge is actually used in: `w` cleared of its inverse.
**THE BRIDGE ITSELF IS NO LONGER IN THIS FILE.** Its first draft proved
`zeta_pow_eq_exp_nat` and `zeta_pow_add_inv_nat` here, and each turned out to be one of THREE
copies in the estate — `ERRATUM 634` and `ERRATUM 636`. Unit 108 moved the hypothesis-free forms to
`CycleLaplacianSpectrum`, where `zeta` is defined and which this file already imports, and deleted
both local copies; `CycleLaplacianSpectrum.zeta_pow_add_inv_nat` is what this proof now calls. -/
theorem mul_self_add_one (N k : ℕ) :
    CycleLaplacianSpectrum.zeta N ^ k * ((2 * Real.cos (2 * Real.pi * (k : ℝ) / (N : ℝ)) : ℝ) : ℂ)
      = (CycleLaplacianSpectrum.zeta N ^ k) ^ 2 + 1 := by
  have hne : CycleLaplacianSpectrum.zeta N ^ k ≠ 0 :=
    pow_ne_zero _ (CycleLaplacianSpectrum.zeta_ne_zero N)
  rw [← CycleLaplacianSpectrum.zeta_pow_add_inv_nat N k, mul_add, mul_inv_cancel₀ hne]
  ring

/-- **THE QUARTIC.** `X⁴ + (1−N)X³ + (N−4)X² + (1−N)X + 1`, monic with integer coefficients — the
`ζ`-cleared form of the hub quadratic. -/
noncomputable def quartic (N : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ 4 + Polynomial.C (1 - (N : ℚ)) * Polynomial.X ^ 3
    + Polynomial.C ((N : ℚ) - 4) * Polynomial.X ^ 2
    + Polynomial.C (1 - (N : ℚ)) * Polynomial.X + 1

theorem quartic_natDegree (N : ℕ) : (quartic N).natDegree = 4 := by
  unfold quartic
  compute_degree!

theorem quartic_ne_zero (N : ℕ) : quartic N ≠ 0 := by
  intro h
  have hd := quartic_natDegree N
  rw [h, Polynomial.natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- **THE ALGEBRAIC CONSEQUENCE OF A COLLISION.** If `s` is real, satisfies the hub's shifted
integer quadratic, and equals `w + w⁻¹` for `w` a nonzero complex number, then `w` is a root of the
quartic. Pure algebra: multiply the quadratic by `w²`. -/
theorem aeval_quartic_eq_zero {N : ℕ} {w : ℂ} {s : ℝ}
    (hws : w * (s : ℂ) = w ^ 2 + 1)
    (hsq : s ^ 2 + (1 - (N : ℝ)) * s + ((N : ℝ) - 6) = 0) :
    Polynomial.aeval w (quartic N) = 0 := by
  have hsqC : (s : ℂ) ^ 2 + (1 - (N : ℂ)) * (s : ℂ) + ((N : ℂ) - 6) = 0 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hsq
    push_cast at this
    exact this
  simp only [quartic, map_add, map_mul, map_pow, Polynomial.aeval_X,
    map_sub, map_one, map_natCast, map_ofNat]
  linear_combination w ^ 2 * hsqC - (w * (s : ℂ) + w ^ 2 + 1 + (1 - (N : ℂ)) * w) * hws

/-! ## the degree step: a root of unity annihilated by a quartic has small order

This is the one step that needs a library fact rather than algebra, and the fact is one unit 100
already used: a primitive `m`-th root of unity's minimal polynomial over `ℚ` is the `m`-th
cyclotomic polynomial, whose degree is `φ m`. `RE-SWEEP #62` looked for the degree of
`ℚ(cos 2π/N)` and did not find it; that is a different and harder object, and the route does not
need it (`ERRATUM 632`). -/

/-- **THE DEGREE STEP.** A root of unity annihilated by the quartic has `φ` of its order at most
four. `IsPrimitiveRoot.orderOf` needs no hypothesis — `orderOf w` is the right `m` by
construction — so the only side condition is that `w` has finite order at all. -/
theorem totient_orderOf_le_four {N : ℕ} {w : ℂ} (hfin : IsOfFinOrder w)
    (hq : Polynomial.aeval w (quartic N) = 0) : Nat.totient (orderOf w) ≤ 4 := by
  have hord : IsPrimitiveRoot w (orderOf w) := IsPrimitiveRoot.orderOf w
  have hpos : 0 < orderOf w := orderOf_pos_iff.2 hfin
  have hdvd : minpoly ℚ w ∣ quartic N := minpoly.dvd ℚ w hq
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hord hpos] at hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd (quartic_ne_zero N)
  rwa [Polynomial.natDegree_cyclotomic, quartic_natDegree] at hle

/-- **AND SO THE ORDER IS AT MOST TWELVE**, by unit 107 rung one. -/
theorem orderOf_le_twelve {N : ℕ} {w : ℂ} (hfin : IsOfFinOrder w)
    (hq : Polynomial.aeval w (quartic N) = 0) : orderOf w ≤ 12 :=
  TotientSmall.le_twelve_of_totient_le_four (orderOf_pos_iff.2 hfin)
    (totient_orderOf_le_four hfin hq)

/-- **AND IT IS ONE OF NINE VALUES.** The `Finset` form is what the case analysis below consumes:
`m ≤ 12` alone would leave `7`, `9` and `11` to refute separately, and they are refuted by `φ`,
not by arithmetic on `N`. -/
theorem orderOf_mem_nine {N : ℕ} {w : ℂ} (hfin : IsOfFinOrder w)
    (hq : Polynomial.aeval w (quartic N) = 0) :
    orderOf w ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) :=
  (TotientSmall.totient_le_four_iff (orderOf_pos_iff.2 hfin)).1 (totient_orderOf_le_four hfin hq)

/-! ## the relation each admissible order forces on `w`

Nine orders survive the degree step. For each, the cyclotomic relation is got by hand from
`w ^ m = 1` and the non-vanishing of one lower power — elementary factoring, no cyclotomic
polynomial evaluated. Writing them out is cheaper than invoking `cyclotomic` at nine concrete
values and having to compute each one. -/

section Relations

variable {w : ℂ}

/-- A complex number of finite order is nonzero. -/
theorem ne_zero_of_orderOf_pos (h : 0 < orderOf w) : w ≠ 0 := by
  intro h0
  have h1 : w ^ orderOf w = 1 := pow_orderOf_eq_one w
  rw [h0] at h1 h
  rw [zero_pow h.ne'] at h1
  exact zero_ne_one h1

theorem rel_one (hm : orderOf w = 1) : w = 1 := orderOf_eq_one_iff.1 hm

theorem rel_two (hm : orderOf w = 2) : w = -1 := by
  have h1 : w ^ 2 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hm; omega
  have hfac : (w - 1) * (w + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · linear_combination h

theorem rel_three (hm : orderOf w = 3) : w ^ 2 + w + 1 = 0 := by
  have h1 : w ^ 3 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hm; omega
  have hfac : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

theorem rel_four (hm : orderOf w = 4) : w ^ 2 + 1 = 0 := by
  have h1 : w ^ 4 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hfac : (w ^ 2 - 1) * (w ^ 2 + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

theorem rel_five (hm : orderOf w = 5) : w ^ 4 + w ^ 3 + w ^ 2 + w + 1 = 0 := by
  have h1 : w ^ 5 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hm; omega
  have hfac : (w - 1) * (w ^ 4 + w ^ 3 + w ^ 2 + w + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

theorem rel_six (hm : orderOf w = 6) : w ^ 2 - w + 1 = 0 := by
  have h1 : w ^ 6 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have h3 : w ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hfac : (w ^ 3 - 1) * (w ^ 3 + 1) = 0 := by linear_combination h1
  have hcube : w ^ 3 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact h
  have hfac2 : (w + 1) * (w ^ 2 - w + 1) = 0 := by linear_combination hcube
  rcases mul_eq_zero.1 hfac2 with h | h
  · exact absurd (show w ^ 2 = 1 by linear_combination (w - 1) * h) h2
  · exact h

theorem rel_eight (hm : orderOf w = 8) : w ^ 4 + 1 = 0 := by
  have h1 : w ^ 8 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hfac : (w ^ 4 - 1) * (w ^ 4 + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact h

theorem rel_ten (hm : orderOf w = 10) : w ^ 4 - w ^ 3 + w ^ 2 - w + 1 = 0 := by
  have h1 : w ^ 10 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h2 : w ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have h5 : w ^ 5 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hfac : (w ^ 5 - 1) * (w ^ 5 + 1) = 0 := by linear_combination h1
  have hfive : w ^ 5 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h5
    · exact h
  have hfac2 : (w + 1) * (w ^ 4 - w ^ 3 + w ^ 2 - w + 1) = 0 := by linear_combination hfive
  rcases mul_eq_zero.1 hfac2 with h | h
  · exact absurd (show w ^ 2 = 1 by linear_combination (w - 1) * h) h2
  · exact h

theorem rel_twelve (hm : orderOf w = 12) : w ^ 4 - w ^ 2 + 1 = 0 := by
  have h1 : w ^ 12 = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have h4 : w ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have h6 : w ^ 6 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hfac : (w ^ 6 - 1) * (w ^ 6 + 1) = 0 := by linear_combination h1
  have hsix : w ^ 6 + 1 = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) h6
    · exact h
  have hfac2 : (w ^ 2 + 1) * (w ^ 4 - w ^ 2 + 1) = 0 := by linear_combination hsix
  rcases mul_eq_zero.1 hfac2 with h | h
  · exact absurd (show w ^ 4 = 1 by linear_combination (w ^ 2 - 1) * h) h4
  · exact h

end Relations

/-! ## the case analysis: nine orders, one surviving side

`ERRATUM 632` ran this table by hand and `ERRATUM 633` corrects two of its entries. What follows is
the table PROVED, one order at a time. Five orders die on the real quadratic alone, one dies on
`orderOf w ∣ N`, two die on integrality after a `ℕ`-valued bound, and one — order three — survives
and pins the side at exactly three. -/

/-- **THE ARITHMETIC HEART OF UNIT 107.** If a root of unity's `w + w⁻¹` satisfies the hub's
shifted quadratic at side `N ≥ 3`, then `N = 3`.

The hypotheses are exactly what a collision supplies and nothing more: `w ^ N = 1` (the rim's
frequency is an `N`-th root of unity), `w * s = w² + 1` (`s = w + w⁻¹`, cleared of the inverse),
and the shifted quadratic. Note `w`'s ORDER is never assumed — it is computed. -/
theorem side_eq_three_of_root {N : ℕ} {w : ℂ} {s : ℝ} (hN : 3 ≤ N)
    (hpow : w ^ N = 1) (hws : w * (s : ℂ) = w ^ 2 + 1)
    (hsq : s ^ 2 + (1 - (N : ℝ)) * s + ((N : ℝ) - 6) = 0) : N = 3 := by
  have hfin : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.2 ⟨N, by omega, hpow⟩
  have hpos : 0 < orderOf w := orderOf_pos_iff.2 hfin
  have hw0 : w ≠ 0 := ne_zero_of_orderOf_pos hpos
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  have hdvd : orderOf w ∣ N := orderOf_dvd_of_pow_eq_one hpow
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmem := orderOf_mem_nine hfin (aeval_quartic_eq_zero hws hsq)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hm | hm | hm | hm | hm | hm | hm | hm | hm
  -- order 1: `w = 1`, so `s = 2`, and the quadratic forces `N = 0`.
  · have hs : s = 2 := by
      have h0 : ((s : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
        rw [rel_one hm] at hws; push_cast; linear_combination hws
      exact_mod_cast h0
    rw [hs] at hsq; exfalso; linarith
  -- order 2: `w = -1`, so `s = -2`, and the quadratic forces `3N = 4`.
  · have hs : s = -2 := by
      have h0 : ((s : ℝ) : ℂ) = ((-2 : ℝ) : ℂ) := by
        rw [rel_two hm] at hws; push_cast; linear_combination -hws
      exact_mod_cast h0
    rw [hs] at hsq; exfalso; linarith
  -- order 3: `w² + w + 1 = 0`, so `s = -1`, and the quadratic forces `N = 3`. THE COLLISION.
  · have key : w * ((s : ℂ) + 1) = 0 := by linear_combination hws + rel_three hm
    have hs : s = -1 := by
      have h0 : ((s : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw0
        · push_cast; linear_combination h
      exact_mod_cast h0
    rw [hs] at hsq
    have : (N : ℝ) = 3 := by linarith
    exact_mod_cast this
  -- order 4: `w² = -1`, so `s = 0`, and the quadratic forces `N = 6` — which `4 ∣ N` forbids.
  · have key : w * (s : ℂ) = 0 := by rw [hws]; exact rel_four hm
    have hs : s = 0 := by
      have h0 : (s : ℂ) = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw0
        · exact h
      exact_mod_cast h0
    rw [hs] at hsq
    have hN6 : N = 6 := by
      have : (N : ℝ) = 6 := by linarith
      exact_mod_cast this
    rw [hm, hN6] at hdvd
    exfalso; omega
  -- order 5: `s² + s - 1 = 0`, so `N² - 15N + 25 = 0`, which has no natural root.
  · have key : w ^ 2 * ((s : ℂ) ^ 2 + (s : ℂ) - 1) = 0 := by
      linear_combination (w * (s : ℂ) + w ^ 2 + 1 + w) * hws + rel_five hm
    have hrel : s ^ 2 + s - 1 = 0 := by
      have h0 : (s : ℂ) ^ 2 + (s : ℂ) - 1 = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw2
        · exact h
      have h1 : ((s ^ 2 + s - 1 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h0
      exact_mod_cast h1
    have hns : (N : ℝ) * s = (N : ℝ) - 5 := by linear_combination hrel - hsq
    have hquad : (N : ℝ) ^ 2 - 15 * (N : ℝ) + 25 = 0 := by
      linear_combination ((N : ℝ) ^ 2) * hrel - ((N : ℝ) * s + 2 * (N : ℝ) - 5) * hns
    have hnat : N * N + 25 = 15 * N := by
      have hr : ((N * N + 25 : ℕ) : ℝ) = ((15 * N : ℕ) : ℝ) := by
        push_cast; linear_combination hquad
      exact_mod_cast hr
    have hub : (N : ℝ) ≤ 15 := by nlinarith [hquad, hNR]
    have hub' : N ≤ 15 := by exact_mod_cast hub
    interval_cases N <;> omega
  -- order 6: `w² - w + 1 = 0`, so `s = 1`, and the quadratic degenerates to `-4 = 0`.
  · have key : w * ((s : ℂ) - 1) = 0 := by linear_combination hws + rel_six hm
    have hs : s = 1 := by
      have h0 : ((s : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw0
        · push_cast; linear_combination h
      exact_mod_cast h0
    rw [hs] at hsq; exfalso; linarith
  -- order 8: `s² = 2`, so `N² + 4N - 14 = 0`, impossible for `N ≥ 3`.
  · have key : w ^ 2 * ((s : ℂ) ^ 2 - 2) = 0 := by
      linear_combination (w * (s : ℂ) + w ^ 2 + 1) * hws + rel_eight hm
    have hrel : s ^ 2 - 2 = 0 := by
      have h0 : (s : ℂ) ^ 2 - 2 = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw2
        · exact h
      have h1 : ((s ^ 2 - 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h0
      exact_mod_cast h1
    have hns : ((N : ℝ) - 1) * s = (N : ℝ) - 4 := by linear_combination hrel - hsq
    have hquad : (N : ℝ) ^ 2 + 4 * (N : ℝ) - 14 = 0 := by
      linear_combination (-(((N : ℝ) - 1) ^ 2)) * hrel + (((N : ℝ) - 1) * s + (N : ℝ) - 4) * hns
    exfalso; nlinarith [hquad, hNR]
  -- order 10: `s² - s - 1 = 0`, so `N² = N + 11`, which has no natural root.
  · have key : w ^ 2 * ((s : ℂ) ^ 2 - (s : ℂ) - 1) = 0 := by
      linear_combination (w * (s : ℂ) + w ^ 2 + 1 - w) * hws + rel_ten hm
    have hrel : s ^ 2 - s - 1 = 0 := by
      have h0 : (s : ℂ) ^ 2 - (s : ℂ) - 1 = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw2
        · exact h
      have h1 : ((s ^ 2 - s - 1 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h0
      exact_mod_cast h1
    have hns : ((N : ℝ) - 2) * s = (N : ℝ) - 5 := by linear_combination hrel - hsq
    have hquad : (N : ℝ) ^ 2 - (N : ℝ) - 11 = 0 := by
      linear_combination (-(((N : ℝ) - 2) ^ 2)) * hrel + (((N : ℝ) - 2) * s - 3) * hns
    have hnat : N * N = N + 11 := by
      have hr : ((N * N : ℕ) : ℝ) = ((N + 11 : ℕ) : ℝ) := by push_cast; linear_combination hquad
      exact_mod_cast hr
    have hub : (N : ℝ) ≤ 4 := by nlinarith [hquad, hNR]
    have hub' : N ≤ 4 := by exact_mod_cast hub
    interval_cases N <;> omega
  -- order 12: `s² = 3`, so `N² = 3`, impossible for `N ≥ 3`.
  · have key : w ^ 2 * ((s : ℂ) ^ 2 - 3) = 0 := by
      linear_combination (w * (s : ℂ) + w ^ 2 + 1) * hws + rel_twelve hm
    have hrel : s ^ 2 - 3 = 0 := by
      have h0 : (s : ℂ) ^ 2 - 3 = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact absurd h hw2
        · exact h
      have h1 : ((s ^ 2 - 3 : ℝ) : ℂ) = 0 := by push_cast; linear_combination h0
      exact_mod_cast h1
    have hns : ((N : ℝ) - 1) * s = (N : ℝ) - 3 := by linear_combination hrel - hsq
    have hquad : 2 * ((N : ℝ) ^ 2 - 3) = 0 := by
      linear_combination (-(((N : ℝ) - 1) ^ 2)) * hrel + (((N : ℝ) - 1) * s + (N : ℝ) - 3) * hns
    exfalso; nlinarith [hquad, hNR]

/-! ## the deliverable: the non-collision holds at every side but the smallest -/

/-- **THE HYPOTHESIS UNIT 92 COULD NOT DISCHARGE, DISCHARGED — AT EVERY SIDE BUT ONE.**
`hubRootMinus (n+3) 2 ∉ rimSet n` holds for every `n ≠ 0`, and unit 91's `hubRootMinus 3 2 = 2`
shows it is FALSE at `n = 0`: the triangle's wheel is `K₄`, where the hub root sits exactly on
the rim. So `n ≠ 0` is not a convenience — it is the exact hypothesis, and
`hubRootMinus_notMem_rimSet_iff` below says so as an iff.

Note the INDEX. `WheelTable` parametrises by `n` with side `N = n + 3`, and
`hubRootMinus_notMem_rimSet_one` is unit 92's witness at `n = 1`, side four. The collision is at
side THREE, which is `n = 0`. `ERRATUM 632` stated the answer as `n = 3` because it wrote the
quadratic in the base size and the rim in the shifted index; `ERRATUM 633` records that. -/
theorem hubRootMinus_notMem_rimSet_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    hubRootMinus (n + 3) 2 ∉ rimSet n := by
  intro hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  have hhub : hubRootMinus (n + 3) 2
      = 3 + 2 * Real.cos (2 * Real.pi * (k : ℝ) / ((n + 3 : ℕ) : ℝ)) := by
    rw [← hk, rimVal]
  have hpow : (CycleLaplacianSpectrum.zeta (n + 3) ^ k) ^ (n + 3) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, CycleLaplacianSpectrum.zeta_pow_card (by omega), one_pow]
  have h3 := side_eq_three_of_root (N := n + 3) (by omega) hpow
    (mul_self_add_one (n + 3) k) (shifted_quadratic hhub)
  omega

/-! ## the table, with the hypothesis gone

`WheelTable`'s eleven conditional declarations are KEPT exactly as they stand (`ERRATUM 94`,
unit 104's precedent). Unit 92's hypothesised form is not superseded: it is the statement a reader
needs at `n = 0`, where the hypothesis is false and the conclusions fail. What follows restates the
five that carry the table's mathematical content, with `hcol` replaced by `n ≠ 0`. -/

/-- **THE TABLE, UNCONDITIONAL OFF `n = 0`.** -/
theorem finrank_coneEig_eq_wheelMult_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∀ v ∈ wheelSet n, Module.finrank ℝ (coneEig (cycleGraph (n + 3)) v) = wheelMult n v :=
  WheelTable.finrank_coneEig_eq_wheelMult n (hubRootMinus_notMem_rimSet_of_ne_zero hn)

/-- **THE RIM MULTIPLICITY IS EXACTLY TWO**, with no hypothesis beyond `n ≠ 0`. -/
theorem finrank_coneEig_rimVal_of_ne_zero {n : ℕ} (hn : n ≠ 0)
    {k : ℕ} (hk : k ≠ 0) (hkN : k < n + 3) (hone : 2 * k ≠ n + 3) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n k)) = 2 :=
  WheelTable.finrank_coneEig_rimVal n (hubRootMinus_notMem_rimSet_of_ne_zero hn) hk hkN hone

/-- **AND EXACTLY ONE AT THE HALF TURN.** -/
theorem finrank_coneEig_rimVal_half_of_ne_zero {n : ℕ} (hn : n ≠ 0)
    {k : ℕ} (hk : 2 * k = n + 3) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n k)) = 1 :=
  WheelTable.finrank_coneEig_rimVal_half n (hubRootMinus_notMem_rimSet_of_ne_zero hn) hk

/-- **AND THE LOWER HUB ROOT IS SIMPLE.** Unit 83 gave `1 ≤`; unit 92 gave the equality under a
hypothesis; this gives it off `n = 0`, and `n = 0` is where it genuinely fails. -/
theorem finrank_coneEig_hubRootMinus_eq_one_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (hubRootMinus (n + 3) 2)) = 1 :=
  WheelTable.finrank_coneEig_hubRootMinus_eq_one n (hubRootMinus_notMem_rimSet_of_ne_zero hn)

/-- **THE SPECTRUM, AS A SET EQUALITY, WITH NO HYPOTHESIS BEYOND `n ≠ 0`.** The wheel on `n + 4`
vertices has exactly the eigenvalues `wheelSet` lists, for every `n ≠ 0`. -/
theorem wheel_spectrum_eq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    {lam : ℝ | ∃ x, x ≠ 0 ∧
        signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x} = ↑(wheelSet n) :=
  WheelTable.wheel_spectrum_eq n (hubRootMinus_notMem_rimSet_of_ne_zero hn)

/-! ## and `λ₂` loses its hypothesis outright

Unit 93's three declarations take `hcol` **and** `hn : 1 ≤ n`. Since `1 ≤ n` already says `n ≠ 0`,
`hcol` is now redundant in exactly those two of the three: `isGreatest_wheel_second` and
`le_rimVal_one_of_eigen_of_ne` become **unconditional on their own existing binder**, with no side
condition added. That is a hypothesis removed rather than traded, and it is the only place in this
cluster where the trade is free. -/

/-- **EVERYTHING BUT THE TOP IS AT OR BELOW THE RIM'S LARGEST VALUE**, with `hcol` gone and no new
hypothesis: unit 93's `1 ≤ n` already implies `n ≠ 0`. -/
theorem le_rimVal_one_of_eigen_of_ne_uncond {n : ℕ} (hn : 1 ≤ n)
    {lam : ℝ} {x : Option (Fin (n + 3)) → ℝ} (hx0 : x ≠ 0)
    (hx : signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (n + 3) 2) : lam ≤ rimVal n 1 :=
  WheelSecondEigen.le_rimVal_one_of_eigen_of_ne n
    (hubRootMinus_notMem_rimSet_of_ne_zero (by omega)) hn hx0 hx hne

/-- **THE WHEEL'S SECOND EIGENVALUE IS `3 + 2cos(2π/N)`, UNCONDITIONALLY.** Unit 93 proved this
under `hcol`; `hcol` is now a consequence of the `1 ≤ n` it already assumed, so the `IsGreatest`
statement stands on that binder alone. -/
theorem isGreatest_wheel_second_uncond {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {lam : ℝ | (∃ x, x ≠ 0 ∧
        signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
      ∧ lam ≠ hubRootPlus (n + 3) 2} (rimVal n 1) :=
  WheelSecondEigen.isGreatest_wheel_second n
    (hubRootMinus_notMem_rimSet_of_ne_zero (by omega)) hn

/-- And its multiplicity is exactly two. This one really does need `n ≠ 0` supplied, because unit
93 stated it without an `hn` — at `n = 0` the value `rimVal 0 1 = 2` has multiplicity three. -/
theorem finrank_coneEig_rimVal_one_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n 1)) = 2 :=
  WheelSecondEigen.finrank_coneEig_rimVal_one n (hubRootMinus_notMem_rimSet_of_ne_zero hn)

/-! ## and the side condition is exactly right, not defensively chosen

`ERRATUM 13`'s discipline: a conditional theorem whose hypothesis is never tested is a theorem
about nothing. Unit 91 already proved the collision AT the triangle, so the converse costs two
lines and the deliverable can be stated as an iff. -/

/-- **THE COLLISION AT `n = 0`, AS A MEMBERSHIP.** Unit 91's `hubRootMinus_eq_rim_three` puts the
hub's lower root exactly on the triangle's rim; this is that, folded into `rimSet`. -/
theorem hubRootMinus_mem_rimSet_zero : hubRootMinus (0 + 3) 2 ∈ rimSet 0 := by
  have h : hubRootMinus (0 + 3) 2 = rimVal 0 1 := by
    rw [rimVal, WheelHubCollision.hubRootMinus_eq_rim_three]
    norm_num
  rw [h]
  exact rimVal_mem_rimSet 0 (by omega) (by omega)

/-- **SO THE NON-COLLISION HOLDS PRECISELY OFF `n = 0`.** The iff, which is what makes `n ≠ 0` the
hypothesis rather than a hypothesis. -/
theorem hubRootMinus_notMem_rimSet_iff {n : ℕ} :
    hubRootMinus (n + 3) 2 ∉ rimSet n ↔ n ≠ 0 := by
  refine ⟨fun h hn => ?_, hubRootMinus_notMem_rimSet_of_ne_zero⟩
  subst hn
  exact h hubRootMinus_mem_rimSet_zero

/-- **AND THE `n ≠ 0` ON THE `λ₂` MULTIPLICITY IS NECESSARY TOO: AT `n = 0` IT IS THREE.** This is
not a new computation — it is unit 91's `finrank_coneEig_hubRootMinus_three` read at `rimVal`,
which is legitimate exactly because the two values coincide there. -/
theorem finrank_coneEig_rimVal_one_zero :
    Module.finrank ℝ (coneEig (cycleGraph 3) (rimVal 0 1)) = 3 := by
  have hval : rimVal 0 1 = hubRootMinus 3 2 := by
    rw [rimVal, WheelHubCollision.hubRootMinus_eq_rim_three]
    norm_num
  rw [hval]
  exact WheelHubCollision.finrank_coneEig_hubRootMinus_three

end WheelCollision
