/-
  TorusSideNine: side 9 FAILS the criterion — so "odd" is not it, composite odd sides are not
  covered by unit 100, and the identity unit 100 said this estate did not have is used here to
  prove it

  WHY THIS FILE EXISTS. Unit 100 proved every ODD PRIME side tight and recorded, as a measurement
  rather than a theorem, that side 9 is tight at `d = 2` and **not** tight at `d = 3`. It also
  said the proof *needs `∑_{j<9} cos(2πj/9) = 0`, which this estate does not have.* **The estate
  has it, and `ERRATUM 627` is that mistake.** `WheelSpectrum.sum_rchi_eq_zero` is
  `∑ⱼ Re(ζ^{kj}) = 0` for `k ≠ 0`; at `k = 1` it is exactly that sum, and `sum_cosCls_eq_zero`
  below is three rewrites away from it. So this unit both lands the theorem and spends the
  identity whose absence was claimed.

  **CHECKED ABSENT BEFORE BEING WRITTEN, BY THE RULE `ERRATUM 627` ADDED — the BODY, not the
  name.** `grep -rn` over every estate `.lean` for `Real.cos (2 * Real.pi * … / 9)` returns
  nothing outside this file, and `awk` over `estate_types.txt` (14687 statements, 1119 modules)
  for each of the fifteen names below returns nothing. The general identity `sum_cosCls_eq_zero`
  is **not** claimed new as mathematics: it is `WheelSpectrum`'s theorem in this chain's
  vocabulary, and the docstring says so.

  WHAT IS PROVED.

  * **`sum_cosCls_eq_zero`** — `∑_{c<n} cos(2πc/n) = 0` at every side, off
    `WheelSpectrum.sum_rchi_eq_zero` at `k = 1` through `CycleLaplacianSpectrum.zeta_pow_eq_exp`
    and `Complex.exp_ofReal_mul_I_re`. `sum_cos_range` is the `Finset.range` form the computation
    below needs.
  * **`cosCls_mirror`** — `a + b = n` gives equal class cosines, off unit 90's
    `CycleEigenvalueDistinct.cos_reflect`. **That leaf file was written Mathlib-only so the torus
    chain could consume it; this is its third consumer**, after units 94 and 97.
  * **`cn`, `cosCls_six_eq`, `sum_cn`, `cn_mirror`, `cn_zero`, `cn_three`** — the side-9 cosines
    as a function of a natural, so the nine-term expansion is a `Finset.range` sum rather than a
    chain of `Fin.succ`.
  * **`cn_one_two_four`** — **THE COINCIDENCE**: `cos(2π/9) + cos(4π/9) + cos(8π/9) = 0`. The
    full-turn sum is `1 + 2(c₁ + c₂ + c₃ + c₄)` by the mirror, and `c₃ = cos(2π/3) = −1/2` cancels
    the `1`. This is an identity about the ninth roots of unity and it is what makes side 9 fail.
  * **`rn`, `relNine`, `not_noCosRelation_six`** — the relation `(1, −1, −1, 2, −1, 0, 0, 0, 0)`:
    coefficients summing to zero, supported on the pair classes, and cosine-weighted sum zero by
    the line above. So **side 9 does not satisfy unit 98's criterion**, and
    **`exists_not_tight_side_nine`**: there is a dimension at which the bound is not an equality.
  * **`sum_relNine_toNat`** — and the relation's positive part sums to `3`, so **unit 98's
    converse construction produces `d = 3`** — the dimension brute force measures as the first at
    which side 9 fails. The prediction and the measurement agree, which is the only test that
    construction has had.

  **WHAT THE SIDES NOW SAY.** `3` tight, `4` not, `5` tight, `6` not, every odd prime tight,
  `9` not. So the answer is not *odd*, not *prime-or-not* in any simple reading, and not monotone.
  The criterion is unit 98's and nothing shorter has been found.

  WHAT IS **NOT** CLAIMED.

  * **THAT SIDE 9 IS TIGHT AT `d = 2`. That is measured and NOT proved**, and it is the one clause
    of this unit's own headline that has no theorem behind it. Proving it needs the relation
    lattice at side 9 — no non-zero relation has positive part summing to `2` or less — which
    needs the degree of `ℚ(cos 2π/9)`, a fact about the ninth cyclotomic field that this estate
    does not have and that this unit does not attempt. **No cost is offered** (`ERRATUM 194`,
    `ERRATUM 246`).
  * **NOTHING ABOUT WHICH FREQUENCIES FAIL AT SIDE 9.** `exists_not_tight_side_nine` gives a
    dimension, not a frequency, and `TorusCosRelation.orbit_eq_nuRFibre_zero` shows the ground
    state is tight there anyway.
  * **NO GENERAL COMPOSITE-SIDE STATEMENT.** Side 9 is one composite odd side; `15`, `21`, `25`
    and the rest are untouched, and the general question is still which sides satisfy
    `NoCosRelation`, which is the classification of vanishing sums of roots of unity.
  * **NO UPPER BOUND ON ANY MULTIPLICITY AT SIDE 9**, and no evaluation of any dimension there.
  * **NOTHING OVER `ℂ` ABOUT THE GRAPH, NOTHING ABOUT THE BOX, THE CASCADE, THE SPINE OR ANY
    WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusPrimeSide
import WheelSpectrum
import CycleEigenvalueDistinct

namespace TorusSideNine

open Finset BoxGraph TorusCosRelation TorusPrimeSide
open CycleLaplacianSpectrum WheelSpectrum
open Real

variable {N : ℕ}

/-- **THE COSINES AROUND A FULL TURN SUM TO ZERO** — the identity unit 100 wrongly recorded as
absent (`ERRATUM 627`). It is `WheelSpectrum.sum_rchi_eq_zero` at `k = 1`. -/
theorem sum_cosCls_eq_zero (N : ℕ) : ∑ c : Fin (N + 3), cosCls N c = 0 := by
  have h1 : (1 : Fin (N + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have h := WheelSpectrum.sum_rchi_eq_zero N 1 h1
  rw [← h]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [rchi, chi, Fin.val_one, mul_one, zeta_pow_eq_exp, Complex.exp_ofReal_mul_I_re, cosCls]

/-- **THE MIRROR**, off unit 90's `CycleEigenvalueDistinct.cos_reflect`. -/
theorem cosCls_mirror {a b : ℕ} (ha : a < N + 3) (hb : b < N + 3) (hab : a + b = N + 3) :
    cosCls N (⟨a, ha⟩ : Fin (N + 3)) = cosCls N (⟨b, hb⟩ : Fin (N + 3)) := by
  have hrefl := CycleEigenvalueDistinct.cos_reflect (N := N + 3) (by omega) (k := b) (by omega)
  rw [cosCls_eq, cosCls_eq]
  have hsub : ((N + 3 - b : ℕ)) = a := by omega
  rw [hsub] at hrefl
  exact hrefl

theorem sum_cos_range (N : ℕ) :
    ∑ j ∈ Finset.range (N + 3), Real.cos (2 * Real.pi * (j : ℝ) / ((N : ℝ) + 3)) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Real.cos (2 * Real.pi * (j : ℝ) / ((N : ℝ) + 3))) (N + 3), ← sum_cosCls_eq_zero N]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cosCls]

/-! ## side 9 -/

noncomputable def cn (j : ℕ) : ℝ := Real.cos (2 * Real.pi * (j : ℝ) / 9)

theorem cosCls_six_eq (c : Fin 9) : cosCls 6 c = cn (c : ℕ) := by
  rw [cosCls, cn]
  norm_num

theorem sum_cn : ∑ j ∈ Finset.range 9, cn j = 0 := by
  have h := sum_cos_range 6
  rw [show (6 : ℕ) + 3 = 9 from rfl] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cn]
  norm_num

theorem cn_mirror {a b : ℕ} (ha : a < 9) (hb : b < 9) (hab : a + b = 9) : cn a = cn b := by
  have h := cosCls_mirror (N := 6) (a := a) (b := b) (by omega) (by omega) (by omega)
  rw [cosCls_six_eq, cosCls_six_eq] at h
  exact h

theorem cn_zero : cn 0 = 1 := by
  rw [cn]; norm_num

theorem cn_three : cn 3 = -(1 / 2) := by
  rw [cn]
  have he : 2 * Real.pi * ((3 : ℕ) : ℝ) / 9 = Real.pi - Real.pi / 3 := by push_cast; ring
  rw [he, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- **THE COINCIDENCE AT SIDE 9**: the three interior classes not fixed by the mirror sum to
zero. This is what makes the relation below vanish. -/
theorem cn_one_two_four : cn 1 + cn 2 + cn 4 = 0 := by
  have h := sum_cn
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [cn_mirror (a := 5) (b := 4) (by omega) (by omega) (by omega),
    cn_mirror (a := 6) (b := 3) (by omega) (by omega) (by omega),
    cn_mirror (a := 7) (b := 2) (by omega) (by omega) (by omega),
    cn_mirror (a := 8) (b := 1) (by omega) (by omega) (by omega), cn_zero, cn_three] at h
  linarith

/-- The relation at side `9`: `1·1 − c₁ − c₂ + 2·(−1/2) − c₄ = 0`, coefficients summing to
zero. **Its positive part sums to `3`**, which is the dimension unit 98's construction produces. -/
def rn : ℕ → ℤ :=
  fun j => if j = 0 then 1 else if j = 1 then -1 else if j = 2 then -1
    else if j = 3 then 2 else if j = 4 then -1 else 0

def relNine : Fin 9 → ℤ := fun c => rn (c : ℕ)

theorem not_noCosRelation_six : ¬ NoCosRelation 6 := by
  intro h
  have hsupp : ∀ j : Fin 9, 6 + 3 < 2 * (j : ℕ) → relNine j = 0 := by
    intro j hj
    have := j.isLt
    fin_cases j <;> simp_all [relNine, rn]
  have hsum : ∑ j, relNine j = 0 := by decide
  have hcos : ∑ c : Fin 9, (relNine c : ℝ) * cosCls 6 c = 0 := by
    have hre : ∀ c : Fin 9, (relNine c : ℝ) * cosCls 6 c = ((rn (c : ℕ) : ℤ) : ℝ) * cn (c : ℕ) := by
      intro c
      rw [relNine, cosCls_six_eq]
    rw [Finset.sum_congr rfl (fun c _ => hre c),
      Fin.sum_univ_eq_sum_range (fun j => ((rn j : ℤ) : ℝ) * cn j) 9]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [cn_zero, cn_three]
    norm_num [rn]
    linarith [cn_one_two_four]
  have h0 := h relNine hsupp hsum hcos 0
  simp [relNine, rn] at h0

/-- **SO AT SIDE 9 THE BOUND IS NOT AN EQUALITY AT EVERY DIMENSION.** -/
theorem exists_not_tight_side_nine (m : ℝ) :
    ∃ (D : ℕ) (k : Site D (6 + 3)),
      TorusHyperoctahedral.orbit k ≠ TorusBoundTightIff.nuRFibre 6 m k := by
  by_contra hc
  refine not_noCosRelation_six ((noCosRelation_iff 6 m).2 ?_)
  intro D k
  by_contra hk
  exact hc ⟨D, k, hk⟩

/-- **AND THE CONSTRUCTION LANDS AT `d = 3`** — the dimension brute force measures as the first
at which side 9 fails. -/
theorem sum_relNine_toNat : ∑ j, (relNine j).toNat = 3 := by decide

end TorusSideNine
