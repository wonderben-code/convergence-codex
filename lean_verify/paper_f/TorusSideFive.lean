/-
  TorusSideFive: side 5 satisfies unit 98's criterion — the first tightness in this chain whose
  proof needs an IRRATIONALITY — the side-5 eigenspace dimension as a number, and side 6 failing,
  so the answer is not monotone in the side

  WHY THIS FILE EXISTS. Unit 98 reduced `L102`'s general question to an arithmetic condition on the
  side, `NoCosRelation N`, and then said in its own header and its own watchlist marker: *SIDE 5 IS
  STILL NOT PROVED, though it is now one arithmetic check rather than a unit … not done here, named
  so it is not rediscovered.* **This day has already produced three errata about one-step fences**
  (`ERRATUM 622`, `ERRATUM 626`, and the struck draft in `WheelTable`'s header), so the check is
  done rather than left standing. It is one unit and it needed something genuinely new.

  **WHY SIDE 5 IS NOT THE SAME KIND OF ARGUMENT AS SIDE 3.** At side 3 the class cosines are
  `1, −1/2`, both RATIONAL, and unit 97's proof is a two-value count with no arithmetic depth. At
  side 5 they are `1, (√5 − 1)/4, −(1 + √5)/4`, and the relation `a` collapses to
  `(4a₀ − a₁ − a₂) + (a₁ − a₂)·√5 = 0`, which forces `a = 0` **only because `√5` is irrational** —
  `a₁ = a₂` and then `2a₀ = a₁` and then `5a₀ = 0` off the zero-sum condition. So this is the first
  tightness statement in the chain that rests on a fact about `ℚ` rather than on counting, and
  `Nat.Prime.irrational_sqrt` is the import that carries it.

  WHAT IS PROVED.

  * **`irrational_sqrt_five`, `eq_zero_of_add_mul_sqrt_five`** — `A + B√5 = 0` with `A, B : ℤ`
    forces both zero, off `Nat.Prime.irrational_sqrt`, `Irrational.intCast_mul` and
    `Irrational.intCast_add`.
  * **`cosCls_two_zero/one/two`** — the three class cosines at side 5: `1`, `(√5 − 1)/4`,
    `−(1 + √5)/4`. The middle one is `Real.cos_two_mul` on Mathlib's `Real.cos_pi_div_five`, the
    last is `Real.cos_pi_sub` on it.
  * **`noCosRelation_two`** — **side 5 satisfies the criterion**, so by
    `TorusCosRelation.noCosRelation_iff` **the degeneracy bound is an equality at every dimension,
    every mass and every frequency of side 5** (`side_five_tight`), read off as
    `bound_eq_finrank_side_five`, `card_orbit_eq_finrank_side_five` and
    `card_orbitsOf_eq_one_side_five`.
  * **`finrank_side_five`** — **and the dimension as a NUMBER**:
    `2 ^ (d − c₀) · d! / (c₀! · c₁! · c₂!)`, where `cⱼ` counts the axes of class `j`. It is a
    **trinomial** where side 3's was a binomial, which is what makes it a second computation rather
    than a re-spelling: `card_interiorAxes_side_five` (every non-zero frequency is interior,
    because `2v = 5` has no solution) and `multinomial_side_five` (three classes carry every axis,
    so `Nat.multinomial`'s definition evaluates directly).
  * **`cosCls_three_*`, `relSix`, `not_noCosRelation_three`, `exists_not_tight_side_six`** — **AND
    SIDE 6 FAILS.** Its class cosines are `1, 1/2, −1/2, −1`, all rational, and
    `a = (1, −1, −1, 1)` is a relation. So the sequence of answers over the sides begins
    **tight, not, tight, not** — `ERRATUM 622`'s rule applied to the parameter rather than the
    size, which is `ERRATUM 626`'s own rule, and it is why all four are theorems here and in
    unit 97 rather than a measurement in a log entry.

  **WHAT THE FOUR SIDES TOGETHER SAY, AND IT IS NOT A PATTERN.** `3` tight, `4` not, `5` tight,
  `6` not — and the mechanism is visible in each: a side is tight exactly when its class cosines
  admit no vanishing integer relation of zero coefficient sum (unit 98), and the rational-valued
  sides `4` and `6` have obvious ones while `3` and `5` do not. **This is NOT evidence that odd
  sides are tight and even ones are not**, and no such claim is made: at side `7` the cosines
  generate a cubic field and the question is whether `1, cos(2π/7), cos(4π/7), cos(6π/7)` admit a
  zero-sum integer relation, which is a different computation from either of the two done here and
  **is not done**. No cost is offered (`ERRATUM 194`, `ERRATUM 246`).

  WHAT IS **NOT** CLAIMED.

  * **NOTHING AT ANY SIDE BUT 3, 4, 5 AND 6.** `NoCosRelation N` is undecided at every other side,
    deciding it in general is the classification of vanishing sums of roots of unity, and the pinned
    Mathlib has none (probed for unit 98 and recorded in `estateclaim_accepted.txt`).
  * **NO PER-FREQUENCY STATEMENT AT A FAILING SIDE.** `exists_not_tight_side_six` exhibits a
    dimension where the bound is strict and says nothing about which frequencies those are;
    `TorusCosRelation.orbit_eq_nuRFibre_zero` shows a failing side still has tight frequencies.
  * **NO UPPER BOUND ON ANY MULTIPLICITY AT A FAILING SIDE.**
  * **NO GENERAL FORMULA FOR THE DIMENSION AT A TIGHT SIDE.** Sides 3 and 5 are evaluated one at a
    time; `TorusCosRelation.bound_eq_finrank_of_noCosRelation` is the general statement and its
    right-hand side is `2 ^ |interiorAxes k| · multinomial`, which this file EVALUATES at side 5
    and nowhere else.
  * **NOTHING OVER `ℂ`, NOTHING ABOUT THE BOX, THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusCosRelation
import Mathlib.NumberTheory.Real.Irrational

namespace TorusSideFive

open Finset BoxGraph TorusHyperoctahedral TorusReflectionCount MassiveTorusSpectrum
open TorusBoundTightIff TorusOrbitInvariant TorusOrbitCharacterisation
open TorusFibreOrbitPartition TorusOrbitMultinomial TorusReflection GraphLaplacian
open TorusCosRelation
open Real

variable {d : ℕ}

theorem irrational_sqrt_five : Irrational (Real.sqrt 5) := by
  have hp : Nat.Prime 5 := by decide
  simpa using hp.irrational_sqrt

theorem eq_zero_of_add_mul_sqrt_five {A B : ℤ}
    (h : (A : ℝ) + (B : ℝ) * Real.sqrt 5 = 0) : A = 0 ∧ B = 0 := by
  have hB : B = 0 := by
    by_contra hB
    have h1 : Irrational ((B : ℝ) * Real.sqrt 5) := irrational_sqrt_five.intCast_mul hB
    have h2 : Irrational ((A : ℝ) + (B : ℝ) * Real.sqrt 5) := h1.intCast_add A
    rw [h] at h2
    exact h2.ne_zero rfl
  subst hB
  refine ⟨?_, rfl⟩
  simp only [Int.cast_zero, zero_mul, add_zero] at h
  exact_mod_cast h

theorem cosCls_two_zero : cosCls 2 0 = 1 := by
  rw [cosCls]
  norm_num

theorem cosCls_two_one : cosCls 2 1 = (Real.sqrt 5 - 1) / 4 := by
  rw [cosCls]
  have he : 2 * π * (((1 : Fin (2 + 3)) : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 3) = 2 * (π / 5) := by
    norm_num
    ring
  rw [he, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

theorem cosCls_two_two : cosCls 2 2 = -((1 + Real.sqrt 5) / 4) := by
  rw [cosCls]
  have he : 2 * π * (((2 : Fin (2 + 3)) : ℕ) : ℝ) / (((2 : ℕ) : ℝ) + 3) = π - π / 5 := by
    norm_num
    ring
  rw [he, Real.cos_pi_sub, Real.cos_pi_div_five]

/-- **SIDE 5 SATISFIES UNIT 98's CRITERION**, and the proof needs the irrationality of `√5`. -/
theorem noCosRelation_two : NoCosRelation 2 := by
  intro a hsupp hsum hcos
  have h3 : a 3 = 0 := hsupp 3 (by norm_num)
  have h4 : a 4 = 0 := hsupp 4 (by norm_num)
  rw [Fin.sum_univ_five, h3, h4] at hsum
  rw [Fin.sum_univ_five, h3, h4, cosCls_two_zero, cosCls_two_one, cosCls_two_two] at hcos
  have hkey : ((4 * a 0 - a 1 - a 2 : ℤ) : ℝ)
      + ((a 1 - a 2 : ℤ) : ℝ) * Real.sqrt 5 = 0 := by
    push_cast at hcos ⊢
    linarith
  obtain ⟨hA, hB⟩ := eq_zero_of_add_mul_sqrt_five hkey
  have e0 : a 0 = 0 := by omega
  have e1 : a 1 = 0 := by omega
  have e2 : a 2 = 0 := by omega
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact h3
  · exact h4

/-! ## readings and the number -/

theorem side_five_tight (m : ℝ) (k : Site d 5) : orbit k = nuRFibre 2 m k :=
  (noCosRelation_iff 2 m).1 noCosRelation_two d k

theorem bound_eq_finrank_side_five (m : ℝ) (k : Site d 5) :
    (2 ^ (interiorAxes k).card * Nat.multinomial univ fun c => Fintype.card {i // cls k i = c})
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d 5) m) - nuR 2 m k • LinearMap.id).ker :=
  bound_eq_finrank_of_noCosRelation noCosRelation_two m k

theorem card_orbit_eq_finrank_side_five (m : ℝ) (k : Site d 5) :
    (orbit k).card
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d 5) m) - nuR 2 m k • LinearMap.id).ker :=
  card_orbit_eq_finrank_of_noCosRelation noCosRelation_two m k

theorem card_orbitsOf_eq_one_side_five (m : ℝ) (k : Site d 5) :
    (orbitsOf 2 m k).card = 1 :=
  card_orbitsOf_eq_one_of_noCosRelation noCosRelation_two m k

theorem card_eq_clsCount {N : ℕ} (k : Site d (N + 3)) (j : Fin (N + 3)) :
    Fintype.card {i // cls k i = j} = clsCount k j := rfl

theorem pairClass_two_eq_zero_iff {v : ℕ} (hv : v < 5) : pairClass 2 v = 0 ↔ v = 0 := by
  interval_cases v <;> simp [pairClass]

theorem clsCount_side_five_zero (k : Site d 5) :
    clsCount k 0 = (univ.filter (fun i : Fin d => (k i).val = 0)).card := by
  rw [clsCount, Fintype.card_subtype]
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [cls, clsF, Fin.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]
  exact pairClass_two_eq_zero_iff hki

theorem card_interiorAxes_side_five (k : Site d 5) :
    (interiorAxes k).card = d - clsCount k 0 := by
  classical
  have hi : interiorAxes k = (univ.filter (fun i : Fin d => (k i).val = 0))ᶜ := by
    ext i
    have hki := (k i).isLt
    simp only [interiorAxes, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hi, Finset.card_compl, Fintype.card_fin, clsCount_side_five_zero]

theorem clsCount_side_five_three (k : Site d 5) : clsCount k 3 = 0 :=
  clsCount_eq_zero_of_not_class k (by norm_num)

theorem clsCount_side_five_four (k : Site d 5) : clsCount k 4 = 0 :=
  clsCount_eq_zero_of_not_class k (by norm_num)

theorem sum_clsCount_side_five (k : Site d 5) :
    clsCount k 0 + clsCount k 1 + clsCount k 2 = d := by
  have h := sum_clsCount k
  rw [Fin.sum_univ_five, clsCount_side_five_three, clsCount_side_five_four] at h
  omega

theorem multinomial_side_five (k : Site d 5) :
    (Nat.multinomial univ fun c : Fin 5 => Fintype.card {i // cls k i = c})
      = Nat.factorial d / (Nat.factorial (clsCount k 0) * Nat.factorial (clsCount k 1)
          * Nat.factorial (clsCount k 2)) := by
  have hs := sum_clsCount_side_five k
  rw [Nat.multinomial, Fin.sum_univ_five, Fin.prod_univ_five]
  simp only [card_eq_clsCount, clsCount_side_five_three, clsCount_side_five_four,
    Nat.factorial_zero, mul_one, Nat.add_zero, hs]

/-- **THE EIGENSPACE DIMENSION AT SIDE 5, AS A NUMBER, IN EVERY DIMENSION** — a TRINOMIAL, where
side 3's was a binomial. -/
theorem finrank_side_five (m : ℝ) (k : Site d 5) :
    Module.finrank ℝ
        (Matrix.toLin' (massive (torusGraph d 5) m) - nuR 2 m k • LinearMap.id).ker
      = 2 ^ (d - clsCount k 0)
        * (Nat.factorial d / (Nat.factorial (clsCount k 0) * Nat.factorial (clsCount k 1)
            * Nat.factorial (clsCount k 2))) := by
  rw [← bound_eq_finrank_side_five m k, card_interiorAxes_side_five, multinomial_side_five]

/-! ## and side 6 fails, so the answer is not monotone in the side -/

theorem cosCls_three_zero : cosCls 3 0 = 1 := by
  rw [cosCls]; norm_num

theorem cosCls_three_one : cosCls 3 1 = 1 / 2 := by
  rw [cosCls]
  have he : 2 * π * (((1 : Fin (3 + 3)) : ℕ) : ℝ) / (((3 : ℕ) : ℝ) + 3) = π / 3 := by
    norm_num; ring
  rw [he, Real.cos_pi_div_three]

theorem cosCls_three_two : cosCls 3 2 = -(1 / 2) := by
  rw [cosCls]
  have he : 2 * π * (((2 : Fin (3 + 3)) : ℕ) : ℝ) / (((3 : ℕ) : ℝ) + 3) = π - π / 3 := by
    norm_num; ring
  rw [he, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem cosCls_three_three : cosCls 3 3 = -1 := by
  rw [cosCls]
  have he : 2 * π * (((3 : Fin (3 + 3)) : ℕ) : ℝ) / (((3 : ℕ) : ℝ) + 3) = π := by
    norm_num; ring
  rw [he, Real.cos_pi]

/-- The relation at side `6`: `1 · 1 − 1 · (1/2) − 1 · (−1/2) + 1 · (−1) = 0`, coefficients
summing to zero. -/
def relSix : Fin 6 → ℤ :=
  fun j => if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then -1
    else if (j : ℕ) = 2 then -1 else if (j : ℕ) = 3 then 1 else 0

theorem not_noCosRelation_three : ¬ NoCosRelation 3 := by
  intro h
  have hsupp : ∀ j : Fin 6, 3 + 3 < 2 * (j : ℕ) → relSix j = 0 := by
    intro j hj
    have := j.isLt
    fin_cases j <;> simp_all [relSix]
  have hsum : ∑ j, relSix j = 0 := by decide
  have hcos : ∑ j, (relSix j : ℝ) * cosCls 3 j = 0 := by
    rw [Fin.sum_univ_six, cosCls_three_zero, cosCls_three_one, cosCls_three_two,
      cosCls_three_three]
    norm_num [relSix]
  have h0 := h relSix hsupp hsum hcos 0
  simp [relSix] at h0

theorem exists_not_tight_side_six (m : ℝ) :
    ∃ (D : ℕ) (k : Site D (3 + 3)), orbit k ≠ nuRFibre 3 m k := by
  by_contra hc
  refine not_noCosRelation_three ((noCosRelation_iff 3 m).2 ?_)
  intro D k
  by_contra hk
  exact hc ⟨D, k, hk⟩

end TorusSideFive
