/-
  TorusSideThree: at side 3 the massive torus's degeneracy bound is TIGHT IN EVERY DIMENSION, the
  eigenspace dimension is `2 ^ (d − c₀) · C(d, c₀)`, and at side 4 it is already NOT tight

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §7 rule 3: *take a result already proved under restrictive
  hypotheses and remove one — dimension, polynomials-only, finite-dimensionality, boundedness.*
  Units 94 and 95 proved the torus degeneracy bound tight, and then computed the eigenspace
  dimension, **at `d = 1` only**. Unit 94's own marker says why that is the easy dimension: at
  `d = 1` the hyperoctahedral group is `{±1}` and the sum defining `νR` has ONE term, so *there is
  no coincidence between sums of cosines to have*. **The fence removed here is the DIMENSION.** The
  price is that the side is fixed at `3`, and the last section proves that price is real.

  **CHECKED ABSENT BEFORE BEING WRITTEN — AND THE FIRST QUERY WAS TOO NARROW, so what it claimed
  is struck and recorded rather than used** (`ERRATUM 621`'s rule is what caught it, applied by
  hand). `awk` over `estate_types.txt` (14573 statements, 1115 modules): for `torusGraph _ 3` it
  returns one statement, `MirrorStrict.reflectionPositive_torus_three_strict`, about reflection
  positivity, naming no orbit; and the only unconditional TIGHTNESS statement anywhere is
  `TorusFibreTight.card_orbit_eq_finrank_one`, at `d = 1`. **A first draft added *and nothing
  states orbit-versus-fibre at a concrete side*, from a query keyed on the `Site` TYPE — which
  misses `TorusBoundTightIff.orbit_ssubset_nuRFibre_eight`**, where the side `24` appears as the
  numeral in `nuRFibre 21 m` and not in any type. That statement is exactly a concrete-side
  orbit-versus-fibre fact, it is the estate's one such, and it is NEGATIVE; §5's side-4 pair is the
  second, at a far smaller side. The claim is narrowed, not softened: **nothing states either
  answer at side 3 or at side 4.** `paper_f/BoxLapSideThree.lean` is the BOX at side three —
  Dirichlet, a path spectrum, no orbits.

  **AND ONE CLAIM THIS FILE DOES NOT MAKE, struck from the same draft.** That
  `finrank_side_three` is the torus chain's *first explicit eigenspace dimension above `d = 1`*.
  **It is not.** `TorusRealMultiplicity.ground_state_simple_real` gives `1` at `m²` and
  `top_eigenvalue_simple_real` gives `1` at `4d + m²`, both at every dimension, and both predate
  this file. What is true and weaker: this is the first one covering **every** frequency rather
  than a distinguished eigenvalue — and `finrank_side_three_ground` **derives the ground-state
  theorem back out of the formula** at side 3, which is the evidence the weaker claim owes.

  WHAT IS PROVED.

  * **`two_cos_val`** — at side 3 the summand of `νR` takes exactly TWO values: `2` at frequency
    `0` and `−1` at the other two. This is the whole reason the section works.
  * **`nuR_side_three`** — so `νR 0 m k = 3d + m² − 3·c₀`, where `c₀ = |{i | kᵢ = 0}|`, and
    **`nuR_eq_iff`**: two frequencies have the same eigenvalue **exactly when they have the same
    `c₀`**. That is a complete answer to the coincidence question at this side.
  * **`orbit_eq_nuRFibre_side_three`** — **the fibre IS the orbit, at every dimension, every mass
    and every frequency.** The reverse inclusion is the content: equal `c₀` gives equal class-count
    vectors for every class (`0` and `1` are the only classes at side 3), which is
    `TorusOrbitCharacterisation.mem_orbit_of_card_eq`'s hypothesis.
    **THE BARE NAME `orbit_eq_nuRFibre` WAS TAKEN, AND THE COLLISION IS NOT A DUPLICATE**:
    `TorusFibreTight.orbit_eq_nuRFibre` is the same sentence at `d = 1` and EVERY side, this one is
    every `d` at side 3, and **neither subsumes the other** — they overlap at exactly one point,
    `d = 1` and side `3`. `ERRATUM 465`'s rule therefore does not merge them, and the suffix records
    that the trade was made knowingly, as unit 90's `cycle_angle_nonneg` did. **THE OVERLAP IS
    CHECKED RATHER THAN ASSUMED**: `finrank_side_three_agrees_one` proves the two chains give the
    same number there.
  * **`bound_eq_finrank_side_three`, `card_orbit_eq_finrank_side_three`,
    `card_orbitsOf_eq_one_side_three`** — the three readings the watchlist item asks for, off the
    criteria of `TorusBoundTightIff` and `TorusFibreOrbitPartition`. The last one is the item's own
    sentence: **the `νR` fibre is a SINGLE hyperoctahedral orbit.**
  * **`finrank_side_three`** — and the dimension as a NUMBER:
    `dim = 2 ^ (d − c₀) · C(d, c₀)`, at every `d`, every side-3 frequency and every mass. The
    exponent is `|interiorAxes k|` (`card_interiorAxes_side_three`) and the binomial is the
    multinomial of `card_orbit` (`multinomial_side_three`, through `Nat.multinomial_spec` and
    `Nat.choose_mul_factorial_mul_factorial`).
  * **`finrank_side_three_agrees_one`, `finrank_side_three_ground`** — **the two special cases a
    new general formula owes** (`ERRATUM 201`'s rule), both proved rather than asserted: at `d = 1`
    the number above is unit 95's `if 0 < k₀ ∧ 2k₀ ≠ N + 3 then 2 else 1`, and at the ground state
    `k = 0` it is `1`, which **re-derives `TorusRealMultiplicity.ground_state_simple_real`** at
    side 3 instead of sitting beside it.
  * **`orbit_ssubset_nuRFibre_four`, `card_orbit_lt_finrank_four`** — **AND AT SIDE 4 IT ALREADY
    FAILS**,
    at `d = 2`, on the smallest pair there is: `(0, 2)` and `(1, 1)` have the same `νR` — both
    `4 + m²` — and lie in different orbits, because the first has an axis of class `0` and the
    second has none. So the bound is STRICTLY below the dimension there.

  **WHY SIDE 3 IS NOT MERELY "SMALL", AND WHAT THE SIDE-4 FAILURE IS.** The classes at side `n` are
  `0, …, ⌊n/2⌋` and the eigenvalue is `2d + m² − 2∑ⱼ cⱼ·cos(2πj/n)` with `∑ⱼ cⱼ = d`. So the bound
  is tight at every frequency and every dimension exactly when no NONZERO integer vector `a` on the
  classes has both `∑ⱼ aⱼ = 0` and `∑ⱼ aⱼ·cos(2πj/n) = 0` — a **vanishing sum of roots of unity**,
  which is the species `L102` records as library-blocked. At side 3 the values are `1, −1/2`, and
  `a₀ − a₁/2 = 0` with `a₀ + a₁ = 0` forces `a = 0`: no relation, hence tight. At side 4 they are
  `1, 0, −1`, and `a = (1, −2, 1)` is a relation — **which is exactly the difference of the two
  class-count vectors `(1,0,1)` and `(0,2,0)` of the last section's counterexample.** The
  equivalence in this paragraph is **NOT formalised here**: the direction used below is the easy one
  (no relation ⇒ tight, and one exhibited relation ⇒ one exhibited failure), and turning it into a
  biconditional over all `n` is the library-blocked item itself. No cost is offered
  (`ERRATUM 194`, `ERRATUM 246`).

  **THE MEASUREMENT THAT DECIDED THE SCOPE, run before a line was written** (`ERRATUM 622`'s rule:
  evaluate the smallest instances before filing a wall). Brute force over every frequency, comparing
  the orbit's size with the `νR` fibre's: **tight at sides 3 and 5 for `d = 1, 2, 3, 4`; NOT tight
  at sides 4 and 6 for `d ≥ 2`.** So the answer is not monotone in the side and the honest headline
  is *the obstruction is arithmetic in the side, not the dimension*. **SIDE 5 IS A REAL NEXT UNIT
  AND IS NOT DONE HERE**: it needs `cos(2π/5) = (√5 − 1)/4` — Mathlib has `Real.cos_pi_div_five`,
  probed — together with the irrationality of `√5` to rule out the relation, and that is a different
  argument from this file's two-value one. Named so it is not rediscovered, not costed.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING AT A GENERAL SIDE.** `L102` asks which frequencies give a one-orbit fibre **in
    general**; this answers it at `n = 3` (all of them) and at `n = 4` (not all of them) and leaves
    every other side untouched. The item does not close.
  * **NO CLASSIFICATION OF VANISHING SUMS OF ROOTS OF UNITY**, and none is approached. The pinned
    Mathlib has none (0 Conway–Jones, 0 Rédei–Schoenberg, probed and recorded at `L102`).
  * **NO UPPER BOUND ON ANY MULTIPLICITY AT A SIDE WHERE THE BOUND FAILS.** The side-4 section
    exhibits a strict inequality; it does not say by how much, and `TorusEightNotTight`'s side-24
    pair is still the estate's only other negative instance.
  * **THE EIGENVALUE IS EVALUATED ONLY AT SIDE 3.** `nuR_side_three` is a number in `c₀`; nothing
    here evaluates `νR` at any other side, and the FULL side-3 spectrum is not assembled — the
    dimensions are one eigenvalue at a time and summing over frequencies double-counts, exactly as
    unit 95's marker says.
  * **NOTHING OVER `ℂ`, NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusFibreCount
import TorusOrbitMultinomial

namespace TorusSideThree

open Finset BoxGraph TorusHyperoctahedral TorusReflectionCount MassiveTorusSpectrum
open TorusBoundTightIff TorusOrbitInvariant TorusOrbitCharacterisation
open TorusFibreOrbitPartition TorusOrbitMultinomial TorusReflection GraphLaplacian
open Real

variable {d : ℕ}

/-! ## 1. The two axis kinds at side 3 -/

section Axes

/-- The axes the frequency vanishes on. Its size is the only invariant at side 3. -/
def zeroAxes (k : Site d 3) : Finset (Fin d) := {i | (k i).val = 0}

/-- The other axes. -/
def nonzeroAxes (k : Site d 3) : Finset (Fin d) := {i | (k i).val ≠ 0}

theorem card_zeroAxes_le (k : Site d 3) : (zeroAxes k).card ≤ d := by
  simpa using Finset.card_le_univ (zeroAxes k)

theorem nonzeroAxes_eq_compl (k : Site d 3) : nonzeroAxes k = (zeroAxes k)ᶜ := by
  ext i; simp [nonzeroAxes, zeroAxes]

theorem card_nonzeroAxes (k : Site d 3) : (nonzeroAxes k).card = d - (zeroAxes k).card := by
  rw [nonzeroAxes_eq_compl, Finset.card_compl, Fintype.card_fin]

/-- **AT SIDE 3 EVERY NON-ZERO FREQUENCY IS INTERIOR**, because `2v = 3` has no solution. -/
theorem card_interiorAxes_side_three (k : Site d 3) :
    (interiorAxes k).card = d - (zeroAxes k).card := by
  rw [← card_nonzeroAxes]
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [interiorAxes, nonzeroAxes, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  omega

end Axes

/-! ## 2. The eigenvalue at side 3 is a function of one integer -/

section Eigenvalue

/-- **THE ONE FACT THE FILE RESTS ON**: at side 3 the summand of `νR` takes two values. -/
theorem two_cos_val (v : Fin 3) :
    2 * Real.cos (2 * π * (v.val : ℝ) / (((0 : ℕ) : ℝ) + 3)) = if v.val = 0 then 2 else -1 := by
  have h := v.isLt
  interval_cases hv : (v : ℕ)
  · norm_num
  · rw [if_neg (by omega)]
    have he : 2 * π * ((1 : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 3) = π - π / 3 := by push_cast; ring
    rw [he, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  · rw [if_neg (by omega)]
    have he : 2 * π * ((2 : ℕ) : ℝ) / (((0 : ℕ) : ℝ) + 3) = π + π / 3 := by push_cast; ring
    rw [he, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]; ring

theorem sum_two_cos (k : Site d 3) :
    ∑ i : Fin d, 2 * Real.cos (2 * π * ((k i).val : ℝ) / (((0 : ℕ) : ℝ) + 3))
      = 3 * ((zeroAxes k).card : ℝ) - d := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => two_cos_val (k i)), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const]
  have hz : zeroAxes k = univ.filter (fun i : Fin d => (k i).val = 0) := rfl
  have hn : nonzeroAxes k = univ.filter (fun i : Fin d => ¬ (k i).val = 0) := rfl
  have hle := card_zeroAxes_le k
  rw [← hz, ← hn, card_nonzeroAxes, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hle]
  ring

/-- **THE EIGENVALUE AT SIDE 3, AS A NUMBER IN THE ZERO-COUNT.** -/
theorem nuR_side_three (m : ℝ) (k : Site d 3) :
    nuR 0 m k = 3 * (d : ℝ) + m ^ 2 - 3 * ((zeroAxes k).card : ℝ) := by
  rw [nuR, sum_two_cos]
  ring

/-- **SO THE COINCIDENCE QUESTION IS SETTLED AT SIDE 3**: two frequencies share an eigenvalue
exactly when they vanish on the same NUMBER of axes. -/
theorem nuR_eq_iff (m : ℝ) (k k' : Site d 3) :
    nuR 0 m k' = nuR 0 m k ↔ (zeroAxes k').card = (zeroAxes k).card := by
  rw [nuR_side_three, nuR_side_three]
  constructor
  · intro h
    exact Nat.cast_injective (R := ℝ) (by linarith)
  · intro h
    rw [h]

end Eigenvalue

/-! ## 3. The fibre is the orbit, in every dimension -/

section Tight

/-- The class-count vector at side 3 has only two entries that can be non-zero. -/
theorem card_pairClass_zero (k : Site d 3) :
    ({i | pairClass 0 (k i).val = 0} : Finset (Fin d)).card = (zeroAxes k).card := by
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [zeroAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold pairClass
  omega

theorem card_pairClass_one (k : Site d 3) :
    ({i | pairClass 0 (k i).val = 1} : Finset (Fin d)).card = d - (zeroAxes k).card := by
  rw [← card_nonzeroAxes]
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [nonzeroAxes, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  unfold pairClass
  omega

theorem card_pairClass_ge_two (k : Site d 3) {c : ℕ} (hc : 2 ≤ c) :
    ({i | pairClass 0 (k i).val = c} : Finset (Fin d)).card = 0 := by
  rw [Finset.card_eq_zero]
  ext i
  have hki := (k i).isLt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  unfold pairClass
  omega

/-- **THE DIMENSION FENCE REMOVED**: at side 3 the `νR` fibre is exactly the hyperoctahedral
orbit, at EVERY dimension, every mass and every frequency. -/
theorem orbit_eq_nuRFibre_side_three (m : ℝ) (k : Site d 3) : orbit k = nuRFibre 0 m k := by
  refine Finset.Subset.antisymm (orbit_subset_nuRFibre 0 m k) ?_
  intro k' hk'
  rw [mem_nuRFibre_iff] at hk'
  have hcard := (nuR_eq_iff m k k').1 hk'
  refine mem_orbit_of_card_eq k k' ?_
  intro c
  match c with
  | 0 => rw [card_pairClass_zero, card_pairClass_zero, hcard]
  | 1 => rw [card_pairClass_one, card_pairClass_one, hcard]
  | (n + 2) =>
      rw [card_pairClass_ge_two (c := n + 2) k' (by omega),
        card_pairClass_ge_two (c := n + 2) k (by omega)]

/-- The bound of `TorusEigenspaceLowerBound` is an EQUALITY at side 3. -/
theorem bound_eq_finrank_side_three (m : ℝ) (k : Site d 3) :
    (2 ^ (interiorAxes k).card * Nat.multinomial univ fun c => Fintype.card {i // cls k i = c})
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d 3) m) - nuR 0 m k • LinearMap.id).ker :=
  (bound_eq_finrank_iff 0 m k).2 (orbit_eq_nuRFibre_side_three m k)

/-- The same statement read on the orbit's size. -/
theorem card_orbit_eq_finrank_side_three (m : ℝ) (k : Site d 3) :
    (orbit k).card
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d 3) m) - nuR 0 m k • LinearMap.id).ker :=
  (card_orbit_eq_finrank_iff 0 m k).2 (orbit_eq_nuRFibre_side_three m k)

/-- **AND IN THE WATCHLIST ITEM'S OWN WORDS**: the fibre is a SINGLE orbit. -/
theorem card_orbitsOf_eq_one_side_three (m : ℝ) (k : Site d 3) :
    (orbitsOf 0 m k).card = 1 :=
  (card_orbitsOf_eq_one_iff 0 m k).2 (orbit_eq_nuRFibre_side_three m k)

end Tight

/-! ## 4. The dimension as a number -/

section Number

theorem card_cls_zero (k : Site d 3) :
    Fintype.card {i // cls k i = (0 : Fin 3)} = (zeroAxes k).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [zeroAxes, cls, clsF, Fin.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_zero]
  unfold pairClass
  omega

theorem card_cls_one (k : Site d 3) :
    Fintype.card {i // cls k i = (1 : Fin 3)} = d - (zeroAxes k).card := by
  rw [Fintype.card_subtype, ← card_nonzeroAxes]
  congr 1
  ext i
  have hki := (k i).isLt
  simp only [nonzeroAxes, cls, clsF, Fin.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.val_one, ne_eq]
  unfold pairClass
  omega

theorem card_cls_two (k : Site d 3) : Fintype.card {i // cls k i = (2 : Fin 3)} = 0 := by
  rw [Fintype.card_subtype, Finset.card_eq_zero]
  ext i
  have hki := (k i).isLt
  simp only [cls, clsF, Fin.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, Fin.val_two]
  unfold pairClass
  omega

/-- **THE MULTINOMIAL OF `card_orbit` IS A BINOMIAL AT SIDE 3**, because two classes carry every
axis. `Nat.multinomial_spec` gives the arithmetic and `Nat.choose_mul_factorial_mul_factorial`
identifies it. -/
theorem multinomial_side_three (k : Site d 3) :
    (Nat.multinomial univ fun c : Fin 3 => Fintype.card {i // cls k i = c})
      = Nat.choose d (zeroAxes k).card := by
  have hle := card_zeroAxes_le k
  have hspec := Nat.multinomial_spec (univ : Finset (Fin 3))
    (fun c => Fintype.card {i // cls k i = c})
  rw [Fin.prod_univ_three, Fin.sum_univ_three] at hspec
  simp only [card_cls_zero, card_cls_one, card_cls_two, Nat.factorial_zero, mul_one,
    Nat.add_zero, Nat.add_sub_cancel' hle] at hspec
  have hchoose := Nat.choose_mul_factorial_mul_factorial hle
  have hpos : 0 < Nat.factorial (zeroAxes k).card * Nat.factorial (d - (zeroAxes k).card) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [hspec, ← hchoose]
  ring

/-- The orbit's size at side 3, explicitly. -/
theorem card_orbit_side_three (k : Site d 3) :
    (orbit k).card = 2 ^ (d - (zeroAxes k).card) * Nat.choose d (zeroAxes k).card := by
  rw [card_orbit k, card_interiorAxes_side_three, multinomial_side_three]

/-- **THE EIGENSPACE DIMENSION AT SIDE 3, AS A NUMBER, IN EVERY DIMENSION.** -/
theorem finrank_side_three (m : ℝ) (k : Site d 3) :
    Module.finrank ℝ
        (Matrix.toLin' (massive (torusGraph d 3) m) - nuR 0 m k • LinearMap.id).ker
      = 2 ^ (d - (zeroAxes k).card) * Nat.choose d (zeroAxes k).card := by
  rw [← card_orbit_eq_finrank_side_three m k, card_orbit_side_three]

/-- **THE SPECIAL CASE THE NEW FORMULA OWES** (`ERRATUM 201`): at `d = 1` it is unit 95's
`TorusFibreCount.finrank_one_explicit`. -/
theorem finrank_side_three_agrees_one (m : ℝ) (k : Site 1 3) :
    2 ^ (1 - (zeroAxes k).card) * Nat.choose 1 (zeroAxes k).card
      = if 0 < (k 0 : ℕ) ∧ 2 * (k 0 : ℕ) ≠ 0 + 3 then 2 else 1 := by
  rw [← finrank_side_three m k, TorusFibreCount.finrank_one_explicit]

theorem zeroAxes_zero : zeroAxes (0 : Site d 3) = univ := by
  ext i; simp [zeroAxes]

/-- **AND THE SECOND SPECIAL CASE IT OWES, WHICH IS AN OLDER THEOREM OF THIS ESTATE**: at the
ground state the formula gives `1`, so `TorusRealMultiplicity.ground_state_simple_real` comes
back out of it at side 3. Derived, not restated — the shape
`TorusOrbitMultinomial.card_orbit_eq_two_pow_mul_factorial` used on its own predecessor. -/
theorem finrank_side_three_ground (m : ℝ) :
    Module.finrank ℝ
        (Matrix.toLin' (massive (torusGraph d 3) m) - (m ^ 2) • LinearMap.id).ker = 1 := by
  rw [← nuR_at_zero (d := d) 0 m, finrank_side_three, zeroAxes_zero, Finset.card_univ,
    Fintype.card_fin]
  simp

end Number

/-! ## 5. And at side 4 the bound is already not tight -/

section SideFour

/-- The frequency `(0, 2)` at side `4`. -/
def gZeroTwo : Site 2 (1 + 3) := ![⟨0, by omega⟩, ⟨2, by omega⟩]

/-- The frequency `(1, 1)` at side `4`. -/
def gOneOne : Site 2 (1 + 3) := ![⟨1, by omega⟩, ⟨1, by omega⟩]

/-- At side 4 the summand of `νR` takes THREE values, and `1 − 2·0 + (−1) = 0` is the relation
that breaks the count. -/
theorem two_cos_val_four (v : Fin (1 + 3)) :
    2 * Real.cos (2 * π * (v.val : ℝ) / (((1 : ℕ) : ℝ) + 3))
      = if v.val = 0 then 2 else if v.val = 2 then -2 else 0 := by
  have h := v.isLt
  interval_cases hv : (v : ℕ)
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega)]
    have he : 2 * π * ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 3) = π / 2 := by push_cast; ring
    rw [he, Real.cos_pi_div_two]; ring
  · rw [if_neg (by omega), if_pos (by omega)]
    have he : 2 * π * ((2 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 3) = π := by push_cast; ring
    rw [he, Real.cos_pi]; ring
  · rw [if_neg (by omega), if_neg (by omega)]
    have he : 2 * π * ((3 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 3) = π + π / 2 := by push_cast; ring
    rw [he, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

theorem nuR_gZeroTwo (m : ℝ) : nuR 1 m gZeroTwo = 4 + m ^ 2 := by
  rw [nuR, Fin.sum_univ_two, two_cos_val_four, two_cos_val_four]
  norm_num [gZeroTwo]

theorem nuR_gOneOne (m : ℝ) : nuR 1 m gOneOne = 4 + m ^ 2 := by
  rw [nuR, Fin.sum_univ_two, two_cos_val_four, two_cos_val_four]
  norm_num [gOneOne]

/-- **THE TWO FREQUENCIES SHARE AN EIGENVALUE.** -/
theorem nuR_gOneOne_eq (m : ℝ) : nuR 1 m gOneOne = nuR 1 m gZeroTwo := by
  rw [nuR_gOneOne, nuR_gZeroTwo]

/-- **AND THEY ARE IN DIFFERENT ORBITS**: `(0, 2)` has an axis of class `0` and `(1, 1)` has
none, so no signed permutation carries one to the other. -/
theorem gOneOne_notMem_orbit : gOneOne ∉ orbit gZeroTwo := by
  refine not_mem_orbit_of_card_ne gZeroTwo gOneOne 0 ?_
  have h1 : ({i | pairClass 1 (gOneOne i).val = 0} : Finset (Fin 2)) = ∅ := by
    ext i
    fin_cases i <;> simp [gOneOne, pairClass]
  have h2 : ({i | pairClass 1 (gZeroTwo i).val = 0} : Finset (Fin 2)) = {0} := by
    ext i
    fin_cases i <;> simp [gZeroTwo, pairClass]
  rw [h1, h2]
  simp

/-- **SO AT SIDE 4 THE ORBIT IS A PROPER PART OF THE FIBRE.** -/
theorem orbit_ssubset_nuRFibre_four (m : ℝ) : orbit gZeroTwo ⊂ nuRFibre 1 m gZeroTwo := by
  refine Finset.ssubset_iff_of_subset (orbit_subset_nuRFibre 1 m gZeroTwo) |>.2 ⟨gOneOne, ?_, ?_⟩
  · rw [mem_nuRFibre_iff]
    exact nuR_gOneOne_eq m
  · exact gOneOne_notMem_orbit

/-- **AND THE BOUND IS STRICTLY BELOW THE DIMENSION THERE.** The contrast with
`bound_eq_finrank_side_three` is the point: one side apart, and the dimension is not the
obstruction. -/
theorem card_orbit_lt_finrank_four (m : ℝ) :
    (orbit gZeroTwo).card
      < Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph 2 (1 + 3)) m)
            - nuR 1 m gZeroTwo • LinearMap.id).ker :=
  (card_orbit_lt_finrank_iff 1 m gZeroTwo).2 (orbit_ssubset_nuRFibre_four m)

end SideFour

end TorusSideThree
