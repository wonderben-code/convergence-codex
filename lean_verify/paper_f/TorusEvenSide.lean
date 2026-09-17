/-
  TorusEvenSide: EVERY EVEN SIDE FAILS the criterion — so tightness forces an ODD side, units 97
  and 99's refutations of sides 4 and 6 become instances, and the only class left open is the odd
  composites

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §1, the Caesar companion to unit 100. That unit proved
  every odd PRIME side tight; units 97 and 99 refuted sides 4 and 6 one at a time, by exhibiting a
  relation in each; and unit 102 refuted side 9. This proves the whole even family at once, and it
  needs no new machinery — unit 102's `sum_cosCls_eq_zero` and the fibre count that
  `TorusPairClassFibre` has had since 31 August do it between them.

  **THE ARGUMENT, AND ITS ONE IDEA.** At a side `n = 2m` two relations are available for free.
  **(A)** the FIBRE-SIZE vector: `A c` is how many frequencies carry class `c` — `1` at the two
  mirror-fixed classes `0` and `m`, `2` at the interior ones, `0` at a non-class. Regrouping the
  full-turn sum `∑_{v<n} cos(2πv/n) = 0` by class gives `∑_c A c · cos(2πc/n) = 0`, and
  `∑_c A c = n`. **(B)** the indicator of `{0, m}`: its cosine sum is `cos 0 + cos π = 1 − 1 = 0`
  and its coefficient sum is `2`. **So `a = 2A − nB` has coefficient sum `2n − 2n = 0` and cosine
  sum `0`, and at the class `1` it is `2·A 1 ≥ 2 ≠ 0`** because class `1` is interior once
  `n ≥ 4`, which every even side here is. **No half-range decomposition of `Finset.range n` is
  needed anywhere** — the fibre regrouping does that work, and that is the whole reason this is
  short.

  **CHECKED ABSENT BY `ERRATUM 627`'s RULE — the BODY, not the name.** `awk` over
  `estate_types.txt` (14702 statements, 1120 modules) for each of the twenty-three names below
  returns **one** hit: `FlipEnergy.sum_indicator`, which is
  `∑ p, (if p ∈ S then c else 0) = |S| · c` over `IsingFiniteVolume.Site n`. **That is the same
  shape over a different index type and does not apply here**, and this file's version is renamed
  `sum_indicator_fixed` so the bare name is not carrying two facts (unit 90's
  `cycle_angle_nonneg` precedent). Both are three lines off `Finset.sum_filter` and
  `Finset.sum_const`, and neither is worth generalising for the other.

  WHAT IS PROVED.

  * **`fibreCount`, `sum_fibreCount_mul`** — the class fibre sizes, and the regrouping: for any `f`
    constant on fibres, `∑_c A c · f c = ∑_v f v`, by `Finset.sum_fiberwise'` over
    `TorusOrbitMultinomial.clsF`.
  * **`cosCls_clsF`** — the cosine IS constant on fibres, off unit 94's
    `TorusFibreTight.cos_pairClass`; hence **`sum_fibreCount_cos`** (`∑_c A c · cos = 0`, through
    unit 102's `sum_cosCls_eq_zero`) and **`sum_fibreCount`** (`∑_c A c = n`).
  * **`one_le_fibreCount`** — a class lies in its own fibre, off unit 100's `pairClass_self`; and
    **`fibreCount_eq_zero`** — a non-class has an empty one, off
    `TorusFibreTight.two_mul_pairClass_le`.
  * **`cosCls_zero_eq_one`, `cosCls_half`** — `cos 0 = 1` and `cos(2πm/2m) = cos π = −1`, which is
    the only place the side's evenness is used for a VALUE.
  * **`relEven`, `filter_fixed`, `zero_ne_half`, `sum_indicator_fixed`, `sum_indicator_cos`,
    `sum_relEven`, `sum_relEven_cos`, `relEven_supp`, `clsOne`, `clsOne_val`,
    `relEven_one_ne_zero`** — the relation and its four obligations.
  * **`not_noCosRelation_of_even`** — **every even side fails**, and hence
    **`exists_not_tight_of_even`**: at every even side there is a dimension where the bound is not
    an equality.
  * **`odd_of_noCosRelation`** — **the contrapositive, which is the headline: tightness forces an
    ODD side.** With unit 100's converse for primes this is the sharpest general statement the
    criterion has.
  * **`not_noCosRelation_one_of_even`, `not_noCosRelation_three_of_even`** — sides 4 and 6, units
    97 and 99's hand-built refutations, now instances (`ERRATUM 201`'s check). Neither original is
    deleted: each exhibits its own relation explicitly, which is worth more to a reader than a
    specialisation.

  **WHERE THE CLASSIFICATION NOW STANDS, AND IT IS WORTH STATING PRECISELY.**

  | side | tight? | by |
  |---|---|---|
  | even (`n ≥ 4`) | **NO**, all of them | this unit |
  | odd prime | **YES**, all of them | unit 100 |
  | `9` | **NO** | unit 102 |
  | odd composite, `15, 21, 25, …` | **UNKNOWN** | — |

  So `NoCosRelation` implies odd; odd prime implies `NoCosRelation`; and the ONLY class still open
  is the odd composites, of which the smallest is settled and the rest are untouched. **That is a
  much smaller residue than "which sides satisfy the condition", and naming it is the point of
  this unit.**

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT ODD COMPOSITE SIDES BEYOND `9`.** `15`, `21`, `25`, `27`, `33`, … are
    untouched. A guess is available and is deliberately not made: the relation at side 9 came from
    `3 ∣ 9`, so a divisor-based family may exist; **no such family is proved, attempted or
    costed** (`ERRATUM 194`, `ERRATUM 246`).
  * **NO PER-FREQUENCY STATEMENT AT AN EVEN SIDE.** `exists_not_tight_of_even` produces a
    dimension, not a frequency, and `TorusCosRelation.orbit_eq_nuRFibre_zero` shows the ground
    state is tight at every side including these.
  * **NO DIMENSION AT WHICH A GIVEN EVEN SIDE FIRST FAILS.** Unit 98's construction produces
    `D = ∑ a⁺ = 2n − 2(m−1)`… which this file does not compute, and which is certainly not the
    least such dimension: at side 4 units 97's hand-built pair fails at `d = 2` and the relation
    here is a multiple of it. **The least failing dimension is not addressed at any even side.**
  * **NO UPPER BOUND ON ANY MULTIPLICITY, NOTHING OVER `ℂ` ABOUT THE GRAPH, NOTHING ABOUT THE BOX,
    THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusSideNine

namespace TorusEvenSide

open Finset BoxGraph TorusOrbitInvariant TorusOrbitMultinomial TorusCosRelation
open TorusPrimeSide TorusSideNine
open Real

variable {N : ℕ}

/-- The size of the class-`c` fibre inside `Fin (N + 3)`. -/
def fibreCount (N : ℕ) (c : Fin (N + 3)) : ℕ :=
  (univ.filter (fun v : Fin (N + 3) => clsF v = c)).card

theorem sum_fibreCount_mul (f : Fin (N + 3) → ℝ)
    (hf : ∀ v : Fin (N + 3), f (clsF v) = f v) :
    ∑ c : Fin (N + 3), (fibreCount N c : ℝ) * f c = ∑ v : Fin (N + 3), f v := by
  classical
  have h1 : ∑ v : Fin (N + 3), f v = ∑ v : Fin (N + 3), f (clsF v) :=
    Finset.sum_congr rfl (fun v _ => (hf v).symm)
  rw [h1, ← Finset.sum_fiberwise' (univ : Finset (Fin (N + 3))) clsF f]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, fibreCount, nsmul_eq_mul]

theorem cosCls_clsF (v : Fin (N + 3)) : cosCls N (clsF v) = cosCls N v := by
  rw [cosCls_eq, cosCls_eq]
  exact TorusFibreTight.cos_pairClass v.isLt

theorem sum_fibreCount_cos : ∑ c : Fin (N + 3), (fibreCount N c : ℝ) * cosCls N c = 0 :=
  (sum_fibreCount_mul (cosCls N) cosCls_clsF).trans (sum_cosCls_eq_zero N)

theorem sum_fibreCount : ∑ c : Fin (N + 3), fibreCount N c = N + 3 := by
  have h := sum_fibreCount_mul (N := N) (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hr : ((∑ c : Fin (N + 3), fibreCount N c : ℕ) : ℝ) = ((N + 3 : ℕ) : ℝ) := by
    push_cast at h ⊢
    linarith
  exact Nat.cast_injective hr

theorem one_le_fibreCount {c : Fin (N + 3)} (hc : 2 * (c : ℕ) ≤ N + 3) : 1 ≤ fibreCount N c := by
  rw [fibreCount]
  refine Finset.card_pos.2 ⟨c, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.ext (by rw [clsF]; exact pairClass_self c.isLt hc)

theorem fibreCount_eq_zero {c : Fin (N + 3)} (hc : N + 3 < 2 * (c : ℕ)) : fibreCount N c = 0 := by
  rw [fibreCount, Finset.card_eq_zero]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  have hv := TorusFibreTight.two_mul_pairClass_le (N := N) (a := (v : ℕ)) v.isLt
  have : pairClass N (v : ℕ) = (c : ℕ) := congrArg Fin.val h
  omega

/-! ## the even side -/

theorem cosCls_zero_eq_one : cosCls N 0 = 1 := by
  rw [cosCls]; norm_num

theorem cosCls_half {m : ℕ} (hm : N + 3 = m + m) :
    cosCls N (⟨m, by omega⟩ : Fin (N + 3)) = -1 := by
  have hm0 : m ≠ 0 := by omega
  rw [cosCls_eq]
  have he : 2 * Real.pi * ((((⟨m, by omega⟩ : Fin (N + 3)) : ℕ)) : ℝ) / ((N + 3 : ℕ) : ℝ)
      = Real.pi := by
    have hmr : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hm0
    have hc : ((N + 3 : ℕ) : ℝ) = (m : ℝ) + (m : ℝ) := by rw [hm]; push_cast; ring
    rw [hc]
    change 2 * Real.pi * ((m : ℕ) : ℝ) / ((m : ℝ) + (m : ℝ)) = Real.pi
    field_simp
    ring
  rw [he, Real.cos_pi]

/-- The relation at an even side: twice the fibre-size vector minus `n` times the indicator of
the two mirror-fixed classes. -/
def relEven (N m : ℕ) (c : Fin (N + 3)) : ℤ :=
  2 * (fibreCount N c : ℤ) - ((N : ℤ) + 3) * (if (c : ℕ) = 0 ∨ (c : ℕ) = m then 1 else 0)

theorem filter_fixed {m : ℕ} (hm : N + 3 = m + m) :
    (univ.filter (fun c : Fin (N + 3) => (c : ℕ) = 0 ∨ (c : ℕ) = m))
      = {(0 : Fin (N + 3)), (⟨m, by omega⟩ : Fin (N + 3))} := by
  classical
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h])

theorem zero_ne_half {m : ℕ} (hm : N + 3 = m + m) :
    (0 : Fin (N + 3)) ∉ ({(⟨m, by omega⟩ : Fin (N + 3))} : Finset (Fin (N + 3))) := by
  simp only [Finset.mem_singleton]
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem sum_indicator_fixed {m : ℕ} (hm : N + 3 = m + m) :
    ∑ c : Fin (N + 3), (if (c : ℕ) = 0 ∨ (c : ℕ) = m then (1 : ℤ) else 0) = 2 := by
  classical
  rw [← Finset.sum_filter, filter_fixed hm, Finset.sum_const,
    Finset.card_insert_of_notMem (zero_ne_half hm), Finset.card_singleton]
  rfl

theorem sum_indicator_cos {m : ℕ} (hm : N + 3 = m + m) :
    ∑ c : Fin (N + 3), (if (c : ℕ) = 0 ∨ (c : ℕ) = m then (1 : ℝ) else 0) * cosCls N c = 0 := by
  classical
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, filter_fixed hm,
    Finset.sum_insert (zero_ne_half hm), Finset.sum_singleton, cosCls_zero_eq_one, cosCls_half hm]
  ring

theorem sum_relEven {m : ℕ} (hm : N + 3 = m + m) : ∑ c : Fin (N + 3), relEven N m c = 0 := by
  simp only [relEven]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Nat.cast_sum,
    sum_fibreCount, sum_indicator_fixed hm]
  push_cast
  ring

theorem sum_relEven_cos {m : ℕ} (hm : N + 3 = m + m) :
    ∑ c : Fin (N + 3), ((relEven N m c : ℤ) : ℝ) * cosCls N c = 0 := by
  have hterm : ∀ c : Fin (N + 3), ((relEven N m c : ℤ) : ℝ) * cosCls N c
      = 2 * ((fibreCount N c : ℝ) * cosCls N c)
        - ((N : ℝ) + 3) * ((if (c : ℕ) = 0 ∨ (c : ℕ) = m then (1 : ℝ) else 0) * cosCls N c) := by
    intro c
    simp only [relEven]
    push_cast
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_fibreCount_cos, sum_indicator_cos hm]
  ring

theorem relEven_supp {m : ℕ} (hm : N + 3 = m + m) (c : Fin (N + 3))
    (hc : N + 3 < 2 * (c : ℕ)) : relEven N m c = 0 := by
  have h1 : fibreCount N c = 0 := fibreCount_eq_zero hc
  have h2 : ¬ ((c : ℕ) = 0 ∨ (c : ℕ) = m) := by omega
  simp only [relEven, h1, if_neg h2]
  ring

/-- The class `1`. It is INTERIOR at every even side, because such a side is at least `4`, and
that is the only frequency this file needs to name. -/
def clsOne {m : ℕ} (hm : N + 3 = m + m) : Fin (N + 3) := ⟨1, by omega⟩

theorem clsOne_val {m : ℕ} (hm : N + 3 = m + m) : ((clsOne hm : Fin (N + 3)) : ℕ) = 1 := rfl

theorem relEven_one_ne_zero {m : ℕ} (hm : N + 3 = m + m) : relEven N m (clsOne hm) ≠ 0 := by
  have hm2 : 2 ≤ m := by omega
  have hfib : 1 ≤ fibreCount N (clsOne hm) := by
    refine one_le_fibreCount ?_
    rw [clsOne_val hm]
    omega
  have h2 : ¬ ((clsOne hm : Fin (N + 3)) : ℕ) = 0 ∧ ¬ ((clsOne hm : Fin (N + 3)) : ℕ) = m := by
    rw [clsOne_val hm]
    omega
  have h3 : ¬ (((clsOne hm : Fin (N + 3)) : ℕ) = 0 ∨ ((clsOne hm : Fin (N + 3)) : ℕ) = m) := by
    rintro (h | h)
    · exact h2.1 h
    · exact h2.2 h
  simp only [relEven, if_neg h3]
  omega

/-- **EVERY EVEN SIDE FAILS THE CRITERION.** -/
theorem not_noCosRelation_of_even {m : ℕ} (hm : N + 3 = m + m) : ¬ NoCosRelation N := by
  intro h
  exact relEven_one_ne_zero hm
    (h (relEven N m) (fun c hc => relEven_supp hm c hc) (sum_relEven hm) (sum_relEven_cos hm)
      (clsOne hm))

theorem exists_not_tight_of_even {m : ℕ} (hm : N + 3 = m + m) (mass : ℝ) :
    ∃ (D : ℕ) (k : Site D (N + 3)),
      TorusHyperoctahedral.orbit k ≠ TorusBoundTightIff.nuRFibre N mass k := by
  by_contra hc
  refine not_noCosRelation_of_even hm ((noCosRelation_iff N mass).2 ?_)
  intro D k
  by_contra hk
  exact hc ⟨D, k, hk⟩

/-- **SO TIGHTNESS FORCES AN ODD SIDE.** With unit 100's converse for primes, this is the
sharpest general statement the criterion has. -/
theorem odd_of_noCosRelation (h : NoCosRelation N) : Odd (N + 3) := by
  rcases Nat.even_or_odd (N + 3) with he | ho
  · obtain ⟨m, hm⟩ := he
    exact absurd h (not_noCosRelation_of_even hm)
  · exact ho

/-- Side 4 — unit 97's refutation, now an instance. -/
theorem not_noCosRelation_one_of_even : ¬ NoCosRelation 1 :=
  not_noCosRelation_of_even (m := 2) (by norm_num)

/-- Side 6 — unit 99's refutation, now an instance. -/
theorem not_noCosRelation_three_of_even : ¬ NoCosRelation 3 :=
  not_noCosRelation_of_even (m := 3) (by norm_num)

end TorusEvenSide
