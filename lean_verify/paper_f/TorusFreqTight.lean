/-
  TorusFreqTight: **WHICH frequencies are tight, not which sides** — `L102`'s own question,
  reduced to arithmetic one frequency at a time, and the LEAST FAILING DIMENSION as the smallest
  positive part of a cancelling combination

  **WHY THIS FILE EXISTS, AND IT IS NOT A CHOICE.** `PROOF_STRATEGY` §3 and §6 q3 are imperative:
  *an item that reached `B` is still OPEN … and if the unit I just finished WAS a `B`, retry
  `B → C` right now, before touching the queue.* Unit 104 answered the UNIFORM reading of `L102`
  completely (`tight_iff_prime`) and that is a `B`; the item literally asks *WHICH eigenvalue
  fibres are a single hyperoctahedral orbit*, and that is the `C`. `ERRATUM 630` records that
  unit 104 wrongly offered this to the author as a closure decision when §3 had already ruled.
  **This file is the remaining leg.**

  **WHAT MADE IT ONE FILE RATHER THAN A CAMPAIGN.** `TorusCosRelation`'s forward proof
  (`clsCount_eq_of_nuR_eq`) already builds `a = clsCount k' − clsCount k`, and already proves it is
  a cancelling combination: supported on classes, coefficient sum `0`, cosine sum `0`. **It uses
  the side-wide hypothesis `NoCosRelation N` in exactly one line, to force `a = 0`.** So the
  per-frequency criterion is that hypothesis weakened to *no cancelling combination FITS INSIDE
  this frequency's own class counts*, and the rest of the proof is unchanged.

  **THE STATEMENT.** `TightAt N k` says: every cancelling combination `a` with
  `clsCount k + a ≥ 0` pointwise is zero. Then

      `orbit k = nuRFibre N m k ↔ TightAt N k`   (`orbit_eq_nuRFibre_iff`)

  at every dimension, every mass and **every single frequency `k`** — and the mass drops out of
  the right-hand side, so tightness at a frequency is mass-independent for the same reason it was
  side-independent (unit 98's `tight_indep_mass`, now per frequency).

  **AND THE CONVERSE IS SHARPER THAN UNIT 98'S.** That one produced *some* dimension `D` from a
  relation — it had to leave the dimension it was given. Here the witness `refFn (clsCount k + a)`
  lives in **the same `Site d`** as `k`, because fitting inside `clsCount k` is exactly what keeps
  the coefficient sum at `d`. That is what upgrades "there is a failing dimension" to "this
  frequency fails".

  **WHAT IT COSTS TO GET THE GROUND STATE BACK, AND IT IS THE `ERRATUM 201` CHECK.**
  `TorusCosRelation.orbit_eq_nuRFibre_zero` proved by hand that the ground state is tight at every
  side. It is now a corollary: at `k = 0` the class vector is `(d, 0, …, 0)`, so a combination
  fitting inside it has `a j ≥ 0` off class `0`; the coefficient sum forces `a 0 ≤ 0`; and the
  cosine sum becomes `∑_{j ≠ 0} a j (cosCls N j − 1) = 0` with every term `≤ 0`, so every term
  vanishes and **strictness finishes it**. `tight_at_zero` re-derives the old theorem
  (`orbit_eq_nuRFibre_zero_of_criterion`), which is what a general statement owes the special case
  it subsumes.

  **THE ONE GENUINELY NEW INEQUALITY, AND IT WAS ABSENT.** `cosCls_lt_one`: a nonzero class has
  `cosCls N j < 1`. Checked by BODY per `ERRATUM 627` — `awk` over `estate_types.txt` (14749
  statements, 1122 modules) for a statement naming `cosCls` under a strict inequality returns only
  `cosCls_subCls`, `cosCls_mirror` and `exists_not_tight_of_relation`, none of them this. It is
  three lines off Mathlib's `Real.cos_eq_one_iff_of_lt_of_lt` plus `Real.cos_le_one`. **It needs
  NO class hypothesis** — a first draft carried `2j ≤ N + 3` and the proof never used it, because
  `0 < x < 2π` already follows from `j < N + 3`, which every `Fin (N + 3)` carries (unit 84's
  remove-the-derivable-hypothesis discipline).

  **THE LEAST FAILING DIMENSION — the number this chain has declined to give for eight units.**
  `FailsAtDim N D` says some frequency in `Site D (N+3)` is not tight. `least_failing_dim_eq`
  characterises the smallest such `D` as **the minimum of `∑ a⁺` over non-zero cancelling
  combinations**: `≥` because a failure at `D` hands back a combination fitting inside a class
  vector of sum `D`, and `≤` because **`refFn a⁻`** — the NEGATIVE part — is a frequency that `a`
  fits inside, its dimension being `∑ a⁺` by `posSum_eq_neg`.
  **A FIRST DRAFT OF THAT SENTENCE SAID `refFn a⁺` AND IT IS FALSE**: `a⁺ + a` is negative exactly
  where `a` is. The two parts have equal totals only because the coefficient sum vanishes, and
  which of them has to fit is not a matter of taste — it is the one that cancels against `a`.

  **AND THE GENERAL LOWER BOUND, WHICH COSTS NOTHING BECAUSE THIS CHAIN ALREADY OWNS IT.**
  `two_le_of_failsAtDim`: **no side fails below dimension `2`**, at every `N`. A first draft was
  going to argue it from the relation lattice — `∑ a⁺ = 1` forces `e_i − e_j`, hence two classes
  with equal cosines, contradicting unit 90's `cos_injOn_half`. **That argument is unnecessary.**
  Dimension `1` is unit 94's `TorusFibreTight.orbit_eq_nuRFibre`, already proved tight at every
  side, and dimension `0` is three lines; read through the biconditional they give the bound with
  no lattice reasoning at all. With unit 98's `sum_relFour_toNat = 2` this yields
  **`least_failing_dim_four`: the least failing dimension at side 4 is exactly `2`**, the number
  unit 97's hand-built pair `(0,2)`, `(1,1)` measured. *The general fact was reachable from a
  landed theorem, and the lattice argument would have been a second proof of something the chain
  had.*

  WHAT IS PROVED.

  * **`cosCls_lt_one`** — strict domination at a nonzero class, and `cosCls_zero_eq_one` is
    already unit 103's.
  * **`TightAt`**, `tightAt_of_noCosRelation`, **`orbit_eq_nuRFibre_iff`** — the biconditional,
    per frequency, at every dimension and mass. `tight_at_indep_mass` is the mass corollary.
  * **`tight_at_zero`** and `orbit_eq_nuRFibre_zero_of_criterion` — the ground state FROM the
    criterion, re-deriving unit 98's hand proof.
  * `not_tight_at_of_fits`, `exists_not_tight_at_of_fits` — the converse construction, in the
    SAME dimension.
  * **`IsRel`**, `posSum`, **`posSum_eq_neg`**, **`FailsAtDim`**, `failsAtDim_posSum`,
    `exists_rel_of_failsAtDim`, **`least_failing_dim_eq`**; `tightAt_dim_zero`,
    **`two_le_of_failsAtDim`**, **`least_failing_dim_four`**.
  * `tightAt_all_iff_prime` — unit 104's classification recovered by quantifying this file's
    criterion over all `k`, the `ERRATUM 201` check against the unit it descends from.

  WHAT IS **NOT** CLAIMED.

  * **NO CLOSED FORM for the set of tight frequencies at a composite side.** The criterion is a
    decidable condition on one frequency's class vector, not an enumeration; which frequencies of
    side 15 fail is a lattice-point question this file does not answer and does not cost
    (`ERRATUM 194`, `ERRATUM 246`).
  * **THE LEAST FAILING DIMENSION AT SIDE 9 IS STILL MEASURED AND NOT PROVED, and this file says
    exactly which case is missing.** `two_le_of_failsAtDim` rules out `∑ a⁺ = 1` at every side. The
    side-9 figure of `3` therefore needs only that **no combination has `∑ a⁺ = 2`** — that is,
    that no two class cosines of the ninth roots sum to two others. `least_failing_dim_eq` reduces
    unit 102's measurement to that single case, **and does not settle it**: it is the degree of
    `ℚ(cos 2π/9)` again, the fact unit 102 recorded as library-blocked (`ERRATUM 194`,
    `ERRATUM 246`). **NOT ATTEMPTED, NO COST OFFERED.** What has changed is that the obstruction is
    now one enumerable case rather than an open-ended lattice question, which is the whole value of
    having the characterisation.
  * **NO EIGENSPACE DIMENSION AT A GENERAL PRIME SIDE** — units 97 and 99 do sides 3 and 5, and
    nothing here changes that.
  * The three `TorusBoundTightIff` `_iff` theorems convert this criterion into eigenspace-dimension
    readings per frequency, and those compositions are stated here; **no new dimension formula is
    proved.**
  * Nothing over `ℂ` about the graph, nothing about the box, the cascade, the spine or any wall.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusCompositeSide

namespace TorusFreqTight

open Finset BoxGraph TorusOrbitInvariant TorusOrbitMultinomial TorusCosRelation
open TorusBoundTightIff TorusHyperoctahedral MassiveTorusSpectrum MultinomialFibreCount
open TorusFibreOrbitPartition
open Real

variable {d N : ℕ}

/-! ## the strict inequality the ground state needs -/

/-- **A NONZERO CLASS HAS COSINE STRICTLY BELOW ONE.** The class angle `2πj/(N+3)` lies in
`(0, π]` when `0 < j` and `2j ≤ N + 3`, so it is not a multiple of `2π`. Absent from the estate:
`awk` over `estate_types.txt` for `cosCls` under a strict inequality returns nothing of this
shape (`ERRATUM 627`'s rule, the BODY and not the name). -/
theorem cosCls_lt_one {j : Fin (N + 3)} (hj : (j : ℕ) ≠ 0) : cosCls N j < 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < (N : ℝ) + 3 := by positivity
  set x : ℝ := 2 * Real.pi * ((j : ℕ) : ℝ) / ((N : ℝ) + 3) with hx
  have hjpos : (0 : ℝ) < ((j : ℕ) : ℝ) := by
    have : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    exact_mod_cast this
  have hjlt : ((j : ℕ) : ℝ) < (N : ℝ) + 3 := by
    have h := (Nat.cast_lt (α := ℝ)).2 j.isLt
    push_cast at h
    linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  -- `x < 2π` needs only `j < N + 3`, which every `Fin (N + 3)` carries.
  have hxlt : x < 2 * Real.pi := by
    have hnum : 0 < 2 * Real.pi * ((N : ℝ) + 3) - 2 * Real.pi * ((j : ℕ) : ℝ) := by nlinarith
    have hq : 0 < (2 * Real.pi * ((N : ℝ) + 3) - 2 * Real.pi * ((j : ℕ) : ℝ)) / ((N : ℝ) + 3) :=
      div_pos hnum hden
    have heq : (2 * Real.pi * ((N : ℝ) + 3) - 2 * Real.pi * ((j : ℕ) : ℝ)) / ((N : ℝ) + 3)
        = 2 * Real.pi - x := by
      rw [hx]; field_simp
    rw [heq] at hq
    linarith
  have hgt : -(2 * Real.pi) < x := by linarith
  have hne : Real.cos x ≠ 1 := by
    intro h
    exact (ne_of_gt hxpos) ((Real.cos_eq_one_iff_of_lt_of_lt hgt hxlt).1 h)
  rw [cosCls]
  exact lt_of_le_of_ne (Real.cos_le_one x) hne

/-! ## the per-frequency criterion -/

/-- **`L102`'s QUESTION, ONE FREQUENCY AT A TIME.** No cancelling combination fits inside `k`'s own
class counts. Compare `TorusCosRelation.NoCosRelation`, which asks the same of the ZERO vector and
so of every frequency at once: this is that condition relativised to `k`, and the only change in
the proof it drives is which vector the combination must stay non-negative against. -/
def TightAt (N : ℕ) {d : ℕ} (k : Site d (N + 3)) : Prop :=
  ∀ a : Fin (N + 3) → ℤ, (∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0) →
    (∑ j, a j = 0) → (∑ j, (a j : ℝ) * cosCls N j = 0) →
    (∀ j, 0 ≤ (clsCount k j : ℤ) + a j) → ∀ j, a j = 0

/-- The side-wide condition is the per-frequency one at every frequency, immediately: a
combination that is zero outright is zero inside any box. -/
theorem tightAt_of_noCosRelation (h : NoCosRelation N) (k : Site d (N + 3)) : TightAt N k :=
  fun a hsupp hsum hcos _ => h a hsupp hsum hcos

/-- **THE FORWARD DIRECTION.** `TorusCosRelation.clsCount_eq_of_nuR_eq` already proves that
`clsCount k' − clsCount k` is a cancelling combination; the only new content is that it fits
inside `clsCount k`, which is immediate because `clsCount k + (clsCount k' − clsCount k)` IS
`clsCount k'` and counts are non-negative. -/
theorem clsCount_eq_of_tightAt {k : Site d (N + 3)} (h : TightAt N k) (m : ℝ)
    (k' : Site d (N + 3)) (heq : nuR N m k' = nuR N m k) :
    ∀ j, clsCount k' j = clsCount k j := by
  set a : Fin (N + 3) → ℤ := fun j => (clsCount k' j : ℤ) - (clsCount k j : ℤ) with ha
  have hsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0 := by
    intro j hj
    simp [ha, clsCount_eq_zero_of_not_class k hj, clsCount_eq_zero_of_not_class k' hj]
  have hsum : ∑ j, a j = 0 := by
    simp only [ha, Finset.sum_sub_distrib]
    rw [← Nat.cast_sum, ← Nat.cast_sum, sum_clsCount, sum_clsCount, sub_self]
  have hS : ∑ j, (clsCount k' j : ℝ) * (2 * cosCls N j)
      = ∑ j, (clsCount k j : ℝ) * (2 * cosCls N j) := by
    rw [nuR_eq_sum_clsCount, nuR_eq_sum_clsCount] at heq
    linarith
  have hcos : ∑ j, (a j : ℝ) * cosCls N j = 0 := by
    have hsplit : ∑ j, (a j : ℝ) * cosCls N j
        = (∑ j, (clsCount k' j : ℝ) * (2 * cosCls N j)
            - ∑ j, (clsCount k j : ℝ) * (2 * cosCls N j)) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [ha]
      push_cast
      ring
    rw [hsplit, hS, sub_self, zero_div]
  have hfit : ∀ j, 0 ≤ (clsCount k j : ℤ) + a j := by
    intro j; simp only [ha]; omega
  intro j
  have := h a hsupp hsum hcos hfit j
  simp only [ha] at this
  omega

/-- **THE CONVERSE, AND IT STAYS IN THE SAME DIMENSION.** A cancelling combination fitting inside
`clsCount k` gives a genuine second frequency of `Site d (N + 3)` — the coefficient sum is `0`, so
`clsCount k + a` still sums to `d` — with the same `νR` and different class counts. Unit 98's
`exists_not_tight_of_relation` had to produce a NEW dimension; this does not, which is exactly the
upgrade from *some dimension fails* to *this frequency fails*. -/
theorem not_tight_at_of_fits {k : Site d (N + 3)} (m : ℝ) (a : Fin (N + 3) → ℤ)
    (hasupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0) (hasum : ∑ j, a j = 0)
    (hacos : ∑ j, (a j : ℝ) * cosCls N j = 0)
    (hfit : ∀ j, 0 ≤ (clsCount k j : ℤ) + a j) {j₀ : Fin (N + 3)} (hj₀ : a j₀ ≠ 0) :
    orbit k ≠ nuRFibre N m k := by
  set c : Fin (N + 3) → ℕ := fun j => ((clsCount k j : ℤ) + a j).toNat with hc
  have hcz : ∀ j, (c j : ℤ) = (clsCount k j : ℤ) + a j := by
    intro j
    have h := hfit j
    simp only [hc]
    omega
  have hcsum : ∑ j, c j = Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    refine Nat.cast_injective (R := ℤ) ?_
    push_cast
    have h1 : ∑ j, (c j : ℤ) = ∑ j, ((clsCount k j : ℤ) + a j) :=
      Finset.sum_congr rfl (fun j _ => hcz j)
    rw [h1, Finset.sum_add_distrib, hasum, add_zero, ← Nat.cast_sum, sum_clsCount]
  have hcsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → c j = 0 := by
    intro j hj
    have h1 := clsCount_eq_zero_of_not_class k hj
    have h2 := hasupp j hj
    simp only [hc, h1, h2]
    rfl
  intro hcontra
  have hcount := clsCount_refFn c hcsum hcsupp
  have hnu : nuR N m (refFn c hcsum : Site d (N + 3)) = nuR N m k := by
    rw [nuR_eq_sum_clsCount, nuR_eq_sum_clsCount]
    refine congrArg (fun z => 2 * (d : ℝ) + m ^ 2 - z) ?_
    have hstep : ∑ j, (clsCount (refFn c hcsum : Site d (N + 3)) j : ℝ) * (2 * cosCls N j)
        = ∑ j, (c j : ℝ) * (2 * cosCls N j) :=
      Finset.sum_congr rfl (fun j _ => by rw [hcount j])
    rw [hstep]
    exact sum_mul_cos_eq_of_relation N c (clsCount k) a (fun j => by rw [hcz j]; ring) hacos
  have hmem : (refFn c hcsum : Site d (N + 3)) ∈ nuRFibre N m k :=
    (mem_nuRFibre_iff m _ _).2 hnu
  have horb : (refFn c hcsum : Site d (N + 3)) ∈ orbit k := hcontra ▸ hmem
  have hall := (mem_orbit_iff_cls k (refFn c hcsum)).1 horb j₀
  rw [show Fintype.card {i // cls (refFn c hcsum : Site d (N + 3)) i = j₀}
      = clsCount (refFn c hcsum : Site d (N + 3)) j₀ from rfl,
    show Fintype.card {i // cls k i = j₀} = clsCount k j₀ from rfl, hcount] at hall
  have := hcz j₀
  omega

/-- **`L102`'s QUESTION, ANSWERED PER FREQUENCY.** At every dimension, every mass and every
frequency: the eigenvalue fibre is a single hyperoctahedral orbit exactly when no cancelling
combination fits inside that frequency's class counts. -/
theorem orbit_eq_nuRFibre_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    orbit k = nuRFibre N m k ↔ TightAt N k := by
  constructor
  · intro h a hsupp hsum hcos hfit j
    by_contra hj
    exact not_tight_at_of_fits m a hsupp hsum hcos hfit hj h
  · intro h
    refine Finset.Subset.antisymm (orbit_subset_nuRFibre N m k) ?_
    intro k' hk'
    rw [mem_nuRFibre_iff] at hk'
    exact (mem_orbit_iff_cls k k').2 (clsCount_eq_of_tightAt h m k' hk')

/-- The mass is absent from `TightAt`, so tightness at a frequency cannot depend on it — unit 98's
`tight_indep_mass` one level down. -/
theorem tight_at_indep_mass (N : ℕ) (m m' : ℝ) (k : Site d (N + 3)) :
    orbit k = nuRFibre N m k ↔ orbit k = nuRFibre N m' k :=
  (orbit_eq_nuRFibre_iff N m k).trans (orbit_eq_nuRFibre_iff N m' k).symm

/-! ## the ground state, FROM the criterion -/

/-- At the ground state every coordinate is `0`, so every axis sits in class `0`. -/
theorem cls_zero_apply (N d : ℕ) (i : Fin d) : cls (0 : Site d (N + 3)) i = (0 : Fin (N + 3)) := by
  have h : ((0 : Site d (N + 3)) i) = (0 : Fin (N + 3)) := rfl
  simp only [cls, h, clsF, pairClass]
  rfl

theorem clsCount_zero_eq (N d : ℕ) (j : Fin (N + 3)) :
    clsCount (0 : Site d (N + 3)) j = if j = (0 : Fin (N + 3)) then d else 0 := by
  by_cases hj : j = (0 : Fin (N + 3))
  · subst hj
    have hcard :
        Fintype.card {i : Fin d // cls (0 : Site d (N + 3)) i = (0 : Fin (N + 3))} = d := by
      rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun i => cls_zero_apply N d i)),
        Fintype.card_fin]
    simpa [clsCount] using hcard
  · rw [if_neg hj, clsCount]
    refine Fintype.card_eq_zero_iff.2 ⟨fun q => ?_⟩
    exact hj (by rw [← q.2, cls_zero_apply])

/-- **THE GROUND STATE IS TIGHT AT EVERY SIDE, OUT OF THE CRITERION.** A combination fitting inside
`(d, 0, …, 0)` is non-negative off class `0`; the coefficient sum then forces `a 0 ≤ 0`; and the
cosine sum rearranges to `∑_{j ≠ 0} a j (cosCls N j − 1) = 0` in which every term is `≤ 0`, so
`cosCls_lt_one` makes every `a j` vanish and the sum returns `a 0 = 0`. **No eigenspace dimension
and no analysis** — unit 98 reached the same conclusion through
`TorusRealMultiplicity.ground_state_simple_real`, and this is the arithmetic proof of it. -/
theorem tight_at_zero (N d : ℕ) : TightAt N (0 : Site d (N + 3)) := by
  intro a hsupp hsum hcos hfit
  have hzero : ∀ j : Fin (N + 3), j ≠ 0 → 0 ≤ a j := by
    intro j hj
    have h := hfit j
    rw [clsCount_zero_eq, if_neg hj] at h
    omega
  -- the cosine sum, minus `1` times the coefficient sum, is supported off class `0`
  have hone : cosCls N (0 : Fin (N + 3)) = 1 := TorusEvenSide.cosCls_zero_eq_one
  have hsplit : ∑ j, (a j : ℝ) * (cosCls N j - 1) = 0 := by
    have h1 : ∑ j, (a j : ℝ) * (cosCls N j - 1)
        = (∑ j, (a j : ℝ) * cosCls N j) - ∑ j, (a j : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have h2 : ∑ j, (a j : ℝ) = 0 := by
      rw [← Int.cast_sum, hsum, Int.cast_zero]
    rw [h1, hcos, h2, sub_zero]
  have hterm : ∀ j ∈ Finset.univ, (a j : ℝ) * (cosCls N j - 1) ≤ 0 := by
    intro j _
    by_cases hj : j = (0 : Fin (N + 3))
    · subst hj; rw [hone]; simp
    · have h1 : (0 : ℝ) ≤ (a j : ℝ) := by exact_mod_cast hzero j hj
      have h2 : cosCls N j - 1 ≤ 0 := by
        have := cosCls_lt_one (N := N) (j := j) (by
          intro h0
          exact hj (Fin.ext h0))
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have hzeroterm := Finset.sum_eq_zero_iff_of_nonpos hterm |>.1 hsplit
  intro j
  by_cases hj : j = (0 : Fin (N + 3))
  · -- class `0`: recover it from the coefficient sum, every other coefficient being zero
    subst hj
    have hrest : ∀ i ∈ Finset.univ, i ≠ (0 : Fin (N + 3)) → a i = 0 := by
      intro i _ hi
      have h := hzeroterm i (Finset.mem_univ i)
      have h2 : cosCls N i - 1 < 0 := by
        have := cosCls_lt_one (N := N) (j := i) (by
          intro h0
          exact hi (Fin.ext h0))
        linarith
      have h3 : (a i : ℝ) = 0 := by
        rcases mul_eq_zero.1 h with h4 | h4
        · exact h4
        · exact absurd h4 (ne_of_lt h2)
      exact_mod_cast h3
    have := Finset.sum_eq_single_of_mem (0 : Fin (N + 3)) (Finset.mem_univ _) hrest
    rw [this] at hsum
    exact hsum
  · have h := hzeroterm j (Finset.mem_univ j)
    have h2 : cosCls N j - 1 < 0 := by
      have := cosCls_lt_one (N := N) (j := j) (by
        intro h0
        exact hj (Fin.ext h0))
      linarith
    have h3 : (a j : ℝ) = 0 := by
      rcases mul_eq_zero.1 h with h4 | h4
      · exact h4
      · exact absurd h4 (ne_of_lt h2)
    exact_mod_cast h3

/-- `ERRATUM 201`'s check: unit 98's `orbit_eq_nuRFibre_zero` out of this file's criterion, by a
route that mentions no eigenspace. The original is NOT withdrawn — it is the analytic proof and it
is the one that shows the fibre has exactly one element. -/
theorem orbit_eq_nuRFibre_zero_of_criterion (N d : ℕ) (m : ℝ) :
    orbit (0 : Site d (N + 3)) = nuRFibre N m (0 : Site d (N + 3)) :=
  (orbit_eq_nuRFibre_iff N m (0 : Site d (N + 3))).2 (tight_at_zero N d)

/-! ## the least failing dimension -/

/-- A cancelling combination of the side's class cosines: zero coefficient sum, zero cosine sum,
supported on the classes. Naming the predicate is what lets the least failing dimension be stated
as a minimum over a set rather than described in prose. -/
def IsRel (N : ℕ) (a : Fin (N + 3) → ℤ) : Prop :=
  (∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0) ∧ (∑ j, a j = 0) ∧
    (∑ j, (a j : ℝ) * cosCls N j = 0)

/-- The positive part's total — the dimension the combination needs in order to fit. -/
def posSum (N : ℕ) (a : Fin (N + 3) → ℤ) : ℕ := ∑ j, (a j).toNat

/-- **THE TWO PARTS HAVE THE SAME TOTAL**, because the coefficient sum is zero. This is why
"positive part" names a single number and not a choice of sign, and it is the step that makes the
NEGATIVE part — the one that actually has to fit inside a class vector — have size `posSum`. -/
theorem posSum_eq_neg {N : ℕ} {a : Fin (N + 3) → ℤ} (hsum : ∑ j, a j = 0) :
    posSum N a = ∑ j, (-a j).toNat := by
  refine Nat.cast_injective (R := ℤ) ?_
  push_cast [posSum]
  have hterm : ∀ j : Fin (N + 3),
      ((a j).toNat : ℤ) - ((-a j).toNat : ℤ) = a j := by
    intro j; omega
  have : ∑ j, (((a j).toNat : ℤ) - ((-a j).toNat : ℤ)) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]; exact hsum
  rw [Finset.sum_sub_distrib] at this
  linarith

/-- Some frequency of `Site D (N + 3)` is not tight. -/
def FailsAtDim (N D : ℕ) : Prop := ∃ k : Site D (N + 3), ¬ TightAt N k

/-- **`≤`: a non-zero combination fails at its own positive-part total.** The frequency is
`refFn a⁻` — the NEGATIVE part, which is what `a` has to fit inside, since `a⁻ j + a j` is `0`
where `a j < 0` and `a j ≥ 0` elsewhere. Its dimension is `posSum` by `posSum_eq_neg`. -/
theorem failsAtDim_posSum {N : ℕ} {a : Fin (N + 3) → ℤ} (hrel : IsRel N a)
    {j₀ : Fin (N + 3)} (hj₀ : a j₀ ≠ 0) : FailsAtDim N (posSum N a) := by
  obtain ⟨hsupp, hsum, hcos⟩ := hrel
  set q : Fin (N + 3) → ℕ := fun j => (-a j).toNat with hq
  have hqsum : ∑ j, q j = Fintype.card (Fin (posSum N a)) := by
    rw [Fintype.card_fin, posSum_eq_neg hsum]
  have hqsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → q j = 0 := by
    intro j hj; simp only [hq, hsupp j hj]; rfl
  refine ⟨refFn q hqsum, ?_⟩
  intro htight
  have hcount := clsCount_refFn q hqsum hqsupp
  have hfit : ∀ j, 0 ≤ (clsCount (refFn q hqsum : Site (posSum N a) (N + 3)) j : ℤ) + a j := by
    intro j
    rw [hcount j]
    simp only [hq]
    omega
  exact hj₀ (htight a hsupp hsum hcos hfit j₀)

/-- **`≥`: a failure at `D` hands back a combination whose positive part is at most `D`.** The
combination is the one the criterion refuses, and it fits inside a class vector summing to `D`. -/
theorem exists_rel_of_failsAtDim {N D : ℕ} (h : FailsAtDim N D) :
    ∃ a : Fin (N + 3) → ℤ, IsRel N a ∧ (∃ j, a j ≠ 0) ∧ posSum N a ≤ D := by
  obtain ⟨k, hk⟩ := h
  rw [TightAt] at hk
  push Not at hk
  obtain ⟨a, hsupp, hsum, hcos, hfit, j₀, hj₀⟩ := hk
  refine ⟨a, ⟨hsupp, hsum, hcos⟩, ⟨j₀, hj₀⟩, ?_⟩
  have hle : ∀ j, (-a j).toNat ≤ clsCount k j := by
    intro j
    have := hfit j
    omega
  calc posSum N a = ∑ j, (-a j).toNat := posSum_eq_neg hsum
    _ ≤ ∑ j, clsCount k j := Finset.sum_le_sum (fun j _ => hle j)
    _ = D := sum_clsCount k

/-- **THE LEAST FAILING DIMENSION, CHARACTERISED.** It is the smallest positive part of a non-zero
cancelling combination — `IsLeast` on both sides, so the two theorems above are exactly the two
inequalities. This is the object units 97 through 104 each recorded as *not attempted and not
costed*. -/
theorem least_failing_dim_eq (N D : ℕ)
    (hD : IsLeast {n : ℕ | ∃ a : Fin (N + 3) → ℤ, IsRel N a ∧ (∃ j, a j ≠ 0) ∧ posSum N a = n} D) :
    IsLeast {n : ℕ | FailsAtDim N n} D := by
  obtain ⟨⟨a, hrel, ⟨j₀, hj₀⟩, hpa⟩, hlb⟩ := hD
  refine ⟨hpa ▸ failsAtDim_posSum hrel hj₀, ?_⟩
  intro n hn
  obtain ⟨b, hbrel, ⟨j₁, hj₁⟩, hble⟩ := exists_rel_of_failsAtDim hn
  exact le_trans (hlb ⟨b, hbrel, ⟨j₁, hj₁⟩, rfl⟩) hble

/-! ## the classification recovered, and the two evaluations -/

/-- Dimension `0` is tight: every class count is `0`, so a combination fitting inside is
non-negative everywhere and its vanishing coefficient sum kills it. -/
theorem tightAt_dim_zero {N : ℕ} (k : Site 0 (N + 3)) : TightAt N k := by
  intro a _ hsum _ hfit
  have hz : ∀ j, clsCount k j = 0 := by
    intro j
    have h := sum_clsCount k
    have hle : clsCount k j ≤ ∑ i, clsCount k i :=
      Finset.single_le_sum (f := fun i => clsCount k i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  have hnn : ∀ j, 0 ≤ a j := by
    intro j
    have := hfit j
    rw [hz j] at this
    simpa using this
  intro j
  by_contra hj
  have hpos : 0 < a j := lt_of_le_of_ne (hnn j) (Ne.symm hj)
  have : 0 < ∑ i, a i :=
    Finset.sum_pos' (fun i _ => hnn i) ⟨j, Finset.mem_univ j, hpos⟩
  omega

/-- **NO SIDE FAILS BELOW DIMENSION TWO**, at every `N`. Not a new argument: dimension `1` is
unit 94's `TorusFibreTight.orbit_eq_nuRFibre`, tight at every side, and dimension `0` is the lemma
above. Read through `orbit_eq_nuRFibre_iff` they say no frequency of either dimension fails, so the
minimum of `∑ a⁺` over non-zero cancelling combinations is at least `2` — which is a statement
about the relation lattice obtained with no lattice reasoning at all. -/
theorem two_le_of_failsAtDim {N D : ℕ} (h : FailsAtDim N D) : 2 ≤ D := by
  rcases Nat.lt_or_ge D 2 with hlt | hge
  · exfalso
    obtain ⟨k, hk⟩ := h
    interval_cases D
    · exact hk (tightAt_dim_zero k)
    · exact hk ((orbit_eq_nuRFibre_iff N 0 k).1 (TorusFibreTight.orbit_eq_nuRFibre N 0 k))
  · exact hge

/-- **THE LEAST FAILING DIMENSION AT SIDE 4 IS EXACTLY `2`.** Unit 98's `relFour` is a non-zero
cancelling combination with `∑ a⁺ = 2`, so `2` fails; `two_le_of_failsAtDim` says nothing smaller
does. This is the number unit 97's hand-built pair `(0,2)`, `(1,1)` measured. -/
theorem least_failing_dim_four : IsLeast {n : ℕ | FailsAtDim 1 n} 2 := by
  refine ⟨?_, fun n hn => two_le_of_failsAtDim hn⟩
  have hrel : IsRel 1 relFour := ⟨relFour_supp, sum_relFour, sum_relFour_cos⟩
  have hne : relFour (0 : Fin 4) ≠ 0 := by decide
  have h := failsAtDim_posSum hrel hne
  rwa [show posSum 1 relFour = 2 from sum_relFour_toNat] at h



/-- `ERRATUM 201`'s check against unit 104: quantifying this file's per-frequency criterion over
every dimension and frequency returns that unit's side-wide classification. -/
theorem tightAt_all_iff_prime (N : ℕ) (m : ℝ) :
    (∀ (D : ℕ) (k : Site D (N + 3)), TightAt N k) ↔ Nat.Prime (N + 3) := by
  rw [← TorusCompositeSide.tight_iff_prime (N := N) m]
  constructor
  · intro h D k
    exact (orbit_eq_nuRFibre_iff N m k).2 (h D k)
  · intro h D k
    exact (orbit_eq_nuRFibre_iff N m k).1 (h D k)

end TorusFreqTight
