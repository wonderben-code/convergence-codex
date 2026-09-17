/-
  TorusCosRelation: the torus degeneracy bound is tight AT EVERY DIMENSION AND EVERY FREQUENCY of
  side `n` **if and only if** the side's class cosines admit no vanishing integer relation of zero
  coefficient sum — `L102`'s general question with the graph theory removed from one side

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §1 (Caesar: conquer the thing that makes the others fall)
  and §6 question 3 (*if the unit I just finished WAS a B, retry B→C right now, before touching
  the queue*). Unit 97 settled side 3 and side 4 by hand and wrote the general criterion **as
  prose in its own header**, adding that *the equivalence in this paragraph is NOT formalised
  here: the direction used below is the easy one*. This file is that paragraph, both directions,
  as theorems — so every further side is an arithmetic check rather than a new unit.

  **CHECKED ABSENT BEFORE BEING WRITTEN, with the queries run and reported rather than
  described** (`ERRATUM 621`, and unit 97's own too-narrow query, struck in that file's header, is
  why there are four of them).

  1. `awk` over `estate_types.txt` (14609 statements, 1116 modules) for a statement carrying BOTH
     `Real.cos` and an integer-valued function (`→ ℤ`): **nothing**.
  2. For a declaration whose NAME suggests a relation, independence, cyclotomic or vanishing-sum
     criterion: 140 hits, every one of them linear independence of vectors, a vanishing trace, a
     spin-class weight or a scaling relation. **Nothing about coincidences among cosines.**
  3. For an `iff` mentioning `orbit`: seven, and they are the criteria this chain already had —
     `TorusBoundTightIff`'s three, `TorusFibreOrbitPartition`'s two,
     `TorusOrbitCharacterisation.mem_orbit_iff` and `TorusOrbitMultinomial.mem_orbit_iff_cls`.
     **Every one of them fixes `d` and `k` and has a geometric left side**; none quantifies over
     the dimension and none has an arithmetic one.
  4. Mathlib, case-insensitively, for `conway.*jones`, `redei`, `schoenberg`: **no file**. This
     re-confirms the probe `L102` records, and it is the reason the criterion is stated rather
     than decided.

  WHAT IS PROVED.

  * **`clsCount`, `cosCls`, `sum_over_classes`, `nuR_eq_sum_clsCount`** — `νR` sees only the
    CLASS-COUNT VECTOR: `νR N m k = 2d + m² − ∑ⱼ cⱼ(k)·2cos(2πj/n)`, where `cⱼ(k)` counts the
    axes of mirror class `j`. The regrouping is `Finset.sum_fiberwise'` over `cls`, and the step
    that lets a frequency be replaced by its class is unit 94's
    `TorusFibreTight.cos_pairClass`.
  * **`NoCosRelation N`** — the arithmetic condition, and it mentions no graph, no orbit and no
    eigenspace: every `a : Fin (N+3) → ℤ` supported on the pair classes (`2j ≤ N+3`) with
    `∑ⱼ aⱼ = 0` and `∑ⱼ aⱼ·cos(2πj/n) = 0` is zero.
  * **`orbit_eq_nuRFibre_of_noCosRelation`** — **the forward direction**: the condition makes the
    `νR` fibre the hyperoctahedral orbit at EVERY dimension, every mass and every frequency. The
    proof is three lines of content: the difference of two class-count vectors is supported on the
    classes (`TorusFibreTight.two_mul_pairClass_le`), sums to zero (`sum_clsCount`), and is
    cosine-orthogonal (`nuR_eq_sum_clsCount`) — so it is a relation, hence zero, hence
    `TorusOrbitMultinomial.mem_orbit_iff_cls` applies.
  * **`exists_not_tight_of_relation`** — **the converse, and it is a construction**: a non-zero
    relation `a` gives `p = a⁺`, `q = a⁻` with `∑p = ∑q = D`, and
    `MultinomialFibreCount.refFn` turns each into an actual frequency in `Site D (N+3)` whose
    class-count vector is `p` respectively `q` (`clsCount_refFn`, off `card_refFn_fibre` and
    `pairClass_self`). The two have the same `νR` and different class counts, so the fibre is
    strictly bigger than the orbit at that `D`.
  * **`noCosRelation_iff`** — **the biconditional**, at every mass. `L102`'s general question is
    now a question about integers and cosines.
  * **`bound_eq_finrank_of_noCosRelation`, `card_orbit_eq_finrank_of_noCosRelation`,
    `card_orbitsOf_eq_one_of_noCosRelation`** — the three readings, at every dimension.
  * **`tight_indep_mass`** — a free corollary worth naming: since the left side of the
    biconditional does not mention `m`, **the mass never affects tightness**.
  * **`orbit_eq_nuRFibre_zero`** — the ground state is tight at every side and every dimension,
    which is what makes the paragraph below a limitation and not a hedge.
  * **`cosCls_zero`, `noCosRelation_zero`** and **`cosCls_one`, `relFour`,
    `not_noCosRelation_one`** — the condition HOLDS at side 3 and FAILS at side 4, with
    `a = (1, −2, 1, 0)` exhibited, so the criterion is neither vacuous nor trivial inside its own
    file. **`side_three_tight_of_criterion` re-derives unit 97's side-3 theorem** from the general
    one, which is the check a new general statement owes its predecessor (`ERRATUM 201`, the shape
    `TorusOrbitMultinomial.card_orbit_eq_two_pow_mul_factorial` used), and
    `exists_not_tight_side_four` is the side-4 failure through the criterion instead of by hand.
    **`sum_relFour_toNat`** records that the construction lands at `D = 2` — the same dimension as
    unit 97's hand-built pair `(0,2)`, `(1,1)`.

  **WHAT THIS IS A REDUCTION OF, AND WHAT IT IS NOT.** `L102` asks **which** frequencies give a
  one-orbit fibre. This file answers **when ALL of them do**, uniformly in the dimension, and that
  is strictly less. The two are genuinely different, and the difference is **proved here rather
  than asserted**: `orbit_eq_nuRFibre_zero` shows the ground state `k = 0` is tight at EVERY side
  and every dimension — including side 4, where the criterion fails — because
  `TorusRealMultiplicity.ground_state_simple_real` makes that eigenspace one-dimensional and
  `TorusHyperoctahedral.one_le_card_orbit` fills it. **So a side that fails the criterion still
  has tight frequencies, and this file says nothing about which.** The per-frequency question
  stays exactly as open as `L102` records. (A first draft of this paragraph justified the same
  example by `MassiveTorusSpectrum.sq_le_nuR` and `nuR_at_zero`, which give that `m²` is the
  MINIMUM and not that it is attained once — the fibre's size is what is wanted, and the
  ground-state theorem is what gives it. Struck and replaced by the theorem.)

  WHAT IS **NOT** CLAIMED.

  * **`NoCosRelation N` IS NOT DECIDED AT ANY SIDE BUT 3 AND 4.** Deciding it in general is the
    classification of vanishing sums of roots of unity, which the pinned Mathlib does not have
    (query 4 above). **No cost is offered** (`ERRATUM 42`, `ERRATUM 194`, `ERRATUM 246`).
  * **NO UPPER BOUND ON ANY MULTIPLICITY AT A FAILING SIDE.** The converse exhibits a dimension
    where the bound is strict; it does not say by how much, and nothing here bounds the number of
    orbits in a fibre.
  * **SIDE 5 IS STILL NOT PROVED**, though it is now one arithmetic check rather than a unit: unit
    97 measured it tight for `d ≤ 4`, and `Real.cos_pi_div_five` plus the irrationality of `√5`
    would settle `NoCosRelation 2`. Not done here, named so it is not rediscovered.
  * **NOTHING ABOUT THE BOX.** Its angles run over a half turn and its eigenvalue index is not a
    mirror class, so `cls` and this criterion do not transfer; that is a different chain.
  * **NOTHING OVER `ℂ`, NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusSideThree

namespace TorusCosRelation

open Finset BoxGraph TorusHyperoctahedral TorusReflectionCount MassiveTorusSpectrum
open TorusBoundTightIff TorusOrbitInvariant TorusOrbitCharacterisation
open TorusFibreOrbitPartition TorusOrbitMultinomial TorusReflection GraphLaplacian
open MultinomialFibreCount TorusFibreTight
open Real

variable {d N : ℕ}

/-- The number of axes in class `j`. -/
def clsCount (k : Site d (N + 3)) (j : Fin (N + 3)) : ℕ := Fintype.card {i // cls k i = j}

/-- The class-`j` cosine at side `N + 3`. -/
noncomputable def cosCls (N : ℕ) (j : Fin (N + 3)) : ℝ :=
  Real.cos (2 * π * ((j : ℕ) : ℝ) / ((N : ℝ) + 3))

theorem sum_over_classes (k : Site d (N + 3)) (f : Fin (N + 3) → ℝ) :
    ∑ i : Fin d, f (cls k i) = ∑ j, (clsCount k j : ℝ) * f j := by
  classical
  rw [← Finset.sum_fiberwise' (univ : Finset (Fin d)) (cls k) f]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_const, clsCount, Fintype.card_subtype, nsmul_eq_mul]

theorem sum_clsCount (k : Site d (N + 3)) : ∑ j, clsCount k j = d := by
  classical
  have h := sum_over_classes k (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have : ((d : ℝ)) = ((∑ j, clsCount k j : ℕ) : ℝ) := by push_cast; linarith
  exact (Nat.cast_injective this).symm

theorem cos_cls (k : Site d (N + 3)) (i : Fin d) :
    cosCls N (cls k i) = Real.cos (2 * π * (((k i : Fin (N+3)) : ℕ) : ℝ) / ((N : ℝ) + 3)) := by
  have h : ((cls k i : Fin (N+3)) : ℕ) = pairClass N ((k i : Fin (N+3)) : ℕ) := rfl
  rw [cosCls, h]
  have := cos_pairClass (N := N) (a := ((k i : Fin (N+3)) : ℕ)) (k i).isLt
  push_cast at this ⊢
  exact this

/-- `νR` sees only the class-count vector. -/
theorem nuR_eq_sum_clsCount (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nuR N m k = 2 * d + m ^ 2 - ∑ j, (clsCount k j : ℝ) * (2 * cosCls N j) := by
  rw [nuR, ← sum_over_classes k (fun j => 2 * cosCls N j)]
  refine congrArg (fun z => 2 * (d : ℝ) + m ^ 2 - z) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [cos_cls]

/-- **THE ARITHMETIC CONDITION.** -/
def NoCosRelation (N : ℕ) : Prop :=
  ∀ a : Fin (N + 3) → ℤ, (∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0) →
    (∑ j, a j = 0) → (∑ j, (a j : ℝ) * cosCls N j = 0) → ∀ j, a j = 0

theorem clsCount_eq_zero_of_not_class (k : Site d (N + 3)) {j : Fin (N + 3)}
    (hj : N + 3 < 2 * (j : ℕ)) : clsCount k j = 0 := by
  refine Fintype.card_eq_zero_iff.2 ⟨fun p => ?_⟩
  have h : pairClass N ((k p.1 : Fin (N + 3)) : ℕ) = (j : ℕ) := congrArg Fin.val p.2
  have hle := two_mul_pairClass_le (N := N) (a := ((k p.1 : Fin (N + 3)) : ℕ)) (k p.1).isLt
  omega

theorem clsCount_eq_of_nuR_eq (h : NoCosRelation N) (m : ℝ) (k k' : Site d (N + 3))
    (heq : nuR N m k' = nuR N m k) : ∀ j, clsCount k' j = clsCount k j := by
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
    rw [hsplit, hS]
    ring
  intro j
  have hz := h a hsupp hsum hcos j
  simp only [ha] at hz
  omega

/-- **THE FIBRE IS THE ORBIT AT EVERY DIMENSION, FROM THE ARITHMETIC CONDITION ALONE.** -/
theorem orbit_eq_nuRFibre_of_noCosRelation (h : NoCosRelation N) (m : ℝ) (k : Site d (N + 3)) :
    orbit k = nuRFibre N m k := by
  refine Finset.Subset.antisymm (orbit_subset_nuRFibre N m k) ?_
  intro k' hk'
  rw [mem_nuRFibre_iff] at hk'
  exact (mem_orbit_iff_cls k k').2 (clsCount_eq_of_nuR_eq h m k k' hk')

/-! ## instances -/

theorem cosCls_zero (j : Fin 3) : cosCls 0 j = if (j : ℕ) = 0 then 1 else -(1 / 2) := by
  have h := TorusSideThree.two_cos_val j
  rw [cosCls]
  split_ifs at h ⊢ with hj
  · push_cast at h ⊢; linarith
  · push_cast at h ⊢; linarith

theorem noCosRelation_zero : NoCosRelation 0 := by
  intro a hsupp hsum hcos
  have h2 : a 2 = 0 := hsupp 2 (by norm_num)
  rw [Fin.sum_univ_three] at hsum
  rw [Fin.sum_univ_three, cosCls_zero, cosCls_zero, cosCls_zero] at hcos
  norm_num at hcos
  have hz : (2 * a 0 : ℤ) = a 1 := by
    have hr : ((2 * a 0 : ℤ) : ℝ) = ((a 1 : ℤ) : ℝ) := by
      push_cast
      rw [h2] at hcos
      push_cast at hcos
      linarith
    exact Int.cast_injective hr
  have e0 : a 0 = 0 := by omega
  have e1 : a 1 = 0 := by omega
  intro j
  fin_cases j
  · exact e0
  · exact e1
  · exact h2

theorem cosCls_one (j : Fin 4) :
    cosCls 1 j = if (j : ℕ) = 0 then 1 else if (j : ℕ) = 2 then -1 else 0 := by
  have h := TorusSideThree.two_cos_val_four j
  rw [cosCls]
  split_ifs at h ⊢ <;> (push_cast at h ⊢; linarith)

/-- The relation at side `4`: `1 · cos 0 − 2 · cos(π/2) + 1 · cos π = 0`, coefficients summing
to zero. -/
def relFour : Fin 4 → ℤ :=
  fun j => if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then -2 else if (j : ℕ) = 2 then 1 else 0

theorem not_noCosRelation_one : ¬ NoCosRelation 1 := by
  intro h
  have hsupp : ∀ j : Fin 4, 1 + 3 < 2 * (j : ℕ) → relFour j = 0 := by
    intro j hj
    have := j.isLt
    fin_cases j <;> simp_all [relFour]
  have hsum : ∑ j, relFour j = 0 := by decide
  have hcos : ∑ j, (relFour j : ℝ) * cosCls 1 j = 0 := by
    rw [Fin.sum_univ_four, cosCls_one, cosCls_one, cosCls_one, cosCls_one]
    norm_num [relFour]
  have h0 := h relFour hsupp hsum hcos 0
  simp [relFour] at h0

/-! ## the converse -/

theorem pairClass_self {N j : ℕ} (hj : j < N + 3) (hc : 2 * j ≤ N + 3) :
    pairClass N j = j := by
  unfold pairClass
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simp
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem refFn_val_pos (p : Fin (N + 3) → ℕ) (hp : ∑ j, p j = Fintype.card (Fin d)) (i : Fin d) :
    0 < p (refFn p hp i) := by
  have h := card_refFn_fibre p hp (refFn p hp i)
  have hpos : 0 < Fintype.card {i' // refFn p hp i' = refFn p hp i} :=
    Fintype.card_pos_iff.2 ⟨⟨i, rfl⟩⟩
  omega

theorem cls_refFn (p : Fin (N + 3) → ℕ) (hp : ∑ j, p j = Fintype.card (Fin d))
    (hsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → p j = 0) (i : Fin d) :
    cls (refFn p hp : Site d (N + 3)) i = refFn p hp i := by
  have hpos := refFn_val_pos p hp i
  have hcl : 2 * ((refFn p hp i : Fin (N + 3)) : ℕ) ≤ N + 3 := by
    by_contra hc
    rw [hsupp _ (by omega)] at hpos
    omega
  exact Fin.ext (by
    rw [cls_apply_val]
    exact pairClass_self (refFn p hp i).isLt hcl)

theorem clsCount_refFn (p : Fin (N + 3) → ℕ) (hp : ∑ j, p j = Fintype.card (Fin d))
    (hsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → p j = 0) (j : Fin (N + 3)) :
    clsCount (refFn p hp : Site d (N + 3)) j = p j := by
  rw [clsCount, ← card_refFn_fibre p hp j]
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight (fun i => by rw [cls_refFn p hp hsupp i]))

theorem sum_mul_cos_eq_of_relation (N : ℕ) (p q : Fin (N + 3) → ℕ) (a : Fin (N + 3) → ℤ)
    (hpq : ∀ j, (p j : ℤ) - (q j : ℤ) = a j) (hacos : ∑ j, (a j : ℝ) * cosCls N j = 0) :
    ∑ j, (p j : ℝ) * (2 * cosCls N j) = ∑ j, (q j : ℝ) * (2 * cosCls N j) := by
  have hterm : ∀ j : Fin (N + 3), (p j : ℝ) * (2 * cosCls N j)
      = (q j : ℝ) * (2 * cosCls N j) + 2 * ((a j : ℝ) * cosCls N j) := by
    intro j
    have hr : ((p j : ℕ) : ℝ) = ((q j : ℕ) : ℝ) + ((a j : ℤ) : ℝ) := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) (hpq j)
      push_cast at hc ⊢
      linarith
    rw [hr]; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum,
    hacos, mul_zero, add_zero]

/-- **AND THE CONVERSE, TAKING THE RELATION AS DATA**: a non-zero integer vector on the pair
classes with zero coefficient sum and zero cosine-weighted sum produces a dimension and a
frequency at which the fibre is strictly bigger than the orbit. -/
theorem exists_not_tight_of_relation (N : ℕ) (m : ℝ) (a : Fin (N + 3) → ℤ)
    (hasupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → a j = 0) (hasum : ∑ j, a j = 0)
    (hacos : ∑ j, (a j : ℝ) * cosCls N j = 0) {j₀ : Fin (N + 3)} (hj₀ : a j₀ ≠ 0) :
    ∃ (D : ℕ) (k : Site D (N + 3)), orbit k ≠ nuRFibre N m k := by
  set p : Fin (N + 3) → ℕ := fun j => (a j).toNat with hpdef
  set q : Fin (N + 3) → ℕ := fun j => (-a j).toNat with hqdef
  have hpq : ∀ j, (p j : ℤ) - (q j : ℤ) = a j := by
    intro j; simp only [hpdef, hqdef]; omega
  have hsums : ∑ j, p j = ∑ j, q j := by
    refine Nat.cast_injective (R := ℤ) ?_
    push_cast
    have hzero : ∑ j, ((p j : ℤ) - (q j : ℤ)) = 0 := by
      rw [Finset.sum_congr rfl (fun j _ => hpq j)]; exact hasum
    rw [Finset.sum_sub_distrib] at hzero
    linarith
  set D : ℕ := ∑ j, p j with hD
  have hp : ∑ j, p j = Fintype.card (Fin D) := by rw [Fintype.card_fin]
  have hq : ∑ j, q j = Fintype.card (Fin D) := by rw [Fintype.card_fin, ← hsums]
  have hpsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → p j = 0 := by
    intro j hj; simp only [hpdef, hasupp j hj]; rfl
  have hqsupp : ∀ j : Fin (N + 3), N + 3 < 2 * (j : ℕ) → q j = 0 := by
    intro j hj; simp only [hqdef, hasupp j hj]; rfl
  refine ⟨D, refFn p hp, ?_⟩
  intro hcontra
  have hcount_p := clsCount_refFn p hp hpsupp
  have hcount_q := clsCount_refFn q hq hqsupp
  have hnu : nuR N m (refFn q hq : Site D (N + 3)) = nuR N m (refFn p hp : Site D (N + 3)) := by
    rw [nuR_eq_sum_clsCount, nuR_eq_sum_clsCount]
    simp only [hcount_p, hcount_q]
    rw [sum_mul_cos_eq_of_relation N p q a hpq hacos]
  have hmem : (refFn q hq : Site D (N + 3)) ∈ nuRFibre N m (refFn p hp) :=
    (mem_nuRFibre_iff m _ _).2 hnu
  have horb : (refFn q hq : Site D (N + 3)) ∈ orbit (refFn p hp) := hcontra ▸ hmem
  have hall := (mem_orbit_iff_cls (refFn p hp : Site D (N + 3)) (refFn q hq)).1 horb j₀
  rw [show Fintype.card {i // cls (refFn q hq : Site D (N + 3)) i = j₀}
      = clsCount (refFn q hq : Site D (N + 3)) j₀ from rfl,
    show Fintype.card {i // cls (refFn p hp : Site D (N + 3)) i = j₀}
      = clsCount (refFn p hp : Site D (N + 3)) j₀ from rfl,
    hcount_p, hcount_q] at hall
  simp only [hpdef, hqdef] at hall
  omega

/-- **L102's GENERAL QUESTION, WITH THE GRAPH THEORY REMOVED FROM ONE SIDE.** -/
theorem noCosRelation_iff (N : ℕ) (m : ℝ) :
    NoCosRelation N ↔ ∀ (D : ℕ) (k : Site D (N + 3)), orbit k = nuRFibre N m k := by
  constructor
  · intro h D k
    exact orbit_eq_nuRFibre_of_noCosRelation h m k
  · intro h a hsupp hsum hcos j
    by_contra hj
    obtain ⟨D, k, hk⟩ := exists_not_tight_of_relation N m a hsupp hsum hcos hj
    exact hk (h D k)

/-! ## readings and the two sides -/

theorem bound_eq_finrank_of_noCosRelation (h : NoCosRelation N) (m : ℝ) (k : Site d (N + 3)) :
    (2 ^ (interiorAxes k).card * Nat.multinomial univ fun c => Fintype.card {i // cls k i = c})
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - nuR N m k • LinearMap.id).ker :=
  (bound_eq_finrank_iff N m k).2 (orbit_eq_nuRFibre_of_noCosRelation h m k)

theorem card_orbit_eq_finrank_of_noCosRelation (h : NoCosRelation N) (m : ℝ)
    (k : Site d (N + 3)) :
    (orbit k).card
      = Module.finrank ℝ
          (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - nuR N m k • LinearMap.id).ker :=
  (card_orbit_eq_finrank_iff N m k).2 (orbit_eq_nuRFibre_of_noCosRelation h m k)

theorem card_orbitsOf_eq_one_of_noCosRelation (h : NoCosRelation N) (m : ℝ)
    (k : Site d (N + 3)) : (orbitsOf N m k).card = 1 :=
  (card_orbitsOf_eq_one_iff N m k).2 (orbit_eq_nuRFibre_of_noCosRelation h m k)

/-- **THE CRITERION RECOVERS UNIT 97's SIDE-3 THEOREM**, which was proved independently. -/
theorem side_three_tight_of_criterion (m : ℝ) (k : Site d 3) : orbit k = nuRFibre 0 m k :=
  (noCosRelation_iff 0 m).1 noCosRelation_zero d k

theorem exists_not_tight_side_four (m : ℝ) :
    ∃ (D : ℕ) (k : Site D (1 + 3)), orbit k ≠ nuRFibre 1 m k := by
  by_contra hc
  refine not_noCosRelation_one ((noCosRelation_iff 1 m).2 ?_)
  intro D k
  by_contra hk
  exact hc ⟨D, k, hk⟩

/-- **AND THE CONSTRUCTION LANDS AT `d = 2`** — the dimension of unit 97's hand-built pair. -/
theorem sum_relFour_toNat : ∑ j, (relFour j).toNat = 2 := by decide

/-- **AND A SIDE THAT FAILS THE CRITERION STILL HAS TIGHT FREQUENCIES.** The ground state is
tight at every side and every dimension, so the criterion is a statement about the SIDE and not
about any one frequency. -/
theorem orbit_eq_nuRFibre_zero (N d : ℕ) (m : ℝ) :
    orbit (0 : Site d (N + 3)) = nuRFibre N m (0 : Site d (N + 3)) := by
  have hf : (nuRFibre N m (0 : Site d (N + 3))).card = 1 := by
    rw [← finrank_eq_card_nuRFibre, nuR_at_zero]
    exact TorusRealMultiplicity.ground_state_simple_real N m
  refine Finset.eq_of_subset_of_card_le (orbit_subset_nuRFibre N m 0) ?_
  rw [hf]
  exact one_le_card_orbit 0

/-- **THE MASS NEVER AFFECTS TIGHTNESS**, because the criterion does not mention it. -/
theorem tight_indep_mass (N : ℕ) (m m' : ℝ) :
    (∀ (D : ℕ) (k : Site D (N + 3)), orbit k = nuRFibre N m k)
      ↔ ∀ (D : ℕ) (k : Site D (N + 3)), orbit k = nuRFibre N m' k :=
  (noCosRelation_iff N m).symm.trans (noCosRelation_iff N m')

end TorusCosRelation
