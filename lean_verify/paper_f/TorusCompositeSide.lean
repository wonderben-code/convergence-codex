/-
  TorusCompositeSide: EVERY COMPOSITE side fails — so the criterion is **exactly primality**, and
  `L102`'s arithmetic question is closed: the torus degeneracy bound is an equality at every
  dimension, every mass and every frequency of side `n` **if and only if `n` is prime**

  WHY THIS FILE EXISTS, AND IT IS UNIT 103'S OWN SENTENCE. That unit proved every even side fails
  and then wrote, under `WHAT IS NOT CLAIMED`: *a guess is available and is deliberately not made:
  side 9's relation came from `3 ∣ 9`, so a divisor-based family may exist; no such family is
  proved, attempted or costed.* **This is that family, and it is unit 103's own argument with the
  divisor `2` replaced by an arbitrary one.** Unit 103 is the `q = 2` case and unit 102's side 9 is
  `q = r = 3`; both are re-derived here and neither original is deleted. `ERRATUM 628` records the
  lesson, which is `ERRATUM 626`'s for the third time in a day: **specialise, or generalise, the
  PARAMETER.**

  **THE ARGUMENT.** Let `n = q·r` with `q, r ≥ 2`. The `q`-th roots of unity sit inside the `n`-th
  as the powers of `ζ^r`, and their sum is zero, so `∑_{i<q} cos(2πi/q) = 0` — and
  `cos(2π·(i·r)/n) = cos(2πi/q)` because `n = q·r`, so in CLASS coordinates that is a relation
  whose coefficient sum is `q`. The fibre-size vector is a relation whose coefficient sum is `n`
  (unit 103's `A`). So `a = n·sub − q·fibre` has coefficient sum `n·q − q·n = 0` and cosine sum
  `0`. **It is non-zero at class `1`, and that is the only step that uses `r ≥ 2`**: no `i·r` has
  class `1`, because `pairClass(i·r) = 1` forces `i·r = 1` or `n − i·r = 1`, and `r` divides both
  `i·r` and `n`, so either way `r ∣ 1`. Hence `a` at class `1` is `−q·fibreCount(1) ≤ −q < 0`.

  **THE CLASSIFICATION IS NOW COMPLETE.** With unit 100's converse:

  | side `n ≥ 3` | tight at every dimension and frequency? |
  |---|---|
  | prime | **YES** — unit 100 |
  | composite | **NO** — this unit |

  `noCosRelation_iff_prime` and **`tight_iff_prime`** state it. Every side is one or the other, so
  **there is no residue left in the arithmetic question at all** — which is the first time in this
  chain that a sentence like that can be written, and it is worth being precise about what it does
  and does not settle (below).

  **CHECKED ABSENT BY `ERRATUM 627`'s RULE — the BODY, not the name.** `awk` over
  `estate_types.txt` (14727 statements, 1121 modules) for each of the twenty-two names here returns
  nothing, and `grep -rn` for the bodies of `subCls`, `relComp` and the class-`1` element returns
  nothing outside this file — **except that the class-`1` element WAS already here**, as unit 103's
  `clsOne`, carrying an even-side hypothesis it never used. **Rather than duplicate it, unit 103's
  definition is edited in place**: `clsOne` becomes `cls1`, the hypothesis is dropped (unit 84's
  remove-the-derivable-hypothesis discipline), and this file consumes it. `ERRATUM 627`'s rule
  found that one, one unit after it was written.

  **^ THAT PARAGRAPH IS WRONG IN BOTH OF ITS NUMBERS AND IT IS KEPT AS WRITTEN (`ERRATUM 94`,
  `ERRATUM 629`), WITH THE CORRECTION HERE.** The count is **TWENTY-THREE**, not twenty-two —
  `grep -cE '^(theorem|lemma|def|noncomputable def|abbrev|instance) '` on this file says 23, and
  that command is now the one that produces the number (`ERRATUM 58`: a number about this
  project's own records is produced by counting, in the same command that writes it). **The name
  the miscount dropped is `noCosRelation_zero_of_prime'`, and its STATEMENT WAS ALREADY IN THE
  ESTATE** — `TorusPrimeSide.noCosRelation_zero_of_prime : NoCosRelation 0`, the identical
  proposition, in a module this file imports, exactly as in `ERRATUM 627`. **The query missed it
  because the name-matching pattern treats `'` as a terminator**, and that same blind spot had
  already been worked around ONCE in this very unit — the axiom audit's declaration regex dropped
  the same name, so that one declaration was audited by hand — and the workaround was not carried
  over to the absence query (`ERRATUM 348`'s reachability lesson in a different costume). Re-run
  with `[A-Za-z0-9_']+`, all **23** names resolve to exactly one module and it is this one, so
  **there is no duplicate to remove**; and the axiom audit re-run the same way covers all 23,
  **21 on `[propext, Classical.choice, Quot.sound]` and 2 on `[propext, Quot.sound]`**. The
  declaration below is not withdrawn and not renamed — see its docstring for why.

  WHAT IS PROVED.

  * **`sum_cos_turn`** — `∑_{i<q} cos(2πi/q) = 0` for every `q ≥ 2`, off `geom_sum_eq` on
    `CycleLaplacianSpectrum.zeta q` and `Complex.re_sum`. **This is unit 102's
    `sum_cosCls_eq_zero` off the `N + 3` shape**, which is what the composite argument needs,
    because the divisor `q` can be `2`.
  * **`subCls`, `subCount`, `sum_subCount`, `cosCls_subCls`, `sum_subCount_cos`** — the `q` inner
    frequencies in class coordinates: coefficient sum `q`, cosine sum `0`.
  * **`two_mul_subCls_le`, `subCount_eq_zero_of_not_class`, `subCount_cls1_eq_zero`** — the
    support, and the divisibility step that makes class `1` the witness.
  * **`relComp`** and its four obligations (`sum_relComp`, `sum_relComp_cos`, `relComp_supp`,
    `relComp_cls1_ne_zero`), then **`not_noCosRelation_of_composite`**.
  * **`prime_of_noCosRelation`** — tightness forces a PRIME side, off
    `Nat.exists_dvd_of_not_prime2`; and **`noCosRelation_iff_prime`**, **`tight_iff_prime`**,
    `exists_not_tight_of_not_prime`.
  * **`not_noCosRelation_of_even_of_composite`** (unit 103, `q = 2`),
    **`not_noCosRelation_six_of_composite`** (unit 102's side 9, `q = r = 3`),
    `noCosRelation_zero_of_prime'` (side 3), and **`not_noCosRelation_twelve`** — **side 15, the
    smallest odd composite nobody had settled**, now one line.

  **WHAT THIS CLOSES, AND WHAT IT DOES NOT — the distinction is the whole of the honest reading.**
  `L102` asks *which eigenvalue fibres of the massive torus Laplacian are a SINGLE hyperoctahedral
  orbit — equivalently, when the estate's degeneracy bound is an equality rather than an
  inequality.* The **uniform** reading of that — for which sides is EVERY fibre a single orbit — is
  now answered completely and with no residue. **The per-frequency reading is not.** At a composite
  side some frequencies are still tight: `TorusCosRelation.orbit_eq_nuRFibre_zero` proves the
  ground state is, at every side. **Which frequencies those are is untouched, and it is what the
  item literally asks.** Whether that makes the item closable is a documentation question and the
  author's to answer — it is the shape of `DECISIONS NEEDED` item 9 — so **nothing here marks it
  closed.**

  **^ THE DISPOSITION IS RIGHT AND BOTH REASONS GIVEN FOR IT ARE WRONG. THE SENTENCE IS KEPT AS
  WRITTEN (`ERRATUM 94`, `ERRATUM 630`).** First, **the citation is false**: `DECISIONS NEEDED <n>`
  means `ASSUMPTIONS_LEDGER` entry `<n>` throughout this estate, and **entry 9 is "su(3) ⊕ su(2) ⊕
  u(1) does not embed in su(4) on the blocks used"** — the Standard-Model embedding, unrelated. The
  entry of this species is **55** (*every finite-volume OS shadow now exists, so whether the item
  titled "for the lattice field" is finished is a reading of its own title*); **51** is close and is
  NOT an exact match, because it is about an item whose stated objective **is** proved and `L102`'s
  is not — only its uniform reading is. Second, and it matters more: **the question was not the
  author's to answer.** `PROOF_STRATEGY` §3 already rules — *"An item that reached B is still OPEN.
  It does not get reported as done, and it does not get a tag. Report it as 'reached B of A→B→C; C
  remains open; here is exactly what is left.'"* `L102`'s `C` is the per-frequency question and
  **this file is a `B`**, so `L102` is **OPEN by rule** and the correct report is that sentence, not
  a deferral. What genuinely is the author's is narrower — whether the item's TITLE should be
  rewritten so the uniform reading is named as its own, now-answered item — and that is entry 55's
  species, filed that way. **CONSEQUENCE, AND IT IS THE POINT:** §6 q3 and §7 item 2 are
  imperative, so the next unit is the **per-frequency criterion**, not a queue item. The remaining
  leg, which §3 requires be written down before a chain may be left: `TorusCosRelation`'s forward
  proof already builds `clsCount k' − clsCount k` and proves it IS a relation, and uses
  `NoCosRelation` only in its final line to force it to zero — so the per-frequency statement is
  that hypothesis weakened to *no relation fits inside `clsCount k`*.
  ⚠ 25 September 2026 (hardening unit 196, `ERRATUM 685`): the FIRST reason in the note above
  is itself false and is kept as written (`ERRATUM 94`). The citation was right: item 9 of the
  running DECISIONS NEEDED list in `PROGRESS_LOG` asks *whether an item whose stated objective
  is proved, by a route its own `BLOCKED ON` line did not anticipate, should be marked closed* —
  the question of `ASSUMPTIONS_LEDGER` 51, which the note itself names as the closest species.
  And *"`DECISIONS NEEDED <n>` means `ASSUMPTIONS_LEDGER` entry `<n>` throughout this estate"* is
  false: three numberings share the phrase (`ERRATUM 683`), and of the note's four examples only
  `48` is read that way. The second reason — `PROOF_STRATEGY` §3 rules `L102` OPEN — stands, and
  unit 105 answered the per-frequency question.

  WHAT IS **NOT** CLAIMED.

  * **NO PER-FREQUENCY STATEMENT AT A COMPOSITE SIDE**, as above.
  * **NO LEAST FAILING DIMENSION ANYWHERE.** Unit 98's construction turns this relation into a
    specific `D`, and that `D` is certainly not minimal: at side 4 unit 97's hand-built pair fails
    at `d = 2` while this relation is a multiple of it, and at side 9 unit 102's relation gives
    `d = 3` where this one gives more. **The least failing dimension is open at every composite
    side** and no cost is offered (`ERRATUM 194`, `ERRATUM 246`).
  * **NO MULTIPLICITY, AND NO UPPER BOUND ON ONE, AT ANY COMPOSITE SIDE.**
  * **NO EVALUATION OF THE DIMENSION AT A PRIME SIDE.** Units 97 and 99 evaluate sides 3 and 5;
    at a general prime the multinomial has `(p−1)/2 + 1` entries and no closed form is offered.
  * **NOTHING OVER `ℂ` ABOUT THE GRAPH** — `ℂ` appears only inside proofs. **NOTHING ABOUT THE BOX,
    THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusEvenSide

namespace TorusCompositeSide

open Finset BoxGraph TorusOrbitInvariant TorusOrbitMultinomial TorusCosRelation
open TorusPrimeSide TorusSideNine TorusEvenSide
open CycleLaplacianSpectrum CycleGreenFormula
open Real

/-- **THE COSINES OF A FULL TURN IN `q` STEPS SUM TO ZERO**, for every `q ≥ 2`. This is unit 102's
`sum_cosCls_eq_zero` off the `N + 3` shape, which is what the composite argument needs: the
divisor `q` can be `2`. -/
theorem sum_cos_turn {q : ℕ} (hq : 2 ≤ q) :
    ∑ i ∈ Finset.range q, Real.cos (2 * Real.pi * (i : ℝ) / (q : ℝ)) = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hprim : IsPrimitiveRoot (zeta q) q := isPrimitiveRoot_zeta hq0
  have hne : zeta q ≠ 1 := by
    intro h
    have := hprim.pow_eq_one_iff_dvd 1
    rw [pow_one, h] at this
    have hd : q ∣ 1 := this.1 rfl
    have : q = 1 := Nat.dvd_one.1 hd
    omega
  have hgeom : ∑ i ∈ Finset.range q, zeta q ^ i = 0 := by
    rw [geom_sum_eq hne, zeta_pow_card hq0, sub_self, zero_div]
  have hre : ∀ i : ℕ, (zeta q ^ i).re = Real.cos (2 * Real.pi * (i : ℝ) / (q : ℝ)) := by
    intro i
    rw [zeta_pow_eq_exp_nat, Complex.exp_ofReal_mul_I_re]
  rw [← Finset.sum_congr rfl (fun i _ => hre i), ← Complex.re_sum, hgeom, Complex.zero_re]

variable {N : ℕ}

/-- The class of the `i`-th multiple of `r`. -/
def subCls (N r : ℕ) (i : ℕ) : Fin (N + 3) :=
  clsF (⟨i * r % (N + 3), Nat.mod_lt _ (by omega)⟩ : Fin (N + 3))

/-- How many of the `q` frequencies `i · r` carry class `c`. -/
def subCount (N q r : ℕ) (c : Fin (N + 3)) : ℕ :=
  ((Finset.range q).filter (fun i => subCls N r i = c)).card

theorem sum_subCount (q r : ℕ) : ∑ c : Fin (N + 3), subCount N q r c = q := by
  classical
  have h := Finset.sum_fiberwise' (Finset.range q) (subCls N r) (fun _ : Fin (N + 3) => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h
  simpa only [subCount] using h

theorem cosCls_subCls {q r : ℕ} (hn : N + 3 = q * r) {i : ℕ} (hi : i < q) (hq : 2 ≤ q) :
    cosCls N (subCls N r i) = Real.cos (2 * Real.pi * (i : ℝ) / (q : ℝ)) := by
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.mul_zero] at hn
      omega
    · exact h0
  have hlt : i * r < N + 3 := by
    rw [hn]
    exact Nat.mul_lt_mul_of_pos_right hi hr0
  rw [subCls, cosCls_clsF, cosCls_eq]
  have hmod : i * r % (N + 3) = i * r := Nat.mod_eq_of_lt hlt
  have hval : ((⟨i * r % (N + 3), Nat.mod_lt _ (by omega)⟩ : Fin (N + 3)) : ℕ) = i * r := hmod
  rw [hval]
  have hqr : ((N + 3 : ℕ) : ℝ) = (q : ℝ) * (r : ℝ) := by rw [hn]; push_cast; ring
  have hq0 : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hrne : ((r : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hqr]
  push_cast
  field_simp

theorem sum_subCount_cos {q r : ℕ} (hn : N + 3 = q * r) (hq : 2 ≤ q) :
    ∑ c : Fin (N + 3), (subCount N q r c : ℝ) * cosCls N c = 0 := by
  classical
  have h := Finset.sum_fiberwise' (Finset.range q) (subCls N r) (cosCls N)
  have hleft : ∑ c : Fin (N + 3), (subCount N q r c : ℝ) * cosCls N c
      = ∑ c : Fin (N + 3), ∑ _i ∈ (Finset.range q).filter (fun i => subCls N r i = c),
          cosCls N c := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_const, subCount, nsmul_eq_mul]
  rw [hleft, h, Finset.sum_congr rfl (fun i hi => cosCls_subCls hn (Finset.mem_range.1 hi) hq),
    sum_cos_turn hq]

theorem two_mul_subCls_le (r i : ℕ) : 2 * ((subCls N r i : Fin (N + 3)) : ℕ) ≤ N + 3 := by
  rw [subCls]
  exact TorusFibreTight.two_mul_pairClass_le (Nat.mod_lt _ (by omega))

theorem subCount_eq_zero_of_not_class (q r : ℕ) {c : Fin (N + 3)}
    (hc : N + 3 < 2 * (c : ℕ)) : subCount N q r c = 0 := by
  rw [subCount, Finset.card_eq_zero]
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro _ hsub
  have := two_mul_subCls_le (N := N) r i
  rw [hsub] at this
  omega

theorem subCount_cls1_eq_zero {q r : ℕ} (hn : N + 3 = q * r) (hr : 2 ≤ r) :
    subCount N q r (cls1) = 0 := by
  rw [subCount, Finset.card_eq_zero]
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
  intro _ hsub
  have hrn : r ∣ N + 3 := ⟨q, by rw [hn]; ring⟩
  have hrv : r ∣ i * r % (N + 3) := (Nat.dvd_mod_iff hrn).2 ⟨i, by ring⟩
  have hvlt : i * r % (N + 3) < N + 3 := Nat.mod_lt _ (by omega)
  have hpc : pairClass N (i * r % (N + 3)) = 1 := by
    have := congrArg Fin.val hsub
    rw [subCls, clsF] at this
    simpa [cls1_val] using this
  rcases Nat.eq_zero_or_pos (i * r % (N + 3)) with h0 | hpos
  · rw [h0] at hpc
    unfold pairClass at hpc
    omega
  · have hmod : (N + 3 - (i * r % (N + 3))) % (N + 3) = N + 3 - (i * r % (N + 3)) :=
      Nat.mod_eq_of_lt (by omega)
    unfold pairClass at hpc
    rw [hmod] at hpc
    have hcase : i * r % (N + 3) = 1 ∨ N + 3 - (i * r % (N + 3)) = 1 := by omega
    rcases hcase with hc1 | hc2
    · rw [hc1] at hrv
      have : r = 1 := Nat.dvd_one.1 hrv
      omega
    · have hd : r ∣ N + 3 - (i * r % (N + 3)) := Nat.dvd_sub hrn hrv
      rw [hc2] at hd
      have : r = 1 := Nat.dvd_one.1 hd
      omega

/-- The composite relation: `n` times the sub-turn vector minus `q` times the fibre-size one. -/
def relComp (N q r : ℕ) (c : Fin (N + 3)) : ℤ :=
  ((N : ℤ) + 3) * (subCount N q r c : ℤ) - (q : ℤ) * (fibreCount N c : ℤ)

theorem sum_relComp (q r : ℕ) : ∑ c : Fin (N + 3), relComp N q r c = 0 := by
  simp only [relComp]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum,
    sum_subCount, sum_fibreCount]
  push_cast
  ring

theorem sum_relComp_cos {q r : ℕ} (hn : N + 3 = q * r) (hq : 2 ≤ q) :
    ∑ c : Fin (N + 3), ((relComp N q r c : ℤ) : ℝ) * cosCls N c = 0 := by
  have hterm : ∀ c : Fin (N + 3), ((relComp N q r c : ℤ) : ℝ) * cosCls N c
      = ((N : ℝ) + 3) * ((subCount N q r c : ℝ) * cosCls N c)
        - (q : ℝ) * ((fibreCount N c : ℝ) * cosCls N c) := by
    intro c
    simp only [relComp]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_subCount_cos hn hq, sum_fibreCount_cos]
  ring

theorem relComp_supp (q r : ℕ) (c : Fin (N + 3)) (hc : N + 3 < 2 * (c : ℕ)) :
    relComp N q r c = 0 := by
  rw [relComp, subCount_eq_zero_of_not_class q r hc, fibreCount_eq_zero hc]
  ring

theorem relComp_cls1_ne_zero {q r : ℕ} (hn : N + 3 = q * r) (hq : 2 ≤ q) (hr : 2 ≤ r) :
    relComp N q r (cls1) ≠ 0 := by
  have hfib : 1 ≤ fibreCount N (cls1) := by
    refine one_le_fibreCount ?_
    rw [cls1_val]
    omega
  rw [relComp, subCount_cls1_eq_zero hn hr]
  push_cast
  have : (1 : ℤ) ≤ (fibreCount N (cls1) : ℤ) := by exact_mod_cast hfib
  have hq' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  nlinarith

/-- **EVERY COMPOSITE SIDE FAILS THE CRITERION.** -/
theorem not_noCosRelation_of_composite {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hn : N + 3 = q * r) : ¬ NoCosRelation N := by
  intro h
  exact relComp_cls1_ne_zero hn hq hr
    (h (relComp N q r) (fun c hc => relComp_supp q r c hc) (sum_relComp q r)
      (sum_relComp_cos hn hq) (cls1))

/-- **SO TIGHTNESS FORCES A PRIME SIDE.** -/
theorem prime_of_noCosRelation (h : NoCosRelation N) : Nat.Prime (N + 3) := by
  by_contra hnp
  obtain ⟨m, hmd, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  obtain ⟨k, hk⟩ := hmd
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> simp_all
    · exact hge
  exact not_noCosRelation_of_composite hm2 hk2 hk h

/-- **AND THE CLASSIFICATION IS EXACT: THE CRITERION HOLDS IFF THE SIDE IS PRIME.** -/
theorem noCosRelation_iff_prime : NoCosRelation N ↔ Nat.Prime (N + 3) := by
  constructor
  · exact prime_of_noCosRelation
  · intro hp
    exact noCosRelation_of_prime hp (hp.odd_of_ne_two (by omega))

/-! ## the readings, and the two earlier refutations as instances -/

/-- **THE COMPLETE ANSWER TO `L102`'s ARITHMETIC QUESTION**: the degeneracy bound is an equality
at every dimension, every mass and every frequency of side `n` **if and only if `n` is prime**. -/
theorem tight_iff_prime (m : ℝ) :
    (∀ (D : ℕ) (k : Site D (N + 3)),
        TorusHyperoctahedral.orbit k = TorusBoundTightIff.nuRFibre N m k)
      ↔ Nat.Prime (N + 3) :=
  (noCosRelation_iff N m).symm.trans noCosRelation_iff_prime

theorem exists_not_tight_of_not_prime (m : ℝ) (hnp : ¬ Nat.Prime (N + 3)) :
    ∃ (D : ℕ) (k : Site D (N + 3)),
      TorusHyperoctahedral.orbit k ≠ TorusBoundTightIff.nuRFibre N m k := by
  by_contra hc
  refine hnp ((tight_iff_prime m).1 ?_)
  intro D k
  by_contra hk
  exact hc ⟨D, k, hk⟩

/-- Unit 103's even-side theorem is the `q = 2` case. -/
theorem not_noCosRelation_of_even_of_composite {m : ℕ} (hm : N + 3 = m + m) :
    ¬ NoCosRelation N :=
  not_noCosRelation_of_composite (q := 2) (r := m) (by norm_num) (by omega) (by omega)

/-- Unit 102's side 9 is the `q = r = 3` case. -/
theorem not_noCosRelation_six_of_composite : ¬ NoCosRelation 6 :=
  not_noCosRelation_of_composite (q := 3) (r := 3) (by norm_num) (by norm_num) (by norm_num)

/-- Side 3, tight — and now a one-line consequence of primality. **This is NOT a new fact**: it is
`TorusPrimeSide.noCosRelation_zero_of_prime`, the identical proposition, re-proved through
`noCosRelation_iff_prime`. It is kept because that re-derivation is the check `ERRATUM 201` says a
general statement owes the special case it subsumes, and the `'` is the standard reading — same
statement, different route. `ERRATUM 629` records that the header's absence query missed it.

**AND THERE IS A THIRD PROOF, WHICH `ERRATUM 629` DID NOT COUNT** (`RE-SWEEP #63` FINDING 2,
`ERRATUM 638`): **`TorusCosRelation.noCosRelation_zero`**, unit 98's direct ten-line argument, in
the module that DEFINES `NoCosRelation` and which this file imports. So this proposition has three
proofs — one from first principles and two `ERRATUM 201` checks — and all three now name the other
two. -/
theorem noCosRelation_zero_of_prime' : NoCosRelation 0 :=
  noCosRelation_iff_prime.2 (by decide)

/-- Side 15, the smallest odd composite nobody had settled. -/
theorem not_noCosRelation_twelve : ¬ NoCosRelation 12 :=
  not_noCosRelation_of_composite (q := 3) (r := 5) (by norm_num) (by norm_num) (by norm_num)

end TorusCompositeSide
