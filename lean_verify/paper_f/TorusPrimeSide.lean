/-
  TorusPrimeSide: EVERY ODD PRIME SIDE IS TIGHT — the torus degeneracy bound is an equality at
  every dimension, every mass and every frequency of every odd prime side, so units 97 and 99's
  sides 3 and 5 become instances and infinitely many new sides are decided at once

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §1: *Caesar — conquer the thing that makes the others
  fall.* Unit 98 reduced `L102`'s general question to an arithmetic condition on the side,
  `NoCosRelation N`; units 97 and 99 then decided four sides ONE AT A TIME, each by hand, and unit
  99's header refused the obvious extrapolation from `3 T, 4 F, 5 T, 6 F` in those words:
  *at side 7 the cosines generate a cubic field and the question is a different computation from
  either of the two done here, and is not done.* **This file does not do that computation either.
  It does the general one**, and side 7 falls out as a corollary along with every other odd prime.

  **THE MATHEMATICS, IN ONE PARAGRAPH.** Let `p = N + 3` be an odd prime and `ζ = exp(2πi/p)`. A
  relation `a` has `∑ⱼ aⱼ = 0` and `∑ⱼ aⱼ·cos(2πj/p) = 0` over the pair classes. Since
  `2cos(2πc/p) = ζ^c + ζ^{p−c}` for **every** `c` (including `c = 0`, where `ζ^p = 1`), the second
  condition says a certain integer combination of the `p`-th roots of unity vanishes: the
  coefficient of `ζ^j` is `aⱼ + a_{σ j}` with `σ j = p − j` the mirror. The `p`-th cyclotomic
  polynomial is `1 + X + ⋯ + X^{p−1}`, so a vanishing integer combination of `1, ζ, …, ζ^{p−1}`
  has **constant** coefficients. Hence `aⱼ + a_{σ j} = a₀ + a₀ = 2a₀` for every `j`. Summing over
  `j` gives `2·∑ⱼ aⱼ = p·2a₀`, so `a₀ = 0`; and for a non-zero class `j` the mirror `σ j` is NOT a
  class — **this is exactly where ODD is used**, since `2j ≤ p` and `p` odd force `2j < p` and
  hence `2(p−j) > p` — so `a_{σ j} = 0` and `aⱼ = 0`. **No counting argument appears anywhere**,
  which is what makes the proof uniform in `p`.

  **CHECKED ABSENT BEFORE BEING WRITTEN — AND THE FIRST DRAFT OF THIS PARAGRAPH WAS FALSE, so it
  is struck here rather than used** (`ERRATUM 621`; `ERRATUM 626`'s rule is the same one at the
  level of a parameter). It said *this estate has used Mathlib's roots-of-unity and cyclotomic API
  nowhere*. **It has used the roots-of-unity API twice.** `awk` over `estate_types.txt` (14665
  statements, 1118 modules) for `cyclotomic`, `IsPrimitiveRoot` or `Irrational` returns
  `CycleGreenFormula.isPrimitiveRoot_zeta` and `TorusSideFive.irrational_sqrt_five`, and
  `grep` over the sources adds `WheelSpectrum`'s use of `IsPrimitiveRoot.pow_inj` and
  `RealDivisionQuadratic`'s use of `minpoly.irreducible`. **What IS new here is the CYCLOTOMIC
  POLYNOMIAL**: `grep -rn cyclotomic` over every `.lean` in the estate returns two prose mentions
  — `ConeDimensionSum` and `TorusEightNotTight`, both naming it as the thing they do NOT have —
  and no declaration. So `Polynomial.cyclotomic` and `cyclotomic_eq_minpoly_rat` are the genuinely
  new import, and `IsPrimitiveRoot` and `minpoly` are not. The four scans of unit 98's header
  (recorded there) stand unchanged.

  WHAT IS PROVED.

  * **`zt`, `zt_pow_eq`, `zt_pow_self`** — the primitive root and its two basic facts, off
    `Complex.isPrimitiveRoot_exp`.
  * **`two_cos_eq_add_pow`** — `2cos(2πc/p) = ζ^c + ζ^{p−c}` for every `c ≤ p`, through
    `Complex.exp_two_pi_mul_I` and the definition of `Complex.cos`. **It holds at `c = 0` too**,
    which is why no case split is needed later.
  * **`sig`, `sig_zero`, `sig_involutive`, `zt_pow_sig`, `sum_sig_reindex`** — the mirror
    `j ↦ (p − j) mod p` as an involution of `Fin p`, and the reindexing it gives.
  * **`sum_zt_eq_zero`** — the bridge: a cosine relation becomes a vanishing integer combination
    of the `p`-th roots of unity, with coefficients `aⱼ + a_{σ j}`.
  * **`const_of_sum_eq_zero`** — **the cyclotomic step, the one genuinely new piece of Mathlib
    this unit takes on** (see the corrected paragraph above): a vanishing integer combination of
    `1, ζ, …, ζ^{p−1}` has constant
    coefficients. `Complex.isPrimitiveRoot_exp`, `Polynomial.cyclotomic_eq_minpoly_rat`,
    `Polynomial.cyclotomic_prime`, `minpoly.dvd`, and a degree argument: the quotient has degree
    `0`, so it is a constant, and the coefficients of `1 + X + ⋯ + X^{p−1}` are all `1`.
  * **`noCosRelation_of_prime`** — **the theorem**: every odd prime side satisfies unit 98's
    criterion. With `TorusCosRelation.noCosRelation_iff` this gives **`tight_of_prime`** — the
    bound is an equality at every dimension, every mass and every frequency — read off as
    `bound_eq_finrank_of_prime`, `card_orbit_eq_finrank_of_prime` and
    `card_orbitsOf_eq_one_of_prime`.
  * **`noCosRelation_four`, `side_seven_tight`** — **side 7, the first side decided here that was
    not decided before**; `noCosRelation_eight` and `noCosRelation_ten` are sides 11 and 13, free.
  * **`noCosRelation_zero_of_prime`, `noCosRelation_two_of_prime`** — **and units 97 and 99's own
    results come back out of the general theorem**, which is the check a new general statement owes
    the special cases it subsumes (`ERRATUM 201`, the shape
    `TorusOrbitMultinomial.card_orbit_eq_two_pow_mul_factorial` used on its predecessor). The two
    earlier proofs are **not** deleted: unit 97's is a two-value count and unit 99's turns on the
    irrationality of `√5`, and each is the shortest proof of its own side.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT COMPOSITE ODD SIDES, AND THEY ARE NOT ALL TIGHT.** Brute force over every
    frequency says side 9 is tight at `d = 2` and **NOT tight at `d = 3`** — so "odd" is not the
    criterion, and the failure appears only in the third dimension, which is exactly what unit
    98's converse construction predicts, its `∑ a⁺` being `3` for the relation
    `(1, −1, −1, 2, −1)` there. **That is a measurement, not a theorem, and proving it is the next
    unit**; it needs `∑_{j<9} cos(2πj/9) = 0`, which this estate does not have. Named so it is not
    rediscovered, not costed (`ERRATUM 194`, `ERRATUM 246`).
  * **NOTHING ABOUT EVEN SIDES.** Sides 4 and 6 are refuted in units 97 and 99; no general
    even-side statement is proved, though the rational-valued cosines at `n = 2m` make one
    plausible. Not attempted.
  * **NO PER-FREQUENCY STATEMENT AT A FAILING SIDE**, and
    `TorusCosRelation.orbit_eq_nuRFibre_zero` shows a failing side still has tight frequencies.
  * **NO EVALUATION OF THE DIMENSION AT A PRIME SIDE.** `bound_eq_finrank_of_prime`'s left-hand
    side is `2 ^ |interiorAxes k| · multinomial`; units 97 and 99 evaluate that at sides 3 and 5,
    and **this file evaluates it nowhere** — at a general prime side the multinomial has
    `(p−1)/2 + 1` entries and no closed form is offered.
  * **NOTHING OVER `ℂ` ABOUT THE GRAPH.** `ℂ` appears only inside the proof, as the field the
    roots of unity live in; every statement about the torus is over `ℝ`.
  * **NOTHING ABOUT THE BOX, THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import TorusCosRelation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace TorusPrimeSide

open Finset BoxGraph TorusOrbitInvariant TorusCosRelation Polynomial

variable {N : ℕ}

noncomputable def zt (p : ℕ) : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / p)

theorem zt_pow_eq {p : ℕ} (hp : p ≠ 0) (c : ℕ) :
    zt p ^ c = Complex.exp ((2 * Real.pi * (c : ℝ) / (p : ℝ) : ℝ) * Complex.I) := by
  rw [zt, ← Complex.exp_nat_mul]
  congr 1
  have hpc : ((p : ℂ)) ≠ 0 := by simpa using Nat.cast_ne_zero.2 hp
  push_cast
  field_simp

theorem zt_pow_self {p : ℕ} (hp : p ≠ 0) : zt p ^ p = 1 :=
  (Complex.isPrimitiveRoot_exp p hp).pow_eq_one

/-- The mirror index. -/
def sig (N : ℕ) (c : Fin (N + 3)) : Fin (N + 3) :=
  ⟨(N + 3 - (c : ℕ)) % (N + 3), Nat.mod_lt _ (by omega)⟩

theorem sig_val_of_pos {c : Fin (N + 3)} (hc : 0 < (c : ℕ)) :
    ((sig N c : Fin (N + 3)) : ℕ) = N + 3 - (c : ℕ) := by
  have h := c.isLt
  simp only [sig]
  exact Nat.mod_eq_of_lt (by omega)

theorem sig_zero : sig N (0 : Fin (N + 3)) = 0 := by
  have : ((0 : Fin (N + 3)) : ℕ) = 0 := rfl
  simp only [sig, this, Nat.sub_zero, Nat.mod_self]
  rfl

theorem sig_involutive : Function.Involutive (sig N) := by
  intro c
  have h := c.isLt
  rcases Nat.eq_zero_or_pos (c : ℕ) with h0 | hpos
  · have hc0 : c = 0 := Fin.ext h0
    rw [hc0, sig_zero, sig_zero]
  · apply Fin.ext
    rw [sig_val_of_pos (by rw [sig_val_of_pos hpos]; omega), sig_val_of_pos hpos]
    omega

theorem zt_pow_sig (c : Fin (N + 3)) :
    zt (N + 3) ^ ((sig N c : Fin (N + 3)) : ℕ) = zt (N + 3) ^ (N + 3 - (c : ℕ)) := by
  have h := c.isLt
  rcases Nat.eq_zero_or_pos (c : ℕ) with h0 | hpos
  · have hc0 : c = 0 := Fin.ext h0
    rw [hc0, sig_zero, show ((0 : Fin (N + 3)) : ℕ) = 0 from rfl, Nat.sub_zero, pow_zero,
      zt_pow_self (by omega)]
  · rw [sig_val_of_pos hpos]

theorem two_cos_eq_add_pow {p : ℕ} (hp : p ≠ 0) {c : ℕ} (hc : c ≤ p) :
    (2 : ℂ) * ((Real.cos (2 * Real.pi * (c : ℝ) / (p : ℝ)) : ℝ) : ℂ)
      = zt p ^ c + zt p ^ (p - c) := by
  have hpc : ((p : ℂ)) ≠ 0 := by simpa using Nat.cast_ne_zero.2 hp
  rw [zt_pow_eq hp c, zt_pow_eq hp (p - c)]
  have hcast : ((p - c : ℕ) : ℝ) = (p : ℝ) - (c : ℝ) := Nat.cast_sub hc
  have he : ((2 * Real.pi * ((p - c : ℕ) : ℝ) / (p : ℝ) : ℝ) : ℂ) * Complex.I
      = -(((2 * Real.pi * (c : ℝ) / (p : ℝ) : ℝ) : ℂ) * Complex.I)
        + 2 * ↑Real.pi * Complex.I := by
    rw [hcast]
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, Complex.ofReal_cos, Complex.cos]
  simp only [neg_mul]
  ring

theorem cosCls_eq (c : Fin (N + 3)) :
    cosCls N c = Real.cos (2 * Real.pi * ((c : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ)) := by
  rw [cosCls]
  push_cast
  ring_nf

theorem sum_sig_reindex {M : Type*} [AddCommMonoid M] (f : Fin (N + 3) → M) :
    ∑ c, f (sig N c) = ∑ c, f c :=
  Equiv.sum_comp (Function.Involutive.toPerm (sig N) sig_involutive) f

theorem sum_zt_eq_zero (a : Fin (N + 3) → ℤ)
    (hacos : ∑ c, (a c : ℝ) * cosCls N c = 0) :
    ∑ c : Fin (N + 3), ((a c + a (sig N c) : ℤ) : ℂ) * zt (N + 3) ^ (c : ℕ) = 0 := by
  have hp : (N + 3) ≠ 0 := by omega
  have hsplit : ∑ c : Fin (N + 3), ((a c + a (sig N c) : ℤ) : ℂ) * zt (N + 3) ^ (c : ℕ)
      = (∑ c : Fin (N + 3), (a c : ℂ) * zt (N + 3) ^ (c : ℕ))
        + ∑ c : Fin (N + 3), (a (sig N c) : ℂ) * zt (N + 3) ^ (c : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    push_cast
    ring
  have hre : ∑ c : Fin (N + 3), (a (sig N c) : ℂ) * zt (N + 3) ^ (c : ℕ)
      = ∑ c : Fin (N + 3), (a c : ℂ) * zt (N + 3) ^ ((sig N c : Fin (N + 3)) : ℕ) := by
    rw [← sum_sig_reindex (N := N)
      (fun c => (a c : ℂ) * zt (N + 3) ^ ((sig N c : Fin (N + 3)) : ℕ))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [sig_involutive c]
  rw [hsplit, hre, ← Finset.sum_add_distrib]
  have hterm : ∀ c : Fin (N + 3),
      (a c : ℂ) * zt (N + 3) ^ (c : ℕ)
        + (a c : ℂ) * zt (N + 3) ^ ((sig N c : Fin (N + 3)) : ℕ)
      = 2 * (((a c : ℝ) * cosCls N c : ℝ) : ℂ) := by
    intro c
    rw [zt_pow_sig, cosCls_eq]
    have h2 := two_cos_eq_add_pow hp (le_of_lt c.isLt)
    push_cast at h2 ⊢
    linear_combination (-(a c : ℂ)) * h2
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum, ← Complex.ofReal_sum, hacos]
  norm_num

/-- A vanishing integer combination of the `p`-th roots of unity has constant coefficients. -/
theorem const_of_sum_eq_zero {p : ℕ} (hp : p.Prime) (b : ℕ → ℤ)
    (h : ∑ j ∈ Finset.range p, (b j : ℂ) * (zt p) ^ j = 0)
    {j : ℕ} (hj : j < p) : b j = b 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set ζ : ℂ := zt p with hzdef
  have hζ : IsPrimitiveRoot ζ p := by
    rw [hzdef, zt]
    exact Complex.isPrimitiveRoot_exp p hp.pos.ne'
  set P : ℚ[X] := ∑ i ∈ Finset.range p, C ((b i : ℚ)) * X ^ i with hPdef
  have hPζ : aeval ζ P = 0 := by
    rw [hPdef]
    simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X]
    rw [← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    norm_num
  have hdvd : minpoly ℚ ζ ∣ P := minpoly.dvd ℚ ζ hPζ
  rw [← cyclotomic_eq_minpoly_rat hζ hp.pos] at hdvd
  have hdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hPdeg : P.natDegree ≤ p - 1 := by
    rw [hPdef]
    refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
    have := Finset.mem_range.1 hi
    calc (C ((b i : ℚ)) * X ^ i).natDegree ≤ i := by
          simpa using natDegree_C_mul_le ((b i : ℚ)) (X ^ i)
      _ ≤ p - 1 := by omega
  have hcoeff : ∀ i, i < p → P.coeff i = (b i : ℚ) := by
    intro i hi
    rw [hPdef, finset_sum_coeff]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi)]
    · simp
    · intro k _ hne
      simp [coeff_X_pow, Ne.symm hne]
  have hcyccoeff : ∀ i, i < p → (cyclotomic p ℚ).coeff i = 1 := by
    intro i hi
    rw [cyclotomic_prime, finset_sum_coeff]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi)]
    · simp
    · intro k _ hne
      simp [coeff_X_pow, Ne.symm hne]
  obtain ⟨q, hq⟩ := hdvd
  by_cases hP0 : P = 0
  · have hz : ∀ i, i < p → (b i : ℚ) = 0 := by
      intro i hi
      rw [← hcoeff i hi, hP0, coeff_zero]
    have h1 := hz j hj
    have h2 := hz 0 hp.pos
    have e1 : b j = 0 := by exact_mod_cast h1
    have e2 : b 0 = 0 := by exact_mod_cast h2
    rw [e1, e2]
  · have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hP0 hq
    have hcycne : cyclotomic p ℚ ≠ 0 := cyclotomic_ne_zero p ℚ
    have hdegsum : P.natDegree = (cyclotomic p ℚ).natDegree + q.natDegree := by
      rw [hq, natDegree_mul hcycne hq0]
    have hqdeg : q.natDegree = 0 := by
      have := hp.two_le
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hqdeg
    have key : ∀ i, i < p → (b i : ℚ) = c := by
      intro i hi
      rw [← hcoeff i hi, hq, ← hc, coeff_mul_C, hcyccoeff i hi, one_mul]
    have h1 := key j hj
    have h2 := key 0 hp.pos
    have : (b j : ℚ) = (b 0 : ℚ) := by rw [h1, h2]
    exact_mod_cast this

theorem noCosRelation_of_prime (hp : Nat.Prime (N + 3)) (hodd : Odd (N + 3)) :
    NoCosRelation N := by
  intro a hasupp hasum hacos
  set b : ℕ → ℤ := fun j => a ⟨j % (N + 3), Nat.mod_lt _ (by omega)⟩
      + a (sig N ⟨j % (N + 3), Nat.mod_lt _ (by omega)⟩) with hbdef
  have hbval : ∀ c : Fin (N + 3), b (c : ℕ) = a c + a (sig N c) := by
    intro c
    have hmod : (⟨(c : ℕ) % (N + 3), Nat.mod_lt _ (by omega)⟩ : Fin (N + 3)) = c :=
      Fin.ext (Nat.mod_eq_of_lt c.isLt)
    simp only [hbdef, hmod]
  have hsum0 : ∑ j ∈ Finset.range (N + 3), (b j : ℂ) * zt (N + 3) ^ j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (b j : ℂ) * zt (N + 3) ^ j) (N + 3),
      Finset.sum_congr rfl (fun c _ => by rw [hbval c])]
    exact sum_zt_eq_zero a hacos
  have hconst : ∀ j, j < N + 3 → b j = b 0 :=
    fun j hj => const_of_sum_eq_zero hp b hsum0 hj
  have hb0 : b 0 = 2 * a 0 := by
    have hz : ((0 : Fin (N + 3)) : ℕ) = 0 := rfl
    rw [← hz, hbval 0, sig_zero]
    ring
  have hsumb : ∑ j ∈ Finset.range (N + 3), b j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range b (N + 3), Finset.sum_congr rfl (fun c _ => hbval c),
      Finset.sum_add_distrib, sum_sig_reindex (N := N) a, hasum]
    ring
  have hsumb2 : ∑ j ∈ Finset.range (N + 3), b j = ((N : ℤ) + 3) * b 0 := by
    rw [Finset.sum_congr rfl (fun j hj => hconst j (Finset.mem_range.1 hj)), Finset.sum_const,
      Finset.card_range]
    ring
  have ha0 : a 0 = 0 := by
    have h : ((N : ℤ) + 3) * (2 * a 0) = 0 := by
      rw [← hb0, ← hsumb2, hsumb]
    have hne : ((N : ℤ) + 3) ≠ 0 := by positivity
    rcases mul_eq_zero.1 h with h1 | h2
    · exact absurd h1 hne
    · omega
  intro j
  by_cases hcl : N + 3 < 2 * (j : ℕ)
  · exact hasupp j hcl
  · rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · have hj0 : j = 0 := Fin.ext h0
      rw [hj0]
      exact ha0
    · obtain ⟨m, hm⟩ := hodd
      have hjlt : 2 * (j : ℕ) < N + 3 := by omega
      have hjle := j.isLt
      have hsigsupp : a (sig N j) = 0 := by
        refine hasupp _ ?_
        rw [sig_val_of_pos hpos]
        omega
      have hbj := hconst (j : ℕ) j.isLt
      rw [hbval j, hb0, ha0, hsigsupp] at hbj
      omega

/-! ## the readings, and the sides this decides -/

theorem tight_of_prime (hp : Nat.Prime (N + 3)) (hodd : Odd (N + 3)) (m : ℝ) (d : ℕ)
    (k : Site d (N + 3)) : TorusHyperoctahedral.orbit k = TorusBoundTightIff.nuRFibre N m k :=
  (noCosRelation_iff N m).1 (noCosRelation_of_prime hp hodd) d k

theorem bound_eq_finrank_of_prime (hp : Nat.Prime (N + 3)) (hodd : Odd (N + 3)) {d : ℕ} (m : ℝ)
    (k : Site d (N + 3)) :
    (2 ^ (TorusReflectionCount.interiorAxes k).card
        * Nat.multinomial univ fun c => Fintype.card {i // TorusOrbitMultinomial.cls k i = c})
      = Module.finrank ℝ
          (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph d (N + 3)) m)
            - MassiveTorusSpectrum.nuR N m k • LinearMap.id).ker :=
  bound_eq_finrank_of_noCosRelation (noCosRelation_of_prime hp hodd) m k

theorem card_orbit_eq_finrank_of_prime (hp : Nat.Prime (N + 3)) (hodd : Odd (N + 3)) {d : ℕ}
    (m : ℝ) (k : Site d (N + 3)) :
    (TorusHyperoctahedral.orbit k).card
      = Module.finrank ℝ
          (Matrix.toLin' (GraphLaplacian.massive (TorusReflection.torusGraph d (N + 3)) m)
            - MassiveTorusSpectrum.nuR N m k • LinearMap.id).ker :=
  card_orbit_eq_finrank_of_noCosRelation (noCosRelation_of_prime hp hodd) m k

theorem card_orbitsOf_eq_one_of_prime (hp : Nat.Prime (N + 3)) (hodd : Odd (N + 3)) {d : ℕ}
    (m : ℝ) (k : Site d (N + 3)) : (TorusFibreOrbitPartition.orbitsOf N m k).card = 1 :=
  card_orbitsOf_eq_one_of_noCosRelation (noCosRelation_of_prime hp hodd) m k

/-- **SIDE 7, THE FIRST SIDE THIS DECIDES THAT WAS NOT ALREADY DECIDED.** -/
theorem noCosRelation_four : NoCosRelation 4 :=
  noCosRelation_of_prime (by decide) (Nat.odd_iff.2 (by norm_num))

theorem side_seven_tight (m : ℝ) (d : ℕ) (k : Site d 7) :
    TorusHyperoctahedral.orbit k = TorusBoundTightIff.nuRFibre 4 m k :=
  (noCosRelation_iff 4 m).1 noCosRelation_four d k

/-- Side 11, free. -/
theorem noCosRelation_eight : NoCosRelation 8 :=
  noCosRelation_of_prime (by decide) (Nat.odd_iff.2 (by norm_num))

/-- Side 13, free. -/
theorem noCosRelation_ten : NoCosRelation 10 :=
  noCosRelation_of_prime (by decide) (Nat.odd_iff.2 (by norm_num))

/-- **AND UNITS 97 AND 99 ARE NOW INSTANCES**: side 3 and side 5 come out of the general theorem,
which is the check a new general statement owes the special cases it replaces (`ERRATUM 201`). -/
theorem noCosRelation_zero_of_prime : NoCosRelation 0 :=
  noCosRelation_of_prime (by decide) (Nat.odd_iff.2 (by norm_num))

theorem noCosRelation_two_of_prime : NoCosRelation 2 :=
  noCosRelation_of_prime (by decide) (Nat.odd_iff.2 (by norm_num))

end TorusPrimeSide
