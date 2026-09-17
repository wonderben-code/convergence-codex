/-
  TotientSmall: **`φ(m) ≤ 4` FORCES `m ≤ 12`**, and the nine values are named — the elementary
  number theory the wheel's eigenvalue-collision question turns out to need, and which the pinned
  Mathlib does not have

  **WHY THIS FILE EXISTS.** `ERRATUM 632`. `RE-SWEEP #62` recorded that the wheel's non-collision
  hypothesis (`WheelTable`'s `hcol : hubRootMinus (n+3) 2 ∉ rimSet n`) was blocked on the degree of
  `ℚ(cos 2π/N)`, absent from Mathlib. **That blocker is sufficient and not necessary.** The hub
  quadratic `x² − (n+5)x + 4n` has INTEGER coefficients, so a collision makes a root of unity
  satisfy a monic integer QUARTIC, so `[ℚ(ζ) : ℚ] ≤ 4`, so `φ(m) ≤ 4` — and the degree of `ℚ(ζ)`
  is `φ(m)` by `Polynomial.cyclotomic_eq_minpoly_rat` and `Polynomial.natDegree_cyclotomic`, both
  of which unit 100 already consumes. **What was actually missing is this file: an elementary bound
  on `m` in terms of `φ(m)`, which is a lemma and not a wall.**

  **CHECKED ABSENT BY READING EVERY THEOREM IN THE FILE, NOT BY SEARCHING NAMES** (`ERRATUM 627`,
  `ERRATUM 631`). `Mathlib/Data/Nat/Totient.lean` has forty declarations and **not one bounds `m`
  from above in terms of `φ m`**: `totient_le` and `totient_lt` are `φ m ≤ m` and `φ m < m`,
  `totient_pos` is positivity, `totient_eq_one_iff` and `dvd_two_of_totient_le_one` are the `φ ≤ 1`
  corner, and the rest are multiplicativity, prime powers, the Gauss sum and parity. No lower bound
  on `φ` in terms of `m` exists anywhere in the pinned version.

  **THE ARGUMENT, and it is three steps.**

  1. **Every prime factor of `m` is at most `5`.** If `p ∣ m` then `φ p ∣ φ m`
     (`Nat.totient_dvd_of_dvd`), and `φ p = p − 1` for `p` prime, so `p − 1 ∣ φ m`; with
     `φ m ≤ 4` and `φ m ≠ 0` that gives `p − 1 ≤ 4`, hence `p ≤ 5`.
  2. **The exponents are bounded**, by the same divisibility applied to prime powers:
     `φ(2^a) = 2^(a−1) ∣ φ m` forces `a ≤ 3`; `φ(3^b) = 2·3^(b−1)` forces `b ≤ 1`;
     `φ(5^c) = 4·5^(c−1)` forces `c ≤ 1`.
  3. **So `m ∣ 2³·3·5 = 120`**, hence `m ≤ 120`, and `Nat.totient` is computable, so the nine
     values fall out by decision on a finite range.

  **WHAT IS PROVED.**

  * **`prime_le_five_of_totient_le_four`** — step 1, at every prime divisor.
  * **`le_of_totient_le_four`** — **`φ m ≤ 4 → m ≤ 120`**, the crude bound, which is the whole of
    the mathematical content.
  * **`totient_le_four_iff`** — the classification: `φ m ≤ 4 ↔ m ∈ {1,2,3,4,5,6,8,10,12}`, as a
    `Finset` membership so it is usable by `fin_cases`.
  * **`totient_le_four_le_twelve`** — the headline in the form the wheel unit wants.

  **WHAT IS NOT CLAIMED.** This is `φ ≤ 4` and nothing more general: no bound for `φ m ≤ k` at
  arbitrary `k` and no `φ m ≥ √(m/2)`. Nor is anything claimed here about the numbers
  `2cos(2πj/m)` themselves — what the wheel argument needs about them it builds ON TOP of this,
  in `WheelCollision.lean`. **AND MATHLIB'S POSITION ON THOSE NUMBERS SHOULD NOT BE GUESSED FROM
  THIS FILE'S SILENCE**: `Mathlib/NumberTheory/Niven.lean` proves NIVEN'S THEOREM — the only
  RATIONAL values of `cos` at rational multiples of `π` are `0, ±1/2, ±1` — and
  `isIntegral_two_mul_cos_rat_mul_pi` gives that `2cos(qπ)` is an algebraic integer. What Mathlib
  does not have is a classification of the IRRATIONAL such values by degree, which is the half of
  the wheel's case analysis Niven cannot reach; `WheelCollision.lean` gets it from the cyclotomic
  degree instead and cites neither.
  **Nothing about the wheel, the cone, the torus or any graph appears in this file**; it is pure
  `Nat`, so that the wheel unit consumes a statement about integers and not a statement about
  itself.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace TotientSmall

open Nat

/-- **STEP 1: a prime divisor of `m` is at most `5`.** `φ p = p − 1` divides `φ m`, and a positive
number at most `4` has every divisor at most `4`. -/
theorem prime_le_five_of_totient_le_four {m p : ℕ} (hm : 0 < m) (h : φ m ≤ 4)
    (hp : p.Prime) (hpm : p ∣ m) : p ≤ 5 := by
  have hdvd : φ p ∣ φ m := Nat.totient_dvd_of_dvd hpm
  rw [Nat.totient_prime hp] at hdvd
  have hpos : 0 < φ m := Nat.totient_pos.2 hm
  have : p - 1 ≤ φ m := Nat.le_of_dvd hpos hdvd
  have := hp.two_le
  omega

/-- **STEP 2, the prime-power exponents.** Stated for the three primes at once through the same
divisibility: `φ (p ^ k) ∣ φ m`, and `φ (p ^ k) = p ^ (k−1) * (p−1)`. -/
theorem pow_exponent_bound {m p k : ℕ} (hm : 0 < m) (h : φ m ≤ 4) (hp : p.Prime)
    (hpk : p ^ k ∣ m) (hk : 0 < k) : p ^ (k - 1) * (p - 1) ≤ 4 := by
  have hdvd : φ (p ^ k) ∣ φ m := Nat.totient_dvd_of_dvd hpk
  rw [Nat.totient_prime_pow hp hk] at hdvd
  have hpos : 0 < φ m := Nat.totient_pos.2 hm
  exact le_trans (Nat.le_of_dvd hpos hdvd) h

/-- The three exponent bounds, as the numbers the decomposition needs. -/
theorem two_pow_bound {m a : ℕ} (hm : 0 < m) (h : φ m ≤ 4) (hda : 2 ^ a ∣ m) : a ≤ 3 := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · omega
  have key := pow_exponent_bound hm h Nat.prime_two hda hpos
  norm_num at key
  by_contra hcon
  have h1 : 3 ≤ a - 1 := by omega
  have h2 : (2 : ℕ) ^ 3 ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem three_pow_bound {m b : ℕ} (hm : 0 < m) (h : φ m ≤ 4) (hdb : 3 ^ b ∣ m) : b ≤ 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hpos
  · omega
  have key := pow_exponent_bound hm h Nat.prime_three hdb hpos
  norm_num at key
  by_contra hcon
  have h1 : 1 ≤ b - 1 := by omega
  have h3 : (3 : ℕ) ^ 1 ≤ 3 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem five_pow_bound {m c : ℕ} (hm : 0 < m) (h : φ m ≤ 4) (hdc : 5 ^ c ∣ m) : c ≤ 1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · omega
  have hfive : Nat.Prime 5 := by norm_num
  have key := pow_exponent_bound hm h hfive hdc hpos
  norm_num at key
  by_contra hcon
  have h1 : 1 ≤ c - 1 := by omega
  have h5 : (5 : ℕ) ^ 1 ≤ 5 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) h1
  omega

/-- **STEP 3: `m` divides `120 = 2³·3·5`.** By `Nat.dvd_iff_prime_pow_dvd_dvd` it is enough to
send each prime power dividing `m` into `120`, and steps 1 and 2 bound both the prime and the
exponent, so each case is a numeral check. **No `Nat.factorization` appears**: a first draft went
through `factorization_le_iff_dvd` and stalled, because `(Nat.factorization 120) 2 = 3` is not
`decide`-able — `Finsupp` does not reduce. -/
theorem dvd_120_of_totient_le_four {m : ℕ} (hm : 0 < m) (h : φ m ≤ 4) : m ∣ 120 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpm : p ∣ m := dvd_trans (dvd_pow_self p (by omega)) hpk
  have hple : p ≤ 5 := prime_le_five_of_totient_le_four hm h hp hpm
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p
  · -- p = 2, k ≤ 3
    have hk3 : k ≤ 3 := two_pow_bound hm h hpk
    interval_cases k <;> norm_num
  · -- p = 3, k ≤ 1
    have hk1 : k ≤ 1 := three_pow_bound hm h hpk
    interval_cases k
    norm_num
  · exact absurd hp (by decide)
  · -- p = 5, k ≤ 1
    have hk1 : k ≤ 1 := five_pow_bound hm h hpk
    interval_cases k
    norm_num

/-- **`φ m ≤ 4` FORCES `m ≤ 120`** — the crude bound, and the whole of the mathematical content.
`0 < m` is the hypothesis the application supplies; `φ 0 = 0 ≤ 4` makes it necessary. -/
theorem le_120_of_totient_le_four {m : ℕ} (hm : 0 < m) (h : φ m ≤ 4) : m ≤ 120 :=
  Nat.le_of_dvd (by norm_num) (dvd_120_of_totient_le_four hm h)

/-- **THE CLASSIFICATION.** `φ m ≤ 4` exactly at the nine values `1, 2, 3, 4, 5, 6, 8, 10, 12`.
The crude bound makes this a finite check, and `Nat.totient` is computable. -/
theorem totient_le_four_iff {m : ℕ} (hm : 0 < m) :
    φ m ≤ 4 ↔ m ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) := by
  constructor
  · intro h
    have hle := le_120_of_totient_le_four hm h
    interval_cases m <;> revert h <;> decide
  · intro h
    fin_cases h <;> decide

/-- **THE HEADLINE, in the form the wheel argument wants**: `φ m ≤ 4` forces `m ≤ 12`. -/
theorem le_twelve_of_totient_le_four {m : ℕ} (hm : 0 < m) (h : φ m ≤ 4) : m ≤ 12 := by
  have := (totient_le_four_iff hm).1 h
  fin_cases this <;> norm_num

end TotientSmall
