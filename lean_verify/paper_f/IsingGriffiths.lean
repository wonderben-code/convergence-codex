/-
  IsingGriffiths.lean — Griffiths' first inequality, for an arbitrary finite Ising model with
  non-negative couplings.

  WHY. `IsingGKSParity` built two of the three ingredients and named the third — *"a sum over
  subsets of the bond set with a parity condition on the induced multiset"* — as the step nobody had
  attempted. **The parity condition never has to be computed.** That is the whole content of this
  file, and it is why the third rung is short.

  THE TRICK, STATED PLAINLY. The expansion produces, for each subset `T` of the interaction terms, a
  configuration sum of a product of spins over some collection of sites WITH REPETITION. Written as
  `∏ v, spin (σ v) ^ (multiplicity of v)` it factorises site by site — `Fintype.prod_sum` — and each
  factor is `∑_b spin b ^ n`, which is `2` for even `n` and `0` for odd. **Both are non-negative,
  so no case split on the parity is needed and the parity set is never constructed.** A first plan
  for this file built the odd-multiplicity set explicitly; it is not needed and is not here.

  WHAT IS PROVED.

  * `sum_pow_spin_nonneg` — `0 ≤ ∑_b spin b ^ n`, the whole parity argument in one line;
  * `prod_spin_eq_prod_pow` — a product of spins over a `Finset`, and any product of such, is
    `∏ v, spin (σ v) ^ c v` for the multiplicity `c`;
  * **`sum_prod_pow_spin_nonneg`** — hence every configuration sum of such a product is `≥ 0`;
  * **`griffiths_nonneg`** — for a finite family of interaction sets `S i` with non-negative
    couplings `J i`, and any observable set `A`,
    `0 ≤ ∑_σ (∏_{v ∈ A} spin (σ v)) · exp (∑_i J i · ∏_{v ∈ S i} spin (σ v))`.
    Bonds are `S i` of size two and a field is `S i` of size one, so **the hypothesis is exactly
    "ferromagnetic, with a field of the same sign as the observable"**;
  * `griffiths_expect_nonneg` — the same divided by the partition function, which is positive.

  WHAT THIS IS NOT. It is not yet a statement about the estate's slab. `energyG` is a sum over a
  path of configurations, and to apply the theorem above one must (i) reindex
  `Fin (M+1) → Cross V` as `(Fin (M+1) × V) → Bool`, and (ii) exhibit `β · energyG` as
  `∑_i J i · ∏_{v ∈ S i} spin` with every `J i ≥ 0` — the bonds along the length, the bonds inside a
  cross-section, and the field, each with coupling `β` or `β h`. **Neither step is attempted here
  and neither has been probed** (`ERRATUM 250`); naming them is not the same as costing them.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGKSParity

namespace IsingGriffiths

open Finset Real
open IsingTransfer2D IsingGKSParity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The parity argument, without the parity -/

/-- **`0 ≤ ∑_b spin b ^ n`.** It is `2` when `n` is even and `0` when `n` is odd, and the proof
needs neither case: `1 ^ n + (−1) ^ n` is `1 + (±1)`. -/
theorem sum_pow_spin_nonneg (n : ℕ) : 0 ≤ ∑ b : Bool, spin b ^ n := by
  have h : ∑ b : Bool, spin b ^ n = 1 + (-1 : ℝ) ^ n := by
    simp [spin]
  rw [h]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

/-- **AND SO EVERY CONFIGURATION SUM OF A PRODUCT OF SPIN POWERS IS NON-NEGATIVE**, whatever the
multiplicities. This is the step that replaces the parity bookkeeping. -/
theorem sum_prod_pow_spin_nonneg (c : V → ℕ) :
    0 ≤ ∑ σ : V → Bool, ∏ v : V, spin (σ v) ^ c v := by
  rw [← Fintype.prod_sum fun (v : V) (b : Bool) => spin b ^ c v]
  exact Finset.prod_nonneg fun v _ => sum_pow_spin_nonneg (c v)

/-! ## 2. Products of spins as products of powers -/

/-- A product over a `Finset` is a product over everything with exponents `0` and `1`. -/
theorem prod_finset_eq_prod_pow (A : Finset V) (σ : V → Bool) :
    ∏ v ∈ A, spin (σ v) = ∏ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0) := by
  have h : ∀ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0)
      = if v ∈ A then spin (σ v) else 1 := by
    intro v
    by_cases hv : v ∈ A <;> simp [hv]
  rw [Finset.prod_congr rfl fun v _ => h v, Finset.prod_ite_mem, Finset.univ_inter]

/-- And a product of such collapses onto the summed exponents. -/
theorem prod_prod_eq_prod_pow {I : Type*} (T : Finset I) (S : I → Finset V)
    (σ : V → Bool) :
    ∏ i ∈ T, ∏ v ∈ S i, spin (σ v)
      = ∏ v : V, spin (σ v) ^ (∑ i ∈ T, if v ∈ S i then 1 else 0) := by
  rw [Finset.prod_congr rfl fun i _ => prod_finset_eq_prod_pow (S i) σ, Finset.prod_comm]
  exact Finset.prod_congr rfl fun v _ => Finset.prod_pow_eq_pow_sum T _ _

/-! ## 3. Each Boltzmann factor -/

omit [Fintype V] [DecidableEq V] in
theorem prod_spin_eq_one_or (A : Finset V) (σ : V → Bool) :
    ∏ v ∈ A, spin (σ v) = 1 ∨ ∏ v ∈ A, spin (σ v) = -1 := by
  classical
  induction A using Finset.induction with
  | empty => left; simp
  | insert a A ha ih =>
      rw [Finset.prod_insert ha]
      rcases spin_eq_one_or (σ a) with h | h <;> rcases ih with h2 | h2 <;>
        rw [h, h2] <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem exp_term (x : ℝ) (A : Finset V) (σ : V → Bool) :
    exp (x * ∏ v ∈ A, spin (σ v))
      = cosh x + (∏ v ∈ A, spin (σ v)) * sinh x :=
  exp_mul_of_abs_one (prod_spin_eq_one_or A σ) x

/-! ## 4. `sinh` is non-negative on the non-negative reals

`Real.sinh_nonneg_iff` did not resolve in this file's import closure, and pulling in the
differentiation file to reach it would import a great deal for one sign. Four lines from
`Real.sinh_eq` instead. -/

theorem sinh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sinh x := by
  rw [Real.sinh_eq]
  have h : exp (-x) ≤ exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

/-! ## 5. Griffiths' first inequality -/

variable {I : Type*} [Fintype I]

/-- **GRIFFITHS' FIRST INEQUALITY.** For any finite family of interaction sets with non-negative
couplings and any observable set, the unnormalised correlation is non-negative. Bonds are sets of
size two and a field is a set of size one, so the hypothesis `0 ≤ J i` is exactly *ferromagnetic,
with a field of the same sign as the observable*. -/
theorem griffiths_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (A : Finset V) :
    0 ≤ ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  classical
  have hfac : ∀ σ : V → Bool,
      (∏ v ∈ A, spin (σ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))
        = ∑ T ∈ Finset.univ.powerset,
            ((∏ i ∈ T, sinh (J i)) * ∏ i ∈ Finset.univ \ T, cosh (J i))
              * ∏ v : V, spin (σ v)
                  ^ ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0) := by
    intro σ
    rw [Real.exp_sum,
      Finset.prod_congr rfl fun i _ => (exp_term (J i) (S i) σ).trans (add_comm _ _),
      Finset.prod_add (fun i => (∏ v ∈ S i, spin (σ v)) * sinh (J i)) (fun i => cosh (J i))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_mul_distrib, prod_prod_eq_prod_pow T S σ, prod_finset_eq_prod_pow A σ]
    have hcomb : (∏ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0))
        * ∏ v : V, spin (σ v) ^ (∑ i ∈ T, if v ∈ S i then 1 else 0)
        = ∏ v : V, spin (σ v)
            ^ ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (pow_add _ _ _).symm
    rw [← hcomb]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hfac σ, Finset.sum_comm]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [← Finset.mul_sum]
  refine mul_nonneg (mul_nonneg ?_ ?_) (sum_prod_pow_spin_nonneg _)
  · exact Finset.prod_nonneg fun i _ => sinh_nonneg (hJ i)
  · exact Finset.prod_nonneg fun i _ => (Real.cosh_pos _).le

/-- **THE MAGNETISATION CASE**, which is the one the watchlist item is about: `A = {v₀}`. -/
theorem griffiths_site_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (v₀ : V) :
    0 ≤ ∑ σ : V → Bool, spin (σ v₀) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  have h := griffiths_nonneg S J hJ {v₀}
  simpa using h

/-- The partition function of such a model is positive, so the normalised correlation is
non-negative too. -/
theorem griffiths_expect_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (A : Finset V) :
    0 ≤ (∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
          * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)))
        / ∑ σ : V → Bool, exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  refine div_nonneg (griffiths_nonneg S J hJ A) ?_
  exact Finset.sum_nonneg fun σ _ => (exp_pos _).le

end

end IsingGriffiths
