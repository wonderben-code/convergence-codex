/-
  IsingGKSParity.lean — the combinatorial heart of Griffiths' first inequality, and the two
  expansions that feed it.

  WHY. `IsingFieldFactorises` answered the watchlist item's question with the sites uncoupled and
  said what that leaves: **the same question with the intra energy switched on**, where the
  factorisation is simply false. That case is not a gap in this estate's machinery — it is a named
  theorem, **Griffiths' first inequality**: for an Ising model with non-negative couplings and a
  non-negative field, every correlation `⟨∏_{v ∈ A} σ_v⟩` is non-negative, and the magnetisation is
  the case `A = {v₀}`.

  ITS PROOF HAS EXACTLY THREE INGREDIENTS AND THIS FILE IS TWO OF THEM.

  1. **Each Boltzmann factor is `cosh` plus a spin product times `sinh`.** `exp_bond` and
     `exp_field`: because a product of spins is `±1` and `exp (±x) = cosh x ± sinh x`, with **no
     approximation and no series** — an identity, at every real argument;
  2. **Summing a product of spins over all configurations kills every non-empty set of sites.**
     `sum_prod_spin_eq_zero`: `∑_σ ∏_{v ∈ A} spin (σ v) = 0` whenever `A` is non-empty, and
     `2 ^ |V|` when it is empty (`sum_prod_spin_empty`). One factorisation and `∑_b spin b = 0`;
  3. **The bookkeeping**, which is not here: multiply out the product of (1) over all bonds and all
     sites, and observe that (2) annihilates every term whose site multiset is not even, leaving a
     sum of products of `cosh`s, `sinh`s and non-negative couplings. **That step is a sum over
     subsets of the bond set with a parity condition on the induced multiset, and nothing in this
     file attempts it.**

  So this is rung one of a named ladder, and the rung after it is stated above rather than
  described. **No inequality is proved here** — (1) and (2) are identities, and the inequality is
  what (3) assembles from them.

  A NOTE ON SCOPE. `sum_prod_spin_eq_zero` is about the uniform measure on configurations — the
  `β = 0` model — so as a *correlation* statement it is the base case and nothing more. Its use in
  Griffiths is not as a correlation but as an annihilator inside the expansion, and that is how it
  is stated: a bare sum, with no partition function anywhere.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingFieldFactorises

namespace IsingGKSParity

open Finset Real
open IsingTransfer2D

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The two Boltzmann expansions

A spin, or a product of two spins, is `±1`, and `exp (±x) = cosh x ± sinh x`. So each factor of the
Boltzmann weight is linear in the spins with `cosh` and `sinh` coefficients — exactly, not to any
order. -/

theorem exp_mul_of_abs_one {u : ℝ} (hu : u = 1 ∨ u = -1) (x : ℝ) :
    exp (x * u) = cosh x + u * sinh x := by
  rcases hu with rfl | rfl
  · rw [mul_one, one_mul, Real.cosh_add_sinh]
  · rw [mul_neg, mul_one, neg_one_mul, ← sub_eq_add_neg, Real.cosh_sub_sinh]

theorem spin_eq_one_or (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

theorem mul_spin_eq_one_or (a b : Bool) : spin a * spin b = 1 ∨ spin a * spin b = -1 := by
  rcases spin_eq_one_or a with ha | ha <;> rcases spin_eq_one_or b with hb | hb <;>
    rw [ha, hb] <;> norm_num

/-- **THE FIELD FACTOR.** -/
theorem exp_field (x : ℝ) (b : Bool) :
    exp (x * spin b) = cosh x + spin b * sinh x :=
  exp_mul_of_abs_one (spin_eq_one_or b) x

/-- **THE BOND FACTOR.** -/
theorem exp_bond (x : ℝ) (a b : Bool) :
    exp (x * (spin a * spin b)) = cosh x + spin a * spin b * sinh x :=
  exp_mul_of_abs_one (mul_spin_eq_one_or a b) x

/-! ## 2. The annihilator -/

theorem sum_spin_bool : ∑ b : Bool, spin b = 0 := by
  simp [spin]

/-- The product over a subset, written as a product over everything. -/
theorem prod_subset_eq_prod_ite (A : Finset V) (σ : V → Bool) :
    ∏ v ∈ A, spin (σ v) = ∏ v : V, (if v ∈ A then spin (σ v) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **SUMMING A PRODUCT OF SPINS OVER ALL CONFIGURATIONS FACTORISES.** -/
theorem sum_prod_spin (A : Finset V) :
    ∑ σ : V → Bool, ∏ v ∈ A, spin (σ v)
      = ∏ v : V, (if v ∈ A then (0 : ℝ) else 2) := by
  have hcongr : ∀ σ : V → Bool, ∏ v ∈ A, spin (σ v)
      = ∏ v : V, (if v ∈ A then spin (σ v) else 1) := prod_subset_eq_prod_ite A
  rw [Finset.sum_congr rfl fun σ _ => hcongr σ,
    ← Fintype.prod_sum fun (v : V) (b : Bool) => if v ∈ A then spin b else 1]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ A
  · simp only [if_pos hv]
    exact sum_spin_bool
  · simp [hv]

/-- **AND KILLS EVERY NON-EMPTY SET OF SITES.** This is the step that makes Griffiths' expansion
collapse onto its even terms. -/
theorem sum_prod_spin_eq_zero {A : Finset V} (hA : A.Nonempty) :
    ∑ σ : V → Bool, ∏ v ∈ A, spin (σ v) = 0 := by
  obtain ⟨v, hv⟩ := hA
  rw [sum_prod_spin A]
  exact Finset.prod_eq_zero (Finset.mem_univ v) (if_pos hv)

/-- The empty set is the exception, and it is the normalisation. Stated about the empty product
rather than about the constant `1`, so that the name says what the theorem says. -/
theorem sum_prod_spin_empty :
    ∑ σ : V → Bool, ∏ v ∈ (∅ : Finset V), spin (σ v) = 2 ^ Fintype.card V := by
  rw [sum_prod_spin]
  simp

end

end IsingGKSParity
