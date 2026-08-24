/-
  IsingCoupledPair.lean — the magnetisation of a bonded pair, computed exactly, and the first
  result in this estate where a field at one site reaches a site that has none.

  WHY. `WALLS §W3.6` names one residue on the Griffiths-comparison arm with no route recorded:
  *"A partially coupled comparison model would need its own magnetisation computed, which is a
  strictly harder problem than the one it is meant to solve unless the partial coupling is chosen
  to keep it tractable. **Nothing in this estate does that and no route to it is recorded.**"*
  This file chooses the partial coupling to keep it tractable — a single bond — and computes it.

  WHY IT MATTERS, AND IT IS ONE NUMBER. `IsingSiteFieldBound` characterised the BOND-FREE
  comparison: it delivers `tanh (β·c p)` at each site, hence **exactly zero** at a site with no
  field of its own (`IsingBoxInteraction.zero_le_integral_interior`). Switch one bond on, of
  strength `J`, between a site carrying field `a` and a site carrying none, and the unfielded
  site's magnetisation is

      ⟨σ₂⟩ = tanh J · tanh a,

  **strictly positive whenever both are.** That is `pair_expect_unfielded`. The bond-free route's
  `0` at that site was a fact about the route, not about the model, and this is the theorem that
  says so.

  AND THE FIELDED SITE IS UNCHANGED, WHICH IS WORTH STATING BECAUSE IT IS SURPRISING.
  `pair_expect_fielded`: ⟨σ₁⟩ = tanh a, with no `J` in it at all. Summing over the partner leaves
  `2 cosh (J · σ₁)`, and `cosh` is even while `σ₁ = ±1`, so the partner contributes the same factor
  either way and cancels. **A bond transmits the field one way here and not the other**, and the
  asymmetry is entirely due to which site carries the field.

  WHAT THIS DOES NOT DO, AND THE ARITHMETIC IS UNCHANGED. Only `O(n)` interior sites of an `n × n`
  box are adjacent to the boundary, so a dimer comparison raises the constant and not the order:
  `IsingSiteFieldBound.route_insufficient_of_small_support` applies to the resulting profile
  exactly as before. **No wall moves.** What changes is that the next rung — chains rather than
  dimers — is now a computation with a first case done, rather than a residue with no route. The
  chain case is NOT attempted here and its cost is not claimed (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingGriffithsMono
import IsingIndependentSpins

namespace IsingCoupledPair

open Finset Real
open IsingGriffiths IsingGriffithsMono IsingTransfer2D

noncomputable section

/-! ## 1. The model: two sites, one bond, one field -/

/-- The two interaction terms: the bond `{0, 1}` and the field at site `0`. -/
def pairSet : Fin 2 → Finset (Fin 2)
  | 0 => {0, 1}
  | 1 => {0}

/-- Coupling `J` on the bond, `a` on the field. -/
def pairCoup (J a : ℝ) : Fin 2 → ℝ
  | 0 => J
  | 1 => a

/-! ## 2. Four configurations, written out -/

/-- Every sum over `Fin 2 → Bool` is a sum of four terms. `finTwoArrowEquiv` does the work. -/
theorem sum_pair (f : (Fin 2 → Bool) → ℝ) :
    ∑ σ : Fin 2 → Bool, f σ
      = f ![true, true] + f ![true, false] + f ![false, true] + f ![false, false] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp f]
  simp [Fintype.sum_prod_type, finTwoArrowEquiv]
  ring

/-- The energy of a configuration, evaluated. -/
theorem pair_energy (J a : ℝ) (σ : Fin 2 → Bool) :
    ∑ i : Fin 2, pairCoup J a i * ∏ v ∈ pairSet i, spin (σ v)
      = J * (spin (σ 0) * spin (σ 1)) + a * spin (σ 0) := by
  rw [Fin.sum_univ_two]
  congr 1
  · rw [pairCoup, pairSet, Finset.prod_pair (by decide)]
  · rw [pairCoup, pairSet, Finset.prod_singleton]

/-- **THE BOLTZMANN FACTOR, FACTORISED BEFORE ANY ARITHMETIC.** Splitting the exponential here
rather than after the four cases are expanded is what keeps the computation to `ring`. -/
theorem exp_pair_energy (J a : ℝ) (σ : Fin 2 → Bool) :
    exp (∑ i : Fin 2, pairCoup J a i * ∏ v ∈ pairSet i, spin (σ v))
      = exp (J * (spin (σ 0) * spin (σ 1))) * exp (a * spin (σ 0)) := by
  rw [pair_energy, Real.exp_add]

/-! ## 3. The partition function and the two magnetisations -/

theorem pair_part (J a : ℝ) :
    part pairSet (pairCoup J a) = (exp J + exp (-J)) * (exp a + exp (-a)) := by
  rw [part, sum_pair]
  simp only [exp_pair_energy]
  simp only [spin, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

theorem pair_num_fielded (J a : ℝ) :
    num pairSet (pairCoup J a) {0} = (exp J + exp (-J)) * (exp a - exp (-a)) := by
  rw [num, sum_pair]
  simp only [exp_pair_energy]
  simp only [Finset.prod_singleton, spin, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

theorem pair_num_unfielded (J a : ℝ) :
    num pairSet (pairCoup J a) {1} = (exp J - exp (-J)) * (exp a - exp (-a)) := by
  rw [num, sum_pair]
  simp only [exp_pair_energy]
  simp only [Finset.prod_singleton, spin, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

theorem pair_part_pos (J a : ℝ) : 0 < part pairSet (pairCoup J a) := by
  rw [pair_part]
  have h1 : (0:ℝ) < exp J + exp (-J) := by positivity
  have h2 : (0:ℝ) < exp a + exp (-a) := by positivity
  exact mul_pos h1 h2

/-- **THE FIELDED SITE IS UNAFFECTED BY THE BOND.** Summing over the partner leaves a factor
`exp J + exp (−J)` in both numerator and denominator, and it cancels — so the answer is the
one-site answer, with no `J` in it at all. -/
theorem pair_expect_fielded (J a : ℝ) :
    num pairSet (pairCoup J a) {0} / part pairSet (pairCoup J a) = tanh a := by
  rw [pair_num_fielded, pair_part, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hJ : (0:ℝ) < exp J + exp (-J) := by positivity
  have ha : (0:ℝ) < exp a + exp (-a) := by positivity
  field_simp

/-- **AND THE SITE WITH NO FIELD OF ITS OWN GETS `tanh J · tanh a`.**

This is the point of the file. The bond-free comparison of `IsingSiteFieldBound` delivers
`tanh (β·c p)` at each site, hence **exactly zero** where the field is off. One bond changes that
to a product of two hyperbolic tangents, **strictly positive whenever both `J` and `a` are**. The
zero was a fact about the route, not about the model. -/
theorem pair_expect_unfielded (J a : ℝ) :
    num pairSet (pairCoup J a) {1} / part pairSet (pairCoup J a) = tanh J * tanh a := by
  rw [pair_num_unfielded, pair_part, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_eq, Real.cosh_eq, Real.sinh_eq, Real.cosh_eq]
  have hJ : (0:ℝ) < exp J + exp (-J) := by positivity
  have ha : (0:ℝ) < exp a + exp (-a) := by positivity
  field_simp

/-- **STRICTLY POSITIVE**, which is the clause the bond-free route cannot have at an unfielded
site. -/
theorem pair_expect_unfielded_pos {J a : ℝ} (hJ : 0 < J) (ha : 0 < a) :
    0 < num pairSet (pairCoup J a) {1} / part pairSet (pairCoup J a) := by
  rw [pair_expect_unfielded]
  exact mul_pos (IsingIndependentSpins.tanh_pos_of_pos hJ)
    (IsingIndependentSpins.tanh_pos_of_pos ha)

end

end IsingCoupledPair
