/-
  IsingSlabField.lean — a magnetic field is an admissible `E`, and it is exactly
  what the decay chain's one hypothesis forbids.

  WHY. `IsingSlabAniso` freed the couplings by observing that `transferG`'s energy
  parameter `E` is arbitrary, and that every slab theorem follows by choosing it.
  The obvious next question is the one a physicist asks first: **why not a
  magnetic field?** `E σ = h · ∑ᵥ spin (σ v)` is a perfectly good energy, the
  transfer matrix is still symmetric with positive entries, and the spectral gap
  still holds — `transferG_gap` asks nothing of `E`.

  BECAUSE THE DECAY CHAIN ASKS ONE THING OF `E` AND A FIELD IS PRECISELY WHAT
  FAILS IT. Every theorem from `flipMatG_mul_transferG` onward carries
  `hE : ∀ σ, E (flipCross σ) = E σ`, and a field reverses sign under the flip
  rather than being invariant under it. **This file is the witness**, so that the
  hypothesis is known to be load-bearing rather than believed to be:
  `flipMatG_not_comm_transferG_field` exhibits `β = 1`, a one-site cross-section
  and a unit field for which the flip does NOT commute with the transfer matrix,
  the two sides being `1` and `exp 2`.

  AND IT IS THE SAME DISTINCTION THE WHOLE CHAIN RESTS ON. `interG_flipCross` is
  invariant with NO hypothesis, because a bond is a product of TWO spins and both
  change sign; `flipMatG_mul_spinDiag` anticommutes with no hypothesis, because
  an observable is ONE spin. A magnetic field is a sum of single spins, so it
  sits on the anticommuting side of that line — which is why it is the thing an
  arbitrary `E` may not be.

  WHAT THIS DOES AND DOES NOT SHOW. It shows the hypothesis is needed at the step
  the chain uses it: with a field, the commuting law is false. It does **not**
  show that `spinEigenG_top_eq_zero`'s conclusion fails — a conclusion can
  survive a broken proof step, and establishing that the magnetisation is
  genuinely nonzero in a field needs the top eigenvector, which this estate does
  not compute. That is stated rather than glossed, and it is the same scope
  `IsingSlabSpectral.exists_insertion_not_conj_invariant` has.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabAniso

namespace IsingSlabField

open Finset Matrix Real
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip

open scoped Matrix

/-! ## 1. A magnetic field, at an arbitrary cross-section -/

/-- **A UNIFORM MAGNETIC FIELD** as a cross-section energy. It is an admissible `E` for everything
that does not need the flip: `transferG β (fieldE h)` is symmetric with strictly positive entries,
so `transferG_gap` applies to it unchanged. -/
def fieldE {V : Type*} [Fintype V] (h : ℝ) (σ : Cross V) : ℝ := ∑ v : V, h * spin (σ v)

/-- **AND IT ANTICOMMUTES WITH THE FLIP RATHER THAN COMMUTING**, because it is a sum of SINGLE
spins. This is the bond-versus-single-spin line that `interG_flipCross` and
`flipMatG_mul_spinDiag` sit on either side of. -/
theorem fieldE_flipCross {V : Type*} [Fintype V] (h : ℝ) (σ : Cross V) :
    fieldE h (flipCross σ) = -fieldE h σ := by
  simp only [fieldE, spin_flipCross, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## 2. The witness: with a field the flip does not commute with the transfer matrix

One site, unit field, `β = 1`. The two sides of the commuting law differ at a single entry, and
the numbers are `1` and `exp 2`. -/

/-- The all-up configuration of a one-site cross-section. -/
def up : Cross (Fin 1) := fun _ => true

/-- The all-down configuration of a one-site cross-section. -/
def down : Cross (Fin 1) := fun _ => false

theorem flipCross_up : flipCross up = down := rfl

theorem flipCross_down : flipCross down = up := rfl

theorem transferG_field_down_down :
    transferG 1 (fieldE (V := Fin 1) 1) down down = 1 := by
  rw [transferG_apply]
  norm_num [fieldE, interG, down, spin, Fin.sum_univ_one, ← Real.exp_add]

theorem transferG_field_up_up :
    transferG 1 (fieldE (V := Fin 1) 1) up up = exp 2 := by
  rw [transferG_apply]
  norm_num [fieldE, interG, up, spin, Fin.sum_univ_one, ← Real.exp_add]

/-- **THE HYPOTHESIS `hE` IS LOAD-BEARING.** At one site, unit field and `β = 1`, the flip does not
commute with the transfer matrix: the two sides of `flipMatG_mul_transferG` differ at the entry
`(up, down)`, where they are `1` and `exp 2`.

So `flipMatG_mul_transferG` is false without its hypothesis, and every theorem downstream of it —
`flipEigenG_comm_diagonal`, `spinEigenG_top_eq_zero`, the decay bound — loses its first step in a
field. -/
theorem flipMatG_not_comm_transferG_field :
    flipMatG (Fin 1) * transferG 1 (fieldE (V := Fin 1) 1)
      ≠ transferG 1 (fieldE (V := Fin 1) 1) * flipMatG (Fin 1) := by
  intro hcon
  have h := congrArg (fun M : Matrix (Cross (Fin 1)) (Cross (Fin 1)) ℝ => M up down) hcon
  simp only [flipMatG_mul_apply, mul_flipMatG_apply, flipCross_up, flipCross_down] at h
  rw [transferG_field_down_down, transferG_field_up_up] at h
  have hlt : (1 : ℝ) < exp 2 := by nlinarith [Real.add_one_le_exp (2 : ℝ)]
  exact absurd h (ne_of_lt hlt)

/-- **AND THE GAP SURVIVES**, which is what makes the previous theorem informative rather than
obvious: a field does not break the transfer matrix, only the symmetry. `transferG_gap` asks
nothing of `E`, so the field model still has one top eigenvalue strictly above the rest — it is
only the identification of the leftover constant as ZERO that the field costs. -/
theorem field_gap (h β : ℝ) {V : Type*} [Fintype V] [DecidableEq V]
    {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β (fieldE (V := V) h)).eigenvalues j
      ≤ (transferG_isHermitian β (fieldE (V := V) h)).eigenvalues p₀)
    {q : Cross V}
    (hne : (transferG_isHermitian β (fieldE (V := V) h)).eigenvalues q
      ≠ (transferG_isHermitian β (fieldE (V := V) h)).eigenvalues p₀) :
    |(transferG_isHermitian β (fieldE (V := V) h)).eigenvalues q|
      < (transferG_isHermitian β (fieldE (V := V) h)).eigenvalues p₀ :=
  transferG_gap _ _ hp₀ hne

/-- **AND THE FIELD IS NOT VACUOUSLY EXCLUDED**: at `h = 0` it is flip-invariant and the whole
chain applies, so `fieldE` meets `hE` exactly where a field is absent. `ERRATUM 48` in the other
direction — a hypothesis that nothing satisfies and a hypothesis that everything satisfies are
both worth checking, and this one is neither. -/
theorem fieldE_zero_flipCross {V : Type*} [Fintype V] (σ : Cross V) :
    fieldE (V := V) 0 (flipCross σ) = fieldE (V := V) 0 σ := by
  simp [fieldE]

end IsingSlabField
