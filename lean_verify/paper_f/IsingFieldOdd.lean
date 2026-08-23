/-
  IsingFieldOdd.lean — the magnetisation is an odd function of the field, and the partition
  function an even one, at every finite length.

  WHY. The `UNLOCK_WATCHLIST` item *"does the magnetisation fail to vanish in a field at a
  cross-section of size two or more?"* names its remaining leg precisely: bound
  `(∑_σ spin(σ v)·(Tᵐ)_σσ) / λ_{p₀}ᵐ` away from zero. It also names, and marks as a route rather
  than a fact (`ERRATUM 204`), the tempting step: *"with a field `h > 0` every diagonal entry
  `(Tᵐ)_σσ` should exceed the one at `flipCross σ`"*.

  **THAT STEP IS NOT AVAILABLE, AND THE REASON IS WORTH THE FILE.** Writing `T_h = D_h A D_h` with
  `D_h` the diagonal of `exp(β h S(σ)/2)` and `A` the field-free factor, entrywise domination
  `T_h ≥ T_{−h}` holds exactly when `S(σ) + S(τ) ≥ 0` — so it fails on half the matrix, and the
  same failure survives to powers, where a closed path contributes `A_P (e^{βhΣ_P} − e^{−βhΣ_P})`
  and `Σ_P` may be negative. **What IS available is the structure underneath it**, and this file
  proves that instead of asserting the step.

  WHAT IS PROVED, and none of it is about matrices.

  * `expectG_flip_odd` and `partitionG_flip_eq` — for any two energies related by the flip
    (`E (flipCross σ) = E' σ`), the partition function is unchanged and the expectation of any
    ODD observable changes sign. **The proof is one reindexing of the configuration sum**, along
    the involution `s ↦ flipCross ∘ s` — no transfer matrix, no eigenvector, no spectral theorem;
  * **`expectG_field_odd`** — hence, for an energy `E₀ + fieldE h` with flip-invariant `E₀`:
    *the expectation of any odd observable is an odd function of `h`*, at every finite
    cross-section, every length, every `β`. `partitionG_field_even`: the partition function is
    even in `h`;
  * `expectG_eq_zero_of_odd_of_flip` — **and at `h = 0` the expectation is exactly `0`, at every
    finite length**. `IsingFlipSymmetry.expect_eq_zero_of_odd` is this for the strip's `Col n`;
    here it is for an arbitrary cross-section `Cross V`, and it arrives as the `h = 0` case of the
    odd law rather than as a separate argument.

  WHAT THIS DOES NOT DO, AND IT IS THE ITEM'S WHOLE QUESTION. It does not bound anything away from
  zero. Oddness says the magnetisation is `0` at `h = 0` and that its values at `±h` are negatives;
  it says nothing about whether either is nonzero. **The item stays open on exactly the leg it
  named**, and this file narrows it by removing a route rather than by supplying one.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingOddObservable

namespace IsingFieldOdd

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip IsingSlabConfig IsingSlabField
open IsingOddObservable

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The field energy under the flip -/

omit [DecidableEq V] in
theorem fieldE_neg (h : ℝ) (σ : Cross V) : fieldE (-h) σ = -fieldE h σ := by
  simp only [fieldE, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq V] in
theorem fieldE_zero (σ : Cross V) : fieldE 0 σ = 0 := by
  simp [fieldE]

/-- The energy of a slab in a field: a flip-invariant part and the field term. -/
def fieldEnergy (E₀ : Cross V → ℝ) (h : ℝ) : Cross V → ℝ := fun σ => E₀ σ + fieldE h σ

omit [DecidableEq V] in
/-- **FLIPPING A CONFIGURATION REVERSES THE FIELD**, and leaves everything else alone. -/
theorem fieldEnergy_flipCross {E₀ : Cross V → ℝ} (hE₀ : ∀ σ, E₀ (flipCross σ) = E₀ σ)
    (h : ℝ) (σ : Cross V) :
    fieldEnergy E₀ h (flipCross σ) = fieldEnergy E₀ (-h) σ := by
  simp only [fieldEnergy, hE₀, fieldE_flipCross, fieldE_neg]

omit [DecidableEq V] in
theorem fieldEnergy_zero (E₀ : Cross V → ℝ) : fieldEnergy E₀ 0 = E₀ := by
  funext σ
  simp [fieldEnergy, fieldE_zero]

/-! ## 2. Flipping a whole path

The involution the argument runs on. It is a bijection of configuration paths, and everything below
is one application of it. -/

/-- Flip every cross-section of a path. -/
def flipPath (M : ℕ) : (Fin (M + 1) → Cross V) ≃ (Fin (M + 1) → Cross V) where
  toFun s := fun j => flipCross (s j)
  invFun s := fun j => flipCross (s j)
  left_inv s := funext fun j => flipCross_involutive (s j)
  right_inv s := funext fun j => flipCross_involutive (s j)

theorem sum_flipPath (M : ℕ) (F : (Fin (M + 1) → Cross V) → ℝ) :
    ∑ s : Fin (M + 1) → Cross V, F (fun j => flipCross (s j)) = ∑ s, F s :=
  Fintype.sum_equiv (flipPath M) _ _ fun _ => rfl

omit [DecidableEq V] in
/-- **THE ENERGY OF A FLIPPED PATH IS THE FLIPPED ENERGY OF THE PATH.** The bond term is invariant
(`interG_flipCross`) and the site term is where the hypothesis is spent. -/
theorem energyG_flipPath {E E' : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E' σ)
    (M : ℕ) (s : Fin (M + 1) → Cross V) :
    energyG E M (fun j => flipCross (s j)) = energyG E' M s := by
  simp only [energyG]
  exact Finset.sum_congr rfl fun j _ => by rw [hE, interG_flipCross]

/-! ## 3. The two laws -/

/-- **THE PARTITION FUNCTION DOES NOT SEE THE FLIP.** -/
theorem partitionG_flip_eq {E E' : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E' σ)
    (β : ℝ) (M : ℕ) : partitionG β E' M = partitionG β E M := by
  simp only [partitionG]
  rw [← sum_flipPath M fun s => exp (β * energyG E M s)]
  exact Finset.sum_congr rfl fun s _ => by rw [energyG_flipPath hE M s]

/-- **AND AN ODD OBSERVABLE CHANGES SIGN.** One reindexing; the numerator picks up the sign from
the observable and the denominator is §3's first law. -/
theorem expectG_flip_odd {E E' : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E' σ)
    (β : ℝ) (M : ℕ) {w : Cross V → ℝ} (hw : OddObs w) :
    expectG β E' M w = -expectG β E M w := by
  have hnum : ∑ s : Fin (M + 1) → Cross V, w (s 0) * exp (β * energyG E' M s)
      = -∑ s : Fin (M + 1) → Cross V, w (s 0) * exp (β * energyG E M s) := by
    rw [← sum_flipPath M fun s => w (s 0) * exp (β * energyG E M s), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [energyG_flipPath hE M s, hw (s 0)]
    ring
  rw [expectG, expectG, hnum, partitionG_flip_eq hE β M, neg_div]

/-! ## 4. The route the item named, refuted

`ERRATUM 247`: a sentence defending a hypothesis is a claim, and claims here are proved or marked.
The header says entrywise domination `T_h ≥ T_{−h}` fails; that is a claim, so here is a witness. -/

/-- **THE ENTRYWISE ROUTE IS NOT AVAILABLE.** At one site, no intra energy, `β = h = 1` and both
arguments spin-down, the field makes the entry SMALLER, not larger: the ratio of the two entries is
`exp (β h (S σ + S τ))` and `S` is negative there. So *"with a field `h > 0` every diagonal entry
exceeds the one at `flipCross σ`"* — the route the watchlist item names and marks as a route — is
false as stated, and the file proves the structure underneath it instead. -/
theorem exists_field_entry_lt :
    ∃ (β h : ℝ) (σ τ : Cross (Fin 1)), 0 < β ∧ 0 < h ∧
      transferG β (fieldEnergy (fun _ => 0) h) σ τ
        < transferG β (fieldEnergy (fun _ => 0) (-h)) σ τ := by
  refine ⟨1, 1, down, down, one_pos, one_pos, ?_⟩
  rw [transferG_apply, transferG_apply]
  have hd : fieldEnergy (fun _ : Cross (Fin 1) => (0 : ℝ)) 1 down = -1 := by
    simp [fieldEnergy, fieldE, down, spin]
  have hd' : fieldEnergy (fun _ : Cross (Fin 1) => (0 : ℝ)) (-1) down = 1 := by
    simp [fieldEnergy, fieldE, down, spin]
  rw [hd, hd']
  have e1 : exp (1 * (-1 : ℝ) / 2) * exp (1 * interG (down : Cross (Fin 1)) down)
      * exp (1 * (-1 : ℝ) / 2) = exp (1 * interG (down : Cross (Fin 1)) down - 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e2 : exp (1 * (1 : ℝ) / 2) * exp (1 * interG (down : Cross (Fin 1)) down)
      * exp (1 * (1 : ℝ) / 2) = exp (1 * interG (down : Cross (Fin 1)) down + 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  exact exp_lt_exp.mpr (by linarith)

/-! ## 5. The field, and the two statements the item is about -/

/-- **THE PARTITION FUNCTION IS EVEN IN THE FIELD.** -/
theorem partitionG_field_even {E₀ : Cross V → ℝ} (hE₀ : ∀ σ, E₀ (flipCross σ) = E₀ σ)
    (β h : ℝ) (M : ℕ) :
    partitionG β (fieldEnergy E₀ (-h)) M = partitionG β (fieldEnergy E₀ h) M :=
  partitionG_flip_eq (fieldEnergy_flipCross hE₀ h) β M

/-- **AND THE EXPECTATION OF AN ODD OBSERVABLE IS AN ODD FUNCTION OF THE FIELD**, at every finite
cross-section, every length and every `β`. -/
theorem expectG_field_odd {E₀ : Cross V → ℝ} (hE₀ : ∀ σ, E₀ (flipCross σ) = E₀ σ)
    (β h : ℝ) (M : ℕ) {w : Cross V → ℝ} (hw : OddObs w) :
    expectG β (fieldEnergy E₀ (-h)) M w = -expectG β (fieldEnergy E₀ h) M w :=
  expectG_flip_odd (fieldEnergy_flipCross hE₀ h) β M hw

/-- **AT ZERO FIELD THE EXPECTATION IS EXACTLY ZERO, AT EVERY FINITE LENGTH.** The `h = 0` case of
the law above: a number equal to its own negative. `IsingFlipSymmetry.expect_eq_zero_of_odd` is
this for the strip's `Col n`; here the cross-section is arbitrary. -/
theorem expectG_eq_zero_of_odd_of_flip {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (M : ℕ) {w : Cross V → ℝ} (hw : OddObs w) :
    expectG β E M w = 0 := by
  have h := expectG_flip_odd (E := E) (E' := E) hE β M hw
  linarith

/-- The magnetisation itself, at zero field. -/
theorem expectG_spin_eq_zero {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (M : ℕ) (v : V) :
    expectG β E M (fun σ => spin (σ v)) = 0 :=
  expectG_eq_zero_of_odd_of_flip hE β M (oddObs_spin v)

/-- And the slab's total magnetisation, at zero field — `oddObs_totalMag` supplies the oddness. -/
theorem expectG_totalMag_eq_zero {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (M : ℕ) :
    expectG β E M (fun σ => ∑ v : V, spin (σ v)) = 0 :=
  expectG_eq_zero_of_odd_of_flip hE β M oddObs_totalMag

end

end IsingFieldOdd
