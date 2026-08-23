/-
  IsingOddObservable.lean — the decay chain needs the observable to be ODD under
  the flip, and nothing else about it.

  WHY. `PROOF_STRATEGY` §7 rule 3, the last restrictive hypothesis left in this
  chain that is not the wall itself: every theorem about the vanishing constant is
  about `spin (σ v)`, the spin at ONE site. That is a genuine restriction — the
  magnetisation a physicist measures is the sum over the whole cross-section, and
  it is not a single spin.

  AND THE ARGUMENT NEVER USED THAT IT WAS ONE. What `flipMatG_mul_spinDiag`
  consumes is `spin (flipCross σ v) = -spin (σ v)`: the observable reverses sign
  under the global flip. Nothing else about `spin` enters — not that it is `±1`,
  not that it depends on one site. So the whole vanishing argument runs for any
  **odd** observable.

  WHAT THAT BUYS, and it is not a re-labelling. The total cross-sectional
  magnetisation `∑_v spin (σ v)` is odd and is not a single spin, so
  `expectG_odd_tendsto_zero` says the long slab's expected TOTAL magnetisation
  vanishes — the statement the physics is about. So are any weighted
  magnetisation, and any product of an ODD number of distinct spins, and
  `IsingSlabField.fieldE` itself, which is where the field's own energy sits on
  this line.

  WHAT DOES NOT CARRY. `sum_sq_spinEigenG_row` — the rows of the observable in the
  eigenbasis summing to one — is `spin_sq`, and a general odd observable does not
  square to one. That row sum is what makes `IsingSlabDecay`'s bound carry no
  constant in front, so the EXPONENTIAL ESTIMATE is not generalised here and the
  file says so rather than quietly restating it. What generalises is the vanishing
  of the constant, which is the part the flip was ever needed for.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGibbsMagnetisation

namespace IsingOddObservable

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingTwoPointSpectral IsingSlabTransfer IsingSlabFlip
open IsingSlabMagnetisation IsingSlabConfig IsingSlabField IsingGibbsMagnetisation

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Odd observables -/

/-- **AN OBSERVABLE THAT REVERSES SIGN UNDER THE GLOBAL FLIP.** The single hypothesis the whole
vanishing argument ever used. -/
def OddObs (w : Cross V → ℝ) : Prop := ∀ σ : Cross V, w (flipCross σ) = -w σ

omit [Fintype V] [DecidableEq V] in
theorem oddObs_spin (v : V) : OddObs (fun σ : Cross V => spin (σ v)) :=
  fun σ => spin_flipCross σ v

omit [DecidableEq V] in
/-- **THE TOTAL CROSS-SECTIONAL MAGNETISATION IS ODD**, and it is not a single spin.
This is the one instance the file exists for. -/
theorem oddObs_totalMag : OddObs (fun σ : Cross V => ∑ v : V, spin (σ v)) := by
  intro σ
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun v _ => spin_flipCross σ v

omit [DecidableEq V] in
/-- Any weighted magnetisation is odd. -/
theorem oddObs_weighted (c : V → ℝ) : OddObs (fun σ : Cross V => ∑ v : V, c v * spin (σ v)) := by
  intro σ
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [spin_flipCross]; ring

omit [DecidableEq V] in
/-- And the magnetic field of `IsingSlabField` is an odd observable — which is exactly why it
cannot be an energy for this chain: an energy has to be EVEN. -/
theorem oddObs_fieldE (h : ℝ) : OddObs (fieldE (V := V) h) := fun σ => fieldE_flipCross h σ

/-! ## 2. The flip anticommutes with any odd observable -/

theorem flipMatG_mul_diagOdd {w : Cross V → ℝ} (hw : OddObs w) :
    flipMatG V * Matrix.diagonal w = -(Matrix.diagonal w * flipMatG V) := by
  ext σ ρ
  rw [flipMatG_mul_apply, Matrix.neg_apply, mul_flipMatG_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : flipCross σ = ρ
  · subst h
    rw [if_pos rfl, if_pos ((flipCross_eq_comm σ (flipCross σ)).mp rfl), hw]
  · rw [if_neg h, if_neg fun hc => h ((flipCross_eq_comm σ ρ).mpr hc).symm, neg_zero]

/-- **THE OBSERVABLE READ IN THE EIGENBASIS.** `spinEigenG` is this at `w = spin (· v)`. -/
noncomputable def obsEigenG (β : ℝ) (E : Cross V → ℝ) (w : Cross V → ℝ) :
    Matrix (Cross V) (Cross V) ℝ :=
  (eigU β E)ᴴ * Matrix.diagonal w * eigU β E

theorem spinEigenG_eq_obsEigenG (β : ℝ) (E : Cross V → ℝ) (v : V) :
    spinEigenG β E v = obsEigenG β E (fun σ => spin (σ v)) := rfl

theorem flipEigenG_anticomm_obsEigenG {w : Cross V → ℝ} (hw : OddObs w) (β : ℝ)
    (E : Cross V → ℝ) :
    flipEigenG β E * obsEigenG β E w = -(obsEigenG β E w * flipEigenG β E) := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [flipEigenG, obsEigenG, conj_mul_conj _ _ _ _ hU, conj_mul_conj _ _ _ _ hU,
    flipMatG_mul_diagOdd hw, Matrix.mul_neg, Matrix.neg_mul]

/-! ## 3. So its top diagonal entry vanishes -/

/-- **THE TOP DIAGONAL ENTRY OF ANY ODD OBSERVABLE IS ZERO.** `spinEigenG_top_eq_zero` is this at
one site; the proof is the same and the hypothesis on the observable is the weakest one that makes
it run. -/
theorem obsEigenG_top_eq_zero {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    {w : Cross V → ℝ} (hw : OddObs w) (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    obsEigenG β E w p₀ p₀ = 0 := by
  classical
  have hoff : ∀ q : Cross V, q ≠ p₀ →
      flipEigenG β E p₀ q = 0 ∧ flipEigenG β E q p₀ = 0 := fun q hq =>
    flipEigenG_apply_eq_zero_of_ne hE β hp₀ hq
  have hsq : flipEigenG β E p₀ p₀ * flipEigenG β E p₀ p₀ = 1 := by
    have h := congrArg (fun X : Matrix (Cross V) (Cross V) ℝ => X p₀ p₀)
      (flipEigenG_mul_self β E)
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [← h, Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp)]
  have hQne : flipEigenG β E p₀ p₀ ≠ 0 := fun h0 => by simp [h0] at hsq
  have hanti := congrArg (fun X : Matrix (Cross V) (Cross V) ℝ => X p₀ p₀)
    (flipEigenG_anticomm_obsEigenG hw β E)
  simp only [Matrix.mul_apply, Matrix.neg_apply] at hanti
  rw [Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp),
    Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).2, mul_zero])
      (fun hp => absurd (mem_univ p₀) hp)] at hanti
  have hz : flipEigenG β E p₀ p₀ * (obsEigenG β E w p₀ p₀ + obsEigenG β E w p₀ p₀) = 0 := by
    linear_combination hanti
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hQne
  · linarith [h0]

/-! ## 4. And the Gibbs expectation of any odd observable tends to zero

Every step of `IsingGibbsMagnetisation` is repeated with `spin (· v)` replaced by `w`; none of
them used anything about `spin`. -/

theorem trace_obsEigenG_mul_conj (β : ℝ) (E w : Cross V → ℝ)
    (X : Matrix (Cross V) (Cross V) ℝ) :
    (obsEigenG β E w * ((eigU β E)ᴴ * X * eigU β E)).trace
      = (Matrix.diagonal w * X).trace := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [obsEigenG, conj_mul_conj _ _ _ _ hU, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem sum_obsEigenG_mul_eigenvalues_pow (β : ℝ) (E w : Cross V → ℝ) (m : ℕ) :
    (∑ p, obsEigenG β E w p p * (transferG_isHermitian β E).eigenvalues p ^ m)
      = ∑ σ : Cross V, w σ * (transferG β E ^ m) σ σ := by
  have h := trace_obsEigenG_mul_conj β E w (transferG β E ^ m)
  rw [IsingFieldTraceLimit.conj_transferG_pow β E m] at h
  have hl : (obsEigenG β E w
        * Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q ^ m).trace
      = ∑ p, obsEigenG β E w p p * (transferG_isHermitian β E).eigenvalues p ^ m := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  have hr : (Matrix.diagonal w * transferG β E ^ m).trace
      = ∑ σ : Cross V, w σ * (transferG β E ^ m) σ σ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  rw [← hl, ← hr, h]

/-- **THE GIBBS EXPECTATION OF ANY OBSERVABLE CONVERGES TO ITS TOP DIAGONAL ENTRY.** No oddness is
needed for this; oddness enters only in §3, which makes the limit zero. -/
theorem expectG_tendsto [Nonempty V] (β : ℝ) (E w : Cross V → ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M w) atTop (𝓝 (obsEigenG β E w p₀ p₀)) := by
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hnum := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => obsEigenG β E w p p)
  have hden := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun _ => (1 : ℝ))
  have hdiv := hnum.div hden one_ne_zero
  rw [div_one] at hdiv
  refine Tendsto.congr (fun M => ?_) hdiv
  simp only [Pi.div_apply]
  have hnumM : (∑ p, obsEigenG β E w p p
        * ((transferG_isHermitian β E).eigenvalues p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ σ : Cross V, w σ * (transferG β E ^ (M + 1)) σ σ)
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    rw [← sum_obsEigenG_mul_eigenvalues_pow β E w (M + 1), Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by rw [div_pow, ← mul_div_assoc]
  have hdenM : (∑ _p : Cross V, (1 : ℝ)
        * ((transferG_isHermitian β E).eigenvalues _p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ σ : Cross V, (transferG β E ^ (M + 1)) σ σ)
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    have htr : (∑ σ : Cross V, (transferG β E ^ (M + 1)) σ σ)
        = ∑ p, (transferG_isHermitian β E).eigenvalues p ^ (M + 1) :=
      TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow (transferG_isHermitian β E) (M + 1)
    rw [htr, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by rw [one_mul, div_pow]
  rw [hnumM, hdenM, div_div_div_cancel_right₀ (pow_ne_zero (M + 1) (ne_of_gt hp₀pos)),
    expectG_eq_sym_trace_div]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- **SO THE LONG SLAB'S EXPECTATION OF ANY ODD OBSERVABLE IS ZERO**, at a flip-invariant energy —
which is `IsingGibbsMagnetisation.expectG_spin_tendsto_zero` with the single spin removed. -/
theorem expectG_odd_tendsto_zero [Nonempty V] {E : Cross V → ℝ}
    (hE : ∀ σ, E (flipCross σ) = E σ) {w : Cross V → ℝ} (hw : OddObs w) (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M w) atTop (𝓝 0) := by
  have h := expectG_tendsto β E w hp₀
  rwa [obsEigenG_top_eq_zero hE hw β hp₀] at h

/-! ## 5. The instances

`ERRATUM 201`. The single spin is recovered first, so the generalisation is visibly a
generalisation of what was there and not a parallel construction; the total magnetisation is what
the file exists for. -/

/-- **THE SINGLE-SPIN CASE RECOVERED**, `IsingSlabMagnetisation.spinEigenG_top_eq_zero` statement
for statement, through `spinEigenG_eq_obsEigenG` which is `rfl`. -/
theorem spinEigen_top_eq_zero_of_odd {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    spinEigenG β E v p₀ p₀ = 0 :=
  obsEigenG_top_eq_zero hE (oddObs_spin v) β hp₀

/-- **THE LONG SLAB'S TOTAL MAGNETISATION VANISHES.** The sum of the spins over the WHOLE
cross-section, not one site — the quantity the physics is about, and not a single spin. -/
theorem expectG_totalMag_tendsto_zero [Nonempty V] {E : Cross V → ℝ}
    (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M (fun σ => ∑ v : V, spin (σ v))) atTop (𝓝 0) :=
  expectG_odd_tendsto_zero hE oddObs_totalMag β hp₀

/-- **AND ANY WEIGHTED MAGNETISATION.** -/
theorem expectG_weighted_tendsto_zero [Nonempty V] {E : Cross V → ℝ}
    (hE : ∀ σ, E (flipCross σ) = E σ) (c : V → ℝ) (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M (fun σ => ∑ v : V, c v * spin (σ v))) atTop (𝓝 0) :=
  expectG_odd_tendsto_zero hE (oddObs_weighted c) β hp₀

/-- **INSTANCE — the three-dimensional slab's total magnetisation vanishes.** -/
theorem slab_totalMag_tendsto_zero (β : ℝ) (a b : ℕ)
    {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (slabTransfer_isHermitian β a b).eigenvalues j
      ≤ (slabTransfer_isHermitian β a b).eigenvalues p₀) :
    Tendsto (fun M : ℕ =>
        expectG β (slabIntra (a := a) (b := b)) M (fun σ => ∑ v, spin (σ v))) atTop (𝓝 0) :=
  expectG_totalMag_tendsto_zero slabIntra_flipCross β hp₀

end IsingOddObservable
