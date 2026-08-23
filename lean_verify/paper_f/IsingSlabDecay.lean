/-
  IsingSlabDecay.lean — the exponential estimate at an arbitrary cross-section,
  and the vanishing of the constant it clusters to.

  WHY. Rung 3 of the retry `PROOF_STRATEGY` §3 demanded after `IsingSlabTransfer`
  produced a slab with a spectral gap and no decay theorem. `IsingSlabFlip` was
  rung 1 and `IsingSlabMagnetisation` rung 2.

  **AND IT IS NOT THE LAST RUNG, WHICH THE WATCHLIST ITEM ASSUMED IT WOULD BE.**
  That item is headed *"exponential decay of the two-point function at an
  arbitrary cross-section"* and named exactly two remaining rungs, the eigenbasis
  step and the estimate. Both are now done and **the headline is still not
  reached**, because the item's framing carried an unexamined assumption: that
  `corr2SepInf` travels as a two-point function. It does not. It travels as a
  SPECTRAL SUM, and what makes it a two-point function at `Col n` is a separate
  theorem that consumes the strip's geometry. See the next paragraph. The item
  stays open with a third leg named, and the estimate of "one to two units" it
  carried was an estimate of the wrong thing.

  WHAT THIS IS. `IsingTwoPointLimit` proves, for the strip's column, that the
  spectral sum `∑_q ‖B_{p₀q}‖² · (λ_q/λ_{p₀})^κ` differs from its `q = p₀` term
  by at most `r ^ κ`, with `r < 1` the largest ratio off the top index. Every
  step of that is repeated here at an arbitrary finite cross-section, and then
  combined with `IsingSlabMagnetisation.spinEigenG_top_eq_zero` — which says the
  `q = p₀` term is ZERO — into a bound on the quantity itself:

      |corr2SepInfG β E v p₀ κ| ≤ r ^ κ,   r < 1.

  READ THE NAME CAREFULLY, BECAUSE IT CARRIES AN IDENTIFICATION THAT IS PROVED
  IN ONE PLACE ONLY. At `Col n` the quantity `corr2SepInf` is proved to BE the
  limit of the finite strip's actual two-point function, as the strip's length
  grows: that is `IsingTwoPointLimit.corr2Sep_tendsto`, and it consumes the
  strip's geometry — `corr2Sep`, a length direction, a lattice. **NONE OF THAT
  EXISTS AT A GENERAL CROSS-SECTION AND NONE OF IT IS PROVED HERE.**
  `corr2SepInfG` is the SPECTRAL SUM and nothing more. For the slab it is not
  known to be a correlation function of anything, because the slab has no
  `corr2Sep` yet; what is proved about it is exactly what is written, an estimate
  on a sum built from `transferG`'s eigenvalues and `spinEigenG`'s entries. The
  strip is where the two coincide, by `rfl`, and that is `ERRATUM 201`'s
  instantiation rather than an argument that they coincide anywhere else.

  WHAT IS STILL OPEN, AND IT IS THE WALL. `r` is built from ONE cross-section's
  eigenvalues. Nothing here says it stays below one as the cross-section grows,
  which is `IsingTopRatio.UniformSubTopRatio`, proved at no `β` but `0`, no
  route — `WALLS` §W4 §6 item 3, untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabMagnetisation

namespace IsingSlabDecay

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTwoPointSpectral IsingTwoPointLimit
open IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The observable squares to one, so its rows are normalised -/

theorem spinDiagG_mul_self (v : V) :
    (Matrix.diagonal fun σ : Cross V => spin (σ v))
        * (Matrix.diagonal fun σ : Cross V => spin (σ v)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  exact (Matrix.diagonal_eq_diagonal_iff.mpr fun σ : Cross V => spin_sq (σ v)).trans
    Matrix.diagonal_one

theorem spinEigenG_mul_self (β : ℝ) (E : Cross V → ℝ) (v : V) :
    spinEigenG β E v * spinEigenG β E v = 1 := by
  have hUs := eigU_conjTranspose_mul β E
  rw [spinEigenG, conj_mul_conj _ _ _ _ (mul_eq_one_comm.mp hUs), spinDiagG_mul_self,
    Matrix.mul_one, hUs]

theorem spinEigenG_isHermitian (β : ℝ) (E : Cross V → ℝ) (v : V) :
    (spinEigenG β E v).IsHermitian :=
  HermitianTwoPointTrace.isHermitian_conj (Matrix.isHermitian_diagonal _) _

theorem spinEigenG_symm (β : ℝ) (E : Cross V → ℝ) (v : V) (p q : Cross V) :
    spinEigenG β E v p q = spinEigenG β E v q p := by
  simpa using ((spinEigenG_isHermitian β E v).apply p q).symm

/-- **THE SQUARED ENTRIES OF EACH ROW SUM TO ONE.** The diagonal of `B² = 1`, with `B` symmetric.
This is what makes the estimate below a bound by `r ^ κ` with no constant in front. -/
theorem sum_sq_spinEigenG_row (β : ℝ) (E : Cross V → ℝ) (v : V) (p : Cross V) :
    ∑ q, ‖spinEigenG β E v p q‖ ^ 2 = 1 := by
  have h := congrArg (fun X : Matrix (Cross V) (Cross V) ℝ => X p p)
    (spinEigenG_mul_self β E v)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Real.norm_eq_abs, sq_abs, pow_two, spinEigenG_symm β E v q p]

/-! ## 2. The spectral sum, and its diagonal term

**This is not called a two-point function**, and the header says why: at a general cross-section
nothing identifies it with one. -/

/-- **THE SPECTRAL SUM AT AN ARBITRARY CROSS-SECTION**, relative to a choice `p₀` of index. At
`E = intra` it is `IsingTwoPointLimit.corr2SepInf` on the nose (§5). -/
noncomputable def corr2SepInfG (β : ℝ) (E : Cross V → ℝ) (v : V) (p₀ : Cross V) (κ : ℕ) : ℝ :=
  ∑ q, ‖spinEigenG β E v p₀ q‖ ^ 2
    * ((transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀) ^ κ

theorem corr2SepInfG_zero (β : ℝ) (E : Cross V → ℝ) (v : V) (p₀ : Cross V) :
    corr2SepInfG β E v p₀ 0 = 1 := by
  rw [corr2SepInfG]
  simpa using sum_sq_spinEigenG_row β E v p₀

/-- **THE `q = p₀` TERM CARRIES NO SEPARATION.** Its ratio is `1`, so it is `‖B_{p₀p₀}‖²` for
every `κ` — which is exactly the term `IsingSlabMagnetisation` proves to vanish. -/
theorem corr2SepInfG_eq_diag_add (β : ℝ) (E : Cross V → ℝ) (v : V) {p₀ : Cross V}
    (hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀) (κ : ℕ) :
    corr2SepInfG β E v p₀ κ
      = ‖spinEigenG β E v p₀ p₀‖ ^ 2
        + ∑ q ∈ univ.erase p₀, ‖spinEigenG β E v p₀ q‖ ^ 2
            * ((transferG_isHermitian β E).eigenvalues q
                / (transferG_isHermitian β E).eigenvalues p₀) ^ κ := by
  classical
  rw [corr2SepInfG, ← Finset.add_sum_erase univ _ (mem_univ p₀),
    div_self (ne_of_gt hp₀pos), one_pow, mul_one]

/-! ## 3. The largest ratio off the top index, and the estimate -/

/-- **THE LARGEST RATIO OFF THE TOP INDEX IS BELOW ONE**, and it is attained.

`[Nonempty V]` is not decoration and `ERRATUM 48` is why it is stated rather than assumed away:
`Cross V` has `2 ^ card V` elements, so a cross-section with no sites gives a ONE-element index
type, `univ.erase p₀` is empty, and the statement — with it the bound below — is vacuous. Both
cross-sections this estate has are nonempty. -/
theorem exists_subTopRatioG [Nonempty V] (β : ℝ) (E : Cross V → ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ q ∈ univ.erase p₀,
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀| ≤ r := by
  classical
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  obtain ⟨w⟩ := ‹Nonempty V›
  have hntriv : (fun v => !(p₀ v)) ≠ p₀ := fun h => by
    have := congrFun h w
    cases hb : p₀ w <;> rw [hb] at this <;> simp at this
  have hne : (univ.erase p₀).Nonempty :=
    ⟨fun v => !(p₀ v), Finset.mem_erase.mpr ⟨hntriv, mem_univ _⟩⟩
  obtain ⟨qm, hqm, hmax⟩ := Finset.exists_max_image (univ.erase p₀)
    (fun q => |(transferG_isHermitian β E).eigenvalues q
      / (transferG_isHermitian β E).eigenvalues p₀|) hne
  have hlt : ∀ q ∈ univ.erase p₀,
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀| < 1 := by
    intro q hq
    have hqne : q ≠ p₀ := (Finset.mem_erase.mp hq).1
    have hvne : (transferG_isHermitian β E).eigenvalues q
        ≠ (transferG_isHermitian β E).eigenvalues p₀ := fun h =>
      hqne (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos hp₀ h)
    rw [abs_div, abs_of_pos hp₀pos, div_lt_one hp₀pos]
    exact PerronGap.abs_eigenvalues_lt_of_ne _ hpos hp₀ hvne
  exact ⟨_, abs_nonneg _, hlt qm hqm, fun q hq => hmax q hq⟩

/-- **THE BOUND FOR ANY `r` THAT DOMINATES THE RATIOS.** As at `Col n`, the argmax hypothesis is
not needed — the calculation uses `p₀` only through `0 < λ_{p₀}` — and `r < 1` never enters it. -/
theorem corr2SepInfG_connected_le_of_ratio_le (β : ℝ) (E : Cross V → ℝ) (v : V) {p₀ : Cross V}
    (hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀) {r : ℝ} (hr0 : 0 ≤ r)
    (hrle : ∀ q ∈ univ.erase p₀,
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀| ≤ r) (κ : ℕ) :
    |corr2SepInfG β E v p₀ κ - ‖spinEigenG β E v p₀ p₀‖ ^ 2| ≤ r ^ κ := by
  classical
  rw [corr2SepInfG_eq_diag_add β E v hp₀pos κ, add_sub_cancel_left]
  calc |∑ q ∈ univ.erase p₀, ‖spinEigenG β E v p₀ q‖ ^ 2
          * ((transferG_isHermitian β E).eigenvalues q
              / (transferG_isHermitian β E).eigenvalues p₀) ^ κ|
      ≤ ∑ q ∈ univ.erase p₀, |‖spinEigenG β E v p₀ q‖ ^ 2
          * ((transferG_isHermitian β E).eigenvalues q
              / (transferG_isHermitian β E).eigenvalues p₀) ^ κ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ univ.erase p₀, ‖spinEigenG β E v p₀ q‖ ^ 2 * r ^ κ := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hrle q hq) κ)
          (sq_nonneg _)
    _ = (∑ q ∈ univ.erase p₀, ‖spinEigenG β E v p₀ q‖ ^ 2) * r ^ κ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ q, ‖spinEigenG β E v p₀ q‖ ^ 2) * r ^ κ := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 κ)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun q _ _ => sq_nonneg _
    _ = r ^ κ := by rw [sum_sq_spinEigenG_row, one_mul]

/-! ## 4. The constant is zero, so this is decay and not merely clustering -/

/-- **EXPONENTIAL DECAY OF THE SPECTRAL SUM, AT EVERY FINITE CROSS-SECTION.** The clustering
estimate of §3 with its constant identified as zero by `spinEigenG_top_eq_zero`, which is where
`hE` — the flip-invariance of the cross-section's own energy — is spent. -/
theorem corr2SepInfG_abs_le [Nonempty V] {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ κ : ℕ, |corr2SepInfG β E v p₀ κ| ≤ r ^ κ := by
  obtain ⟨r, hr0, hr1, hrle⟩ := exists_subTopRatioG β E hp₀
  refine ⟨r, hr0, hr1, fun κ => ?_⟩
  have hzero : ‖spinEigenG β E v p₀ p₀‖ ^ 2 = 0 := by
    rw [spinEigenG_top_eq_zero hE β v hp₀]
    simp
  have h := corr2SepInfG_connected_le_of_ratio_le β E v
    (PerronGap.eigenvalue_max_pos _ (transferG_pos β E) hp₀) hr0 hrle κ
  rwa [hzero, sub_zero] at h

/-! ## 5. Both instances

`ERRATUM 201` again. The strip is where `corr2SepInfG` is known to be a limit of genuine
correlations; the slab is where it is not, and the second theorem below says only what it says. -/

/-- The strip's spectral sum IS the general one at `E = intra`, by `rfl`. -/
theorem corr2SepInf_eq_corr2SepInfG (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (p₀ : Col n) (κ : ℕ) :
    corr2SepInf β n i p₀ κ = corr2SepInfG β (intra (n := n)) i p₀ κ := rfl

/-- **INSTANCE ONE — the strip.** `IsingMagnetisationVanishes.corr2SepInf_abs_le` obtained from the
general theorem: the infinite strip's two-point function decays exponentially in the separation. -/
theorem strip_corr2SepInf_abs_le (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ κ : ℕ, |corr2SepInf β n i p₀ κ| ≤ r ^ κ :=
  corr2SepInfG_abs_le intra_flipCross β i hp₀

/-- **INSTANCE TWO — the three-dimensional slab.** The spectral sum built from the slab's transfer
matrix decays exponentially. **It is not called a correlation function**: the identification with a
limit of finite-volume correlations is `corr2Sep_tendsto`, which exists at `Col n` and has no
analogue here, because the slab has no `corr2Sep`. That is the remaining leg and it is written down
in `UNLOCK_WATCHLIST`. -/
theorem slab_corr2SepInfG_abs_le (β : ℝ) (a b : ℕ) (v : Fin (a + 1) × Fin (b + 1))
    {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (slabTransfer_isHermitian β a b).eigenvalues j
        ≤ (slabTransfer_isHermitian β a b).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ κ : ℕ,
      |corr2SepInfG β (slabIntra (a := a) (b := b)) v p₀ κ| ≤ r ^ κ :=
  corr2SepInfG_abs_le slabIntra_flipCross β v hp₀

end IsingSlabDecay
