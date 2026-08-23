/-
  IsingTwoObservableLimit.lean — the length limit and the clustering estimate for
  two different observables, and the constant that is not `1`.

  WHY. `IsingTwoObservable` produced the finite-volume two-observable correlation
  and its spectral form, and named the two remaining legs. This is both.

  LEG 1, THE LIMIT. `corr2SepG2_tendsto_of_max`: at fixed cross-section and fixed
  separation `κ`, the finite-length two-observable correlation converges as the
  length grows to `∑_q A_{p₀q}·B_{qp₀}·(λ_q/λ_{p₀})^κ`. Same engine as the
  one-observable case, at two weight families, and one `p₀` serves every `κ`.

  LEG 2, THE ESTIMATE, AND IT IS NOT THE ONE-OBSERVABLE ESTIMATE.
  `IsingSlabDecay`'s bound carries **no constant** because the rows of a spin
  observable in the eigenbasis sum to one — which is `spin_sq`, and neither of two
  general observables squares to the identity. So the honest statement is

      |corr2SepInfG2 κ − A_{p₀p₀}·B_{p₀p₀}| ≤ C · r^κ,
      C = ∑_{q ≠ p₀} |A_{p₀q}|·|B_{qp₀}|,

  and **`crossConst` is a real number that is not `1`**. Anyone who states this
  without a constant has restated the one-observable theorem.

  AND THE CONSTANT SPECIALISES CORRECTLY, which is the check that it is the right
  constant: `crossConst_le_one_of_spin` shows that at `A = B = spin (· v)` it is at
  most `1`, by the row sum the one-observable case used — so the old bound is
  recovered rather than contradicted.

  WHAT THE CONSTANT IS SUBTRACTED FROM. `A_{p₀p₀}·B_{p₀p₀}` is the **product of
  the two one-point functions**, which `IsingGibbsMagnetisation` identifies as the
  product of the two Gibbs expectations in the long limit. So this is clustering
  to `⟨A⟩⟨B⟩`, and when either observable is ODD that product is zero
  (`IsingOddObservable.obsEigenG_top_eq_zero`) and clustering becomes decay.

  A NOTE ON A HYPOTHESIS THAT IS NOT THERE. The one-observable estimate carries
  `0 ≤ r`; this one does not, and the first draft did until Lean's unused-variable
  linter said so. The difference is that the one-observable proof ends by
  enlarging a sum over `univ.erase p₀` to one over `univ`, which needs `r ^ κ ≥ 0`;
  here the sum stays where it is, because the constant is the sum itself. **The
  hypothesis was copied, not derived** — the second time today the linter has
  caught an assumption made out of habit.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingTwoObservable

namespace IsingTwoObservableLimit

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation
open IsingSlabConfig IsingSlabSpectral IsingSlabDecay IsingOddObservable IsingTwoObservable

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The infinite-length two-observable correlation -/

/-- **THE SPECTRAL SUM FOR TWO OBSERVABLES.** `IsingSlabDecay.corr2SepInfG` is this at `A = B`,
where `A_{p₀q}·B_{qp₀}` becomes `‖B_{p₀q}‖²`. -/
noncomputable def corr2SepInfG2 (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ) (p₀ : Cross V)
    (κ : ℕ) : ℝ :=
  ∑ q, obsEigenG β E w p₀ q * obsEigenG β E u q p₀
    * ((transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀) ^ κ

/-- **LEG 1 — THE LENGTH LIMIT.** `p₀` is a hypothesis rather than produced, so one `p₀` serves
every `κ`. -/
theorem corr2SepG2_tendsto_of_max [Nonempty V] (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ)
    {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) (κ : ℕ) :
    Tendsto (fun M : ℕ =>
        corr2SepG2 β E (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ w u)
      atTop (𝓝 (corr2SepInfG2 β E w u p₀ κ)) := by
  classical
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hp₀ne : (transferG_isHermitian β E).eigenvalues p₀ ≠ 0 := ne_of_gt hp₀pos
  have hnum := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => ∑ q, obsEigenG β E w p q * obsEigenG β E u q p
      * (transferG_isHermitian β E).eigenvalues q ^ κ)
  have hden := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => (transferG_isHermitian β E).eigenvalues p ^ κ)
  have hdiv := hnum.div hden (pow_ne_zero κ hp₀ne)
  have hlim : (∑ q, obsEigenG β E w p₀ q * obsEigenG β E u q p₀
        * (transferG_isHermitian β E).eigenvalues q ^ κ)
        / (transferG_isHermitian β E).eigenvalues p₀ ^ κ
      = corr2SepInfG2 β E w u p₀ κ := by
    rw [corr2SepInfG2, Finset.sum_div]
    exact Finset.sum_congr rfl fun q _ => by rw [div_pow, mul_div_assoc]
  rw [← hlim]
  refine Tendsto.congr (fun M => ?_) hdiv
  simp only [Pi.div_apply]
  have hnumM : (∑ p, (∑ q, obsEigenG β E w p q * obsEigenG β E u q p
          * (transferG_isHermitian β E).eigenvalues q ^ κ)
        * ((transferG_isHermitian β E).eigenvalues p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ p, ∑ q, obsEigenG β E w p q
            * (transferG_isHermitian β E).eigenvalues q ^ κ
            * (obsEigenG β E u q p * (transferG_isHermitian β E).eigenvalues p ^ (M + 1)))
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [div_pow, ← mul_div_assoc]
    ring_nf
  have hdenM : (∑ p, (transferG_isHermitian β E).eigenvalues p ^ κ
        * ((transferG_isHermitian β E).eigenvalues p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ p, (transferG_isHermitian β E).eigenvalues p ^ (M + κ + 1))
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_pow, ← mul_div_assoc, ← pow_add, show κ + (M + 1) = M + κ + 1 from by omega]
  have hval : ((⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ : Fin (M + κ + 1)) : ℕ) = κ := rfl
  rw [hnumM, hdenM, div_div_div_cancel_right₀ (pow_ne_zero (M + 1) hp₀ne),
    corr2SepG2_eq_spectral, hval, show M + κ + 1 - κ = M + 1 from by omega]

/-! ## 2. The constant, and the estimate -/

/-- **THE CONSTANT THE TWO-OBSERVABLE ESTIMATE CARRIES.** It is `1` only by accident of the
one-observable case; in general it is this number. -/
noncomputable def crossConst (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ) (p₀ : Cross V) : ℝ :=
  ∑ q ∈ univ.erase p₀, |obsEigenG β E w p₀ q| * |obsEigenG β E u q p₀|

theorem crossConst_nonneg (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ) (p₀ : Cross V) :
    0 ≤ crossConst β E w u p₀ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- **THE `q = p₀` TERM CARRIES NO SEPARATION**, and it is the PRODUCT OF THE TWO ONE-POINT
FUNCTIONS. -/
theorem corr2SepInfG2_eq_diag_add (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ) {p₀ : Cross V}
    (hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀) (κ : ℕ) :
    corr2SepInfG2 β E w u p₀ κ
      = obsEigenG β E w p₀ p₀ * obsEigenG β E u p₀ p₀
        + ∑ q ∈ univ.erase p₀, obsEigenG β E w p₀ q * obsEigenG β E u q p₀
            * ((transferG_isHermitian β E).eigenvalues q
                / (transferG_isHermitian β E).eigenvalues p₀) ^ κ := by
  classical
  rw [corr2SepInfG2, ← Finset.add_sum_erase univ _ (mem_univ p₀),
    div_self (ne_of_gt hp₀pos), one_pow, mul_one]

/-- **LEG 2 — THE CLUSTERING ESTIMATE, WITH ITS CONSTANT.** The connected two-observable
correlation is bounded by `crossConst · r ^ κ`. -/
theorem corr2SepInfG2_connected_le (β : ℝ) (E : Cross V → ℝ) (w u : Cross V → ℝ) {p₀ : Cross V}
    (hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀) {r : ℝ}
    (hrle : ∀ q ∈ univ.erase p₀,
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀| ≤ r) (κ : ℕ) :
    |corr2SepInfG2 β E w u p₀ κ - obsEigenG β E w p₀ p₀ * obsEigenG β E u p₀ p₀|
      ≤ crossConst β E w u p₀ * r ^ κ := by
  classical
  rw [corr2SepInfG2_eq_diag_add β E w u hp₀pos κ, add_sub_cancel_left, crossConst,
    Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun q hq => ?_)
  rw [abs_mul, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hrle q hq) κ)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **AND WITH EITHER OBSERVABLE ODD IT IS DECAY**, because the product of the two one-point
functions is then zero. -/
theorem corr2SepInfG2_abs_le_of_odd {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    {w : Cross V → ℝ} (hw : OddObs w) (u : Cross V → ℝ) (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) {r : ℝ}
    (hrle : ∀ q ∈ univ.erase p₀,
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues p₀| ≤ r) (κ : ℕ) :
    |corr2SepInfG2 β E w u p₀ κ| ≤ crossConst β E w u p₀ * r ^ κ := by
  have hzero : obsEigenG β E w p₀ p₀ * obsEigenG β E u p₀ p₀ = 0 := by
    rw [obsEigenG_top_eq_zero hE hw β hp₀, zero_mul]
  have h := corr2SepInfG2_connected_le β E w u
    (PerronGap.eigenvalue_max_pos _ (transferG_pos β E) hp₀) hrle κ
  rwa [hzero, sub_zero] at h

/-! ## 3. The constant specialises correctly

The check that `crossConst` is the RIGHT constant and not merely a constant: at the
one-observable case it is at most `1`, which is exactly the bound
`IsingSlabDecay.corr2SepInfG_connected_le_of_ratio_le` carries. -/

/-- **AT `A = B = spin (· v)` THE CONSTANT IS AT MOST ONE**, by the row sum the one-observable
case used — so the old bound is recovered and not contradicted. -/
theorem crossConst_le_one_of_spin (β : ℝ) (E : Cross V → ℝ) (v : V) (p₀ : Cross V) :
    crossConst β E (fun σ => spin (σ v)) (fun σ => spin (σ v)) p₀ ≤ 1 := by
  classical
  have hrow : ∑ q, ‖spinEigenG β E v p₀ q‖ ^ 2 = 1 := sum_sq_spinEigenG_row β E v p₀
  have hterm : ∀ q ∈ univ.erase p₀,
      |spinEigenG β E v p₀ q| * |spinEigenG β E v q p₀| = ‖spinEigenG β E v p₀ q‖ ^ 2 := by
    intro q _
    rw [spinEigenG_symm β E v q p₀, ← abs_mul, Real.norm_eq_abs, sq_abs, sq]
    exact abs_of_nonneg (mul_self_nonneg _)
  calc crossConst β E (fun σ => spin (σ v)) (fun σ => spin (σ v)) p₀
      = ∑ q ∈ univ.erase p₀, ‖spinEigenG β E v p₀ q‖ ^ 2 :=
        Finset.sum_congr rfl hterm
    _ ≤ ∑ q, ‖spinEigenG β E v p₀ q‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun q _ _ => sq_nonneg _
    _ = 1 := hrow

/-! ## 4. The three-dimensional instance -/

/-- **TWO SPINS AT TWO DIFFERENT SITES OF THE THREE-DIMENSIONAL SLAB**, `κ` layers apart: the
correlation converges as the slab grows long, and the limit decays like `r ^ κ` with a constant,
because a single spin is odd. -/
theorem slab_two_site_decay (β : ℝ) (a b : ℕ) (v v' : Fin (a + 1) × Fin (b + 1))
    {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (slabTransfer_isHermitian β a b).eigenvalues j
      ≤ (slabTransfer_isHermitian β a b).eigenvalues p₀) {r : ℝ}
    (hrle : ∀ q ∈ univ.erase p₀,
      |(slabTransfer_isHermitian β a b).eigenvalues q
        / (slabTransfer_isHermitian β a b).eigenvalues p₀| ≤ r) (κ : ℕ) :
    |corr2SepInfG2 β (slabIntra (a := a) (b := b))
        (fun σ => spin (σ v)) (fun σ => spin (σ v')) p₀ κ|
      ≤ crossConst β (slabIntra (a := a) (b := b))
          (fun σ => spin (σ v)) (fun σ => spin (σ v')) p₀ * r ^ κ :=
  corr2SepInfG2_abs_le_of_odd slabIntra_flipCross (oddObs_spin v) _ β hp₀ hrle κ

end IsingTwoObservableLimit
