/-
  IsingGibbsMagnetisation.lean — the number the decay chain needs to vanish is
  the infinite-length limit of the Gibbs expectation of one spin.

  WHY. `spinEigenG β E v p₀ p₀` has been the pivot of this whole chain: it is the
  constant the two-point function clusters to, and `spinEigenG_top_eq_zero` makes
  it zero, which is what turns clustering into decay. **And until this file it was
  a matrix entry with no physical reading attached** — the `B_{p₀p₀}` of an
  eigenbasis, defended in prose as "the magnetisation" and nowhere shown to be
  one.

  `IsingFieldTraceLimit` wrote it as a limit of trace ratios,
  `(∑_σ spin (σ v)·(Tᵐ)_{σσ}) / λ_{p₀}ᵐ`. The denominator there is a power of an
  eigenvalue, and it can be replaced: `trace (Tᵐ) / λ_{p₀}ᵐ → 1`. What is left is

      (∑_σ spin (σ v)·(Tᵐ)_{σσ}) / (∑_σ (Tᵐ)_{σσ}),

  **a weighted average of spins with no spectral quantity anywhere in it** — and
  that ratio is exactly `IsingSlabConfig.expectG`, the Gibbs expectation of the
  spin at one site over all configurations of a slab of `m` layers.

  SO THE PIVOT IS THE MAGNETISATION AFTER ALL, and now by proof:
  **`expectG_spin_tendsto`** — the finite-volume Gibbs expectation of a single
  spin converges, as the slab grows long, to `spinEigenG β E v p₀ p₀`. The bridge
  is that a ONE-sided insertion crosses the symmetrisation for the same reason a
  two-sided one does (`IsingSlabSpectral.diag_mul_transferG_pow` and
  `trace_conj_halfIntraG`), which was proved and never used this way.

  AND TWO READINGS FALL OUT. At a flip-invariant energy the limit is zero, so the
  Gibbs magnetisation of the long slab vanishes — the physical content of the
  decay chain, stated about the measure rather than about a matrix. In a unit
  field at one site it does not, by `IsingFieldNonzero`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingFieldTraceLimit

namespace IsingGibbsMagnetisation

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation
open IsingSlabConfig IsingSlabSpectral IsingSlabField IsingFieldNonzero IsingFieldTraceLimit

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A one-sided insertion crosses the symmetrisation

`trace_two_point_symG` does this for TWO insertions and is what the spectral formula needed. One
insertion is easier and was never stated. -/

theorem trace_diag_mul_transferG_pow (β : ℝ) (E : Cross V → ℝ) (d : Cross V → ℝ) (k : ℕ) :
    (Matrix.diagonal d * transferG β E ^ k).trace
      = (Matrix.diagonal d * transfer2G β E ^ k).trace := by
  rw [diag_mul_transferG_pow, trace_conj_halfIntraG]

/-- **THE GIBBS EXPECTATION, OVER THE SYMMETRISED MATRIX.** `expectG_eq_trace_div` states it over
`transfer2G`, which is what the configuration sum produces; this is the same number over the
matrix spectral theory applies to. -/
theorem expectG_eq_sym_trace_div (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (w : Cross V → ℝ) :
    expectG β E M w
      = (Matrix.diagonal w * transferG β E ^ (M + 1)).trace
          / (transferG β E ^ (M + 1)).trace := by
  rw [expectG_eq_trace_div, trace_diag_mul_transferG_pow, trace_transferG_pow]

/-! ## 2. The Gibbs expectation of one spin, as an entry ratio -/

/-- **A WEIGHTED AVERAGE OF SPINS, WITH NO SPECTRAL QUANTITY IN IT.** Both sums are over the
diagonal entries of a power of the transfer matrix. -/
theorem expectG_spin_eq_entry_ratio (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (v : V) :
    expectG β E M (fun σ => spin (σ v))
      = (∑ σ : Cross V, spin (σ v) * (transferG β E ^ (M + 1)) σ σ)
          / ∑ σ : Cross V, (transferG β E ^ (M + 1)) σ σ := by
  rw [expectG_eq_sym_trace_div]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-! ## 3. The limit, and what it is -/

/-- **THE GIBBS EXPECTATION OF ONE SPIN CONVERGES TO THE PIVOT.** As the slab grows long, the
finite-volume expectation of the spin at any site converges to `spinEigenG β E v p₀ p₀` — the
number the whole decay chain turns on.

At every finite cross-section, for every energy, **with no flip hypothesis**. So the pivot is the
magnetisation, by proof rather than by the name it was given. -/
theorem expectG_spin_tendsto [Nonempty V] (β : ℝ) (E : Cross V → ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M (fun σ => spin (σ v)))
      atTop (𝓝 (spinEigenG β E v p₀ p₀)) := by
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hnum := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => spinEigenG β E v p p)
  have hden := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun _ => (1 : ℝ))
  have hdiv := hnum.div hden one_ne_zero
  rw [div_one] at hdiv
  refine Tendsto.congr (fun M => ?_) hdiv
  simp only [Pi.div_apply]
  have hnumM : (∑ p, spinEigenG β E v p p
        * ((transferG_isHermitian β E).eigenvalues p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ σ : Cross V, spin (σ v) * (transferG β E ^ (M + 1)) σ σ)
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    rw [← sum_spinEigenG_mul_eigenvalues_pow β E v (M + 1), Finset.sum_div]
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
    expectG_spin_eq_entry_ratio]

/-! ## 4. The two readings -/

/-- **AT A FLIP-INVARIANT ENERGY THE LONG SLAB'S MAGNETISATION IS ZERO.** The physical content of
the decay chain, stated about the Gibbs measure rather than about a matrix entry. -/
theorem expectG_spin_tendsto_zero [Nonempty V] {E : Cross V → ℝ}
    (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β E M (fun σ => spin (σ v))) atTop (𝓝 0) := by
  have h := expectG_spin_tendsto β E v hp₀
  rwa [spinEigenG_top_eq_zero hE β v hp₀] at h

/-- **AND IN A UNIT FIELD AT ONE SITE IT IS NOT.** The limit exists and is a number
`IsingFieldNonzero` proved nonzero, so the long chain in a field is magnetised. -/
theorem field_expectG_spin_tendsto_ne_zero {p₀ : Cross (Fin 1)}
    (hp₀ : ∀ j, (transferG_isHermitian 1 (fieldE (V := Fin 1) 1)).eigenvalues j
      ≤ (transferG_isHermitian 1 (fieldE (V := Fin 1) 1)).eigenvalues p₀) :
    Tendsto (fun M : ℕ =>
        expectG 1 (fieldE (V := Fin 1) 1) M (fun σ => spin (σ 0)))
      atTop (𝓝 (spinEigenG 1 (fieldE (V := Fin 1) 1) 0 p₀ p₀))
    ∧ spinEigenG 1 (fieldE (V := Fin 1) 1) 0 p₀ p₀ ≠ 0 :=
  ⟨expectG_spin_tendsto 1 (fieldE (V := Fin 1) 1) 0 hp₀, field_spinEigen_diag_ne_zero p₀⟩

/-- **AND THE STRIP'S CHECK, WHICH SHARES NO STEP WITH ANY OF THIS.**
`IsingFlipSymmetry.expect_spin_eq_zero` proves the finite-volume expectation of a spin is EXACTLY
zero at every length, by reindexing a configuration sum with no matrix algebra in it. §4's limit
must therefore be zero for the strip, and it is — for a completely different reason. -/
theorem strip_expect_spin_tendsto_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
      ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    Tendsto (fun M : ℕ => expectG β (intra (n := n)) M (fun σ => spin (σ i))) atTop (𝓝 0) :=
  expectG_spin_tendsto_zero intra_flipCross β i hp₀

end IsingGibbsMagnetisation
