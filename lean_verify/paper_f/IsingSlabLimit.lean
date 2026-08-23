/-
  IsingSlabLimit.lean — the length limit at an arbitrary cross-section, and the
  three-dimensional Ising slab's exponential decay.

  WHY. This is R3c, the last leg of the chain `IsingSlabTransfer` opened. The
  state before it: `IsingSlabDecay` bounds `corr2SepInfG`, a spectral sum, by
  `r ^ κ` with `r < 1`; `IsingSlabSpectral` writes the FINITE-length two-point
  function `corr2SepG` in the same eigenvalues, with exponents `k` and
  `M + 1 - k`. `ERRATUM 245` is the entry recording that those were two different
  objects and that saying otherwise would have been an unproved identification.

  WHAT THIS DOES. It identifies them: at fixed separation `κ`, as the length
  grows, `corr2SepG` converges to `corr2SepInfG`. Both sums are
  `∑ₚ cₚ · (λₚ/λ_{p₀})^(M+1)` for weights that do not depend on `M`, so
  `TransferPowerSum.tendsto_weighted_ratio_pow` supplies both limits and the
  denominator's is `λ_{p₀}^κ ≠ 0`.

  AND THEN THE HEADLINE, which the watchlist item has carried since the chain
  opened. `slab_corr2Sep_decay`: for the periodic three-dimensional Ising slab of
  cross-section `(a+1) × (b+1)`, there is `r < 1` such that the two-point
  function at separation `κ` along the length — the honest one, a ratio of
  configuration sums — converges as the slab grows long, and the limit is bounded
  by `r ^ κ`. **Exponential decay, of a genuine correlation, in three
  dimensions.**

  WHAT IS STILL NOT TRUE, AND THE ITEM DOES NOT CLOSE ON IT. `r` is built from
  ONE cross-section's eigenvalues. Nothing here says it stays below one as the
  cross-section grows, which is `IsingTopRatio.UniformSubTopRatio` — proved at no
  `β` but `0`, no route. That is `WALLS` §W4 §6 item 3 and it is exactly where it
  was before this chain started. A three-dimensional slab of FIXED cross-section
  is not a three-dimensional system in the sense that question is about, and this
  file does not pretend otherwise.

  AND THE SHARPEST WAY TO SEE THAT IS THAT THE THEOREM HOLDS AT EVERY `β`.
  `slab_corr2Sep_decay` is quantified over all `β`, large ones included — where
  the three-dimensional Ising model has long-range order and its correlations do
  NOT decay. There is no contradiction and there is no strength being smuggled:
  at fixed finite cross-section and growing length the system is a chain whose
  single site happens to be a `(a+1) × (b+1)` grid, and a finite-range chain does
  not order. **A decay theorem that survives every `β` is, by that very fact, not
  a theorem about the phase transition.** What it would take to be one is
  uniformity as the cross-section grows, which is the sentence above, and `r`
  here depends on `β` and on `(a, b)` with no uniformity claimed in either.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabSpectral

namespace IsingSlabLimit

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointLimit
open IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation IsingSlabDecay
open IsingSlabConfig IsingSlabSpectral

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The length limit -/

/-- **AT FIXED CROSS-SECTION AND FIXED SEPARATION, THE TWO-POINT FUNCTION CONVERGES AS THE SLAB
GROWS LONG.** The separation is written `κ` and the length `M + κ`, so that `κ` is a natural number
held fixed while the `Fin` it lives in grows with `M`.

`p₀` is taken as a hypothesis rather than produced, so that one `p₀` serves every `κ` — which is
what the decay statement in §2 needs and what an existential inside the statement would not give. -/
theorem corr2SepG_tendsto_of_max (β : ℝ) (E : Cross V → ℝ) (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) (κ : ℕ) :
    Tendsto (fun M : ℕ =>
        corr2SepG β E (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ v)
      atTop (𝓝 (corr2SepInfG β E v p₀ κ)) := by
  classical
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hp₀pos : 0 < (transferG_isHermitian β E).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hp₀ne : (transferG_isHermitian β E).eigenvalues p₀ ≠ 0 := ne_of_gt hp₀pos
  have hnum := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => ∑ q, ‖spinEigenG β E v p q‖ ^ 2 * (transferG_isHermitian β E).eigenvalues q ^ κ)
  have hden := TransferPowerSum.tendsto_weighted_ratio_pow (transferG_isHermitian β E) hpos hp₀
    (fun p => (transferG_isHermitian β E).eigenvalues p ^ κ)
  have hdiv := hnum.div hden (pow_ne_zero κ hp₀ne)
  have hlim : (∑ q, ‖spinEigenG β E v p₀ q‖ ^ 2
        * (transferG_isHermitian β E).eigenvalues q ^ κ)
        / (transferG_isHermitian β E).eigenvalues p₀ ^ κ
      = corr2SepInfG β E v p₀ κ := by
    rw [corr2SepInfG, Finset.sum_div]
    exact Finset.sum_congr rfl fun q _ => by rw [div_pow, mul_div_assoc]
  rw [← hlim]
  refine Tendsto.congr (fun M => ?_) hdiv
  simp only [Pi.div_apply]
  have hnumM : (∑ p, (∑ q, ‖spinEigenG β E v p q‖ ^ 2
          * (transferG_isHermitian β E).eigenvalues q ^ κ)
        * ((transferG_isHermitian β E).eigenvalues p
            / (transferG_isHermitian β E).eigenvalues p₀) ^ (M + 1))
      = (∑ p, ∑ q, ‖spinEigenG β E v p q‖ ^ 2
            * ((transferG_isHermitian β E).eigenvalues q ^ κ
              * (transferG_isHermitian β E).eigenvalues p ^ (M + 1)))
        / (transferG_isHermitian β E).eigenvalues p₀ ^ (M + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [div_pow, ← mul_div_assoc, mul_assoc]
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
    corr2SepG_eq_spectral, hval, show M + κ + 1 - κ = M + 1 from by omega]

/-- The same with the argmax produced rather than assumed, which is the shape
`IsingTwoPointLimit.corr2Sep_tendsto` has. -/
theorem corr2SepG_tendsto (β : ℝ) (E : Cross V → ℝ) (v : V) (κ : ℕ) :
    ∃ p₀ : Cross V,
      (∀ j, (transferG_isHermitian β E).eigenvalues j
          ≤ (transferG_isHermitian β E).eigenvalues p₀) ∧
      0 < (transferG_isHermitian β E).eigenvalues p₀ ∧
      Tendsto (fun M : ℕ =>
          corr2SepG β E (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ v)
        atTop (𝓝 (corr2SepInfG β E v p₀ κ)) := by
  obtain ⟨p₀, hp₀⟩ := PerronGap.exists_max_eigenvalue (transferG_isHermitian β E)
  exact ⟨p₀, hp₀, PerronGap.eigenvalue_max_pos _ (transferG_pos β E) hp₀,
    corr2SepG_tendsto_of_max β E v hp₀ κ⟩

/-! ## 2. So the correlations of a long slab decay exponentially

`IsingSlabDecay.corr2SepInfG_abs_le` bounds the limit; §1 says the limit is a limit of genuine
two-point functions. Together they are the statement the chain was opened for. -/

/-- **EXPONENTIAL DECAY OF THE INFINITE-LENGTH TWO-POINT FUNCTION, AT EVERY FINITE
CROSS-SECTION.** One `p₀` and one `r` serve every separation. -/
theorem corr2Sep_limit_decay [Nonempty V] {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) (v : V) :
    ∃ (p₀ : Cross V) (r : ℝ), 0 ≤ r ∧ r < 1 ∧
      (∀ κ : ℕ, Tendsto (fun M : ℕ =>
          corr2SepG β E (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ v)
        atTop (𝓝 (corr2SepInfG β E v p₀ κ)))
      ∧ ∀ κ : ℕ, |corr2SepInfG β E v p₀ κ| ≤ r ^ κ := by
  obtain ⟨p₀, hp₀⟩ := PerronGap.exists_max_eigenvalue (transferG_isHermitian β E)
  obtain ⟨r, hr0, hr1, hrle⟩ := corr2SepInfG_abs_le hE β v hp₀
  exact ⟨p₀, r, hr0, hr1, fun κ => corr2SepG_tendsto_of_max β E v hp₀ κ, hrle⟩

/-! ## 3. Both instances -/

/-- **INSTANCE ONE — the strip**, recovering `IsingTwoPointLimit.corr2Sep_tendsto`. -/
theorem strip_corr2Sep_tendsto (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (κ : ℕ) :
    ∃ p₀ : Col n,
      (∀ j, (transferSym_isHermitian β n).eigenvalues j
          ≤ (transferSym_isHermitian β n).eigenvalues p₀) ∧
      0 < (transferSym_isHermitian β n).eigenvalues p₀ ∧
      Tendsto (fun M : ℕ =>
          corr2Sep β n (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ i)
        atTop (𝓝 (corr2SepInf β n i p₀ κ)) :=
  corr2SepG_tendsto β (intra (n := n)) i κ

/-- **INSTANCE TWO — THE THREE-DIMENSIONAL ISING SLAB, AND THE HEADLINE OF THE CHAIN.**

For the periodic three-dimensional Ising model on `(a+1) × (b+1) × (M+1)` sites there is `r < 1`
such that the two-point function at separation `κ` along the length — **a ratio of configuration
sums, with no eigenvalue in its definition** — converges as the slab grows long, and the limit is
bounded in absolute value by `r ^ κ`.

**What this is not.** `r` comes from ONE cross-section's eigenvalues, and whether it stays below
one as `a` and `b` grow is untouched — `IsingTopRatio.UniformSubTopRatio`, proved at no `β` but
`0`, no route. `WALLS` §W4 §6 item 3 is exactly where it was. **The `∀ β` in front of this
statement is the proof that it is not about the phase transition**: at large `β` the
three-dimensional Ising model orders and its correlations do not decay, and this theorem still
holds, because a slab of fixed cross-section is a chain and a chain does not order. -/
theorem slab_corr2Sep_decay (β : ℝ) (a b : ℕ) (v : Fin (a + 1) × Fin (b + 1)) :
    ∃ (p₀ : Cross (Fin (a + 1) × Fin (b + 1))) (r : ℝ), 0 ≤ r ∧ r < 1 ∧
      (∀ κ : ℕ, Tendsto (fun M : ℕ =>
          corr2SepG β (slabIntra (a := a) (b := b)) (M + κ)
            ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ v)
        atTop (𝓝 (corr2SepInfG β (slabIntra (a := a) (b := b)) v p₀ κ)))
      ∧ ∀ κ : ℕ, |corr2SepInfG β (slabIntra (a := a) (b := b)) v p₀ κ| ≤ r ^ κ :=
  corr2Sep_limit_decay slabIntra_flipCross β v

end IsingSlabLimit
