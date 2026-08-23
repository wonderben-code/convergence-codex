/-
  IsingTwoObservable.lean — the two-point function between two DIFFERENT
  observables, which is what a two-point function is.

  WHY. Every correlation in this estate pairs one observable with ITSELF:
  `corr2SepG` puts `spin (σ v)` at layer `0` and `spin (σ v)` — the same site, the
  same observable — at layer `k`. A two-point function is `⟨A₀ B_k⟩` and the
  physics is in the case `A ≠ B`: two different sites of the cross-section, a spin
  against a magnetisation, an observable against the energy.

  AND THE GENERALITY WAS ALREADY THERE, UNUSED. `TracePathSeq.sum_cyc_two_weight`
  takes **two** weight functions `w` and `v`, and every caller in the estate has
  passed the same function twice. This file passes two, and the whole finite-volume
  half falls out: `separated_sum_eq_trace2`, `corr2SepG2` and
  **`corr2SepG2_eq_trace_div`** — the two-observable correlation as a ratio of
  traces with the two diagonals inserted at the two ends. Likewise
  `trace_two_point_symG` was proved for one diagonal used twice and its proof
  never needed them equal, so `trace_two_point_symG2` is the same three rewrites.

  AND THEN THE SPECTRAL FORM. `HermitianTwoPointTrace.trace_mul_pow_mul_pow` was
  already stated for two matrices `D` and `E` — the estate's `corr2Sep_eq_spectral`
  calls it at `D = E` — so **`corr2SepG2_eq_spectral`** costs one instantiation.
  Its `p = q = p₀` term is `A_{p₀p₀} · B_{p₀p₀}`: **the PRODUCT of the two
  one-point functions**, which is what a two-point function is supposed to cluster
  to and which the `A = B` case could only show as a square.

  WHAT IS NOT HERE. The length limit and the clustering estimate for two
  observables. The limit is `IsingSlabLimit`'s argument at two weight families
  instead of one; the estimate needs a constant, and with `A ≠ B` that constant is
  `∑_{q ≠ p₀} |A_{p₀q}| · |B_{qp₀}|` rather than `1`, because the row sum that
  makes it `1` is `spin_sq` and applies only when the observable squares to the
  identity. Both are written into a watchlist item rather than sketched here.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingOddObservable

namespace IsingTwoObservable

open Finset Matrix Real
open IsingTransfer2D IsingTwoPoint IsingTwoPointSpectral IsingSlabTransfer IsingSlabFlip
open IsingSlabConfig IsingSlabSpectral IsingOddObservable

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The separated sum, with two observables -/

/-- **THE SEPARATED NUMERATOR FOR TWO OBSERVABLES.** `IsingSlabConfig.separated_sum_eq_trace` is
this at `w = u`, and its `k = 0` case needed `spin_sq`; here that case is
`IsingTwoPoint.sum_cyc_weighted` at the pointwise product, which is cleaner and asks nothing of
the observables. -/
theorem separated_sum_eq_trace2 (β : ℝ) (E : Cross V → ℝ) (M k : ℕ) (hk : k ≤ M)
    (w u : Cross V → ℝ) :
    (∑ s : Fin (M + 1) → Cross V, w (s 0) * u (s ⟨k, by omega⟩) * exp (β * energyG E M s))
      = Matrix.trace (Matrix.diagonal w * transfer2G β E ^ k
          * Matrix.diagonal u * transfer2G β E ^ (M + 1 - k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hz : (⟨0, by omega⟩ : Fin (M + 1)) = 0 := rfl
    have hd : Matrix.diagonal w * Matrix.diagonal u
        = Matrix.diagonal fun σ : Cross V => w σ * u σ := Matrix.diagonal_mul_diagonal w u
    rw [pow_zero, Matrix.mul_one, hd, Nat.sub_zero, hz]
    rw [Finset.sum_congr rfl fun s _ => by rw [exp_energyG_eq_prod β E M s]]
    exact sum_cyc_weighted (transfer2G β E) M (fun σ : Cross V => w σ * u σ)
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, M = k' + m + 1 := ⟨M - k' - 1, by omega⟩
    have hsub : k' + m + 1 + 1 - (k' + 1) = m + 1 := by omega
    rw [hsub, Finset.sum_congr rfl fun s _ => by rw [exp_energyG_eq_prod β E (k' + m + 1) s]]
    exact TracePathSeq.sum_cyc_two_weight (transfer2G β E) w u k' m

/-- **THE TWO-OBSERVABLE TWO-POINT FUNCTION** at separation `k` along the length. -/
noncomputable def corr2SepG2 (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1))
    (w u : Cross V → ℝ) : ℝ :=
  (∑ s : Fin (M + 1) → Cross V, w (s 0) * u (s k) * exp (β * energyG E M s)) / partitionG β E M

theorem corr2SepG_eq_corr2SepG2 (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1)) (v : V) :
    corr2SepG β E M k v
      = corr2SepG2 β E M k (fun σ => spin (σ v)) (fun σ => spin (σ v)) := rfl

/-- **AND IT IS A RATIO OF TRACES**, with the two observables at the two ends. -/
theorem corr2SepG2_eq_trace_div (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1))
    (w u : Cross V → ℝ) :
    corr2SepG2 β E M k w u
      = Matrix.trace (Matrix.diagonal w * transfer2G β E ^ (k : ℕ)
            * Matrix.diagonal u * transfer2G β E ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β E ^ (M + 1)) := by
  have hkM : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.isLt
  have hke : (⟨(k : ℕ), by omega⟩ : Fin (M + 1)) = k := Fin.ext rfl
  rw [corr2SepG2, partitionG_eq_trace]
  rw [show (∑ s : Fin (M + 1) → Cross V, w (s 0) * u (s k) * exp (β * energyG E M s))
      = ∑ s : Fin (M + 1) → Cross V,
          w (s 0) * u (s (⟨(k : ℕ), by omega⟩ : Fin (M + 1))) * exp (β * energyG E M s)
    from by rw [hke]]
  rw [separated_sum_eq_trace2 β E M (k : ℕ) hkM w u]

/-! ## 2. Across the symmetrisation, and into the eigenvalues -/

/-- `trace_two_point_symG` for two DIFFERENT diagonals. Its proof never used that they were the
same, which is the finding rather than the theorem. -/
theorem trace_two_point_symG2 (β : ℝ) (E : Cross V → ℝ) (d e : Cross V → ℝ) (k m : ℕ) :
    (Matrix.diagonal d * transferG β E ^ k * Matrix.diagonal e * transferG β E ^ m).trace
      = (Matrix.diagonal d * transfer2G β E ^ k * Matrix.diagonal e
          * transfer2G β E ^ m).trace := by
  rw [Matrix.mul_assoc (Matrix.diagonal d * transferG β E ^ k),
    diag_mul_transferG_pow, diag_mul_transferG_pow,
    conj_mul_conj (halfIntraG β E) (halfIntraGInv β E) _ _ (halfIntraG_mul_inv β E),
    trace_conj_halfIntraG, Matrix.mul_assoc (Matrix.diagonal d * transfer2G β E ^ k)]

/-- **THE TWO-OBSERVABLE CORRELATION IN THE EIGENVALUES.** The `p = q = p₀` term is
`A_{p₀p₀} · B_{p₀p₀}` — **the product of the two one-point functions**, which is what a two-point
function clusters to and which the `A = B` case could only display as a square. -/
theorem corr2SepG2_eq_spectral (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1))
    (w u : Cross V → ℝ) :
    corr2SepG2 β E M k w u
      = (∑ p, ∑ q, obsEigenG β E w p q
            * (transferG_isHermitian β E).eigenvalues q ^ (k : ℕ)
            * (obsEigenG β E u q p
              * (transferG_isHermitian β E).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (transferG_isHermitian β E).eigenvalues p ^ (M + 1) := by
  rw [corr2SepG2_eq_trace_div, ← trace_two_point_symG2, ← partitionG_eq_trace,
    partitionG_eq_sum_eigenvalues_pow,
    HermitianTwoPointTrace.trace_mul_pow_mul_pow (transferG_isHermitian β E)
      (Matrix.diagonal w) (Matrix.diagonal u) (k : ℕ) (M + 1 - (k : ℕ))]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rfl

/-! ## 3. Instances

`ERRATUM 201`. The one-observable case is recovered first; the second instance is a genuinely
different correlation, two spins at two DIFFERENT sites of the cross-section. -/

/-- **INSTANCE ONE — the one-observable case recovered**, `IsingSlabConfig.corr2SepG_eq_trace_div`
statement for statement, through `corr2SepG_eq_corr2SepG2` which is `rfl`. -/
theorem corr2SepG_eq_trace_div_of_two (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1))
    (v : V) :
    corr2SepG β E M k v
      = Matrix.trace (Matrix.diagonal (fun σ : Cross V => spin (σ v))
            * transfer2G β E ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Cross V => spin (σ v))
            * transfer2G β E ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β E ^ (M + 1)) := by
  rw [corr2SepG_eq_corr2SepG2]
  exact corr2SepG2_eq_trace_div β E M k _ _

/-- **INSTANCE TWO — two spins at two DIFFERENT sites**, `k` layers apart. This is a correlation
the estate could not write down before: the whole chain paired a site with itself. -/
theorem corr2SepG2_two_sites (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1)) (v v' : V) :
    corr2SepG2 β E M k (fun σ => spin (σ v)) (fun σ => spin (σ v'))
      = Matrix.trace (Matrix.diagonal (fun σ : Cross V => spin (σ v))
            * transfer2G β E ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Cross V => spin (σ v'))
            * transfer2G β E ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β E ^ (M + 1)) :=
  corr2SepG2_eq_trace_div β E M k _ _

/-- **INSTANCE THREE — a spin against the total magnetisation**, at the three-dimensional slab.
Both observables are odd, so both one-point functions vanish in the long limit and the constant
this correlation clusters to is their product. -/
theorem slab_spin_vs_totalMag (β : ℝ) (a b M : ℕ) (k : Fin (M + 1))
    (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG2 β (slabIntra (a := a) (b := b)) M k (fun σ => spin (σ v))
        (fun σ => ∑ v' : Fin (a + 1) × Fin (b + 1), spin (σ v'))
      = (∑ p, ∑ q, obsEigenG β (slabIntra (a := a) (b := b)) (fun σ => spin (σ v)) p q
            * (slabTransfer_isHermitian β a b).eigenvalues q ^ (k : ℕ)
            * (obsEigenG β (slabIntra (a := a) (b := b))
                  (fun σ => ∑ v' : Fin (a + 1) × Fin (b + 1), spin (σ v')) q p
              * (slabTransfer_isHermitian β a b).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (slabTransfer_isHermitian β a b).eigenvalues p ^ (M + 1) :=
  corr2SepG2_eq_spectral _ _ _ _ _ _

end IsingTwoObservable
