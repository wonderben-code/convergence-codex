/-
  IsingSlabConfig.lean — the configuration layer at an arbitrary cross-section:
  energy, partition function, Gibbs expectation, and the two-point function at
  separation `k`, each a ratio of traces.

  WHY, AND IT IS A CORRECTION. `IsingSlabDecay` closed by saying the remaining
  leg — the identification of the spectral sum with a genuine correlation — was
  "geometry the estate does not have", and `ERRATUM 245` said so in the record.
  **That was wrong, and this file is the retraction.** The geometry is
  `Fin (M + 1) → Cross V`: a configuration of `M + 1` layers, each layer a spin
  assignment on the cross-section. At `V = Fin (a+1) × Fin (b+1)` that IS the
  periodic three-dimensional lattice, and `energyG` at `E = slabIntra` IS the
  three-dimensional Ising energy — the two in-layer directions through
  `slabIntra`, the third through `interG`, every bond of the torus once.

  So nothing had to be invented. `IsingTransfer2D`'s `energy` / `partition2` /
  `partition2_eq_trace` and `IsingTwoPoint`'s `expect` / `corr2Sep` /
  `corr2Sep_eq_trace_div` are transcribed here with `Col n` replaced by
  `Cross V` and `intra` by `E`, and every combinatorial lemma they call —
  `TracePathSum.sum_cyc_eq_trace`, `sum_cyc_weighted`,
  `TracePathSeq.sum_cyc_two_weight` — was already stated over an arbitrary index
  type and needed no change whatsoever.

  WHAT THIS DOES NOT YET DO. `corr2SepG` is the finite-volume correlation. The
  identification `IsingSlabDecay` actually needs is with the LIMIT as `M → ∞`,
  which is `IsingTwoPointLimit.corr2Sep_tendsto`, and that also needs the
  symmetrised matrix (`transferG`) in place of `transfer2G` and the spectral
  formula between them. Those are the next two legs and they are NOT here. What
  is closed is the claim that the geometry was missing: it was not.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabDecay

namespace IsingSlabConfig

open Finset Matrix Real
open IsingTransfer2D IsingTwoPoint IsingSlabTransfer

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The unsymmetrised transfer matrix at an arbitrary cross-section

`IsingSlabTransfer.transferG` is the SYMMETRISED matrix, which is what a spectral argument wants.
The configuration sum produces the other one, with the layer's own energy entirely on the left —
exactly as `IsingTransfer2D.transfer2` does at `Col n`. -/

/-- **THE TRANSFER MATRIX OF THE CONFIGURATION SUM.** -/
noncomputable def transfer2G (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  fun σ τ => exp (β * (E σ + interG σ τ))

omit [DecidableEq V] in
theorem transfer2G_pos (β : ℝ) (E : Cross V → ℝ) (σ τ : Cross V) :
    0 < transfer2G β E σ τ := exp_pos _

/-- At `E = intra` it is `IsingTransfer2D.transfer2`, on the nose. -/
theorem transfer2_eq_transfer2G (β : ℝ) (n : ℕ) :
    transfer2 β n = transfer2G β (intra (n := n)) := rfl

/-! ## 2. The energy of a configuration, and the partition function -/

/-- **THE ENERGY OF A CONFIGURATION OF `M + 1` LAYERS.** Each layer contributes its own internal
energy `E` and its bonds to the next layer, and the layer index wraps.

**At `E = slabIntra` this is the three-dimensional Ising energy** on the periodic
`(a+1) × (b+1) × (M+1)` lattice: `slabIntra` carries the two in-layer directions, `interG` the
third, and every bond appears exactly once — the same accounting `IsingTransfer2D.energy` states
for the two-dimensional torus. -/
def energyG (E : Cross V → ℝ) (M : ℕ) (s : Fin (M + 1) → Cross V) : ℝ :=
  ∑ j : Fin (M + 1), (E (s j) + interG (s j) (s (j + 1)))

theorem energy_eq_energyG (n M : ℕ) (s : Fin (M + 1) → Col n) :
    energy M s = energyG (intra (n := n)) M s := rfl

/-- **THE PARTITION FUNCTION.** -/
noncomputable def partitionG (β : ℝ) (E : Cross V → ℝ) (M : ℕ) : ℝ :=
  ∑ s : Fin (M + 1) → Cross V, exp (β * energyG E M s)

theorem partition2_eq_partitionG (β : ℝ) (n M : ℕ) :
    partition2 β n M = partitionG β (intra (n := n)) M := rfl

theorem partitionG_pos (β : ℝ) (E : Cross V → ℝ) (M : ℕ) : 0 < partitionG β E M := by
  simp only [partitionG]
  exact Finset.sum_pos (fun s _ => exp_pos _)
    ⟨(fun _ _ => true : Fin (M + 1) → Cross V), Finset.mem_univ _⟩

omit [DecidableEq V] in
/-- The factorisation of `exp (β · energy)` over layers, which is the only thing the three trace
identities below need and is stated once. -/
theorem exp_energyG_eq_prod (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (s : Fin (M + 1) → Cross V) :
    exp (β * energyG E M s) = ∏ j : Fin (M + 1), transfer2G β E (s j) (s (j + 1)) := by
  simp only [energyG, transfer2G, Finset.mul_sum]
  exact Real.exp_sum _ _

/-- **THE PARTITION FUNCTION IS THE TRACE OF A POWER.** -/
theorem partitionG_eq_trace (β : ℝ) (E : Cross V → ℝ) (M : ℕ) :
    partitionG β E M = Matrix.trace (transfer2G β E ^ (M + 1)) := by
  simp only [partitionG]
  rw [Finset.sum_congr rfl fun s _ => exp_energyG_eq_prod β E M s]
  exact TracePathSum.sum_cyc_eq_trace (transfer2G β E) M

/-! ## 3. The Gibbs expectation of an observable on one layer -/

/-- **THE GIBBS EXPECTATION** of an observable evaluated on layer `0`. -/
noncomputable def expectG (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (w : Cross V → ℝ) : ℝ :=
  (∑ s : Fin (M + 1) → Cross V, w (s 0) * exp (β * energyG E M s)) / partitionG β E M

theorem expectG_eq_trace_div (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (w : Cross V → ℝ) :
    expectG β E M w
      = Matrix.trace (Matrix.diagonal w * transfer2G β E ^ (M + 1))
          / Matrix.trace (transfer2G β E ^ (M + 1)) := by
  rw [expectG, partitionG_eq_trace,
    Finset.sum_congr rfl fun s _ => by rw [exp_energyG_eq_prod β E M s], sum_cyc_weighted]

theorem expect_eq_expectG (β : ℝ) (n M : ℕ) (w : Col n → ℝ) :
    expect β n M w = expectG β (intra (n := n)) M w := rfl

/-! ## 4. The two-point function along the length direction -/

/-- **THE SEPARATED NUMERATOR IS A TRACE WITH THE OBSERVABLE INSERTED TWICE.** This is
`IsingTwoPoint.separatedTransferFormula_holds` with `Col n` replaced; the `k = 0` case closes by
`spin_sq` and every `k ≥ 1` is `TracePathSeq.sum_cyc_two_weight`, which was already stated over an
arbitrary index type. -/
theorem separated_sum_eq_trace (β : ℝ) (E : Cross V → ℝ) (M k : ℕ) (hk : k ≤ M) (v : V) :
    (∑ s : Fin (M + 1) → Cross V, spin (s 0 v) * spin (s ⟨k, by omega⟩ v)
        * exp (β * energyG E M s))
      = Matrix.trace (Matrix.diagonal (fun σ : Cross V => spin (σ v)) * transfer2G β E ^ k
          * Matrix.diagonal (fun σ : Cross V => spin (σ v)) * transfer2G β E ^ (M + 1 - k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hz : (⟨0, by omega⟩ : Fin (M + 1)) = 0 := rfl
    have hlhs : (∑ s : Fin (M + 1) → Cross V,
        spin (s 0 v) * spin (s (⟨0, by omega⟩ : Fin (M + 1)) v) * exp (β * energyG E M s))
          = partitionG β E M := by
      simp only [partitionG, hz]
      exact Finset.sum_congr rfl fun s _ => by rw [spin_sq, one_mul]
    have hd : Matrix.diagonal (fun σ : Cross V => spin (σ v))
        * Matrix.diagonal (fun σ : Cross V => spin (σ v)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hone : (fun σ : Cross V => spin (σ v) * spin (σ v)) = fun _ => (1 : ℝ) := by
        funext σ; exact spin_sq (σ v)
      rw [hone, Matrix.diagonal_one]
    rw [hlhs, pow_zero, Matrix.mul_one, hd, Matrix.one_mul, Nat.sub_zero, partitionG_eq_trace]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, M = k' + m + 1 := ⟨M - k' - 1, by omega⟩
    have hsub : k' + m + 1 + 1 - (k' + 1) = m + 1 := by omega
    rw [hsub, Finset.sum_congr rfl fun s _ => by rw [exp_energyG_eq_prod β E (k' + m + 1) s]]
    exact TracePathSeq.sum_cyc_two_weight (transfer2G β E)
      (fun σ : Cross V => spin (σ v)) (fun σ : Cross V => spin (σ v)) k' m

/-- **THE TWO-POINT FUNCTION AT SEPARATION `k` ALONG THE LENGTH DIRECTION**, at an arbitrary
cross-section. At `V = Fin (a+1) × Fin (b+1)` and `E = slabIntra` this is a genuine
three-dimensional Ising correlation: two sites of the periodic `(a+1) × (b+1) × (M+1)` lattice,
at the same cross-sectional position, `k` layers apart. -/
noncomputable def corr2SepG (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1)) (v : V) : ℝ :=
  (∑ s : Fin (M + 1) → Cross V, spin (s 0 v) * spin (s k v) * exp (β * energyG E M s))
    / partitionG β E M

/-- **AND IT IS A RATIO OF TRACES.** -/
theorem corr2SepG_eq_trace_div (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1)) (v : V) :
    corr2SepG β E M k v
      = Matrix.trace (Matrix.diagonal (fun σ : Cross V => spin (σ v)) * transfer2G β E ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Cross V => spin (σ v))
            * transfer2G β E ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β E ^ (M + 1)) := by
  have hkM : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.isLt
  have hke : (⟨(k : ℕ), by omega⟩ : Fin (M + 1)) = k := Fin.ext rfl
  rw [corr2SepG, partitionG_eq_trace]
  rw [show (∑ s : Fin (M + 1) → Cross V, spin (s 0 v) * spin (s k v) * exp (β * energyG E M s))
      = ∑ s : Fin (M + 1) → Cross V,
          spin (s 0 v) * spin (s (⟨(k : ℕ), by omega⟩ : Fin (M + 1)) v)
            * exp (β * energyG E M s)
    from by rw [hke]]
  rw [separated_sum_eq_trace β E M (k : ℕ) hkM v]

/-- **THE NORMALISATION CHECK**, from `spin_sq` rather than asserted. -/
theorem corr2SepG_zero (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (v : V) :
    corr2SepG β E M 0 v = 1 := by
  have hnum : (∑ s : Fin (M + 1) → Cross V,
      spin (s 0 v) * spin (s 0 v) * exp (β * energyG E M s)) = partitionG β E M := by
    simp only [partitionG]
    exact Finset.sum_congr rfl fun s _ => by rw [spin_sq, one_mul]
  simp only [corr2SepG]
  rw [hnum]
  exact div_self (ne_of_gt (partitionG_pos β E M))

/-! ## 5. Both instances

The strip's objects ARE these at `E = intra`, by `rfl` in every case — the definitions were
already this general and nobody had noticed. The slab's are the three-dimensional Ising
partition function and two-point function. -/

theorem corr2Sep_eq_corr2SepG (β : ℝ) (n M : ℕ) (k : Fin (M + 1)) (i : Fin (n + 1)) :
    corr2Sep β n M k i = corr2SepG β (intra (n := n)) M k i := rfl

/-- **THE THREE-DIMENSIONAL ISING PARTITION FUNCTION IS A TRACE OF A POWER.** -/
theorem slabPartition_eq_trace (β : ℝ) (a b M : ℕ) :
    partitionG β (slabIntra (a := a) (b := b)) M
      = Matrix.trace (transfer2G β (slabIntra (a := a) (b := b)) ^ (M + 1)) :=
  partitionG_eq_trace _ _ _

/-- **AND THE THREE-DIMENSIONAL TWO-POINT FUNCTION IS A RATIO OF TRACES**, with the spin diagonal
inserted twice — the shape every transfer-matrix account of correlation decay starts from, now in
three dimensions. -/
theorem slabCorr2Sep_eq_trace_div (β : ℝ) (a b M : ℕ) (k : Fin (M + 1))
    (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG β (slabIntra (a := a) (b := b)) M k v
      = Matrix.trace (Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
            * transfer2G β (slabIntra (a := a) (b := b)) ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
            * transfer2G β (slabIntra (a := a) (b := b)) ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β (slabIntra (a := a) (b := b)) ^ (M + 1)) :=
  corr2SepG_eq_trace_div _ _ _ _ _

/-- **AND IT IS CORRECTLY NORMALISED.** -/
theorem slabCorr2Sep_zero (β : ℝ) (a b M : ℕ) (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG β (slabIntra (a := a) (b := b)) M 0 v = 1 :=
  corr2SepG_zero _ _ _ _

end IsingSlabConfig
