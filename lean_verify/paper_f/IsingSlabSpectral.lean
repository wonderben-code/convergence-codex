/-
  IsingSlabSpectral.lean — the symmetrised matrix and the spectral formula at an
  arbitrary cross-section: R3a and R3b of the slab chain.

  WHY. `IsingSlabConfig` gave the slab an honest finite-volume two-point function
  and wrote it as a ratio of traces of `transfer2G` — the UNSYMMETRISED matrix,
  which is what a configuration sum produces and which no spectral theorem
  applies to. `IsingSlabDecay`'s estimate is about `transferG`, the symmetrised
  one. This file joins them, transcribing `IsingTransferSym` §3 and
  `IsingTwoPointSpectral` §2–§6 with `Col n` replaced by `Cross V` and `intra`
  by `E`.

  WHAT IS PROVED

  * `halfIntraGInv` and its two inverse laws — the half-energy diagonal is
    invertible, written down rather than obtained — with `isUnit_halfIntraGInv`
    and `inv_halfIntraGInv`, so Mathlib's `Matrix.trace_conj` applies verbatim;
  * `trace_transferG_pow` — **the trace powers of the two matrices agree**,
    hence `partitionG_eq_trace_sym` and
    **`partitionG_eq_sum_eigenvalues_pow`**: the partition function of the
    three-dimensional slab is a power sum of `transferG`'s own eigenvalues;
  * `transferG_eq_conj` and `transferG_pow_eq_conj` — `transferG` is a diagonal
    conjugate of `transfer2G`;
  * **`trace_two_point_symG`** — for any DIAGONAL insertion the two-point trace
    is the same for both matrices. The diagonal hypothesis is what the proof
    needs and is exactly what the spin observable satisfies;
  * **`corr2SepG_eq_spectral`** — so the finite-volume two-point function at an
    arbitrary cross-section is
    `(∑ₚ ∑_q ‖Bₚq‖² · λ_qᵏ · λₚᴹ⁺¹⁻ᵏ) / (∑ₚ λₚᴹ⁺¹)`, with `λ` the eigenvalues of
    `transferG` and `B = spinEigenG`. At the square cross-section that is the
    three-dimensional statement, `slabCorr2Sep_eq_spectral`.

  WHAT IS STILL MISSING, AND IT IS ONE STEP. The exponents are `k` and
  `M + 1 - k`; `IsingSlabDecay` bounds a sum with a single exponent `κ`, which is
  what survives the limit `M → ∞`. That limit is R3c —
  `IsingTwoPointLimit.corr2Sep_tendsto` at `Cross V`, over
  `TransferPowerSum.tendsto_weighted_ratio_pow`, which is already generic. Until
  it is taken, this file's formula and `IsingSlabDecay`'s estimate are about
  different objects, and nothing here says otherwise.

  AND THE WIDTH LIMIT IS UNTOUCHED, as it has been by every unit of this chain.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabConfig

namespace IsingSlabSpectral

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointSpectral
open IsingSlabTransfer IsingSlabMagnetisation IsingSlabConfig

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The half-energy diagonal is invertible, explicitly -/

/-- The inverse of `halfIntraG`, written down rather than obtained. -/
noncomputable def halfIntraGInv (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  Matrix.diagonal fun σ => exp (-(β * E σ / 2))

theorem halfIntraG_mul_inv (β : ℝ) (E : Cross V → ℝ) :
    halfIntraG β E * halfIntraGInv β E = 1 := by
  rw [halfIntraG, halfIntraGInv, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun σ => ?_).trans Matrix.diagonal_one
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem halfIntraGInv_mul (β : ℝ) (E : Cross V → ℝ) :
    halfIntraGInv β E * halfIntraG β E = 1 := by
  rw [halfIntraG, halfIntraGInv, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun σ => ?_).trans Matrix.diagonal_one
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem isUnit_halfIntraGInv (β : ℝ) (E : Cross V → ℝ) : IsUnit (halfIntraGInv β E) :=
  ⟨⟨halfIntraGInv β E, halfIntraG β E, halfIntraGInv_mul β E, halfIntraG_mul_inv β E⟩, rfl⟩

theorem inv_halfIntraGInv (β : ℝ) (E : Cross V → ℝ) :
    (halfIntraGInv β E)⁻¹ = halfIntraG β E :=
  Matrix.inv_eq_right_inv (halfIntraGInv_mul β E)

/-- **CONJUGATION BY THE DIAGONAL FACTOR DOES NOT MOVE A TRACE.** Mathlib's `Matrix.trace_conj`,
reached through the two bridge lemmas rather than restated. -/
theorem trace_conj_halfIntraG (β : ℝ) (E : Cross V → ℝ) (X : Matrix (Cross V) (Cross V) ℝ) :
    (halfIntraGInv β E * X * halfIntraG β E).trace = X.trace := by
  rw [← inv_halfIntraGInv β E]
  exact Matrix.trace_conj (isUnit_halfIntraGInv β E) X

/-! ## 2. The trace powers agree, so the partition function is unchanged -/

/-- `transfer2G` is the diagonal weight applied on one side only. -/
theorem transfer2G_eq (β : ℝ) (E : Cross V → ℝ) :
    transfer2G β E = (halfIntraG β E * halfIntraG β E) * horizG β := by
  ext σ τ
  simp only [transfer2G, halfIntraG, horizG, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
    ← Real.exp_add]
  ring_nf

/-- **THE TRACE POWERS AGREE.** Both matrices are `D·W·D` and `D²·W` for the same `D` and `W`, and
`trace_pow_mul_comm` moves the leading factor to the back. -/
theorem trace_transferG_pow (β : ℝ) (E : Cross V → ℝ) (k : ℕ) :
    Matrix.trace (transferG β E ^ k) = Matrix.trace (transfer2G β E ^ k) := by
  rw [transfer2G_eq, transferG, Matrix.mul_assoc]
  rw [trace_pow_mul_comm (halfIntraG β E) (horizG β * halfIntraG β E) k,
    trace_pow_mul_comm (halfIntraG β E * halfIntraG β E) (horizG β) k]
  rw [Matrix.mul_assoc]

/-- **THE PARTITION FUNCTION IS THE TRACE OF A POWER OF A SYMMETRIC MATRIX**, at any
cross-section — so the operator carrying it may be handed to spectral theory. -/
theorem partitionG_eq_trace_sym (β : ℝ) (E : Cross V → ℝ) (M : ℕ) :
    partitionG β E M = Matrix.trace (transferG β E ^ (M + 1)) := by
  rw [trace_transferG_pow, partitionG_eq_trace]

/-- **AND THEREFORE A POWER SUM OF `transferG`'S OWN EIGENVALUES.** -/
theorem partitionG_eq_sum_eigenvalues_pow (β : ℝ) (E : Cross V → ℝ) (M : ℕ) :
    partitionG β E M = ∑ p, (transferG_isHermitian β E).eigenvalues p ^ (M + 1) := by
  rw [partitionG_eq_trace_sym]
  exact TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow (transferG_isHermitian β E) (M + 1)

/-! ## 3. A diagonal conjugate, and an insertion that does not see the conjugation -/

theorem transferG_eq_conj (β : ℝ) (E : Cross V → ℝ) :
    transferG β E = halfIntraGInv β E * transfer2G β E * halfIntraG β E := by
  rw [transfer2G_eq, transferG]
  simp only [← Matrix.mul_assoc]
  rw [halfIntraGInv_mul, Matrix.one_mul]

theorem transferG_pow_eq_conj (β : ℝ) (E : Cross V → ℝ) (k : ℕ) :
    transferG β E ^ k = halfIntraGInv β E * transfer2G β E ^ k * halfIntraG β E := by
  rw [transferG_eq_conj]
  exact Units.conj_pow' ⟨halfIntraG β E, halfIntraGInv β E, halfIntraG_mul_inv β E,
    halfIntraGInv_mul β E⟩ (transfer2G β E) k

/-- The insertion slides through the left-hand factor: the only place the diagonality of the
observable is used, and it is used once. -/
theorem diag_mul_transferG_pow (β : ℝ) (E : Cross V → ℝ) (d : Cross V → ℝ) (k : ℕ) :
    Matrix.diagonal d * transferG β E ^ k
      = halfIntraGInv β E * (Matrix.diagonal d * transfer2G β E ^ k) * halfIntraG β E := by
  rw [transferG_pow_eq_conj]
  simp only [← Matrix.mul_assoc]
  rw [halfIntraGInv, (Matrix.commute_diagonal _ _).eq]

/-- **THE TWO-POINT TRACE IS THE SAME FOR BOTH MATRICES**, for any DIAGONAL insertion — which is
what the spin observable is. The diagonality is what the proof consumes, and it is **not**
decoration: §6 exhibits a two-by-two insertion that does not commute with the conjugating factor
and for which the two traces differ. -/
theorem trace_two_point_symG (β : ℝ) (E : Cross V → ℝ) (d : Cross V → ℝ) (k m : ℕ) :
    (Matrix.diagonal d * transferG β E ^ k * Matrix.diagonal d * transferG β E ^ m).trace
      = (Matrix.diagonal d * transfer2G β E ^ k * Matrix.diagonal d
          * transfer2G β E ^ m).trace := by
  rw [Matrix.mul_assoc (Matrix.diagonal d * transferG β E ^ k),
    diag_mul_transferG_pow, diag_mul_transferG_pow,
    conj_mul_conj (halfIntraG β E) (halfIntraGInv β E) _ _ (halfIntraG_mul_inv β E),
    trace_conj_halfIntraG, Matrix.mul_assoc (Matrix.diagonal d * transfer2G β E ^ k)]

/-! ## 4. The two-point function of a finite slab, in the eigenvalues -/

/-- **THE FINITE-VOLUME TWO-POINT FUNCTION AT AN ARBITRARY CROSS-SECTION, IN THE EIGENVALUES.**
Every coefficient `‖spinEigenG p q‖²` is real and non-negative, so no term of the numerator cancels
another; the two exponents land on different eigenvalues, which is why this is a two-point function
and not a partition function.

**It is not yet decay.** The exponents are `k` and `M + 1 - k`, which is the symmetry about the
midpoint that forbids decay in `k` at finite length; a decay statement has to take `M → ∞` first,
and that is R3c and is not here. -/
theorem corr2SepG_eq_spectral (β : ℝ) (E : Cross V → ℝ) (M : ℕ) (k : Fin (M + 1)) (v : V) :
    corr2SepG β E M k v
      = (∑ p, ∑ q, ‖spinEigenG β E v p q‖ ^ 2
            * ((transferG_isHermitian β E).eigenvalues q ^ (k : ℕ)
              * (transferG_isHermitian β E).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (transferG_isHermitian β E).eigenvalues p ^ (M + 1) := by
  rw [spinEigenG, corr2SepG_eq_trace_div, ← trace_two_point_symG, ← partitionG_eq_trace,
    partitionG_eq_sum_eigenvalues_pow,
    HermitianTwoPointTrace.trace_mul_pow_mul_pow_self (transferG_isHermitian β E)
      (Matrix.isHermitian_diagonal _)]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rfl

/-! ## 5. Both instances -/

/-- The strip's half-energy factor IS the general one at `E = intra`, by `rfl`. -/
theorem halfIntra_eq_halfIntraG (β : ℝ) (n : ℕ) :
    halfIntra β n = halfIntraG β (intra (n := n)) := rfl

/-- **INSTANCE ONE — the strip.** `IsingTwoPointSpectral.corr2Sep_eq_spectral` recovered from the
general formula. -/
theorem strip_corr2Sep_eq_spectral (β : ℝ) (n M : ℕ) (k : Fin (M + 1)) (i : Fin (n + 1)) :
    corr2Sep β n M k i
      = (∑ p, ∑ q, ‖spinEigen β n i p q‖ ^ 2
            * ((transferSym_isHermitian β n).eigenvalues q ^ (k : ℕ)
              * (transferSym_isHermitian β n).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (transferSym_isHermitian β n).eigenvalues p ^ (M + 1) :=
  corr2SepG_eq_spectral β (intra (n := n)) M k i

/-- **INSTANCE TWO — the three-dimensional slab's partition function** as a power sum of its own
transfer matrix's eigenvalues. -/
theorem slabPartition_eq_sum_eigenvalues_pow (β : ℝ) (a b M : ℕ) :
    partitionG β (slabIntra (a := a) (b := b)) M
      = ∑ p, (slabTransfer_isHermitian β a b).eigenvalues p ^ (M + 1) :=
  partitionG_eq_sum_eigenvalues_pow _ _ _

/-- **AND ITS TWO-POINT FUNCTION IN THE EIGENVALUES.** This is the shape every transfer-matrix
account of correlation decay is read off, now for a genuine three-dimensional Ising slab of finite
length. **What it is not is a decay statement**: see the header, and R3c. -/
theorem slabCorr2Sep_eq_spectral (β : ℝ) (a b M : ℕ) (k : Fin (M + 1))
    (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG β (slabIntra (a := a) (b := b)) M k v
      = (∑ p, ∑ q, ‖spinEigenG β (slabIntra (a := a) (b := b)) v p q‖ ^ 2
            * ((slabTransfer_isHermitian β a b).eigenvalues q ^ (k : ℕ)
              * (slabTransfer_isHermitian β a b).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (slabTransfer_isHermitian β a b).eigenvalues p ^ (M + 1) :=
  corr2SepG_eq_spectral _ _ _ _ _

/-! ## 6. The diagonality is necessary, with a witness

`IsingTwoPointSpectral.trace_two_point_sym` says of its own diagonal hypothesis that *"for a
general insertion the two traces differ"*, and so did the first draft of §3's docstring here. **The
claim is asserted in the estate three times and was proved nowhere**, which is the shape
`ERRATUM 48` is about: a hypothesis is only known to be needed when something fails without it.

This is the witness. It is stated about the conjugation itself rather than about `transferG`,
because that is what the proof of §3 actually uses — the insertion has to commute with the
conjugating diagonal — and a counterexample there is a counterexample for every `β` and `E` whose
half-energy factor is non-scalar. -/

/-- **A NON-COMMUTING INSERTION BREAKS THE IDENTITY.** With `P · Q = 1` the two-point trace
through `Q · A · P` equals the one through `A` when the insertion commutes with the diagonal
factor; here it does not, and `17/4 ≠ 2`. -/
theorem exists_insertion_not_conj_invariant :
    ∃ A P Q X : Matrix (Fin 2) (Fin 2) ℝ, P * Q = 1 ∧
      (X * (Q * A * P) * X * (Q * A * P)).trace ≠ (X * A * X * A).trace := by
  refine ⟨!![0, 1; 1, 0], !![1, 0; 0, 2], !![1, 0; 0, 1/2], !![0, 1; 1, 0], ?_, ?_⟩
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num
  · norm_num [Matrix.mul_fin_two, Matrix.trace_fin_two]

end IsingSlabSpectral
