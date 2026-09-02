import PerronDominant
import PerronVector

/-!
# The two-dimensional transfer matrix gets a positive eigenvector, and it costs no fixed point

`PerronDominant` dominates the spectrum of a nonnegative matrix by the eigenvalue of a strictly
positive eigenvector, **with no symmetry**, and its own `WHAT THIS IS NOT` says the theorem is not
available at `IsingTransfer2D.transfer2` because the estate has no positive eigenvector for it —
`PerronVector.exists_pos_top_eigenvector` is the only producer of one and it takes
`Matrix.IsHermitian`, which `transfer2` is not. **That sentence is answered here, and the answer is
not Perron–Frobenius.**

**THE OBSERVATION.** `IsingTransferSym.transfer2_eq` gives `transfer2 = D·D·W` and `transferSym` is
`D·W·D`, for the **same** `D = halfIntra` and `W = horiz`. So `transfer2 · D = D · transferSym`
— both sides are `D·D·W·D` — and `D` is `Matrix.diagonal` with entries `exp (β · intra σ / 2)`,
strictly positive. **A positive diagonal conjugation carries a positive eigenvector to a positive
eigenvector**, so the symmetric case the estate already proved hands `transfer2` one for free.

> **§1. The similarity.** `transfer2_mul_halfIntra` — `transfer2 · D = D · transferSym`, one
> associativity step from `transfer2_eq`. `halfIntra_mulVec` and `halfIntra_mulVec_pos` — `D` acts
> entrywise and preserves strict positivity.
>
> **§2. The eigenvector.** `mulVec_transfer2_of_transferSym` transports an eigenvector across the
> similarity **at the same eigenvalue**, and `exists_pos_eigenvector_transfer2` composes it with
> `PerronVector.exists_pos_top_eigenvector_transferSym`. **No fixed-point theorem, no compactness,
> no Brouwer** — the content is that `D` is diagonal and positive.
>
> **§3. What `PerronDominant` then says about `transfer2`.** `abs_le_of_eigenvector_transfer2` —
> every real eigenvalue of `transfer2` is at most `M` in modulus, where `M` is `transferSym`'s top
> eigenvalue. `abs_lt_of_not_signConstant_transfer2` — strictly less for every sign-changing
> eigenvector, `transfer2` being strictly positive (`IsingTransfer2D.transfer2_pos`). **These are
> statements about `transfer2` itself**, which `IsingTransferSym`'s header records as a matrix
> *"nothing in Mathlib's spectral theory applies to"*.

**WHAT THIS IS NOT, as of 2026-09-02, and the first clause is the one that matters.** **No wall
moves and no gap is new.** `IsingTwoPoint` states the position exactly: `PerronGap` and
`PerronSimple` already supply a gap *"for a primitive matrix at a fixed side length"*, and what
stands between the estate and a mass gap is **uniformity in the width**. That is untouched here;
`IsingTopRatio.UniformSubTopRatio` is not attempted in this file and its cost is not claimed
(`ERRATUM 194`, `ERRATUM 246`). What is added is the statement at the object the physics is about
rather than at its symmetrisation — the two are similar, and **nothing in this estate had said so at
the level of eigenvectors** (grepped, `ERRATUM 396`: no declaration under `paper_f/` mentions both
`transfer2` and an eigenvector before this file).

**Nor is this Perron–Frobenius without symmetry.** The positive eigenvector is *transported* from a
Hermitian matrix, not produced; a `transfer2`-shaped matrix that is not similar to a symmetric one
is reached by nothing here, and that remains not attempted. Nothing earlier is restated, deleted or
deprecated, and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace Transfer2Perron

open Matrix IsingTransfer2D IsingTransferSym

variable {n : ℕ} {β : ℝ}

/-! ### §1. The similarity, and that `D` preserves positivity -/

/-- **`transfer2 · D = D · transferSym`.** Both sides are `D·D·W·D`; the only step is associativity
on `IsingTransferSym.transfer2_eq`. -/
theorem transfer2_mul_halfIntra (β : ℝ) (n : ℕ) :
    transfer2 β n * halfIntra β n = halfIntra β n * transferSym β n := by
  rw [transfer2_eq, transferSym]
  simp [Matrix.mul_assoc]

/-- `D` is diagonal, so it acts entrywise. -/
theorem halfIntra_mulVec (β : ℝ) (n : ℕ) (u : Col n → ℝ) (σ : Col n) :
    (halfIntra β n *ᵥ u) σ = Real.exp (β * intra σ / 2) * u σ := by
  rw [halfIntra, Matrix.mulVec_diagonal]

/-- And its entries are strictly positive, so it carries a positive vector to a positive one. -/
theorem halfIntra_mulVec_pos (β : ℝ) (n : ℕ) {u : Col n → ℝ} (hu : ∀ σ, 0 < u σ) (σ : Col n) :
    0 < (halfIntra β n *ᵥ u) σ := by
  rw [halfIntra_mulVec]
  exact mul_pos (Real.exp_pos _) (hu σ)

/-! ### §2. The positive eigenvector, transported -/

/-- **AN EIGENVECTOR OF `transferSym` BECOMES ONE OF `transfer2`, AT THE SAME EIGENVALUE.** -/
theorem mulVec_transfer2_of_transferSym {u : Col n → ℝ} {M : ℝ}
    (hu : transferSym β n *ᵥ u = M • u) :
    transfer2 β n *ᵥ (halfIntra β n *ᵥ u) = M • (halfIntra β n *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, transfer2_mul_halfIntra, ← Matrix.mulVec_mulVec, hu,
    Matrix.mulVec_smul]

/-- **`transfer2` HAS A STRICTLY POSITIVE EIGENVECTOR**, for `transferSym`'s top eigenvalue. The
symmetric case is `PerronVector.exists_pos_top_eigenvector_transferSym`; everything this adds is
that a positive diagonal conjugation preserves positivity. -/
theorem exists_pos_eigenvector_transfer2 (β : ℝ) (n : ℕ) :
    ∃ (M : ℝ) (v : Col n → ℝ), (∀ σ, 0 < v σ) ∧ 0 < M ∧ transfer2 β n *ᵥ v = M • v := by
  obtain ⟨M, u, hupos, -, hMpos, heig⟩ := PerronVector.exists_pos_top_eigenvector_transferSym β n
  have hmv : transferSym β n *ᵥ (WithLp.ofLp u) = M • (WithLp.ofLp u) := by
    have h := congrArg WithLp.ofLp heig
    simpa [RayleighMatrix.mv] using h
  exact ⟨M, halfIntra β n *ᵥ (WithLp.ofLp u), halfIntra_mulVec_pos β n hupos, hMpos,
    mulVec_transfer2_of_transferSym hmv⟩

/-! ### §3. What `PerronDominant` says about `transfer2` -/

/-- **EVERY REAL EIGENVALUE OF `transfer2` IS DOMINATED**, by the eigenvalue of §2's positive
eigenvector. `transfer2` is not Hermitian, so `PerronGap`'s theorem cannot say this. -/
theorem abs_le_of_eigenvector_transfer2 (β : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {lam : ℝ} {w : Col n → ℝ},
      transfer2 β n *ᵥ w = lam • w → w ≠ 0 → |lam| ≤ M := by
  obtain ⟨M, v, hvpos, hMpos, hv⟩ := exists_pos_eigenvector_transfer2 β n
  refine ⟨M, hMpos, fun hw hw0 => ?_⟩
  exact PerronDominant.abs_le_of_pos_eigenvector
    (fun σ τ => (transfer2_pos β σ τ).le) hv hvpos hw hw0

/-- **AND STRICTLY, FOR EVERY SIGN-CHANGING EIGENVECTOR**, since `transfer2` is strictly positive.
This is `PerronDominant.abs_lt_of_not_signConstant` at the estate's own two-dimensional matrix. -/
theorem abs_lt_of_not_signConstant_transfer2 (β : ℝ) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {lam : ℝ} {w : Col n → ℝ},
      transfer2 β n *ᵥ w = lam • w → w ≠ 0 →
      ¬((∀ σ, 0 ≤ w σ) ∨ (∀ σ, w σ ≤ 0)) → |lam| < M := by
  obtain ⟨M, v, hvpos, hMpos, hv⟩ := exists_pos_eigenvector_transfer2 β n
  refine ⟨M, hMpos, fun hw hw0 hsign => ?_⟩
  exact PerronDominant.abs_lt_of_not_signConstant
    (fun σ τ => transfer2_pos β σ τ) hv hvpos hw hw0 hsign

end Transfer2Perron
