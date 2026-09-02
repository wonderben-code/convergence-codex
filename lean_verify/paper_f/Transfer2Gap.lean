import Transfer2Perron
import PerronGap

/-!
# The spectral gap at `transfer2` itself, by running the similarity backwards

`Transfer2Perron` carried a positive eigenvector **forward** across
`transfer2 · D = D · transferSym`, and got from `PerronDominant` that every eigenvalue of
`transfer2` is dominated, strictly for a **sign-changing** eigenvector. `PerronGap.transferSym_gap`
asks for much less — `lam ≠ M` and nothing about signs — but it is stated for `transferSym`.
**Running the same similarity backwards moves it to `transfer2`, and the inverse of `D` needs no
inverse API: it is `halfIntra (-β)`.**

> **§1. The inverse.** `halfIntra_mul_neg` and `halfIntra_neg_mul` — `halfIntra β · halfIntra (-β)`
> is `1`, since `exp (βx/2) · exp (-βx/2) = exp 0`. **The estate's own definition at `-β` is the
> inverse**, so no `Matrix.inv`, no `IsUnit`, no `Invertible` instance.
>
> **§2. The similarity backwards.** `transferSym_mul_halfIntra_neg` — `transferSym · D⁻¹ =
> D⁻¹ · transfer2`, from `Transfer2Perron.transfer2_mul_halfIntra` and §1.
> `mulVec_transferSym_of_transfer2` transports an eigenvector of `transfer2` to one of
> `transferSym` **at the same eigenvalue**, and `halfIntra_mulVec_ne_zero` keeps it nonzero because
> every entry of `D⁻¹` is an exponential.
>
> **§3. The gap.** `transfer2_gap` — the whole `PerronGap.transferSym_gap` package at `transfer2`:
> a strictly positive eigenvector for a strictly positive `M`, and `|lam| < M` for **every**
> eigenvalue other than `M`, with no hypothesis on the eigenvector beyond being nonzero.

**THIS SUBSUMES `Transfer2Perron.abs_lt_of_not_signConstant_transfer2`, WHICH IS KEPT AND NOT
DELETED** (`ERRATUM 176`, `ERRATUM 94`). That theorem asks the eigenvector to change sign; this one
asks only `lam ≠ M`, so it is strictly stronger and the older statement is now its corollary. The
two proofs share no step — that one goes through `PerronEquality`'s triangle-inequality equality
case with no symmetry anywhere, this one through the spectral theorem on `transferSym` — so **the
older route remains the only one available for a positive matrix not similar to a symmetric one**,
which is exactly the generality `PerronDominant` was written for.

**WHAT THIS IS NOT, as of 2026-09-02. NO WALL MOVES AND NO GAP IS NEW.** `PerronGap.transferSym_gap`
has held since it was proved, and `IsingTopRatio` already turns it into exponential decay of the
strip's two-point function; `IsingTwoPoint` records that what stands between this estate and a mass
gap is **uniformity in the width**, and that is untouched here. `IsingTopRatio.UniformSubTopRatio`
is not attempted in this file and its cost is not claimed (`ERRATUM 194`, `ERRATUM 246`). What is
added is the statement at the matrix the physics is about instead of at its symmetrisation.

**And it is not a second proof of the gap.** Every hard step is `PerronGap`'s; this file supplies a
diagonal conjugation and nothing else. Nothing earlier is restated, deleted or deprecated, and no
published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace Transfer2Gap

open Matrix IsingTransfer2D IsingTransferSym RayleighMatrix

variable {n : ℕ} {β : ℝ}

/-! ### §1. `halfIntra (-β)` is the inverse of `halfIntra β` -/

theorem halfIntra_mul_neg (β : ℝ) (n : ℕ) :
    halfIntra β n * halfIntra (-β) n = 1 := by
  rw [halfIntra, halfIntra, Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : Col n => Real.exp (β * intra σ / 2) * Real.exp (-β * intra σ / 2))
      = fun _ : Col n => (1 : ℝ) by
    funext σ; rw [← Real.exp_add]; ring_nf; exact Real.exp_zero]
  exact Matrix.diagonal_one

theorem halfIntra_neg_mul (β : ℝ) (n : ℕ) :
    halfIntra (-β) n * halfIntra β n = 1 := by
  rw [halfIntra, halfIntra, Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : Col n => Real.exp (-β * intra σ / 2) * Real.exp (β * intra σ / 2))
      = fun _ : Col n => (1 : ℝ) by
    funext σ; rw [← Real.exp_add]; ring_nf; exact Real.exp_zero]
  exact Matrix.diagonal_one

/-- `D⁻¹` has no zero entry, so it kills no vector. -/
theorem halfIntra_mulVec_ne_zero (β : ℝ) (n : ℕ) {w : Col n → ℝ} (hw : w ≠ 0) :
    halfIntra β n *ᵥ w ≠ 0 := by
  intro h
  refine hw (funext fun σ => ?_)
  have := congrFun h σ
  rw [Transfer2Perron.halfIntra_mulVec] at this
  have hσ : Real.exp (β * intra σ / 2) ≠ 0 := (Real.exp_pos _).ne'
  simpa [hσ] using this

/-! ### §2. The similarity, backwards -/

/-- **`transferSym · D⁻¹ = D⁻¹ · transfer2`**, which is
`Transfer2Perron.transfer2_mul_halfIntra` conjugated by §1. -/
theorem transferSym_mul_halfIntra_neg (β : ℝ) (n : ℕ) :
    transferSym β n * halfIntra (-β) n = halfIntra (-β) n * transfer2 β n := by
  have h : halfIntra (-β) n * (transfer2 β n * halfIntra β n)
      = halfIntra (-β) n * (halfIntra β n * transferSym β n) := by
    rw [Transfer2Perron.transfer2_mul_halfIntra]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, halfIntra_neg_mul, Matrix.one_mul] at h
  calc transferSym β n * halfIntra (-β) n
      = (halfIntra (-β) n * transfer2 β n * halfIntra β n) * halfIntra (-β) n := by rw [h]
    _ = halfIntra (-β) n * transfer2 β n * (halfIntra β n * halfIntra (-β) n) := by
        rw [Matrix.mul_assoc]
    _ = halfIntra (-β) n * transfer2 β n := by rw [halfIntra_mul_neg, Matrix.mul_one]

/-- **AN EIGENVECTOR OF `transfer2` BECOMES ONE OF `transferSym`, AT THE SAME EIGENVALUE.** -/
theorem mulVec_transferSym_of_transfer2 {w : Col n → ℝ} {lam : ℝ}
    (hw : transfer2 β n *ᵥ w = lam • w) :
    transferSym β n *ᵥ (halfIntra (-β) n *ᵥ w) = lam • (halfIntra (-β) n *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, transferSym_mul_halfIntra_neg, ← Matrix.mulVec_mulVec, hw,
    Matrix.mulVec_smul]

/-! ### §3. The gap at `transfer2` -/

/-- **THE SPECTRAL GAP, AT THE MATRIX THE PHYSICS IS ABOUT.** Every eigenvalue other than `M` is
strictly inside `|lam| < M`, with **no hypothesis on the eigenvector beyond being nonzero** — which
is what `PerronGap.transferSym_gap` gives for the symmetrisation and what
`Transfer2Perron.abs_lt_of_not_signConstant_transfer2` could not, since it asks the eigenvector to
change sign. -/
theorem transfer2_gap (β : ℝ) (n : ℕ) :
    ∃ (M : ℝ) (v : Col n → ℝ), (∀ σ, 0 < v σ) ∧ 0 < M ∧ transfer2 β n *ᵥ v = M • v ∧
      ∀ (lam : ℝ) (w : Col n → ℝ), transfer2 β n *ᵥ w = lam • w → w ≠ 0 → lam ≠ M →
        |lam| < M := by
  obtain ⟨M, u, hupos, hMpos, heig, hgap⟩ := PerronGap.transferSym_gap β n
  have hmv : transferSym β n *ᵥ (WithLp.ofLp u) = M • (WithLp.ofLp u) := by
    have h := congrArg WithLp.ofLp heig
    simpa [RayleighMatrix.mv] using h
  refine ⟨M, halfIntra β n *ᵥ (WithLp.ofLp u),
    Transfer2Perron.halfIntra_mulVec_pos β n hupos, hMpos,
    Transfer2Perron.mulVec_transfer2_of_transferSym hmv, ?_⟩
  intro lam w hw hw0 hlam
  refine hgap lam (WithLp.toLp 2 (halfIntra (-β) n *ᵥ w)) ?_ ?_ hlam
  · have h := mulVec_transferSym_of_transfer2 hw
    simpa [RayleighMatrix.mv] using congrArg (WithLp.toLp 2) h
  · intro hzero
    exact halfIntra_mulVec_ne_zero (-β) n hw0 (by simpa using congrArg WithLp.ofLp hzero)

end Transfer2Gap
