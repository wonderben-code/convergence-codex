import BoxLapModeOrthogonal
import BoxMassiveSpectrum
import BoxMassiveBound
import OrthogonalQuadForm

/-!
# The box's operator bound, sharp

`BoxMassiveBound` improved `LaplacianDegreeBound`'s `4d + m²` on the box to
`2d + 2d·cos(π/(n+1)) + m²`, and said plainly that it **is not sharp**: it adds two separately
attained bounds and nothing says one vector attains both. `BoxMassiveSpectrum` then computed the
**exact** largest eigenvalue, `d·(2 + 2cos(π/n)) + m²`, and `STATUS (21)` recorded that this still
moved no constant, because an eigenvalue maximum becomes an operator bound only through an
**orthogonal** eigenbasis. `BoxLapModeOrthogonal` supplied that. This file spends it.

> **`massive_le_smul_one_sharp`** — `massive (boxGraph d n) m ≼ (d·(2 + 2cos(π/n)) + m²)·1`.
>
> **`sharp_lt_bound`** — strictly better than `BoxMassiveBound`'s constant, at every `d ≥ 1` and
> every side length, and hence strictly better than `4d + m²`.
>
> **`not_le_of_lt_sharp`** — **and no smaller constant works.** The value is an eigenvalue
> (`BoxMassiveSpectrum.massive_eigenvalue_top`), so `massive ≼ c·1` forces `c ≥` it. **The constant
> is optimal, which is a statement this estate has not been able to make about any other operator
> bound it carries.**
>
> **`smul_one_le_green_sharp`** — the propagator's lower bound improves by the same amount.

## What this is NOT

**No continuum limit.** `d·(2 + 2cos(π/n)) → 4d` is arithmetic about the answer and is not stated;
as of 31 Aug 2026 it is not costed (`ERRATUM 194`, `ERRATUM 246`).

**Nothing downstream is rewired.** `SqrtGreenBound.inv_sqrt_green_boxGraph_le` still carries
`√(4d + m²)`, `LatticeWitnessBound` its own constants, and re-deriving them from this is **not done
here**.

**No multiplicity**, which is `STATUS (21)`'s item (a) and remains untouched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxMassiveSharp

open Finset Matrix SimpleGraph BoxGraph PathLapSpectrum BoxLapSpectrum BoxLapBasis
open GraphLaplacian
open scoped MatrixOrder

variable {d m : ℕ}

/-- The sharp constant: `d·(2 + 2cos(π/n)) + m²`. -/
noncomputable def sharp (d m : ℕ) (mass : ℝ) : ℝ :=
  (d : ℝ) * (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) + mass ^ 2

/-! ## 1. The quadratic form -/

theorem massive_quadForm_le (d m : ℕ) (mass : ℝ) (x : Site d (m + 1) → ℝ) :
    x ⬝ᵥ massive (boxGraph d (m + 1)) mass *ᵥ x ≤ sharp d m mass * (x ⬝ᵥ x) := by
  refine OrthogonalQuadForm.quadForm_le_of_orthogonal_eigenbasis (boxLapBasis d m)
    (ν := fun k => boxLapEig d (m + 1) (fun i => (k i).val) + mass ^ 2)
    (fun k => by
      rw [boxLapBasis_apply]
      exact BoxMassiveSpectrum.massive_mulVec_siteLapVec d m mass k)
    (fun k l hkl => by
      rw [boxLapBasis_apply, boxLapBasis_apply]
      exact BoxLapModeOrthogonal.siteLapVec_dotProduct_eq_zero hkl)
    (fun k => by
      rw [boxLapBasis_apply]
      exact le_of_lt (BoxLapModeOrthogonal.siteLapVec_dotProduct_self_pos k))
    (fun k => ?_) x
  have hsum : boxLapEig d (m + 1) (fun i => (k i).val)
      ≤ ∑ _i : Fin d, (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) :=
    Finset.sum_le_sum fun i _ =>
      BoxMassiveSpectrum.lapEig_axis_le m (k i).val (Nat.lt_succ_iff.1 (k i).isLt)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [sharp]
  linarith

/-! ## 2. The Loewner bound -/

/-- **`massive (boxGraph d n) m ≼ (d·(2 + 2cos(π/n)) + m²)·1`.** -/
theorem massive_le_smul_one_sharp (d m : ℕ) (mass : ℝ) :
    massive (boxGraph d (m + 1)) mass
      ≤ sharp d m mass • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) := by
  classical
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ (massive_isSymm (boxGraph d (m + 1)) mass)
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have hconst : x ⬝ᵥ (sharp d m mass • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ)) *ᵥ x
        = sharp d m mass * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hconst]
    exact massive_quadForm_le d m mass x

/-! ## 3. It really is sharp -/

/-- **NO SMALLER CONSTANT WORKS.** The sharp value is attained as an eigenvalue, and a Loewner
bound dominates every eigenvalue. -/
theorem not_le_of_lt_sharp (d m : ℕ) (mass : ℝ) {c : ℝ} (hc : c < sharp d m mass) :
    ¬ massive (boxGraph d (m + 1)) mass
        ≤ c • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) := by
  classical
  intro hle
  obtain ⟨v, hv0, hv⟩ := BoxMassiveSpectrum.massive_eigenvalue_top d m mass
  have hps := Matrix.le_iff.mp hle
  have hnn := hps.dotProduct_mulVec_nonneg v
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, hv, dotProduct_smul,
    smul_eq_mul] at hnn
  have hconst : v ⬝ᵥ (c • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ)) *ᵥ v
      = c * (v ⬝ᵥ v) := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hconst] at hnn
  have hpos : 0 < v ⬝ᵥ v := by
    have hnn' : (0 : ℝ) ≤ v ⬝ᵥ v := by
      rw [dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    rcases hnn'.lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hv0
  rw [sharp] at hc
  nlinarith [hnn, hpos, hc]

/-! ## 4. Strictly better than what the estate carried -/

/-- **STRICTLY BELOW `BoxMassiveBound`'s CONSTANT**, hence strictly below `4d + m²` too. -/
theorem sharp_lt_bound (d m : ℕ) (hd : 0 < d) (mass : ℝ) :
    sharp d m mass
      < 2 * (d : ℝ) + BoxMassiveBound.adjRadius d (m + 1) + mass ^ 2 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hlt : Real.pi / ((m : ℝ) + 1 + 1) < Real.pi / ((m : ℝ) + 1) := by
    rw [div_lt_div_iff₀ (by linarith) hm1]
    nlinarith [Real.pi_pos]
  have hnn : (0 : ℝ) ≤ Real.pi / ((m : ℝ) + 1 + 1) := by positivity
  have hle : Real.pi / ((m : ℝ) + 1) ≤ Real.pi := by
    rw [div_le_iff₀ hm1]; nlinarith [Real.pi_pos]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hnn hle hlt
  rw [sharp, BoxMassiveBound.adjRadius]
  push_cast
  nlinarith

/-! ## 5. And the propagator -/

/-- **`(d·(2 + 2cos(π/n)) + m²)⁻¹ · 1 ≼ green (boxGraph d n) m`.** -/
theorem smul_one_le_green_sharp (d m : ℕ) {mass : ℝ} (hm : mass ≠ 0) :
    (sharp d m mass)⁻¹ • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ)
      ≤ green (boxGraph d (m + 1)) mass := by
  have hpos : (0 : ℝ) < sharp d m mass := by
    have hcos : -1 ≤ Real.cos (Real.pi / ((m : ℝ) + 1)) := Real.neg_one_le_cos _
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hm2 : (0 : ℝ) < mass ^ 2 := by positivity
    rw [sharp]
    nlinarith
  have hinv := MatrixLoewner.posDef_inv_le_inv (massive_posDef (boxGraph d (m + 1)) hm)
    (massive_le_smul_one_sharp d m mass)
  have hd : ((sharp d m mass) • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ))⁻¹
      = (sharp d m mass)⁻¹ • (1 : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  rwa [hd] at hinv

end BoxMassiveSharp
