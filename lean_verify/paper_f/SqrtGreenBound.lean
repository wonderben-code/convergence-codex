import LaplacianDegreeBound
import LatticeSqrtEquiv
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# The inverse square root of the propagator, bounded uniformly in the box

`LaplacianDegreeBound` proved the half of `LatticeUniformStein`'s fence that a degree bound gives:
`(2Δ + m²)⁻¹ • 1 ≼ green G m`, and on the box `(4d + m²)⁻¹ • 1 ≼ green (boxGraph d n) m` with a
constant naming the dimension and not the side length. **What that fence actually wants is a bound
on `(√G)⁻¹`**, because that is what appears when the uniform variance bound is applied to a
concrete observable, and `LatticeSqrtEquiv` builds the change of variables out of
`CFC.sqrt (green K m)`.

This file takes the Loewner bound through the square root and the inverse, and the whole of it is
three Mathlib facts pointed at one estate theorem.

* **`sqrt_smul_one`** — `CFC.sqrt (c • 1) = √c • 1` for `0 ≤ c`, from `CFC.sqrt_unique`: the scalar
  matrix squares to the right thing and is positive semidefinite.
* **`smul_one_le_sqrt_green`** — hence `√c • 1 ≼ CFC.sqrt (green G m)`, by **`CFC.sqrt_le_sqrt`,
  which is operator monotonicity of the square root**. That is a real theorem — Löwner's — and
  Mathlib has it for C\*-algebras; the matrices carry that structure through
  `Mathlib.Analysis.CStarAlgebra.Matrix`, which `MatrixLoewner` already relies on.
* **`inv_sqrt_green_le`** — and inverting once more through `MatrixLoewner.posDef_inv_le_inv`,
  **`(CFC.sqrt (green G m))⁻¹ ≼ √(2Δ + m²) • 1`**.
* **`inv_sqrt_green_boxGraph_le`** — on the box, `≼ √(4d + m²) • 1` at **every** side length.

## What this closes, and what it does not

**It closes the shape of the fence**: the object `LatticeUniformStein` says nothing analyses is now
bounded, and the bound does not see the volume. `WALLS` and the watch-list item say what that is
worth.

**It is a Loewner bound, not a norm bound**, and the difference is not pedantic. `A ≼ c • 1` for a
positive semidefinite `A` does give `‖A‖ ≤ c` in the operator norm, but that step is about the
norm's characterisation and is **not taken here** — nothing in this file mentions a norm.
`LatticeUniformStein`'s constant is stated in terms of a pointwise `ℓ²` gradient bound, and
threading this inequality into it is a separate join. **Not attempted, no cost claimed**
(`ERRATUM 246`), **no estimate offered** (`ERRATUM 183`), and this chain's own record — four
difficulty estimates out of five wrong — is why.

**`OS4` does not move**, for the reason it has not moved throughout this chain: a constant that does
not blow up is an ingredient of a tightness argument and not one. No sequence of measures, no limit,
no compactness appears here.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SqrtGreenBound

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator MatrixLoewner

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The square root of a nonnegative scalar matrix -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A nonnegative scalar matrix is positive semidefinite. -/
theorem posSemidef_smul_one {c : ℝ} (hc : 0 ≤ c) :
    ((c • (1 : Matrix V V ℝ))).PosSemidef := by
  rw [Matrix.smul_one_eq_diagonal]
  exact Matrix.PosSemidef.diagonal fun _ => hc

omit [DecidableRel G.Adj] in
/-- **`CFC.sqrt (c • 1) = √c • 1`.** `CFC.sqrt_unique`: the candidate squares to `c • 1` and is
nonnegative, and the square root of a nonnegative element is unique. -/
theorem sqrt_smul_one {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • (1 : Matrix V V ℝ)) = Real.sqrt c • (1 : Matrix V V ℝ) := by
  refine CFC.sqrt_unique ?_ ?_
  · rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt hc]
  · simpa using (Matrix.le_iff.mpr (by
      simpa using posSemidef_smul_one (V := V) (Real.sqrt_nonneg c)) :
      (0 : Matrix V V ℝ) ≤ Real.sqrt c • (1 : Matrix V V ℝ))

/-! ## 2. Operator monotonicity of the square root, over ℝ

**Mathlib has `CFC.sqrt_le_sqrt` and it does not apply here.** That lemma lives in a
`NonUnitalCStarAlgebra` section, and a `NonUnitalCStarAlgebra` in Mathlib is a **complex**
C\*-algebra: `Matrix V V ℝ` is not one and cannot be made one. `Matrix V V ℂ` is, under the L2
operator norm, which `MatrixLoewner` already relies on.

So the real case goes the way `MatrixLoewner.posDef_inv_le_inv` goes — **through that file's own
complexification**, and the only new ingredient is that `cx` commutes with the square root. That is
`CFC.sqrt_unique` applied on the complex side: `cx (√A)` squares to `cx A` because `cx` is
multiplicative, and it is nonnegative because `cx` preserves positive semidefiniteness.

**This is a theorem the estate did not have and Mathlib does not state**: operator monotonicity of
the square root for real symmetric matrices. -/

/- `linter.unusedDecidableInType` fires on the next two theorems and **its advice cannot be
followed**, which is why it is silenced here with a reason rather than obeyed. It reports
`DecidableEq V` as *"used in type, but only in a proof"* and suggests dropping it for `classical`.
Tested: `omit [DecidableEq V] in` fails with *"cannot omit referenced section variable"*, because
`CFC.sqrt` on `Matrix V V ℝ` needs the instance to elaborate the STATEMENT, not just the proof. -/
set_option linter.unusedDecidableInType false in
/-- **COMPLEXIFICATION COMMUTES WITH THE SQUARE ROOT.** -/
theorem cx_sqrt {A : Matrix V V ℝ} (hA : 0 ≤ A) :
    MatrixLoewner.cx (CFC.sqrt A) = CFC.sqrt (MatrixLoewner.cx A) := by
  refine (CFC.sqrt_unique ?_ ?_).symm
  · rw [← MatrixLoewner.cx_mul, CFC.sqrt_mul_sqrt_self A hA]
  · refine Matrix.le_iff.mpr ?_
    have hs : (0 : Matrix V V ℝ) ≤ CFC.sqrt A := CFC.sqrt_nonneg A
    simpa using MatrixLoewner.cx_posSemidef (by simpa using Matrix.le_iff.mp hs)

set_option linter.unusedDecidableInType false in
/-- **THE SQUARE ROOT IS OPERATOR MONOTONE ON REAL MATRICES.** Mathlib proves it for complex
C\*-algebras only; this is the real case, by complexification. -/
theorem sqrt_le_sqrt_real {A B : Matrix V V ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ≤ B) :
    CFC.sqrt A ≤ CFC.sqrt B := by
  rw [← MatrixLoewner.cx_le_iff, cx_sqrt hA, cx_sqrt hB]
  exact CFC.sqrt_le_sqrt _ _ (MatrixLoewner.cx_le_iff.mpr h)

/-! ## 3. Through the square root -/

/-- **`√c • 1 ≼ CFC.sqrt (green G m)`**, by operator monotonicity of the square root. -/
theorem smul_one_le_sqrt_green {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ} (hm : m ≠ 0)
    (hpos : 0 < 2 * Δ + m ^ 2) :
    Real.sqrt ((2 * Δ + m ^ 2)⁻¹) • (1 : Matrix V V ℝ) ≤ CFC.sqrt (green G m) := by
  have h := LaplacianDegreeBound.smul_one_le_green G hΔ hm hpos
  have hnn : (0 : Matrix V V ℝ) ≤ (2 * Δ + m ^ 2)⁻¹ • (1 : Matrix V V ℝ) :=
    Matrix.le_iff.mpr (by simpa using posSemidef_smul_one (V := V) (le_of_lt (inv_pos.mpr hpos)))
  have hgn : (0 : Matrix V V ℝ) ≤ green G m :=
    Matrix.le_iff.mpr (by simpa using (green_posDef G hm).posSemidef)
  have hs := sqrt_le_sqrt_real hnn hgn h
  rwa [sqrt_smul_one (V := V) (le_of_lt (inv_pos.mpr hpos))] at hs

/-! ## 4. And back through the inverse -/

/-- **`(CFC.sqrt (green G m))⁻¹ ≼ √(2Δ + m²) • 1`** — the object `LatticeUniformStein`'s fence
names, bounded by a constant built only from a degree bound and the mass. -/
theorem inv_sqrt_green_le {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ} (hm : m ≠ 0)
    (hpos : 0 < 2 * Δ + m ^ 2) :
    (CFC.sqrt (green G m))⁻¹ ≤ Real.sqrt (2 * Δ + m ^ 2) • (1 : Matrix V V ℝ) := by
  have hcpos : 0 < Real.sqrt ((2 * Δ + m ^ 2)⁻¹) := Real.sqrt_pos.mpr (inv_pos.mpr hpos)
  have hPD : (Real.sqrt ((2 * Δ + m ^ 2)⁻¹) • (1 : Matrix V V ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => hcpos
  have hinv := MatrixLoewner.posDef_inv_le_inv hPD (smul_one_le_sqrt_green G hΔ hm hpos)
  have hd : (Real.sqrt ((2 * Δ + m ^ 2)⁻¹) • (1 : Matrix V V ℝ))⁻¹
      = Real.sqrt (2 * Δ + m ^ 2) • (1 : Matrix V V ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      Real.sqrt_inv, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hpos)), one_smul]
  rwa [hd] at hinv

/-! ## 5. The box, where the constant still does not see the side length -/

open BoxGraph BoxDegree in
/-- **THE POINT.** `(CFC.sqrt (green (boxGraph d n) m))⁻¹ ≼ √(4d + m²) • 1` at **every** side
length `n`. -/
theorem inv_sqrt_green_boxGraph_le (d n : ℕ) {m : ℝ} (hm : m ≠ 0) :
    (CFC.sqrt (green (boxGraph d n) m))⁻¹
      ≤ Real.sqrt (4 * (d : ℝ) + m ^ 2) • (1 : Matrix (Site d n) (Site d n) ℝ) := by
  have hΔ : ∀ p : Site d n, ((boxGraph d n).degree p : ℝ) ≤ 2 * (d : ℝ) := by
    intro p
    have h := boxGraph_degree_le (d := d) (n := n) p
    have : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
    simpa using this
  have hpos : 0 < 2 * (2 * (d : ℝ)) + m ^ 2 := by positivity
  have h := inv_sqrt_green_le (boxGraph d n) hΔ hm hpos
  have harith : 2 * (2 * (d : ℝ)) + m ^ 2 = 4 * (d : ℝ) + m ^ 2 := by ring
  rwa [harith] at h

end SqrtGreenBound
