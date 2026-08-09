/-
  HermitePi.lean — stair N1 of the n-dimensional staircase: the multi-index
  Hermite system is orthogonal against the Gaussian product measure.

  WHY. `UNLOCK_WATCHLIST`'s n-dimensional item was given a six-stair
  staircase with the lemmas named. This is N1, the one everything above it
  consumes: `Hpi n m x = ∏ᵢ H_{mᵢ}(xᵢ)`, and the claim that these are
  pairwise orthogonal in `L²(γⁿ)` with `‖Hpi n m‖² = ∏ᵢ (mᵢ)!`.

  WHAT MADE IT SHORT, and it is worth recording because the staircase
  predicted otherwise. The map said to induct on `n`, peeling a coordinate
  through the estate's `measurePreserving_peel` — the pattern
  `EN_eq_integral` uses — and estimated N1 as "a unit". **Mathlib has
  `integral_fintype_prod_eq_prod`**: the integral of a product of
  single-coordinate functions against a product measure is the product of
  the integrals, with NO integrability hypothesis. So there is no
  induction, no peeling, and no Fubini bookkeeping; N1 is three lemmas.
  The estimate was wrong in the safe direction, and it was wrong for the
  usual reason — the route was designed from the estate's habits instead
  of from a search of the library (ERRATA 40/42, again).

  WHAT THIS FILE PROVES:
  * **`Hpi_orthogonal`** — `∫ Hpi n m · Hpi n k dγⁿ = ∏ᵢ (mᵢ)!` when
    `m = k` and `0` otherwise. The multi-index version of the estate's
    `hermite_orthogonal_gauss`.
  * **`Hpi_memLp`** — each `Hpi n m` is in `L²(γⁿ)`, which N3 needs before
    it can speak of an orthonormal family at all.
  * **`Hpi_norm_sq`**, **`Hpi_ne_zero_norm`** — the norms, and that they
    are nonzero, so the normalisation N3 performs is legal.

  WHAT THIS DOES NOT DO. Stair N2 — completeness of the multi-index system
  — is untouched and remains the stair that decides whether the
  n-dimensional item is a build or a project. Nothing here bears on it:
  orthogonality is the easy half of "complete orthogonal system", and the
  1-dimensional file needed a separate and much harder argument for the
  other half.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GaussianProductMeasure
import HermiteHilbertBasis
import Mathlib.MeasureTheory.Integral.Pi

namespace HermitePi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel GaussianProductMeasure

noncomputable section

/-! ## 1. The multi-index Hermite product -/

/-- `Hpi n m x = ∏ᵢ H_{mᵢ}(xᵢ)`. -/
def Hpi (n : ℕ) (m : Fin n → ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, (H (m i)).eval (x i)

theorem Hpi_continuous (n : ℕ) (m : Fin n → ℕ) : Continuous (Hpi n m) := by
  refine continuous_finset_prod _ fun i _ => ?_
  exact (Polynomial.continuous (H (m i))).comp (continuous_apply i)

/-- Each one-dimensional factor is square-integrable — a polynomial against
    a Gaussian. -/
theorem integrable_H_sq (j : ℕ) : Integrable (fun y : ℝ => ((H j).eval y) ^ 2) gauss := by
  have h := MemLp.integrable_mul
    (GaussianPoincare.memLp_polynomial_gaussianReal (H j) 0 1)
    (GaussianPoincare.memLp_polynomial_gaussianReal (H j) 0 1)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.mul_apply]
  ring

/-! ## 2. Membership of `L²(γⁿ)` -/

theorem Hpi_memLp (n : ℕ) (m : Fin n → ℕ) : MemLp (Hpi n m) 2 (gaussPi n) := by
  refine (memLp_two_iff_integrable_sq (Hpi_continuous n m).aestronglyMeasurable).mpr ?_
  have hsq : ∀ x : Fin n → ℝ, Hpi n m x ^ 2 = ∏ i, ((H (m i)).eval (x i)) ^ 2 := by
    intro x
    rw [Hpi, Finset.prod_pow]
  simp_rw [hsq]
  rw [gaussPi]
  exact Integrable.fintype_prod_dep fun i => integrable_H_sq (m i)

/-! ## 3. Orthogonality

No induction and no peeling: Mathlib's `integral_fintype_prod_eq_prod`
turns the whole statement into the one-dimensional one, coordinate by
coordinate.
-/

/-- **THE MULTI-INDEX HERMITE SYSTEM IS ORTHOGONAL IN `L²(γⁿ)`.** -/
theorem Hpi_orthogonal (n : ℕ) (m k : Fin n → ℕ) :
    ∫ x, Hpi n m x * Hpi n k x ∂gaussPi n
      = if m = k then ∏ i, ((m i).factorial : ℝ) else 0 := by
  have hint : ∀ x : Fin n → ℝ, Hpi n m x * Hpi n k x
      = ∏ i, ((H (m i)).eval (x i) * (H (k i)).eval (x i)) := by
    intro x
    rw [Hpi, Hpi, ← Finset.prod_mul_distrib]
  simp_rw [hint]
  rw [gaussPi, integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => (H (m i)).eval y * (H (k i)).eval y)]
  rw [Finset.prod_congr rfl fun i _ => hermite_orthogonal_gauss (m i) (k i)]
  by_cases h : m = k
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The norm², as a product of factorials. -/
theorem Hpi_norm_sq (n : ℕ) (m : Fin n → ℕ) :
    ∫ x, Hpi n m x * Hpi n m x ∂gaussPi n = ∏ i, ((m i).factorial : ℝ) := by
  rw [Hpi_orthogonal, if_pos rfl]

/-- **The norms are nonzero**, so the normalisation stair N3 performs is
    legal. Without this the "orthonormal system" it wants to build could
    contain a zero vector and the whole construction would be empty. -/
theorem Hpi_norm_sq_pos (n : ℕ) (m : Fin n → ℕ) :
    0 < ∫ x, Hpi n m x * Hpi n m x ∂gaussPi n := by
  rw [Hpi_norm_sq]
  refine Finset.prod_pos fun i _ => ?_
  exact_mod_cast (m i).factorial_pos

/-- Distinct multi-indices give genuinely orthogonal vectors — stated
    separately because that is the form N3 consumes. -/
theorem Hpi_inner_eq_zero (n : ℕ) {m k : Fin n → ℕ} (h : m ≠ k) :
    ∫ x, Hpi n m x * Hpi n k x ∂gaussPi n = 0 := by
  rw [Hpi_orthogonal, if_neg h]

/-! ## 4. Review round 43 — the ways this could be hollow

**"`n = 0` could make it vacuous."** It does not make it false, and it is
worth knowing what it says: at `n = 0` there is exactly one multi-index,
`Hpi 0 m` is the empty product `1`, `γ⁰` is a Dirac mass on the unique
point, and the theorem reads `1 = 1`. The statement is degenerate there
and non-degenerate for every `n ≥ 1`; `Hpi_norm_sq_pos` holds in both
cases.

**"It could be the one-dimensional theorem in disguise."** It is derived
from the one-dimensional theorem, which is the point — but it is not the
same statement: the index set is `Fin n → ℕ`, the measure is a product
measure, and the `m ≠ k` case needs only ONE coordinate to differ, which
is where `Finset.prod_eq_zero` does the work.

**"Orthogonality might be all there is."** It is not all that is needed,
and the header says so: N2, completeness, is untouched. A complete
orthogonal system needs both halves and this file supplies the easy one.
-/

/-- At `n = 0` the system is the constant `1` and the statement degenerates
    honestly — recorded so that the degenerate case is a theorem rather
    than something a reader has to work out. -/
theorem Hpi_zero_dim (m : Fin 0 → ℕ) (x : Fin 0 → ℝ) : Hpi 0 m x = 1 := by
  simp [Hpi]

end

end HermitePi
