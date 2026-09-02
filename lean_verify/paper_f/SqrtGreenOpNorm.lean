import PosSemidefNormBound

/-!
# The inverse square root of the propagator, in the operator norm

`SqrtGreenBound` ends with `inv_sqrt_green_boxGraph_le` — `(√green)⁻¹ ≼ √(4d + m²) • 1` at every
side length — and fences itself in its own words: *"It is a Loewner bound, not a norm bound, and
the difference is not pedantic. `A ≼ c • 1` for a positive semidefinite `A` does give `‖A‖ ≤ c` in
the operator norm, but that step is about the norm's characterisation and is **not taken here** —
nothing in this file mentions a norm."*

`PosSemidefNormBound.l2_opNorm_le` takes that step, so this file spends it.

> **THE WATCHLIST TRIGGER THIS FIRES, QUOTED SO IT CAN BE CHECKED RATHER THAN TAKEN ON TRUST.**
> The `UNLOCK_WATCHLIST` item *"applying the volume-uniform variance bound to
> `LatticeFieldWitness.absCoordField` gives a constant uniform in the box"* has
> `REVISIT WHEN: OPEN — when the square root's spectrum is related to `green`'s. Concretely: when
> something in this estate turns a Loewner bound `c • 1 ≼ A` into a bound on `‖(A.sqrt)⁻¹‖`.`
> **`norm_inv_sqrt_green_le_of_le` is that, verbatim**: from `c⁻¹ • 1 ≼ green G m` it concludes
> `‖(CFC.sqrt (green G m))⁻¹‖ ≤ √c`. The trigger's condition is met.

**AND THE ITEM'S OWN GOAL WAS REACHED ON 29 AUGUST BY A DIFFERENT ROUTE, WHICH IS THE MORE
USEFUL HALF OF THIS NOTE.** `WitnessVarianceUniform.absCoordField_var_le_boxGraph` already gives
the variance of that witness as at most `m⁻²·(2d + m²)` at every side length, and it does so
without any norm: `WitnessVarianceUniform.sqrtGreenInv_col_sq` computes the quantity the
application actually consumes — the squared length of ONE column of `(√G)⁻¹` — **exactly**, as
`deg(v) + m²`. So this file fires a trigger onto an item whose stated objective is already met, and
**it does not close that item**; what it removes is the fence in `SqrtGreenBound`, which is a
different sentence in a different file. Saying otherwise would be `ERRATUM 253`'s error.

**THE COMPARISON IS NOT IN THIS FILE'S FAVOUR AND IS RECORDED ANYWAY.** §3 derives from the
operator-norm bound that every column of `(√G)⁻¹` has squared length at most `4d + m²`. The exact
identity gives `deg(v) + m² ≤ 2d + m²`. **The older route is sharper by a factor of two under the
square root**, on the one quantity the estate's consumer uses. What §2 buys instead is generality:
a bound at every vector rather than at the basis vectors, which is what an operator norm is for.
§3 exists so that the two agree — an independently proved exact value bounding the new estimate is
a check on the new estimate, and it is the only check available that does not reuse its proof.

**WHAT IS NOT PROVED HERE.** No sequence of measures, no limit, no compactness: `OS4` does not
move, for the reason it has not moved anywhere in this chain. The empty case is genuinely excluded
— `l2_opNorm_le` needs `Nonempty V`, and `Site d n` is empty when `d > 0` and `n = 0` — so §2's box
statement carries `1 ≤ n` where `SqrtGreenBound`'s carries no hypothesis on `n` at all. That is a
real restriction and not an artefact of the proof (`ERRATUM 426`). **No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SqrtGreenOpNorm

open Matrix GraphLaplacian SqrtGreenBound
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The inverse square root is positive semidefinite -/

/-- **`(CFC.sqrt (green G m))⁻¹` HAS NO NEGATIVE DIRECTIONS**, which is the hypothesis
`PosSemidefNormBound.l2_opNorm_le` needs and `SqrtGreenBound` never states. It comes out of the
same lower bound: `√(c⁻¹) • 1 ≼ CFC.sqrt (green G m)` with the left side positive definite makes
the right side positive definite, and the inverse of a positive definite matrix is one. -/
theorem nonneg_inv_sqrt_green_of_le {c : ℝ} (hpos : 0 < c) {m : ℝ} (hm : m ≠ 0)
    (hg : c⁻¹ • (1 : Matrix V V ℝ) ≤ green G m) :
    0 ≤ (CFC.sqrt (green G m))⁻¹ := by
  have hcpos : 0 < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hpos)
  have hPD : (Real.sqrt c⁻¹ • (1 : Matrix V V ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => hcpos
  have hle := smul_one_le_sqrt_green_of_le G hpos hm hg
  have heq : Real.sqrt c⁻¹ • (1 : Matrix V V ℝ)
      + (CFC.sqrt (green G m) - Real.sqrt c⁻¹ • (1 : Matrix V V ℝ)) = CFC.sqrt (green G m) := by
    abel
  have hsq : (CFC.sqrt (green G m)).PosDef := by
    have h := hPD.add_posSemidef (Matrix.le_iff.mp hle)
    rwa [heq] at h
  exact hsq.inv.posSemidef.nonneg

/-! ## 2. The Loewner bound spent as a norm bound -/

/-- **THE STEP `SqrtGreenBound` FENCED OFF.** A Loewner lower bound on `green G m` becomes an
operator-norm bound on `(CFC.sqrt (green G m))⁻¹`, with the same constant. -/
theorem norm_inv_sqrt_green_le_of_le [Nonempty V] {c : ℝ} (hpos : 0 < c) {m : ℝ} (hm : m ≠ 0)
    (hg : c⁻¹ • (1 : Matrix V V ℝ) ≤ green G m) :
    ‖(CFC.sqrt (green G m))⁻¹‖ ≤ Real.sqrt c :=
  PosSemidefNormBound.l2_opNorm_le (nonneg_inv_sqrt_green_of_le G hpos hm hg)
    (inv_sqrt_green_le_of_le G hpos hm hg)

/-- The same from a degree bound, mirroring `SqrtGreenBound.inv_sqrt_green_le`. -/
theorem norm_inv_sqrt_green_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ)
    {m : ℝ} (hm : m ≠ 0) (hpos : 0 < 2 * Δ + m ^ 2) :
    ‖(CFC.sqrt (green G m))⁻¹‖ ≤ Real.sqrt (2 * Δ + m ^ 2) :=
  norm_inv_sqrt_green_le_of_le G hpos hm (LaplacianDegreeBound.smul_one_le_green G hΔ hm hpos)

open BoxGraph in
/-- **ON THE BOX, AND THE CONSTANT STILL DOES NOT SEE THE SIDE LENGTH.**
`‖(CFC.sqrt (green (boxGraph d n) m))⁻¹‖ ≤ √(4d + m²)` for every `n ≥ 1`. **The hypothesis `1 ≤ n`
is not decoration**: `Site d n = Fin d → Fin n` is empty when `d > 0` and `n = 0`, and there the
norm bound is unavailable because `l2_opNorm_le` is false without a vertex (`ERRATUM 426`).
`SqrtGreenBound.inv_sqrt_green_boxGraph_le`, being an order statement, needs no such hypothesis. -/
theorem norm_inv_sqrt_green_boxGraph_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    ‖(CFC.sqrt (green (boxGraph d n) m))⁻¹‖ ≤ Real.sqrt (4 * (d : ℝ) + m ^ 2) := by
  haveI : Nonempty (Site d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hpos : 0 < 4 * (d : ℝ) + m ^ 2 := by positivity
  exact norm_inv_sqrt_green_le_of_le (boxGraph d n) hpos hm
    (LaplacianDegreeBound.smul_one_le_green_boxGraph d n hm)

/-! ## 3. The check: the new bound against a value the estate already knows exactly -/

/-- **EVERY COLUMN OF `(CFC.sqrt (green G m))⁻¹` HAS SQUARED LENGTH AT MOST `c`**, read off §2 at a
standard basis vector. **This is a consistency check and not an improvement.**
`WitnessVarianceUniform.sqrtGreenInv_col_sq` computes the same sum EXACTLY, as `deg(v) + m²`, by a
route with no norm in it — so on the box the exact value is `≤ 2d + m²` where this gives
`4d + m²`, and the older result is strictly sharper on the quantity the estate's consumer uses.
What this direction shows is that the two agree, which is the only check on §2 available that does
not reuse §2's proof. -/
theorem col_sq_le_of_le [Nonempty V] {c : ℝ} (hpos : 0 < c) {m : ℝ} (hm : m ≠ 0)
    (hg : c⁻¹ • (1 : Matrix V V ℝ) ≤ green G m) (v : V) :
    ∑ j, ((CFC.sqrt (green G m))⁻¹ j v) ^ 2 ≤ c := by
  set A := (CFC.sqrt (green G m))⁻¹ with hA
  have hb := PosSemidefNormBound.norm_mulVec_le (nonneg_inv_sqrt_green_of_le G hpos hm hg)
    (inv_sqrt_green_le_of_le G hpos hm hg) (EuclideanSpace.single v (1 : ℝ))
  rw [PiLp.norm_single, norm_one, mul_one] at hb
  have hsq := PosSemidefNormBound.norm_sq_eq_dotProduct
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) (EuclideanSpace.single v (1 : ℝ)))
  rw [Matrix.ofLp_toEuclideanCLM, PiLp.ofLp_single, Matrix.mulVec_single_one] at hsq
  have hcol : A.col v ⬝ᵥ A.col v = ∑ j, (A j v) ^ 2 := by
    simp [dotProduct, Matrix.col_apply, pow_two]
  rw [hcol] at hsq
  nlinarith [hb, hsq, norm_nonneg ((Matrix.toEuclideanCLM (𝕜 := ℝ) A)
    (EuclideanSpace.single v (1 : ℝ))), Real.sq_sqrt hpos.le, Real.sqrt_nonneg c]

end SqrtGreenOpNorm
