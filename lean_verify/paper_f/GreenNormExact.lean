import GreenExpansion
import OpNormLowerBound

/-!
# The propagator's operator norm is not bounded by `(m²)⁻¹`. It IS `(m²)⁻¹`.

`OpNormLowerBound` proved `(2Δ + m²)⁻¹ ≤ ‖green G m‖ ≤ (m²)⁻¹` and priced the sandwich in its own
header: *"It is not sharp at either end. The upper bound is `green ≼ (m²)⁻¹ • 1` read as a norm,
tight only when `green` has an eigenvalue at `(m²)⁻¹`, **which needs an isolated vertex**."*

**THAT CLAUSE IS FALSE AND `GreenExpansion` REFUTES IT IN ONE LINE** (`ERRATUM 434`).
`GreenExpansion.green_mulVec_one` — proved 2026-08-12, in a file the operator-norm chain cites —
says `green G m *ᵥ 1 = (m²)⁻¹ • 1` on **every** finite graph, because the graph Laplacian kills
constants (`SimpleGraph.lapMatrix_mulVec_const_eq_zero`, Mathlib, no hypotheses). So `(m²)⁻¹` is an
eigenvalue of `green` at the all-ones vector always: no isolated vertex, no regularity, no
connectivity, no degree bound.

## What this file proves

* **`abs_le_opNorm_of_mulVec_smul`** — if `A *ᵥ v = c • v` with `v ⬝ᵥ v ≠ 0`, then `|c| ≤ ‖A‖`. An
  eigenvalue is below the operator norm, stated in `dotProduct` rather than in `EuclideanSpace`, and
  proved from `RemainderFormBound.dotProduct_mulVec_sq_le` alone. **No symmetry, no positivity, and
  no `Nonempty V`** — the hypothesis `v ⬝ᵥ v ≠ 0` supplies the vector that an empty type cannot.
* **`inv_massSq_le_norm_green`** — `(m²)⁻¹ ≤ ‖green G m‖` at the all-ones vector.
* **`norm_green_eq`** — `‖green G m‖ = (m²)⁻¹`, on every finite nonempty graph at every `m ≠ 0`.

## What that costs the previous unit, stated rather than left to be inferred

`LaplacianOpNorm.norm_green_le` is **exactly attained**, so nothing can improve it. And
`OpNormLowerBound.norm_green_ge`'s `(2Δ + m²)⁻¹` is **strictly worse than the truth at every graph
with an edge**: `(2Δ + m²)⁻¹ < (m²)⁻¹` as soon as `Δ > 0`, so the lower half of `norm_green_bounds`
is superseded and carries a pointer saying so. It is kept (`ERRATUM 94`): it is a *Loewner* bound
read as a norm and its route — `LaplacianDegreeBound.smul_one_le_green` — bounds every eigenvalue
from below, which this file does not.

**THE HYPOTHESIS THAT COMES OFF IS THE DEGREE BOUND**, `PROOF_STRATEGY` §7 rule 3 exactly: the
sandwich needed `∀ p, deg p ≤ Δ` and `0 < 2Δ + m²`, and the equality needs neither.

## What it is not

**It is not about a reflection and no wall moves.** `W1` asks for a lower bound on the cross form's
negative direction; this is the propagator's norm, a different object, and `WALLS.md` §W1.5 names
the difference. **Nothing consumes the equality either**, for the same reason the lower bound had no
consumer: the chain's users want `‖green‖ ≤ (m²)⁻¹` and now have it as sharp rather than as a
bound.

**⚠ THE REASON THAT SENTENCE GIVES IS FALSE AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`,
**`ERRATUM 441`**, 2026-09-03). *"No wall moves"* stands; what `W1` asks for does not.
`ReflectionPositive → hcross` has been a **theorem** since 2026-08-13 —
`ReflectionConverse.reflectionPositive_iff_hcross`, on every finite graph at every mass with no
fixed point — and with a fixed layer the converse is **refuted**
(`MirrorConverseFails.converse_fails_with_mirror`). `W1`'s open part is `OS0`/`OS1`/`OS4`, which is
what `W1`'s own row in `WALLS.md` says.

**AND IT SAYS NOTHING ABOUT `(√green)⁻¹`.** `SqrtGreenOpNorm` bounds `‖(CFC.sqrt (green G m))⁻¹‖`,
which is governed by the SMALLEST eigenvalue of `green`; this is the largest. The two ends of the
spectrum are different questions and only one of them is settled here.

**⚠ THE OTHER END WAS SETTLED THE SAME DAY AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`GreenSpectrumRange.isLeast_eigenvalue_green` gives the smallest eigenvalue of `green G m` as
`‖massive G m‖⁻¹`, at every finite nonempty graph, off an eigenvector transfer under the inverse.
**The sentence stays true of `(√green)⁻¹`**, which is `SqrtGreenOpNorm`'s object and involves a
square root nothing here takes; what has changed is that the propagator's own bottom is no longer
an open end.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenNormExact

open Matrix GraphLaplacian
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. An eigenvalue is below the operator norm -/

/-- **`A *ᵥ v = c • v` WITH `v ≠ 0` GIVES `|c| ≤ ‖A‖`.**
`RemainderFormBound.dotProduct_mulVec_sq_le` reads `‖A v‖² ≤ ‖A‖²‖v‖²`, and at an eigenvector the
left side is `c²‖v‖²`. **No symmetry, no positivity, no `Nonempty V`**: the vector is supplied by
the hypothesis. -/
theorem abs_le_opNorm_of_mulVec_smul {A : Matrix V V ℝ} {c : ℝ} {v : V → ℝ}
    (hv : v ⬝ᵥ v ≠ 0) (h : A *ᵥ v = c • v) : |c| ≤ ‖A‖ := by
  have hnn : 0 ≤ v ⬝ᵥ v := by
    rw [dotProduct]; exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne hnn (Ne.symm hv)
  have hcs := RemainderFormBound.dotProduct_mulVec_sq_le A v
  rw [h] at hcs
  have hsmul : (c • v) ⬝ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ v) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [hsmul] at hcs
  have hsq : c ^ 2 ≤ ‖A‖ ^ 2 := le_of_mul_le_mul_right (by linarith) hpos
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (norm_nonneg A))

/-! ## 2. The propagator, exactly -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`(m²)⁻¹ ≤ ‖green G m‖` ON EVERY FINITE NONEMPTY GRAPH**, with no degree bound and no other
hypothesis on `G`. The witness is the all-ones vector, which `GreenExpansion.green_mulVec_one` makes
an eigenvector at `(m²)⁻¹`. -/
theorem inv_massSq_le_norm_green [Nonempty V] {m : ℝ} (hm : m ≠ 0) :
    (m ^ 2)⁻¹ ≤ ‖green G m‖ := by
  classical
  have hne : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) := by
      rw [dotProduct]
      exact Finset.sum_pos (fun p _ => by norm_num)
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    exact ne_of_gt hpos
  have heig : green G m *ᵥ (fun _ : V => (1 : ℝ)) = (m ^ 2)⁻¹ • (fun _ : V => (1 : ℝ)) := by
    rw [GreenExpansion.green_mulVec_one (G := G) hm]
    ext p; simp
  have habs := abs_le_opNorm_of_mulVec_smul hne heig
  rwa [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg m))] at habs

/-- **THE OPERATOR NORM OF THE PROPAGATOR IS `(m²)⁻¹`**, on every finite nonempty graph at every
`m ≠ 0`. No regularity, no connectivity, no degree bound, and no dependence on the vertex count. -/
theorem norm_green_eq [Nonempty V] {m : ℝ} (hm : m ≠ 0) : ‖green G m‖ = (m ^ 2)⁻¹ :=
  le_antisymm (LaplacianOpNorm.norm_green_le G hm) (inv_massSq_le_norm_green G hm)

/-- **AND SO THE 2026-09-03 SANDWICH IS SHARP ABOVE AND STRICT BELOW.** At any graph with an edge
the degree ceiling is positive and `(2Δ + m²)⁻¹ < ‖green G m‖`, so `norm_green_bounds`' lower half
is never attained there. -/
theorem norm_green_ge_lt_of_pos [Nonempty V] {Δ : ℝ} (hΔ : 0 < Δ) {m : ℝ} (hm : m ≠ 0) :
    (2 * Δ + m ^ 2)⁻¹ < ‖green G m‖ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  rw [norm_green_eq G hm]
  exact inv_strictAnti₀ hm2 (by linarith)

end GreenNormExact
