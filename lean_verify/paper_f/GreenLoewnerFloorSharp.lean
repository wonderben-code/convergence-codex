import GreenQuadFormSharp
import LaplacianNormSharp

/-!
# The propagator's Loewner floor is the massive operator's norm, inverted

Three files this session bounded `‖green G m‖` and `‖massive G m‖` from above and settled when each
bound is attained. **This one is the other end of the propagator's spectrum**, and it closes the
pair `LaplacianDegreeBound` opened: `smul_one_le_green` proves `(2Δ + m²)⁻¹ • 1 ≼ green G m` from a
degree bound and says nothing about whether that constant can be raised.

## The general step, which has no graph in it

> **`smul_one_le_inv_iff_opNorm_le`** — for a positive definite real matrix `A` and `c > 0`,
> `c • 1 ≼ A⁻¹` **iff** `‖A‖ ≤ c⁻¹`.

Both directions are `MatrixLoewner.posDef_inv_le_inv` — the estate's own antitonicity, gap `G2` of
the reflection-positivity ladder — composed with
`OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one`.
**It is the mirror of `LaplacianNormSharp.opNorm_eq_iff_min_smul_one`**: that one says an operator
norm is the least Loewner CEILING; this one says the inverse's greatest Loewner FLOOR is that norm
inverted. Together they turn every statement of one kind into a statement of the other.

## What comes out at the propagator

* **`smul_one_le_green_iff`** — `c • 1 ≼ green K m` **iff** `‖massive K m‖ ≤ c⁻¹`, at every finite
  graph and every `c > 0`. So the greatest admissible `c` is `‖massive K m‖⁻¹`, exactly.
* **`greatest_floor_iff_exists_component_colorable`** — hence on a `Δ`-regular graph,
  `(2Δ + m²)⁻¹ • 1 ≼ green K m` holds always, and **it is the greatest such constant precisely when
  some connected component is two-colourable** — `LaplacianNormSharp`'s characterisation, read
  through the inversion.

**THAT IS AN `IF AND ONLY IF` WHERE `LaplacianDegreeBound` HAD AN INEQUALITY**, and the condition is
combinatorial: no mass, no vectors, no analysis. `PROOF_STRATEGY` §6 question 1 — *what did the last
unit unlock* — with the answer that `LaplacianNormSharp`'s norm equality was the missing half of a
bound proved on 2026-08-30.

## What it is not

**It is not about the other end.** `GreenNormExact.norm_green_eq` settles `‖green‖` — the
propagator's LARGEST eigenvalue — and is exactly `(m²)⁻¹` on every graph. This is the SMALLEST,
and it depends on the graph through `‖massive‖`; the two are different questions and only the first
is graph-free.

**Nothing consumes it**, recorded here rather than left to be discovered: `SqrtGreenBound` and
`SqrtGreenOpNorm` take a floor `c⁻¹ • 1 ≼ green` as a HYPOTHESIS and are indifferent to whether the
`c` handed to them is the best one. **No wall moves**: `W1` asks for a lower bound on the cross form
(`WALLS.md` §W1.5), a different object, and nothing here is about a reflection.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenLoewnerFloorSharp

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A Loewner floor on the inverse is a norm ceiling on the matrix -/

/-- **`c • 1 ≼ A⁻¹` IFF `‖A‖ ≤ c⁻¹`**, for a positive definite real matrix and `c > 0`. The mirror
of `LaplacianNormSharp.opNorm_eq_iff_min_smul_one`: an operator norm is the least Loewner ceiling,
and the inverse's greatest Loewner floor is that norm inverted. -/
theorem smul_one_le_inv_iff_opNorm_le [Nonempty V] {A : Matrix V V ℝ} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) : c • (1 : Matrix V V ℝ) ≤ A⁻¹ ↔ ‖A‖ ≤ c⁻¹ := by
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  have hsmul : ∀ r : ℝ, r ≠ 0 → (r • (1 : Matrix V V ℝ))⁻¹ = r⁻¹ • (1 : Matrix V V ℝ) := by
    intro r hr
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hr, one_smul]
  constructor
  · intro hle
    have hpd : ((c • (1 : Matrix V V ℝ))).PosDef :=
      (Matrix.PosDef.one : (1 : Matrix V V ℝ).PosDef).smul hc
    have hinv := MatrixLoewner.posDef_inv_le_inv hpd hle
    have hdet : IsUnit (A.det) := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
    rw [hsmul c hc.ne', Matrix.nonsing_inv_nonsing_inv _ hdet] at hinv
    exact (OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA.posSemidef.nonneg).mpr hinv
  · intro hnorm
    have hle : A ≤ c⁻¹ • (1 : Matrix V V ℝ) :=
      (OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA.posSemidef.nonneg).mp hnorm
    have hinv := MatrixLoewner.posDef_inv_le_inv hA hle
    rwa [hsmul c⁻¹ hcinv.ne', inv_inv] at hinv

/-! ## 2. At the propagator -/

variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-- **THE GREATEST LOEWNER FLOOR OF THE PROPAGATOR IS `‖massive K m‖⁻¹`.** `green` is `massive`'s
inverse, so §1 reads there directly. -/
theorem smul_one_le_green_iff [Nonempty V] (hm : m ≠ 0) {c : ℝ} (hc : 0 < c) :
    c • (1 : Matrix V V ℝ) ≤ green K m ↔ ‖massive K m‖ ≤ c⁻¹ :=
  smul_one_le_inv_iff_opNorm_le (massive_posDef K hm) hc

/-- **AND SO `LaplacianDegreeBound.smul_one_le_green`'s CONSTANT CANNOT BE RAISED EXACTLY WHEN SOME
CONNECTED COMPONENT IS TWO-COLOURABLE**, on a `Δ`-regular graph. The floor itself holds always; what
the colouring decides is whether it is the best one. -/
theorem greatest_floor_iff_exists_component_colorable [Nonempty V] {Δ : ℕ}
    (hreg : K.IsRegularOfDegree Δ) (hm : m ≠ 0) (hpos : 0 < 2 * (Δ : ℝ) + m ^ 2) :
    (∀ c : ℝ, 0 < c → c • (1 : Matrix V V ℝ) ≤ green K m → c ≤ (2 * (Δ : ℝ) + m ^ 2)⁻¹)
      ↔ ∃ C : K.ConnectedComponent, (K.induce C.supp).Colorable 2 := by
  have hdeg : ∀ p : V, (K.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  have hup : ‖massive K m‖ ≤ 2 * (Δ : ℝ) + m ^ 2 := LaplacianOpNorm.norm_massive_le K hdeg hm
  have hnpos : (0 : ℝ) < ‖massive K m‖ := by
    have hm2 : (0 : ℝ) < m ^ 2 := by positivity
    exact lt_of_lt_of_le hm2
      (OpNormLowerBound.le_opNorm_of_smul_one_le (GreenLargeMass.massSq_le_massive K m))
  rw [← LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable K hreg hm]
  constructor
  · intro hmin
    refine le_antisymm hup ?_
    have hfloor : ‖massive K m‖⁻¹ • (1 : Matrix V V ℝ) ≤ green K m :=
      (smul_one_le_green_iff K hm (inv_pos.mpr hnpos)).mpr (by rw [inv_inv])
    have := hmin _ (inv_pos.mpr hnpos) hfloor
    rwa [inv_le_inv₀ hnpos hpos] at this
  · intro heq c hc hle
    have hmc := (smul_one_le_green_iff K hm hc).mp hle
    rw [heq] at hmc
    have := inv_anti₀ hpos hmc
    rwa [inv_inv] at this

end GreenLoewnerFloorSharp
