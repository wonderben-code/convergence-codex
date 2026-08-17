import LatticeSteinPoincarePi
import SteinDifferentiablePi

/-!
# The differentiable criterion at every finite index type

`SteinDifferentiablePi` removed `ContDiff ℝ 1` from the n-dimensional criterion, at `Fin n`.
Everything the lattice chain uses is indexed by a **vertex type**, not by `Fin n`, and reaches it
through `LatticeSteinPoincarePi`'s relabelling. This file carries the weakened criterion across that
relabelling, which is the stair — and the only stair — between
`SteinDifferentiablePi.poincare_differentiable` and the field.

## Why the transport is not automatic, and what the one new fact is

`LatticeSteinPoincarePi.steinPairOf_of_contDiff` already transports the `C¹` criterion, and its
proof needs `ContDiff` for one thing only: to hand `ContDiff` to the `Fin n` theorem at the end.
Every other step runs on `Differentiable ℝ Ψ`, which that proof derives on its first line.

The genuine difference is the **hypothesis being transported**. The `C¹` criterion carries `MemLp`
side conditions, and `MemLp` transports along a measure-preserving map by
`memLp_map_measure_iff` — machinery the estate already has. The differentiable criterion carries
a **polynomial growth bound**, and a growth bound transports only if the relabelling **preserves
the norm**. It does, because relabelling permutes coordinates and the norm on `V → ℝ` is a supremum
over them — but that is a fact about `relabel` that nothing in the estate had needed, and
`norm_relabel` is this file's one piece of new content.

*`relabel` is a `ContinuousLinearMap`, so it has an operator norm, and the inequality
`‖relabel f y‖ ≤ ‖relabel f‖·‖y‖` is free. That is **not** what is wanted: an inequality with a
constant would push the growth constant `C` around at every transport and would not compose. The
equality is what makes the criterion transport with `C` and `k` untouched.*

## What is proved

* **`norm_relabel`** — relabelling is norm-preserving, both inequalities by `norm_le_pi_norm`;
* **`steinPairOf_of_differentiable`** — a differentiable `Ψ` of polynomial growth is a `SteinPairOf`
  at **every finite index type**, with its gradient;
* **`poincare_differentiable_pi`** — hence `Var Ψ ≤ ∑_{v : V} ∫ (∂_v Ψ)²` against `gaussPiOf V`,
  with **no continuity of the gradient**;
* **`poincare_wigCoordOf`** — run on `x ↦ wig (x v)`, which is not `ContDiff ℝ 1`, so the statement
  is exercised on something `LatticePoincarePi.poincare_contDiff_pi` cannot reach.

## What this is NOT

**It does not reach the field.** `gaussPiOf V` is the product measure on the vertex type; the
lattice field `gaussianField K m` is its push-forward along `√G`, and
`LatticeCorrelatedPoincare.poincare_correlated_general` is still stated for `C¹`. Weakening **that**
needs polynomial growth pushed through `√G ·`, which is an operator-norm estimate this file does not
attempt and does not claim. What is settled here is the stair below it.

**It does not subsume the `C¹` transport.** `steinPairOf_of_contDiff` takes `MemLp` clauses and no
growth bound; the two are incomparable in the same way their `Fin n` originals are, and for the same
reason.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SteinDifferentiablePiOf

open MeasureTheory ProbabilityTheory GaussianProductMeasure
open HermitePiStein HermitePiPoincare LatticePoincarePi LatticeSteinPoincarePi
open SteinDifferentiablePi

variable {V : Type*} [Fintype V]

/-! ## 1. Relabelling preserves the norm -/

/-- **RELABELLING IS NORM-PRESERVING.** `relabel f` permutes coordinates and the norm on a `Pi` type
is a supremum over them, so no constant appears. This is what lets a polynomial growth bound cross
the relabelling with its `C` and `k` untouched; the operator-norm inequality that comes free with
`relabel` being a `ContinuousLinearMap` would not. -/
theorem norm_relabel (f : Fin (Fintype.card V) ≃ V) (y : Fin (Fintype.card V) → ℝ) :
    ‖relabel f y‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun v => ?_
    rw [relabel_apply]
    exact norm_le_pi_norm y (f.symm v)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have hi : y i = relabel f y (f i) := by rw [relabel_apply, Equiv.symm_apply_apply]
    rw [hi]
    exact norm_le_pi_norm (relabel f y) (f i)

/-! ## 2. The criterion, transported -/

/-- **THE MEMBERSHIP CRITERION AT EVERY FINITE INDEX TYPE, WITHOUT `C¹`.**

Compare `LatticeSteinPoincarePi.steinPairOf_of_contDiff`, which asks for `ContDiff ℝ 1` and two
`MemLp` side conditions. This asks for differentiability and one polynomial bound covering both the
function and its partials — the shape `SteinDifferentiablePi` and the 1-d twin both use. -/
theorem steinPairOf_of_differentiable [DecidableEq V] {Ψ : (V → ℝ) → ℝ}
    (hΨ : Differentiable ℝ Ψ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Ψ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (v : V) (x), |fderiv ℝ Ψ x (Pi.single v (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    SteinPairOf V Ψ (fun v x => fderiv ℝ Ψ x (Pi.single v (1 : ℝ))) := by
  classical
  have hcomp : Differentiable ℝ (fun z : Fin (Fintype.card V) → ℝ => Ψ (relabel (eqv V) z)) :=
    hΨ.comp (relabel (eqv V)).differentiable
  have hchain : ∀ (y : Fin (Fintype.card V) → ℝ) (i : Fin (Fintype.card V)),
      fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y (Pi.single i (1 : ℝ))
        = fderiv ℝ Ψ (relabel (eqv V) y) (Pi.single (eqv V i) (1 : ℝ)) := by
    intro y i
    have h := fderiv_comp (𝕜 := ℝ) y (hΨ (relabel (eqv V) y)) (relabel (eqv V)).differentiableAt
    simp only [Function.comp_def] at h
    rw [h]
    simp [relabel_single]
  have hbc : ∀ y : Fin (Fintype.card V) → ℝ,
      |Ψ (relabel (eqv V) y)| ≤ C * (1 + ‖y‖ ^ 2) ^ k := by
    intro y
    have := hb (relabel (eqv V) y)
    rwa [norm_relabel] at this
  have hbc' : ∀ (i : Fin (Fintype.card V)) (y : Fin (Fintype.card V) → ℝ),
      |fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y (Pi.single i (1 : ℝ))|
        ≤ C * (1 + ‖y‖ ^ 2) ^ k := by
    intro i y
    rw [hchain y i]
    have := hb' (eqv V i) (relabel (eqv V) y)
    rwa [norm_relabel] at this
  have key := steinPairPi_of_differentiable hcomp hbc hbc'
  have hEq : (fun (i : Fin (Fintype.card V)) (y : Fin (Fintype.card V) → ℝ) =>
      fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y (Pi.single i (1 : ℝ)))
      = fun i y => fderiv ℝ Ψ (relabel (eqv V) y) (Pi.single (eqv V i) (1 : ℝ)) := by
    funext i y
    exact hchain y i
  rw [hEq] at key
  exact key

/-- **THE GAUSSIAN POINCARÉ INEQUALITY AT EVERY FINITE INDEX TYPE, FOR A DIFFERENTIABLE FUNCTION.**
`Var Ψ ≤ ∑_{v : V} ∫ (∂_v Ψ)²` against `gaussPiOf V`, with no continuity of the gradient. -/
theorem poincare_differentiable_pi [DecidableEq V] {Ψ : (V → ℝ) → ℝ}
    (hΨ : Differentiable ℝ Ψ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Ψ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (v : V) (x), |fderiv ℝ Ψ x (Pi.single v (1 : ℝ))| ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    (∫ x, Ψ x * Ψ x ∂(gaussPiOf V)) - (∫ x, Ψ x ∂(gaussPiOf V)) ^ 2
      ≤ ∑ v : V, ∫ x, fderiv ℝ Ψ x (Pi.single v (1 : ℝ))
          * fderiv ℝ Ψ x (Pi.single v (1 : ℝ)) ∂(gaussPiOf V) :=
  poincare_steinPi_of (steinPairOf_of_differentiable hΨ hb hb')

/-! ## 3. Exercised on a function the `C¹` transport cannot reach -/

/-- `x ↦ wig (x v)` at a vertex type, the `Fin n` witness relabelled by hand rather than
transported — the definition is one coordinate projection either way. -/
noncomputable def wigCoordOf (v : V) : (V → ℝ) → ℝ := fun x => DifferentiableNotC1.wig (x v)

set_option linter.unusedFintypeInType false in
/-- The derivative of `wigCoordOf`, by the chain rule through the projection.

*`linter.unusedFintypeInType` asks for `[Fintype V]` to be dropped here, and the same on
`differentiable_wigCoordOf`. **Both were tried and both fail to build**:
`NormedAddCommGroup (V → ℝ)` does not synthesise without it, so the instance is load-bearing in
the STATEMENT even though the linter cannot see it. The section-variable linter did NOT fire on
either — the discriminator recorded in `LatticeUniformPoincare.fderiv_coord`, that one linter
alone is not evidence, holding again.* -/
theorem hasFDerivAt_wigCoordOf (v : V) (x : V → ℝ) :
    HasFDerivAt (wigCoordOf v)
      (DifferentiableNotC1.wig' (x v) • (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) x := by
  have hproj : HasFDerivAt (fun y : V → ℝ => y v)
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ).hasFDerivAt
  exact (DifferentiableNotC1.hasDerivAt_wig (x v)).comp_hasFDerivAt x hproj

set_option linter.unusedFintypeInType false in
theorem differentiable_wigCoordOf (v : V) : Differentiable ℝ (wigCoordOf v) :=
  fun x => (hasFDerivAt_wigCoordOf v x).differentiableAt

theorem sq_apply_le_of (x : V → ℝ) (v : V) : (x v) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h : |x v| ≤ ‖x‖ := by
    have := norm_le_pi_norm x v
    rwa [Real.norm_eq_abs] at this
  nlinarith [abs_nonneg (x v), sq_abs (x v), norm_nonneg x]

theorem wigCoordOf_bound (v : V) (x : V → ℝ) : |wigCoordOf v x| ≤ 2 * (1 + ‖x‖ ^ 2) ^ 1 := by
  have h1 := DifferentiableNotC1.wig_bound (x v)
  have h2 := sq_apply_le_of x v
  simp only [pow_one] at h1 ⊢
  simp only [wigCoordOf]
  nlinarith [sq_nonneg (x v), norm_nonneg x]

theorem fderiv_wigCoordOf_bound [DecidableEq V] (v w : V) (x : V → ℝ) :
    |fderiv ℝ (wigCoordOf v) x (Pi.single w (1 : ℝ))| ≤ 2 * (1 + ‖x‖ ^ 2) ^ 1 := by
  have h2 := sq_apply_le_of x v
  have hw := DifferentiableNotC1.wig'_bound (x v)
  simp only [pow_one] at hw ⊢
  rw [(hasFDerivAt_wigCoordOf v x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [abs_mul]
  have hs : |(Pi.single w (1 : ℝ) : V → ℝ) v| ≤ 1 := by
    rw [Pi.single_apply]
    split <;> simp
  nlinarith [abs_nonneg (DifferentiableNotC1.wig' (x v)),
    abs_nonneg ((Pi.single w (1 : ℝ) : V → ℝ) v), sq_nonneg (x v), norm_nonneg x]

/-- **AND IT IS NOT `ContDiff ℝ 1`.** Restricting to the `v`-th axis returns `wig`. -/
theorem not_contDiff_wigCoordOf (v : V) : ¬ ContDiff ℝ 1 (wigCoordOf v) := by
  classical
  intro h
  have hline : ContDiff ℝ 1 (fun t : ℝ => (Pi.single v t : V → ℝ)) :=
    (ContinuousLinearMap.single ℝ (fun _ : V => ℝ) v).contDiff (n := 1)
  have hcomp := h.comp hline
  have heq : (fun t : ℝ => wigCoordOf v (Pi.single v t)) = DifferentiableNotC1.wig := by
    funext t
    simp [wigCoordOf]
  rw [Function.comp_def, heq] at hcomp
  exact DifferentiableNotC1.not_contDiff_wig hcomp

/-- **THE INEQUALITY AT A VERTEX TYPE, ON A FUNCTION THE `C¹` TRANSPORT CANNOT REACH.** -/
theorem poincare_wigCoordOf [DecidableEq V] (v : V) :
    (∫ x, wigCoordOf v x * wigCoordOf v x ∂(gaussPiOf V))
        - (∫ x, wigCoordOf v x ∂(gaussPiOf V)) ^ 2
      ≤ ∑ w : V, ∫ x, fderiv ℝ (wigCoordOf v) x (Pi.single w (1 : ℝ))
          * fderiv ℝ (wigCoordOf v) x (Pi.single w (1 : ℝ)) ∂(gaussPiOf V) :=
  poincare_differentiable_pi (differentiable_wigCoordOf v) (wigCoordOf_bound v)
    (fun w x => fderiv_wigCoordOf_bound v w x)

end SteinDifferentiablePiOf
