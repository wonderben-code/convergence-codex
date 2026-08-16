import LatticeSqrtEquiv

/-!
# A non-smooth observable of the lattice field, so the class really is bigger

`LatticeCorrelatedStein` proved the correlated Poincaré inequality on the Stein pair class, and
its header recorded — twice, and again in `LatticeSqrtEquiv` — exactly what it did **not** prove:

> So this file proves the class **contains** `C¹` and does **not** prove it strictly larger.
> Claiming otherwise would be asserting the corollary of a theorem nobody has written.

This is that theorem. The gap is closed by exhibiting the witness rather than by rewording the
caveat.

## The witness, and why it needed the previous unit

Against a *product* measure the witness is `x ↦ |x v|` (`LatticeSteinPoincarePi`). Against the
field it has to be pulled back through the change of variables, which means **inverting** `√G`:

```
absCoordField v ω  =  |((√G)⁻¹ ω) v|
```

composes with `√G` to give exactly `|y v|`. That inverse is
`LatticeSqrtEquiv.isUnit_det_sqrt_green`, which is why this unit could not have come first — and
it is the whole reason that unit's invertibility was worth isolating.

## The gradient tuple, which is forced and not guessed

`SteinPairField` constrains the combination `√G *ᵥ γ(√G ·)`, and it must equal `sgn(y v)·e_v`. So
`γ(√G y) = sgn(y v)·((√G)⁻¹ column v)`, i.e.

```
sgnCoordField v j ω  =  ((√G)⁻¹) j v · sgn (((√G)⁻¹ ω) v)
```

There is no choice here: the tuple is determined by the requirement, and `√G · (√G)⁻¹ = 1` is what
collapses the sum back to `sgn(y v)·δ` — with `isSymm_sqrt_green` used to turn `(√G *ᵥ eᵢ)ⱼ` into
`√G ᵢ ⱼ` so the product is a matrix product rather than a transpose of one.

## What is proved

* `absCoordField_comp` — the witness composed with the change of variables is `|y v|`;
* **`absCoordField_steinPairField`** — it is in the Stein class against `gaussianField K m`;
* **`not_contDiff_absCoordField`** — and it is **not** `ContDiff ℝ 1`;
* **`steinPairField_strictly_wider_than_contDiff`** — the two together, as one statement: there is
  an observable of the field that the class reaches and `C¹` does not.

**So `poincare_correlated_stein_of_class` is not a restatement of
`poincare_correlated_general`** — it holds for observables that theorem cannot express. Every file
in this chain that declined to claim this can now cite it.

## What this is NOT

**It is not a claim that the inequality is sharp, or new, for this observable.** What is proved is
membership and non-smoothness — that the class is strictly larger. Whether the resulting variance
bound is interesting for `|((√G)⁻¹ ω) v|` specifically is not addressed and is not claimed.

**The witness is one function, not a characterisation.** No description of the class's boundary is
offered; a single point outside `C¹` is enough for strictness and is all that is here.

**The strictness is about the FUNCTION, not about its a.e. equivalence class.**
`not_contDiff_absCoordField` says this `Φ` is not `C¹`; it does **not** say that no `C¹` function
agrees with it almost everywhere against the field. That stronger statement is true — two
continuous functions agreeing a.e. against a fully-supported measure agree everywhere, and
`continuous_absCoordField` supplies the continuity — but **the support argument is not formalised
here**, so the stronger claim is not made (`ERRATUM 183`).

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeFieldWitness

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GaussianProductMeasure
open LatticeFieldProduct LatticeGradientForm LatticeCorrelatedPoincare
open LatticeSteinPoincarePi LatticePoincarePi LatticeCorrelatedStein LatticeSqrtEquiv
open AbsSteinWitness AbsSteinWitnessPi
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The witness and its forced gradient tuple -/

/-- `|((√G)⁻¹ ω) v|` — the product-measure witness `|x v|`, pulled back through the change of
variables. -/
noncomputable def absCoordField (K : SimpleGraph W) [DecidableRel K.Adj] (m : ℝ) (v : W)
    (ω : EuclideanSpace ℝ W) : ℝ :=
  |((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v|

/-- The tuple `SteinPairField` forces: `((√G)⁻¹ column v)` scaled by the sign. -/
noncomputable def sgnCoordField (K : SimpleGraph W) [DecidableRel K.Adj] (m : ℝ) (v : W)
    (j : W) (ω : EuclideanSpace ℝ W) : ℝ :=
  (CFC.sqrt (green K m))⁻¹ j v * sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)

/-- Composed with the change of variables, the witness is exactly `|y v|`. -/
theorem absCoordField_comp (hm : m ≠ 0) (v : W) (y : W → ℝ) :
    absCoordField K m v (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)) = absCoordOf W v y := by
  simp only [absCoordField, absCoordOf, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_green (K := K) hm), Matrix.one_mulVec]

/-! ## 2. It is in the class -/

/-- **THE NON-SMOOTH OBSERVABLE IS A STEIN PAIR AGAINST THE FIELD.**

The tuple collapses because `√G · (√G)⁻¹ = 1`: the combination `∑ⱼ γⱼ(√G y)·(√G eᵢ)ⱼ` is
`sgn(y v)·δᵢᵥ`, which is precisely `LatticeSteinPoincarePi.sgnCoordOf`. -/
theorem absCoordField_steinPairField (hm : m ≠ 0) (v : W) :
    SteinPairField K m (absCoordField K m v) (sgnCoordField K m v) := by
  classical
  have hsym : ∀ a b, CFC.sqrt (green K m) a b = CFC.sqrt (green K m) b a := fun a b =>
    congrFun (congrFun (isSymm_sqrt_green (G := K) (m := m)) b) a
  have hf : (fun y => absCoordField K m v (sqrtMapOf (CFC.sqrt (green K m)) y))
      = absCoordOf W v := funext fun y => absCoordField_comp (K := K) hm v y
  have hg : (fun i y => ∑ j, sgnCoordField K m v j (sqrtMapOf (CFC.sqrt (green K m)) y)
        * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j)
      = sgnCoordOf W v := by
    funext i y
    have hcol : ∀ j, (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) j
        = CFC.sqrt (green K m) j i := by
      intro j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hinv : ((CFC.sqrt (green K m))⁻¹ *ᵥ
        (CFC.sqrt (green K m) *ᵥ y)) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_green (K := K) hm),
        Matrix.one_mulVec]
    -- the sign factor is constant in `j`
    have hsgn : ∀ j, sgnCoordField K m v j (sqrtMapOf (CFC.sqrt (green K m)) y)
        = (CFC.sqrt (green K m))⁻¹ j v * sgn (y v) := by
      intro j
      simp only [sgnCoordField, sqrtMapOf_apply, WithLp.ofLp_toLp, hinv]
    simp only [hsgn, hcol]
    -- `∑ j, (√G)⁻¹ j v * sgn (y v) * √G j i = (√G * (√G)⁻¹) i v * sgn (y v)`
    have hentry : (∑ j, (CFC.sqrt (green K m))⁻¹ j v * sgn (y v) * CFC.sqrt (green K m) j i)
        = (CFC.sqrt (green K m) * (CFC.sqrt (green K m))⁻¹) i v * sgn (y v) := by
      rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hsym i j]; ring
    rw [hentry, Matrix.mul_nonsing_inv _ (isUnit_det_sqrt_green (K := K) hm)]
    by_cases hiv : i = v
    · subst hiv; simp [sgnCoordOf]
    · simp [sgnCoordOf, hiv]
  change SteinPairOf W _ _
  rw [hf, hg]
  exact absCoordOf_steinPairOf v

/-! ## 3. It is continuous, and it is not `C¹` -/

/-- **The witness is continuous**, so the failure below is genuinely one of *differentiability* and
not of regularity in general — it is `|·|` composed with a linear map, nothing worse.

*Added in review: a reader is entitled to ask whether "not `C¹`" is hiding something wilder, and
the cheapest honest answer is the theorem rather than the assurance.* -/
theorem continuous_absCoordField (v : W) : Continuous (absCoordField K m v) := by
  unfold absCoordField
  fun_prop

/-! ### And not `C¹` -/

/-- **AND IT IS NOT CONTINUOUSLY DIFFERENTIABLE.** Along the line `t ↦ √G (t·e_v)` it is `|t|`. -/
theorem not_contDiff_absCoordField (hm : m ≠ 0) (v : W) :
    ¬ ContDiff ℝ 1 (absCoordField K m v) := by
  classical
  intro h
  have hd : Differentiable ℝ (absCoordField K m v) := h.differentiable (by norm_num)
  have hline : Differentiable ℝ
      (fun t : ℝ => sqrtMapOf (CFC.sqrt (green K m)) (Pi.single v t)) :=
    (sqrtMapOf (CFC.sqrt (green K m))).differentiable.comp (differentiable_single v)
  have hcomp : DifferentiableAt ℝ
      (fun t : ℝ => absCoordField K m v (sqrtMapOf (CFC.sqrt (green K m)) (Pi.single v t))) 0 :=
    (hd _).comp 0 (hline 0)
  have heq : (fun t : ℝ => absCoordField K m v
      (sqrtMapOf (CFC.sqrt (green K m)) (Pi.single v t))) = fun t : ℝ => |t| := by
    funext t
    rw [sqrtMapOf_apply, absCoordField_comp (K := K) hm v]
    simp [absCoordOf]
  rw [heq] at hcomp
  exact not_differentiableAt_abs_zero hcomp

/-! ## 4. The two halves as one statement -/

/-- **THE STEIN CLASS AT THE FIELD IS STRICTLY WIDER THAN `C¹`.**

There is an observable of `gaussianField K m` which lies in the class `poincare_correlated_stein`
is stated on and which `poincare_correlated_general` cannot express, because it is not `C¹`.

This is the statement `LatticeCorrelatedStein` and `LatticeSqrtEquiv` both declined to make. -/
theorem steinPairField_strictly_wider_than_contDiff (hm : m ≠ 0) (v : W) :
    ∃ (Φ : EuclideanSpace ℝ W → ℝ) (γ : W → EuclideanSpace ℝ W → ℝ),
      SteinPairField K m Φ γ ∧ ¬ ContDiff ℝ 1 Φ :=
  ⟨absCoordField K m v, sgnCoordField K m v,
    absCoordField_steinPairField (K := K) hm v, not_contDiff_absCoordField (K := K) hm v⟩

end LatticeFieldWitness
