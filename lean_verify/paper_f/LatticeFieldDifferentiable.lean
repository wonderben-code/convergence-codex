import LatticeSqrtEquiv
import SteinDifferentiablePiOf

/-!
# The correlated Poincaré inequality without `C¹`

`SteinDifferentiablePiOf` carried the differentiable criterion to an arbitrary finite index type and
named what it could not do: reach the **field**. `gaussPiOf W` is the product measure on the vertex
type; `gaussianField K m` is that measure pushed through `√G`, and
`LatticeCorrelatedPoincare.poincare_correlated_general` is still stated for `ContDiff ℝ 1`. This
file closes the gap it named.

## The one estimate that was missing, and where it comes from

Transporting a polynomial growth bound through `sqrtMapOf S` needs `‖S y‖` controlled by `‖y‖`.
`sqrtMapOf S` is a `ContinuousLinearMap`, so `‖sqrtMapOf S y‖ ≤ ‖sqrtMapOf S‖·‖y‖` is **free**.

*That is the same free operator-norm inequality `SteinDifferentiablePiOf` explicitly rejected, and
the contrast is worth stating because it looks like an inconsistency and is not.* There, the
transport was a **relabelling**, applied at every index type and composable with itself, so a
constant would have multiplied at every step; nothing short of the equality `norm_relabel` would do.
Here the transport happens **once**, from the product measure to the field, and never composes with
another. A constant that appears once is a constant in the final theorem, which is exactly what a
growth bound is allowed to have. **The right question about a free inequality is not whether it is
sharp but how many times it will be applied.**

## What is proved

* **`polyGrowth_comp_sqrtMapOf`** — `|Φ x| ≤ C(1+‖x‖²)^k` gives `|Φ(√S y)| ≤ C(1+M²)^k(1+‖y‖²)^k`
  with `M = ‖sqrtMapOf S‖`, the exponent `k` **unchanged**;
* **`absSum_le`**, **`polyGrowth_partial_comp_sqrtMapOf`** — the same for the partial derivatives,
  where the chain rule turns `∂ᵢ` into a fixed linear combination of the `∂ⱼΦ` and the extra factor
  is the sum of `|Sⱼᵢ|` over `j`, bounded uniformly by the sum of all `|S|` entries;
* **`steinPairField_of_differentiable`** — a differentiable `Φ` of polynomial growth is a
  `SteinPairField` with its gradient, **with no continuity of the gradient**;
* **`poincare_correlated_differentiable`** — hence
  `Var Φ ≤ ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ)` against `gaussianField K m`, the conclusion of
  `poincare_correlated_general` on a strictly different hypothesis class.

## What this is NOT

**The two theorems are not ordered.** `poincare_correlated_general` takes `C¹` and two `MemLp` side
conditions and **no growth bound**, so it reaches `C¹` observables of super-polynomial growth that
remain `L²`, which this excludes outright. This reaches observables that are not `C¹`, which that
excludes. Incomparable — the third time this pattern has appeared in this chain, and by now it
should be read as the normal shape rather than a coincidence.

**No constant here is claimed to be sharp**, and `‖sqrtMapOf S‖` is not evaluated: it is a real
number produced by Mathlib's operator norm and carried through. Nothing is said about how it grows
with the box (`ERRATUM 183`).

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeFieldDifferentiable

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeCorrelatedPoincare LatticeCorrelatedStein LatticeSqrtEquiv
open SteinDifferentiablePiOf
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}
variable {Φ : EuclideanSpace ℝ W → ℝ}

/-! ## 1. Polynomial growth crosses `sqrtMapOf`, with the exponent untouched -/

/-- `1 + M²t² ≤ (1 + M²)(1 + t²)`: the elementary step that keeps `k` fixed while `C` absorbs the
operator norm. Both sides expand and the difference is `t² + M² ≥ 0`. -/
theorem one_add_sq_mul_le (M t : ℝ) : 1 + M ^ 2 * t ^ 2 ≤ (1 + M ^ 2) * (1 + t ^ 2) := by
  nlinarith [sq_nonneg M, sq_nonneg t]

omit [DecidableEq W] in
/-- **A GROWTH BOUND CROSSES `sqrtMapOf`, PAYING ONE CONSTANT AND NO EXPONENT.** -/
theorem polyGrowth_comp_sqrtMapOf (S : Matrix W W ℝ) {Φ : EuclideanSpace ℝ W → ℝ}
    {C : ℝ} {k : ℕ} (hb : ∀ x, |Φ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k) (y : W → ℝ) :
    |Φ (sqrtMapOf S y)| ≤ C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k := by
  have hC : 0 ≤ C := by
    have h0 := hb (sqrtMapOf S y)
    have hpos : (0 : ℝ) < (1 + ‖sqrtMapOf S y‖ ^ 2) ^ k := by positivity
    nlinarith [abs_nonneg (Φ (sqrtMapOf S y))]
  refine (hb _).trans ?_
  have hop : ‖sqrtMapOf S y‖ ≤ ‖sqrtMapOf S‖ * ‖y‖ := (sqrtMapOf S).le_opNorm y
  have hsq : ‖sqrtMapOf S y‖ ^ 2 ≤ ‖sqrtMapOf S‖ ^ 2 * ‖y‖ ^ 2 := by
    have h1 : (0:ℝ) ≤ ‖sqrtMapOf S y‖ := norm_nonneg _
    nlinarith [norm_nonneg (sqrtMapOf S), norm_nonneg y]
  have hstep : (1 + ‖sqrtMapOf S y‖ ^ 2) ^ k
      ≤ ((1 + ‖sqrtMapOf S‖ ^ 2) * (1 + ‖y‖ ^ 2)) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    exact le_trans (by linarith) (one_add_sq_mul_le ‖sqrtMapOf S‖ ‖y‖)
  calc C * (1 + ‖sqrtMapOf S y‖ ^ 2) ^ k
      ≤ C * ((1 + ‖sqrtMapOf S‖ ^ 2) * (1 + ‖y‖ ^ 2)) ^ k := mul_le_mul_of_nonneg_left hstep hC
    _ = C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k := by rw [mul_pow]; ring

/-! ## 2. The same for the partial derivatives, through the chain rule -/

omit [DecidableEq W] in
/-- The total of all absolute entries dominates any single column's. -/
theorem absSum_le (S : Matrix W W ℝ) (i : W) :
    ∑ j, |S j i| ≤ ∑ j, ∑ l, |S j l| := by
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun l => |S j l|) (fun l _ => abs_nonneg _) (Finset.mem_univ i)

/-- **AND THE PARTIAL DERIVATIVES CROSS TOO.** The chain rule makes `∂ᵢ(Φ∘√S)` a fixed linear
combination of the `∂ⱼΦ`, with coefficients the `i`-th column of `S`, so the bound picks up the
column's absolute sum — dominated uniformly in `i` by the total. -/
theorem polyGrowth_partial_comp_sqrtMapOf (S : Matrix W W ℝ) {Φ : EuclideanSpace ℝ W → ℝ}
    (hΦ : Differentiable ℝ Φ) {C : ℝ} {k : ℕ}
    (hb' : ∀ (j : W) (x), |fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖x‖ ^ 2) ^ k) (i : W) (y : W → ℝ) :
    |fderiv ℝ (fun z => Φ (sqrtMapOf S z)) y (Pi.single i (1 : ℝ))|
      ≤ (∑ j, ∑ l, |S j l|) * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k) * (1 + ‖y‖ ^ 2) ^ k := by
  classical
  have hC : 0 ≤ C := by
    have h0 := hb' i (sqrtMapOf S y)
    have hpos : (0 : ℝ) < (1 + ‖sqrtMapOf S y‖ ^ 2) ^ k := by positivity
    nlinarith [abs_nonneg (fderiv ℝ Φ (sqrtMapOf S y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))))]
  have hexp : fderiv ℝ (fun z => Φ (sqrtMapOf S z)) y (Pi.single i (1 : ℝ))
      = ∑ j, (S *ᵥ Pi.single i (1 : ℝ)) j
          * fderiv ℝ Φ (sqrtMapOf S y) (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
    rw [fderiv_comp_sqrtMapOf _ hΦ y (Pi.single i (1 : ℝ)), sqrtMapOf_apply,
      LatticeGradientForm.apply_eq_sum_coords]
    rfl
  have hcol : ∀ j : W, (S *ᵥ Pi.single i (1 : ℝ)) j = S j i := by
    intro j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hbound : ∀ j : W,
      |(S *ᵥ Pi.single i (1 : ℝ)) j
        * fderiv ℝ Φ (sqrtMapOf S y) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ |S j i| * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k) := by
    intro j
    rw [abs_mul, hcol j]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact polyGrowth_comp_sqrtMapOf S (Φ := fun x =>
      fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) (hb' j) y
  have hsum : |∑ j, (S *ᵥ Pi.single i (1 : ℝ)) j
      * fderiv ℝ Φ (sqrtMapOf S y) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ ∑ j, |S j i| * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hbound j)
  rw [hexp]
  refine hsum.trans ?_
  rw [← Finset.sum_mul]
  have hpos : (0:ℝ) ≤ C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k := by positivity
  calc (∑ j, |S j i|) * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k)
      ≤ (∑ j, ∑ l, |S j l|) * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k * (1 + ‖y‖ ^ 2) ^ k) :=
        mul_le_mul_of_nonneg_right (absSum_le S i) hpos
    _ = (∑ j, ∑ l, |S j l|) * (C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k) * (1 + ‖y‖ ^ 2) ^ k := by ring

/-! ## 3. The class membership, and the inequality -/

/-- **A DIFFERENTIABLE OBSERVABLE OF POLYNOMIAL GROWTH IS A STEIN PAIR AGAINST THE FIELD.**

Compare `LatticeCorrelatedStein.steinPairField_of_contDiff`, which asks for `ContDiff ℝ 1` and two
`MemLp` conditions. **No continuity of the gradient appears here.** -/
theorem steinPairField_of_differentiable (hΦd : Differentiable ℝ Φ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Φ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (j : W) (x), |fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    SteinPairField K m Φ
      (fun j ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) := by
  classical
  set S : Matrix W W ℝ := CFC.sqrt (green K m) with hS
  set A : ℝ := ∑ j, ∑ l, |S j l| with hA
  set D : ℝ := C * (1 + ‖sqrtMapOf S‖ ^ 2) ^ k with hD
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDnn : 0 ≤ D := by
    have hC : 0 ≤ C := by
      have h0 := hb (WithLp.toLp 2 (0 : W → ℝ))
      have hpos : (0 : ℝ) < (1 + ‖(WithLp.toLp 2 (0 : W → ℝ) : EuclideanSpace ℝ W)‖ ^ 2) ^ k := by
        positivity
      nlinarith [abs_nonneg (Φ (WithLp.toLp 2 (0 : W → ℝ)))]
    rw [hD]; positivity
  have hcomp : Differentiable ℝ (fun z : W → ℝ => Φ (sqrtMapOf S z)) :=
    hΦd.comp (sqrtMapOf S).differentiable
  -- the two bounds, with a single constant covering both
  have hb1 : ∀ y : W → ℝ, |Φ (sqrtMapOf S y)| ≤ (1 + A) * D * (1 + ‖y‖ ^ 2) ^ k := by
    intro y
    refine (polyGrowth_comp_sqrtMapOf S hb y).trans ?_
    have hpow : (0:ℝ) ≤ (1 + ‖y‖ ^ 2) ^ k := by positivity
    have : D ≤ (1 + A) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right this hpow
  have hb2 : ∀ (i : W) (y : W → ℝ),
      |fderiv ℝ (fun z => Φ (sqrtMapOf S z)) y (Pi.single i (1 : ℝ))|
        ≤ (1 + A) * D * (1 + ‖y‖ ^ 2) ^ k := by
    intro i y
    refine (polyGrowth_partial_comp_sqrtMapOf S hΦd hb' i y).trans ?_
    have hpow : (0:ℝ) ≤ (1 + ‖y‖ ^ 2) ^ k := by positivity
    have : A * D ≤ (1 + A) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right this hpow
  have key := steinPairOf_of_differentiable hcomp hb1 hb2
  -- and the gradient tuple is the one `SteinPairField` names
  have hEq : (fun (i : W) (y : W → ℝ) =>
      fderiv ℝ (fun z => Φ (sqrtMapOf S z)) y (Pi.single i (1 : ℝ)))
      = fun i y => ∑ j, fderiv ℝ Φ (sqrtMapOf S y) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
          * (S *ᵥ Pi.single i (1 : ℝ)) j := by
    funext i y
    rw [fderiv_comp_sqrtMapOf _ hΦd y (Pi.single i (1 : ℝ)), sqrtMapOf_apply,
      LatticeGradientForm.apply_eq_sum_coords]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hEq] at key
  exact key

/-- **THE CORRELATED POINCARÉ INEQUALITY FOR A DIFFERENTIABLE OBSERVABLE.**

`∫Φ² − (∫Φ)² ≤ ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ)` against `gaussianField K m` — the conclusion of
`LatticeCorrelatedPoincare.poincare_correlated_general`, reached without `ContDiff ℝ 1`. -/
theorem poincare_correlated_differentiable (hm : m ≠ 0) (hΦd : Differentiable ℝ Φ) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |Φ x| ≤ C * (1 + ‖x‖ ^ 2) ^ k)
    (hb' : ∀ (j : W) (x), |fderiv ℝ Φ x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖x‖ ^ 2) ^ k) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green K m *ᵥ (fun j => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField K m) :=
  poincare_correlated_stein_of_class hm (steinPairField_of_differentiable hΦd hb hb')

end LatticeFieldDifferentiable
