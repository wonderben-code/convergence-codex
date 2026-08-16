import LatticePoincarePi
import AbsSteinWitnessPi

/-!
# The multi-dimensional Poincaré inequality off `Fin n` AND off `C¹`

`LatticePoincarePi.poincare_contDiff_pi` freed the estate's `n`-dimensional Gaussian Poincaré
inequality from the index type `Fin n`, but left it stated for **continuously differentiable**
observables. `LatticeUniformPoincare`'s header names that as the remaining restriction, and this
file removes it.

```
∫f² dμ − (∫f dμ)²  ≤  ∑_{v : V} ∫ (g v)² dμ
```

against the product of independent standard Gaussians indexed by any finite `V`, for `f` in the
**Stein pair class** with gradient tuple `g` — no differentiability of any kind assumed.

## Why the class and not the smooth condition

`HermitePiPoincare.poincare_steinPi` is already stated on `SteinPairPi`, which is defined by a
pairing identity against Hermite polynomials rather than by a derivative;
`SteinGeneralPi.steinPairPi_of_contDiff` is only the *bridge into* it from the smooth side. So on
`Fin n` the estate has had the general statement all along and has been citing the specialisation.
The `Fin n` was the only thing in the way.

## The class is STRICTLY wider, and that is proved rather than asserted

`absCoordOf_steinPairOf`: `x ↦ |x v|` is in the class at every finite `V`, with gradient
`sgn(x v)` in slot `v` and zero elsewhere. `not_contDiff_absCoordOf`: it is **not** `ContDiff ℝ 1`
— restrict to the line `t ↦ Pi.single v t` and it is `|t|` at the origin.

**So `poincare_steinPi_of` is not a restatement of `poincare_contDiff_pi`; it covers observables
that theorem cannot reach.** And the containment the other way is a theorem rather than a remark:
`poincare_contDiff_pi_of_stein` derives `LatticePoincarePi.poincare_contDiff_pi`'s exact statement
from §3 in one line. *That corollary exists because the adversarial review of this file's first
draft found the subsumption claimed in prose and not in Lean.*

## The one thing that is honest to flag about `SteinPairOf`

**The class at `V` is DEFINED BY TRANSPORT** along the canonical relabelling `Fin (card V) ≃ V`,
not characterised intrinsically. Membership is therefore checked by unfolding through that
equivalence, as `absCoordOf_steinPairOf` does. An intrinsic definition would need the Hermite
system re-indexed by `V`, which is a real piece of work and is **not done here and not costed**
(`ERRATUM 183`). Nothing downstream needs it: the two ways in — `steinPairOf_of_contDiff` and the
`|x v|` witness — are both proved, and both are stated in terms of `V` alone.

*Independence of the choice of equivalence is likewise NOT proved. It is true (the measure is
exchangeable) and nothing here relies on it, because the definition names one canonical
equivalence and every theorem below uses that same one.*

## What this is NOT

**This is not the correlated inequality.** It is against a product measure. Carrying it to
`gaussianField K m` through `√G`, which is what would actually weaken
`LatticeCorrelatedPoincare.poincare_correlated_general`'s `ContDiff ℝ 1`, is the next step and is
**not done here**.

**No spectral gap is claimed, `OS4` does not move, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeSteinPoincarePi

open MeasureTheory ProbabilityTheory GaussianProductMeasure
open HermitePiStein HermitePiPoincare LatticePoincarePi
open AbsSteinWitness AbsSteinWitnessPi

variable {V : Type*} [Fintype V]

/-! ## 1. The canonical relabelling, and transport of `MemLp` across it -/

/-- The canonical `Fin (card V) ≃ V`. Named once so that every declaration below uses the *same*
equivalence — see the header on why independence of the choice is not proved and not needed. -/
noncomputable def eqv (V : Type*) [Fintype V] : Fin (Fintype.card V) ≃ V :=
  (Fintype.equivFin V).symm

/-- `relabel` is a measurable embedding, because it *is* `MeasurableEquiv.piCongrLeft`. -/
theorem measurableEmbedding_relabel (e : Fin (Fintype.card V) ≃ V) :
    MeasurableEmbedding (relabel e : (Fin (Fintype.card V) → ℝ) → (V → ℝ)) := by
  rw [coe_relabel_eq]
  exact (MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) e).measurableEmbedding

/-- Square-integrability transports back across the relabelling **with no measurability
hypothesis**, because `MeasurableEmbedding.memLp_map_measure_iff` asks for none. -/
theorem memLp_of_comp_relabel {h : (V → ℝ) → ℝ}
    (hc : MemLp (fun y => h (relabel (eqv V) y)) 2 (gaussPi (Fintype.card V))) :
    MemLp h 2 (gaussPiOf V) := by
  have hiff := (measurableEmbedding_relabel (eqv V)).memLp_map_measure_iff
    (μ := gaussPi (Fintype.card V)) (g := h) (p := 2)
  rw [(measurePreserving_relabel (eqv V)).map_eq] at hiff
  exact hiff.mpr hc

/-! ## 2. The Stein pair class at an arbitrary finite index type -/

/-- **The Stein pair class at any finite index type**, defined by transport along `eqv V`.

`f` is paired with the tuple `g : V → ((V → ℝ) → ℝ)` exactly when the relabelled function is
paired with the relabelled tuple on `Fin (card V)`. -/
def SteinPairOf (V : Type*) [Fintype V] (f : (V → ℝ) → ℝ) (g : V → ((V → ℝ) → ℝ)) : Prop :=
  SteinPairPi (Fintype.card V)
    (fun y => f (relabel (eqv V) y))
    (fun i y => g (eqv V i) (relabel (eqv V) y))

theorem SteinPairOf.memLp {f : (V → ℝ) → ℝ} {g : V → ((V → ℝ) → ℝ)}
    (h : SteinPairOf V f g) : MemLp f 2 (gaussPiOf V) :=
  memLp_of_comp_relabel h.1

theorem SteinPairOf.memLp_grad {f : (V → ℝ) → ℝ} {g : V → ((V → ℝ) → ℝ)}
    (h : SteinPairOf V f g) (v : V) : MemLp (g v) 2 (gaussPiOf V) := by
  refine memLp_of_comp_relabel ?_
  have := h.2.1 ((eqv V).symm v)
  simpa using this

/-! ## 3. The inequality -/

/-- **THE ESTATE'S MULTI-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY, OFF `Fin n` AND OFF `C¹`.**

`∫f² − (∫f)² ≤ ∑_{v : V} ∫ (g v)²` against `gaussPiOf V`, for any Stein pair `(f, g)`. No
differentiability is assumed anywhere; `g` is whatever the pairing identity says it is. -/
theorem poincare_steinPi_of {f : (V → ℝ) → ℝ} {g : V → ((V → ℝ) → ℝ)}
    (h : SteinPairOf V f g) :
    (∫ x, f x * f x ∂(gaussPiOf V)) - (∫ x, f x ∂(gaussPiOf V)) ^ 2
      ≤ ∑ v : V, ∫ x, g v x * g v x ∂(gaussPiOf V) := by
  classical
  have hmap : Measure.map (relabel (eqv V)) (gaussPi (Fintype.card V)) = gaussPiOf V :=
    (measurePreserving_relabel (eqv V)).map_eq
  have htrans : ∀ u : (V → ℝ) → ℝ, AEStronglyMeasurable u (gaussPiOf V) →
      ∫ x, u x ∂(gaussPiOf V) = ∫ y, u (relabel (eqv V) y) ∂(gaussPi (Fintype.card V)) := by
    intro u hu
    rw [← hmap] at hu ⊢
    rw [integral_map (by fun_prop) hu]
  have key := poincare_steinPi (Fintype.card V) h
  have hfm : MemLp f 2 (gaussPiOf V) := h.memLp
  rw [htrans (fun x => f x * f x) (hfm.1.mul hfm.1), htrans f hfm.1]
  refine key.trans (le_of_eq ?_)
  rw [← Equiv.sum_comp (eqv V) (fun v => ∫ x, g v x * g v x ∂(gaussPiOf V))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hgm : MemLp (g (eqv V i)) 2 (gaussPiOf V) := h.memLp_grad _
  rw [htrans (fun x => g (eqv V i) x * g (eqv V i) x) (hgm.1.mul hgm.1)]

/-! ## 4. The smooth side is inside the class, so §3 subsumes `poincare_contDiff_pi` -/

/-- A `C¹` observable with square-integrable value and coordinate derivatives is a Stein pair with
its own gradient. This is `SteinGeneralPi.steinPairPi_of_contDiff` carried across the
relabelling, and it is what makes `poincare_contDiff_pi` a corollary of §3. -/
theorem steinPairOf_of_contDiff [DecidableEq V] {Ψ : (V → ℝ) → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hmem : MemLp Ψ 2 (gaussPiOf V))
    (hgrad : ∀ v : V, MemLp (fun x => fderiv ℝ Ψ x (Pi.single v (1 : ℝ))) 2 (gaussPiOf V)) :
    SteinPairOf V Ψ (fun v x => fderiv ℝ Ψ x (Pi.single v (1 : ℝ))) := by
  classical
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hmap : Measure.map (relabel (eqv V)) (gaussPi (Fintype.card V)) = gaussPiOf V :=
    (measurePreserving_relabel (eqv V)).map_eq
  have hchain : ∀ (y : Fin (Fintype.card V) → ℝ) (i : Fin (Fintype.card V)),
      fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y (Pi.single i (1 : ℝ))
        = fderiv ℝ Ψ (relabel (eqv V) y) (Pi.single (eqv V i) (1 : ℝ)) := by
    intro y i
    have hcomp := fderiv_comp (𝕜 := ℝ) y (hΨd (relabel (eqv V) y))
      (relabel (eqv V)).differentiableAt
    simp only [Function.comp_def] at hcomp
    rw [hcomp]
    simp [relabel_single]
  have hmem' : MemLp (fun y => Ψ (relabel (eqv V) y)) 2 (gaussPi (Fintype.card V)) := by
    have := (memLp_map_measure_iff (μ := gaussPi (Fintype.card V))
      (f := (relabel (eqv V) : (Fin (Fintype.card V) → ℝ) → (V → ℝ)))
      (by rw [hmap]; exact hmem.1) (by fun_prop)).mp (by rw [hmap]; exact hmem)
    simpa [Function.comp_def] using this
  have hgrad' : ∀ i, MemLp (fun y => fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y
      (Pi.single i (1 : ℝ))) 2 (gaussPi (Fintype.card V)) := by
    intro i
    have hb := (memLp_map_measure_iff (μ := gaussPi (Fintype.card V))
      (f := (relabel (eqv V) : (Fin (Fintype.card V) → ℝ) → (V → ℝ)))
      (g := fun x => fderiv ℝ Ψ x (Pi.single (eqv V i) (1 : ℝ)))
      (by rw [hmap]; exact (hgrad (eqv V i)).1) (by fun_prop)).mp
        (by rw [hmap]; exact hgrad (eqv V i))
    simpa [Function.comp_def, hchain] using hb
  have hcomp : ContDiff ℝ 1 (fun y => Ψ (relabel (eqv V) y)) := hΨ.comp (relabel (eqv V)).contDiff
  have hst := SteinGeneralPi.steinPairPi_of_contDiff (n := Fintype.card V) hcomp hmem' hgrad'
  have hfun : (fun i y => fderiv ℝ (fun z => Ψ (relabel (eqv V) z)) y (Pi.single i (1 : ℝ)))
      = fun i y => fderiv ℝ Ψ (relabel (eqv V) y) (Pi.single (eqv V i) (1 : ℝ)) := by
    funext i y; exact hchain y i
  rw [hfun] at hst
  exact hst

/-- **THE SUBSUMPTION, PROVED RATHER THAN ASSERTED.** `LatticePoincarePi.poincare_contDiff_pi`
falls out of §3 by composing with `steinPairOf_of_contDiff` — same statement, same constant, no
extra hypothesis.

*The header of the first draft of this file said `poincare_contDiff_pi` "is recovered" from §3 and
left a reader to check it. The adversarial review of the file called that what it was — a claim
about the estate stated in prose and not in Lean — so it is a theorem now.* -/
theorem poincare_contDiff_pi_of_stein [DecidableEq V] {Ψ : (V → ℝ) → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hmem : MemLp Ψ 2 (gaussPiOf V))
    (hgrad : ∀ v : V, MemLp (fun x => fderiv ℝ Ψ x (Pi.single v (1 : ℝ))) 2 (gaussPiOf V)) :
    (∫ x, Ψ x * Ψ x ∂(gaussPiOf V)) - (∫ x, Ψ x ∂(gaussPiOf V)) ^ 2
      ≤ ∑ v : V, ∫ x, fderiv ℝ Ψ x (Pi.single v (1 : ℝ))
          * fderiv ℝ Ψ x (Pi.single v (1 : ℝ)) ∂(gaussPiOf V) :=
  poincare_steinPi_of (steinPairOf_of_contDiff hΨ hmem hgrad)

/-! ## 5. A member of the class that is not `C¹`, so §3 is STRICTLY stronger -/

/-- `x ↦ |x v|` at an arbitrary finite index type. -/
def absCoordOf (V : Type*) [Fintype V] (v : V) (x : V → ℝ) : ℝ := |x v|

/-- Its gradient: `sgn (x v)` in slot `v`, zero elsewhere. -/
noncomputable def sgnCoordOf (V : Type*) [Fintype V] [DecidableEq V] (v w : V) (x : V → ℝ) : ℝ :=
  if w = v then sgn (x v) else 0

/-- **THE NON-SMOOTH WITNESS, AT EVERY FINITE INDEX TYPE.** `|x v|` is a Stein pair with
`sgn(x v)·e_v`, transported from `AbsSteinWitnessPi.absCoord_steinPairPi`. -/
theorem absCoordOf_steinPairOf [DecidableEq V] (v : V) :
    SteinPairOf V (absCoordOf V v) (sgnCoordOf V v) := by
  classical
  have hbase := absCoord_steinPairPi (Fintype.card V) ((eqv V).symm v)
  have hf : (fun y => absCoordOf V v (relabel (eqv V) y))
      = absCoord (Fintype.card V) ((eqv V).symm v) := by
    funext y
    simp [absCoordOf, absCoord]
  have hg : (fun i y => sgnCoordOf V v (eqv V i) (relabel (eqv V) y))
      = sgnCoord (Fintype.card V) ((eqv V).symm v) := by
    funext i y
    have hiff : (eqv V i = v) ↔ (i = (eqv V).symm v) := by
      constructor
      · intro hh; rw [← hh]; simp
      · intro hh; rw [hh]; simp
    by_cases hcase : i = (eqv V).symm v
    · simp [sgnCoordOf, sgnCoord, hcase]
    · have h1 : ¬ (eqv V i = v) := fun hh => hcase (hiff.mp hh)
      simp [sgnCoordOf, sgnCoord, h1, hcase]
  change SteinPairPi (Fintype.card V) _ _
  rw [hf, hg]
  exact hbase

omit [Fintype V] in
/-- The line `t ↦ Pi.single v t` is differentiable — each coordinate is `id` or a constant. -/
theorem differentiable_single [DecidableEq V] (v : V) :
    Differentiable ℝ (fun t : ℝ => (Pi.single v t : V → ℝ)) := by
  classical
  refine differentiable_pi.mpr fun w => ?_
  by_cases h : w = v
  · subst h
    simp
  · have : (fun t : ℝ => (Pi.single v t : V → ℝ) w) = fun _ => (0 : ℝ) := by
      funext t
      simp [h]
    rw [this]
    exact differentiable_const _

/-- **AND IT IS NOT `C¹`.** Restricted to the line through `e_v` it is `|t|`, which is not
differentiable at the origin. So the Stein pair class strictly contains the smooth class and §3
proves something `poincare_contDiff_pi` cannot. -/
theorem not_contDiff_absCoordOf (v : V) :
    ¬ ContDiff ℝ 1 (absCoordOf V v) := by
  classical
  intro h
  have hd : Differentiable ℝ (absCoordOf V v) := h.differentiable (by norm_num)
  have hline : DifferentiableAt ℝ (fun t : ℝ => absCoordOf V v (Pi.single v t)) 0 :=
    (hd _).comp 0 ((differentiable_single v) 0)
  have heq : (fun t : ℝ => absCoordOf V v (Pi.single v t)) = fun t : ℝ => |t| := by
    funext t
    simp [absCoordOf]
  rw [heq] at hline
  exact not_differentiableAt_abs_zero hline

end LatticeSteinPoincarePi
