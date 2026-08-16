import LatticePoincare
import TextbookSobolevScaled

/-!
# The same inequality on the maximal class: weak derivatives, no continuity

`LatticePoincare.poincare_smeared` removed the *product-measure* fence and left two hypotheses
behind: the observable had to be `C¹`, and it had to have polynomial growth. **This removes both.**

The estate's one-dimensional chain does not stop at `C¹` either — `TextbookSobolevScaled`
identifies the Gaussian Sobolev space `W^{1,2}(γ_{σ²})` at every variance and proves Poincaré on
it, which is the *maximal* class for this inequality: a weak derivative and square-integrability,
nothing else. That theorem had also never met a field.

## What had to change in the transport, and it is a real generalisation

`LatticePoincare.integral_comp_pair` assumed the observable was **continuous**, which was free
there because a `C¹` function is. **A Sobolev function is not**, so the transport is re-proved
here from `AEStronglyMeasurable` alone — and `SobolevWeakScaled` carries exactly that, twice, in
its two `MemLp` components. `integral_comp_pair_ae` is therefore strictly stronger than the lemma
it replaces, and `LatticePoincare.integral_comp_pair` is recovered from it in one line
(`integral_comp_pair_of_continuous`) so the two files cannot drift apart.

## The one hypothesis that is genuinely new, and why it is not a weakening

`TextbookSobolevScaled` needs `σ ≠ 0`, so this needs `fᵀGf ≠ 0`, so it needs **`f ≠ 0`**.

That is not a fence quietly added to make the proof work: at `f = 0` the smeared field is the
constant `0`, every observable is `F 0`, the variance is `0` and the inequality is `0 ≤ 0` — which
`poincare_smeared_zero` proves separately, so the two together still cover every test function.
**`linVar_pos` is where the positive-definiteness of the Green function is used**, and it is the
first place in this chain that needs more than positive *semi*-definiteness.

## What is proved

* **`linVar_pos`** — `0 < fᵀGf` for `f ≠ 0`, from `green_posDef`;
* `integral_comp_pair_ae`, `integral_comp_pair_of_continuous` — the transport at the weaker
  hypothesis, and the old one recovered from it;
* **`poincare_smeared_sobolev`** — for `F` in `W^{1,2}` at variance `fᵀGf` with weak derivative
  `Fd`:

  ```
  ∫ F(⟪f,ω⟫)² dμ − (∫ F(⟪f,ω⟫) dμ)²  ≤  (fᵀGf) · ∫ Fd(⟪f,ω⟫)² dμ
  ```

  **No continuity, no growth condition, no polynomials** — on every finite simple graph, at every
  nonzero mass, for every nonzero test function;
* `poincare_smeared_zero` — and the degenerate case, so nothing is lost at `f = 0`. It needs no
  hypothesis on the mass **at all**, which is not how it was first written; see its docstring.

## What this is NOT

**Still one direction at a time.** As in `LatticePoincare`: this is a function of a *single*
linear functional of the field, and the transport works precisely because that pushforward is
one-dimensional. The correlated multi-dimensional inequality is untouched and **is not costed
here** (`ERRATUM 183`).

**And no spectral gap is claimed for the field.** **OS4 does not move. No published tag moves.**
-/

namespace LatticeSobolevPoincare

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlisSmeared LatticeGeneratingFunctional
open LatticeHigherClustering LatticePoincare
open PoincareSteinScaled TextbookSobolevScaled

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Strict positivity of the variance -/

/-- **THE GREEN FORM IS STRICTLY POSITIVE OFF ZERO.** `linVar_nonneg` came from the form being a
second moment; this needs the propagator's positive-**definiteness**, and is the first point in
this chain where semi-definiteness is not enough. -/
theorem linVar_pos (hm : m ≠ 0) {f : EuclideanSpace ℝ V} (hf : f ≠ 0) : 0 < linVar G m f := by
  have hne : f.ofLp ≠ 0 := fun h => hf (by ext i; simpa using congrFun h i)
  have h := (Matrix.posDef_iff_dotProduct_mulVec.mp (green_posDef G hm)).2 hne
  simpa [linVar] using h

theorem sqrt_linVar_ne_zero (hm : m ≠ 0) {f : EuclideanSpace ℝ V} (hf : f ≠ 0) :
    Real.sqrt (linVar G m f) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (linVar_pos hm hf))

/-! ## 2. The transport, at the hypothesis a Sobolev function actually has -/

/-- **THE TRANSPORT WITHOUT CONTINUITY.** `LatticePoincare.integral_comp_pair` asked for a
continuous observable, which a `C¹` function supplies for free and a Sobolev function does not.
`integral_map` never needed more than measurability of the map and a.e.-strong measurability of the
integrand, and this is that statement. -/
theorem integral_comp_pair_ae (hm : m ≠ 0) (f : EuclideanSpace ℝ V) {F : ℝ → ℝ}
    (hF : AEStronglyMeasurable F
      (gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal)) :
    ∫ x, F x ∂(gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal)
      = ∫ ω, F (inner ℝ f ω : ℝ) ∂(gaussianField G m) := by
  rw [← map_pair hm f] at hF ⊢
  rw [integral_map (pair f).continuous.measurable.aemeasurable hF]
  rfl

/-- And the continuous case is a corollary, so the two files cannot drift apart. -/
theorem integral_comp_pair_of_continuous (hm : m ≠ 0) (f : EuclideanSpace ℝ V) {F : ℝ → ℝ}
    (hFc : Continuous F) :
    ∫ x, F x ∂(gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal)
      = ∫ ω, F (inner ℝ f ω : ℝ) ∂(gaussianField G m) :=
  integral_comp_pair_ae hm f hFc.aestronglyMeasurable

/-! ## 3. The inequality on the maximal class -/

/-- **POINCARÉ FOR THE SMEARED LATTICE FIELD, ON THE GAUSSIAN SOBOLEV SPACE.**

`∫F(⟪f,ω⟫)² − (∫F(⟪f,ω⟫))² ≤ (fᵀGf)·∫Fd(⟪f,ω⟫)²` for `F` in `W^{1,2}(γ_{fᵀGf})` with weak
derivative `Fd`. **No continuity and no growth hypothesis** — this is the maximal class on which
the inequality holds even in one dimension. -/
theorem poincare_smeared_sobolev (hm : m ≠ 0) {f : EuclideanSpace ℝ V} (hf : f ≠ 0) {F Fd : ℝ → ℝ}
    (h : SobolevWeakScaled (Real.sqrt (linVar G m f)) F Fd) :
    (∫ ω, F (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, F (inner ℝ f ω : ℝ) ∂(gaussianField G m)) ^ 2
      ≤ linVar G m f * ∫ ω, Fd (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m) := by
  have key := poincare_sobolevWeakScaled (sqrt_linVar_ne_zero hm hf) h
  -- `gaussSc σ` at `σ = √(fᵀGf)` IS the pushforward, by `nnreal_linVar`
  rw [show (gaussSc (Real.sqrt (linVar G m f)))
      = gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal from by
    rw [gaussSc, nnreal_linVar hm f]] at key
  rw [sq_sqrt_linVar hm f] at key
  have hFm := h.1.aestronglyMeasurable
  have hFdm := h.2.1.aestronglyMeasurable
  rw [show (gaussSc (Real.sqrt (linVar G m f)))
      = gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal from by
    rw [gaussSc, nnreal_linVar hm f]] at hFm hFdm
  rw [integral_comp_pair_ae hm f (F := fun x => F x ^ 2) (hFm.pow 2),
    integral_comp_pair_ae hm f hFm,
    integral_comp_pair_ae hm f (F := fun x => Fd x ^ 2) (hFdm.pow 2)] at key
  exact key

/-- **AND THE DEGENERATE CASE**, so that the two together cover every test function and `f ≠ 0`
above is a case split rather than a fence. At `f = 0` the smeared field is constantly `0`, both
integrals are `F 0`, and the inequality reads `0 ≤ 0`.

**It holds at EVERY mass, including `m = 0`.** The `m ≠ 0` this was first written with was never
used — the linter said so — and it is dropped rather than kept for symmetry with its neighbour:
the statement only needs `gaussianField G m` to be a probability measure, which it is
unconditionally. -/
theorem poincare_smeared_zero (F Fd : ℝ → ℝ) :
    (∫ ω, F (inner ℝ (0 : EuclideanSpace ℝ V) ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, F (inner ℝ (0 : EuclideanSpace ℝ V) ω : ℝ) ∂(gaussianField G m)) ^ 2
      ≤ linVar G m (0 : EuclideanSpace ℝ V)
        * ∫ ω, Fd (inner ℝ (0 : EuclideanSpace ℝ V) ω : ℝ) ^ 2 ∂(gaussianField G m) := by
  have hz : linVar G m (0 : EuclideanSpace ℝ V) = 0 := by simp [linVar]
  simp only [inner_zero_left, hz, zero_mul]
  simp

end LatticeSobolevPoincare
