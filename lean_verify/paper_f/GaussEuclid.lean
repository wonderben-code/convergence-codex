/-
  GaussEuclid.lean — stair N2b: the Gaussian product measure moved onto an
  INNER-PRODUCT space, and characteristic-function uniqueness transported
  back.

  WHY. After `GaussPiExp` the completeness stair N2 had exactly one
  unknown left, and it is not analysis. The route closes with Mathlib's
  `Measure.ext_of_charFun`, which requires `[InnerProductSpace ℝ E]`.
  The estate's Gaussian product measure lives on `Fin n → ℝ`, which
  carries the SUP norm and has no inner product; `EuclideanSpace ℝ (Fin n)`
  is the same underlying type with different instances. **Lean does not
  accept a measure on one where the other is expected** — probed, the type
  synonym does not unfold at that transparency — so a genuine transport is
  needed.

  WHAT THIS FILE PROVES:
  * **`gaussEuc`** — the estate's `gaussPi n` pushed onto
    `EuclideanSpace ℝ (Fin n)` along `MeasurableEquiv.toLp`,
    with the probability-measure instance carried across.
  * **`integral_gaussEuc`**, **`memLp_gaussEuc`** — integrals and `L²`
    membership move both ways, so nothing proved on `Fin n → ℝ` is lost.
  * **`ext_of_charFun_pi`** — **the payoff.** Two finite measures on
    `Fin n → ℝ` whose transported characteristic functions agree are
    EQUAL. That is `Measure.ext_of_charFun` available where the estate
    actually works, and it is the last tool N2 was missing.

  WHAT THIS DOES NOT DO. It does not prove completeness. With
  `GaussPiExp` supplying the domination and this file supplying the
  uniqueness theorem, what remains of N2 is the convergence argument and
  the bookkeeping that assembles them — the one-dimensional
  `polynomials_complete` pattern, with no ingredient now missing. That
  claim is a prediction about a route, which this project has learned to
  distrust (ERRATA 40/42 applied to routes), so it is written as a
  prediction and not as a plan.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GaussPiExp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace GaussEuclid

open MeasureTheory ProbabilityTheory Filter Topology
open GaussianProductMeasure

noncomputable section

/-! ## 1. The transport map -/

/-- `Fin n → ℝ ≃ᵐ EuclideanSpace ℝ (Fin n)` — the identity on points,
    a change of instances on types. -/
def toEuc (n : ℕ) : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
  MeasurableEquiv.toLp 2 (Fin n → ℝ)

/-- The Gaussian product measure, on a space with an inner product. -/
def gaussEuc (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map (toEuc n) (gaussPi n)

instance instIsProbabilityMeasureGaussEuc (n : ℕ) : IsProbabilityMeasure (gaussEuc n) := by
  rw [gaussEuc]
  exact Measure.isProbabilityMeasure_map (toEuc n).measurable.aemeasurable

/-! ## 2. Nothing is lost in the move -/

theorem integral_gaussEuc (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEStronglyMeasurable f (gaussEuc n)) :
    ∫ y, f y ∂gaussEuc n = ∫ x, f (toEuc n x) ∂gaussPi n := by
  rw [gaussEuc] at hf ⊢
  exact integral_map (toEuc n).measurable.aemeasurable hf

theorem memLp_gaussEuc (n : ℕ) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEStronglyMeasurable f (gaussEuc n)) :
    MemLp f 2 (gaussEuc n) ↔ MemLp (fun x => f (toEuc n x)) 2 (gaussPi n) := by
  rw [gaussEuc] at hf ⊢
  exact memLp_map_measure_iff hf (toEuc n).measurable.aemeasurable

/-! ## 3. The payoff: characteristic-function uniqueness where the estate
       actually works

`Measure.ext_of_charFun` is stated for inner-product spaces. Pushing two
measures forward along a measurable EQUIVALENCE loses nothing, because the
pushforward can be undone — which is the whole reason an equivalence and
not merely a measurable map is needed here.
-/

theorem map_toEuc_injective (n : ℕ) {μ ν : Measure (Fin n → ℝ)}
    (h : Measure.map (toEuc n) μ = Measure.map (toEuc n) ν) : μ = ν := by
  have hback : ∀ ρ : Measure (Fin n → ℝ),
      Measure.map (toEuc n).symm (Measure.map (toEuc n) ρ) = ρ := by
    intro ρ
    rw [Measure.map_map (toEuc n).symm.measurable (toEuc n).measurable]
    have hid : ((toEuc n).symm ∘ (toEuc n)) = id := by
      funext x
      simp
    rw [hid, Measure.map_id]
  rw [← hback μ, h, hback ν]

/-- **THE TOOL N2 WAS MISSING.** Two finite measures on `Fin n → ℝ` whose
    transported characteristic functions agree are equal. -/
theorem ext_of_charFun_pi (n : ℕ) {μ ν : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFun (Measure.map (toEuc n) μ) = charFun (Measure.map (toEuc n) ν)) :
    μ = ν := by
  have hμ : IsFiniteMeasure (Measure.map (toEuc n) μ) :=
    Measure.isFiniteMeasure_map μ (toEuc n)
  have hν : IsFiniteMeasure (Measure.map (toEuc n) ν) :=
    Measure.isFiniteMeasure_map ν (toEuc n)
  exact map_toEuc_injective n (Measure.ext_of_charFun h)

/-! ## 3b. The bridge to `GaussPiExp`

Without this section the two halves of N2 never meet: `GaussPiExp` bounds
the partial sums of `exp(∑ᵢ tᵢxᵢ)`, and `charFun` is written with an inner
product on the Euclidean side. **They are the same linear form**, and
saying so is a theorem, not a remark.
-/

/-- The Euclidean inner product, read back on the estate's side. -/
theorem inner_toEuc (n : ℕ) (t : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    inner ℝ (toEuc n x) t = ∑ i, t i * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (RCLike.inner_apply (𝕜 := ℝ) _ _).trans (by simp [toEuc, mul_comm])

/-- **The characteristic function of the transported measure, as an
    integral on the estate's side.** This is the form N2 will compute
    with, and its exponent is exactly the linear form
    `GaussPiExp.partial_exp_bound` bounds. -/
theorem charFun_map_toEuc (n : ℕ) (μ : Measure (Fin n → ℝ))
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun (Measure.map (toEuc n) μ) t
      = ∫ x, Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply, integral_map (toEuc n).measurable.aemeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [inner_toEuc]
  · exact (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp
        (continuous_inner.comp (Continuous.prodMk continuous_id continuous_const))).mul
          continuous_const))).aestronglyMeasurable

/-! ## 4. Review round 46 — the ways this could be hollow

**"The transport could lose information."** It cannot, and
`map_toEuc_injective` is the proof rather than the assurance: the
pushforward along a measurable EQUIVALENCE is undone by the pushforward
along its inverse. This is exactly why the file uses `≃ᵐ` and not a
measurable map — with a mere map, `ext_of_charFun_pi` would be false.

**"`gaussEuc` could be a different measure from `gaussPi`."** It is the
pushforward along a map that is the identity on points, and §2 records
what that means concretely: integrals and `L²` membership correspond, so
every statement proved about `gaussPi n` reads across.

**"`ext_of_charFun_pi` might be vacuous because nothing has a
characteristic function here."** `gaussEuc n` is a probability measure by
the instance in §1, so it is finite and `charFun` applies to it and to
every `withDensity` of it by a bounded density — which is the family N2
will actually feed in.

**"This might not be the missing piece."** It is the piece named in
`GaussPiExp`'s header and in the watchlist as N2's one remaining unknown.
What is still missing after it is the convergence argument, and this file
says so rather than implying the stair is finished.
-/

/-- The transported measure really is a probability measure, stated
    rather than left to instance search — so §3's finiteness hypotheses
    are known to be satisfiable. -/
theorem gaussEuc_univ (n : ℕ) : (gaussEuc n) Set.univ = 1 :=
  measure_univ

/-- And the transport is available in the direction N2 needs: a function
    on the Euclidean side restricts to the estate's side without any
    hypothesis, because the map is a plain composition. -/
theorem comp_toEuc_eq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : Fin n → ℝ) :
    (fun z => f (toEuc n z)) x = f (toEuc n x) := rfl

end

end GaussEuclid
