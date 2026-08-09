/-
  TextbookSobolevPiScaled.lean — the n-dimensional Gaussian Sobolev space at
  every variance, and the Poincaré inequality with the sharp constant σ².

  WHY. Every theorem in the n-dimensional chain — orthogonality through the
  coefficient characterisation — is stated against `gaussPi n`, the product
  of STANDARD Gaussians. The one-dimensional chain does not have that
  restriction: `PoincareSteinScaled` and `TextbookSobolevScaled` run at every
  variance. That asymmetry was the last item on the n-dimensional line.

  **THE PROBE THAT PLANNED THIS FILE COSTED A PIECE THAT ALREADY EXISTED**,
  and that is ERRATUM 54. It named `MeasureTheory.measurePreserving_pi` as
  the crux, checked that it exists, and then estimated two to three units
  "because the n-dimensional version needs the scaled product measure and
  its probability instance". Both were already in the estate:
  `GaussianProductMeasure.gaussPiVar` and — the crux itself, fully proved —
  `GaussianProductMeasure.measurePreserving_scale`, built for the Λ²/2
  cascade statement and using `measurePreserving_pi` exactly as the probe
  proposed to. I probed Mathlib and did not grep my own files.

  WHAT THIS FILE PROVES:
  1. **`SmoothSteinPairPiVar`** — the `Cc^∞`-tested Gaussian pairing at
     variance σ². The `xᵢ/σ²` in place of `xᵢ` is the whole difference, and
     it is in the DEFINITION rather than in any proof.
  2. **`smoothSteinPairPiVar_toStd`** — the transport. A σ-pair `(f, g)`
     becomes the standard pair `(f(σ·), σ·g(σ·))`, with the test function
     composed with the scaling on the way through. **The reason this works
     at all is that `Cc^∞` is CLOSED under scaling** — which the Hermite
     test family is not, since a scaled Hermite product is a linear
     combination of Hermite products and not one of them. So this file could
     not have been written before `SteinSmoothPi` made the two classes
     equal; that is the third thing that equality unlocked.
  3. **`poincare_smoothSteinPairPiVar`** — **`Var_{γ_σⁿ}(f) ≤ σ²·Σᵢ ∫ gᵢ²`**,
     the n-dimensional Gaussian Poincaré inequality at every variance.
  4. **`poincare_sobolevWeakPiVar`** — the same on the textbook side, and
     **`var_coord_scaled`**: the variance of a coordinate under `γ_σⁿ` is
     exactly σ², so the LEFT-hand side of (3) reaches σ² on a concrete
     function. **THAT IS NOT YET SHARPNESS AND THE HEADER SAYS SO** — see
     the second paragraph of WHAT THIS DOES NOT DO.

  WHAT THIS DOES NOT DO — a dated claim, per ERRATUM 53, to be re-read after
  the next unit rather than trusted. It does not carry the COEFFICIENT
  characterisation to variance σ². `HermitePiCoeff` decides membership by a
  series in the Hermite coefficients, and those are defined against
  `gaussPi n`; the transport here moves functions, not coefficient systems,
  so a σ-indexed Hermite basis would have to be built to state the analogue.
  Nothing below attempts it. Nor does it treat σ = 0, where the measure
  degenerates to a Dirac mass — the 1-d chain handles that case explicitly
  (`PoincareSteinScaled.gaussSc_zero`) and this file simply requires σ ≠ 0.

  **AND IT DOES NOT PROVE σ² SHARP, which an earlier draft of this header
  claimed.** `var_coord_scaled` computes the left-hand side on the
  coordinate function and gets σ². To conclude the constant is ATTAINED one
  also needs the right-hand side to be σ², i.e. the coordinate to be a
  member of `SmoothSteinPairPiVar σ n` with a unit gradient — and the
  transport below runs from variance σ² to variance `1`, not back, so
  nothing here supplies that. The route is a backward transport
  `smoothSteinPairPiVar_ofStd`, mirroring §3 with `σ⁻¹` in place of `σ`;
  the estate has the standard-variance witness it would need
  (`W6ConversePi.poincare_coord_textbook`, where both sides are `1`). At
  σ = 1 sharpness IS known, by that theorem. For general σ the inequality
  below is a bound whose left side is known to reach σ², which is weaker
  than sharpness and is stated as such.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiCoeff

namespace TextbookSobolevPiScaled

open MeasureTheory ProbabilityTheory Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open HermitePiStein HermitePiPoincare TextbookSobolevPi
open W6ConversePi SteinGeneralPi SteinSmoothPi

noncomputable section

variable {n : ℕ}

/-! ## 1. The scaling map, and what it does to measures and integrals

`GaussianProductMeasure.measurePreserving_scale` is the whole of the measure
theory and it was already proved. Everything here is its consequences.
-/

/-- The coordinatewise scaling, as a scalar action so that Mathlib's `smul`
    lemmas apply to it. -/
def scl (σ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ := σ • y

theorem scl_apply (σ : ℝ) (y : Fin n → ℝ) (i : Fin n) : scl σ y i = σ * y i := rfl

theorem scl_eq (σ : ℝ) : (scl σ : (Fin n → ℝ) → Fin n → ℝ) = fun x i => σ * x i := rfl

theorem measurePreserving_scl (σ : ℝ) (n : ℕ) :
    MeasurePreserving (scl σ : (Fin n → ℝ) → Fin n → ℝ) (gaussPi n) (gaussPiVar σ n) := by
  rw [scl_eq]
  exact measurePreserving_scale σ n

instance instIsProbabilityMeasureVar (σ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (gaussPiVar σ n) := by
  rw [gaussPiVar]
  infer_instance

/-- Change of variables: an integral at variance σ² is an integral at
    variance `1` of the rescaled integrand. -/
theorem integral_scl (σ : ℝ) {h : (Fin n → ℝ) → ℝ}
    (hmeas : AEStronglyMeasurable h (gaussPiVar σ n)) :
    ∫ x, h x ∂gaussPiVar σ n = ∫ y, h (scl σ y) ∂gaussPi n := by
  rw [← (measurePreserving_scl σ n).map_eq] at hmeas ⊢
  exact integral_map (measurePreserving_scl σ n).measurable.aemeasurable hmeas

theorem memLp_comp_scl (σ : ℝ) {h : (Fin n → ℝ) → ℝ}
    (hh : MemLp h 2 (gaussPiVar σ n)) : MemLp (fun y => h (scl σ y)) 2 (gaussPi n) := by
  rw [← (measurePreserving_scl σ n).map_eq] at hh
  exact (memLp_map_measure_iff hh.aestronglyMeasurable
    (measurePreserving_scl σ n).measurable.aemeasurable).mp hh

/-! ## 2. `Cc^∞` is closed under scaling, and the Hermite products are not

This is the reason the transport is done on the `Cc^∞`-tested class. A
scaled Hermite product `Hpi n m (x/σ)` is a linear COMBINATION of Hermite
products, not one of them, so `SteinPairPi`'s test family does not survive
the substitution. `Cc^∞`'s does, trivially. `SteinSmoothPi` is what lets the
result be carried back.
-/

/-- The scaling as a continuous linear map, which is what the chain rule
    wants. -/
def sclL (σ : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := σ • ContinuousLinearMap.id ℝ _

theorem sclL_apply (σ : ℝ) (y : Fin n → ℝ) : sclL σ y = scl σ y := rfl

theorem continuous_scl (σ : ℝ) : Continuous (scl σ : (Fin n → ℝ) → Fin n → ℝ) :=
  (sclL σ).continuous

theorem contDiff_comp_scl (σ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => φ (scl σ y) :=
  hφ.comp ((sclL σ).contDiff)

theorem hasCompactSupport_comp_scl {σ : ℝ} (hσ : σ ≠ 0) {φ : (Fin n → ℝ) → ℝ}
    (hcφ : HasCompactSupport φ) : HasCompactSupport fun y => φ (scl σ y) :=
  hcφ.comp_smul hσ

/-- **The chain rule for the scaling**: `∂ᵢ(φ ∘ σ·)(y) = σ·(∂ᵢφ)(σy)`. -/
theorem fderiv_comp_scl (σ : ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin n) (y : Fin n → ℝ) :
    fderiv ℝ (fun z => φ (scl σ z)) y (Pi.single i (1:ℝ))
      = σ * fderiv ℝ φ (scl σ y) (Pi.single i (1:ℝ)) := by
  have hdφ : HasFDerivAt φ (fderiv ℝ φ (scl σ y)) (scl σ y) :=
    ((hφ.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hcomp : HasFDerivAt (fun z => φ (scl σ z))
      ((fderiv ℝ φ (scl σ y)).comp (sclL σ)) y := by
    have h := hdφ.comp y ((sclL σ).hasFDerivAt (x := y))
    exact h
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, sclL_apply, scl]
  rw [map_smul, smul_eq_mul]

/-! ## 3. The class at variance σ², and the transport -/

/-- **The `Cc^∞`-tested Gaussian pairing at variance σ².** The `xᵢ/σ²` is
    where the variance enters; at σ = 1 this is
    `TextbookSobolevPi.SmoothSteinPairPi` verbatim. -/
def SmoothSteinPairPiVar (σ : ℝ) (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) : Prop :=
  MemLp f 2 (gaussPiVar σ n) ∧ (∀ i, MemLp (g i) 2 (gaussPiVar σ n)) ∧
    ∀ (i : Fin n) (φ : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * (x i * φ x / σ ^ 2 - fderiv ℝ φ x (Pi.single i (1:ℝ)))
          ∂gaussPiVar σ n
        = ∫ x, g i x * φ x ∂gaussPiVar σ n

/-- **THE TRANSPORT.** A σ-pair becomes a standard pair, with the gradient
    picking up a factor σ. The test function is composed with the scaling on
    the way through, which is legal exactly because `Cc^∞` is closed under
    it. -/
theorem smoothSteinPairPiVar_toStd {σ : ℝ} (hσ : σ ≠ 0) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPiVar σ n f g) :
    SmoothSteinPairPi n (fun y => f (scl σ y)) (fun i y => σ * g i (scl σ y)) := by
  obtain ⟨hf, hg, hpair⟩ := h
  refine ⟨memLp_comp_scl σ hf, fun i => (memLp_comp_scl σ (hg i)).const_mul σ,
    fun i φ hφ hcφ => ?_⟩
  -- run the σ-pairing at the rescaled test function
  have hp := hpair i (fun z => φ (scl σ⁻¹ z))
    (contDiff_comp_scl σ⁻¹ hφ) (hasCompactSupport_comp_scl (inv_ne_zero hσ) hcφ)
  -- both sides, pulled back to variance 1
  have hkey : ∀ z : Fin n → ℝ, scl σ⁻¹ (scl σ z) = z := by
    intro z
    funext j
    rw [scl_apply, scl_apply]
    field_simp
  have hL : (∫ x, f x * (x i * (fun z => φ (scl σ⁻¹ z)) x / σ ^ 2
        - fderiv ℝ (fun z => φ (scl σ⁻¹ z)) x (Pi.single i (1:ℝ))) ∂gaussPiVar σ n)
      = σ⁻¹ * ∫ y, f (scl σ y) * (y i * φ y - fderiv ℝ φ y (Pi.single i (1:ℝ)))
          ∂gaussPi n := by
    rw [integral_scl σ (by
      refine (hf.aestronglyMeasurable.mul ?_)
      exact (((continuous_apply i).mul
        (hφ.continuous.comp (continuous_scl σ⁻¹))).div_const _).sub
        (continuous_partial n (contDiff_comp_scl σ⁻¹ hφ) i) |>.aestronglyMeasurable),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [fderiv_comp_scl σ⁻¹ hφ i (scl σ y), hkey y, scl_apply]
    field_simp
  have hR : (∫ x, g i x * (fun z => φ (scl σ⁻¹ z)) x ∂gaussPiVar σ n)
      = ∫ y, g i (scl σ y) * φ y ∂gaussPi n := by
    rw [integral_scl σ (by
      exact ((hg i).aestronglyMeasurable.mul
        (hφ.continuous.comp (continuous_scl σ⁻¹)).aestronglyMeasurable))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hkey y]
  rw [hL, hR] at hp
  -- and solve for the standard pairing
  have hσinv : σ⁻¹ ≠ 0 := inv_ne_zero hσ
  have hgoal : (∫ y, f (scl σ y) * (y i * φ y - fderiv ℝ φ y (Pi.single i (1:ℝ)))
        ∂gaussPi n)
      = σ * ∫ y, g i (scl σ y) * φ y ∂gaussPi n := by
    field_simp at hp
    linarith [hp]
  rw [hgoal, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  ring

/-! ## 4. The inequality at every variance -/

/-- **THE n-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY AT VARIANCE σ².**
    `Var_{γ_σⁿ}(f) ≤ σ²·Σᵢ ∫ gᵢ² dγ_σⁿ`. -/
theorem poincare_smoothSteinPairPiVar {σ : ℝ} (hσ : σ ≠ 0) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPiVar σ n f g) :
    (∫ x, f x * f x ∂gaussPiVar σ n) - (∫ x, f x ∂gaussPiVar σ n) ^ 2
      ≤ σ ^ 2 * ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPiVar σ n := by
  have hf := h.1
  have hg := h.2.1
  have hstd := poincare_smoothSteinPairPi n (smoothSteinPairPiVar_toStd hσ h)
  -- rewrite each of the three integrals as an integral at variance σ²
  have h1 : (∫ y, f (scl σ y) * f (scl σ y) ∂gaussPi n)
      = ∫ x, f x * f x ∂gaussPiVar σ n :=
    (integral_scl σ (hf.aestronglyMeasurable.mul hf.aestronglyMeasurable)).symm
  have h2 : (∫ y, f (scl σ y) ∂gaussPi n) = ∫ x, f x ∂gaussPiVar σ n :=
    (integral_scl σ hf.aestronglyMeasurable).symm
  have h3 : ∀ i : Fin n,
      (∫ y, (σ * g i (scl σ y)) * (σ * g i (scl σ y)) ∂gaussPi n)
        = σ ^ 2 * ∫ x, g i x * g i x ∂gaussPiVar σ n := by
    intro i
    have hm : AEStronglyMeasurable (fun x : Fin n → ℝ => g i x * g i x)
        (gaussPiVar σ n) :=
      (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
    rw [integral_scl σ hm, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    ring
  rw [h1, h2] at hstd
  simp_rw [h3] at hstd
  rw [← Finset.mul_sum] at hstd
  exact hstd

/-- The same on the textbook side, through stair N5 at variance `1`: a σ-pair
    whose standard transport is a `SobolevWeakPi` member. Stated as the
    composite the reader wants. -/
theorem poincare_sobolevWeakPiVar {σ : ℝ} (hσ : σ ≠ 0) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPiVar σ n f g) :
    SobolevWeakPi n (fun y => f (scl σ y)) (fun i y => σ * g i (scl σ y))
      ∧ (∫ x, f x * f x ∂gaussPiVar σ n) - (∫ x, f x ∂gaussPiVar σ n) ^ 2
          ≤ σ ^ 2 * ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPiVar σ n :=
  ⟨(smoothSteinPairPi_iff_sobolevWeakPi n _ _).mp (smoothSteinPairPiVar_toStd hσ h),
    poincare_smoothSteinPairPiVar hσ h⟩

/-! ## 5. The left-hand side reaches σ² — which is not yet sharpness

At σ = 1 sharpness is known: `W6ConversePi.poincare_coord_textbook` computes
BOTH sides on a coordinate and gets `1`. Here only the left side is computed.
Getting the right side needs the coordinate to be a member of
`SmoothSteinPairPiVar σ n`, and §3's transport runs the other way, so this
section stops where the proof stops. The gap is named in the header and
routed there.
-/

/-- The variance of a coordinate at variance σ² is σ². -/
theorem var_coord_scaled (σ : ℝ) (i : Fin n) :
    (∫ x : Fin n → ℝ, x i * x i ∂gaussPiVar σ n)
        - (∫ x : Fin n → ℝ, x i ∂gaussPiVar σ n) ^ 2
      = σ ^ 2 := by
  have hco : MemLp (fun x : Fin n → ℝ => x i) 2 (gaussPi n) := memLp_coord n i
  have h1 : (∫ x : Fin n → ℝ, x i * x i ∂gaussPiVar σ n)
      = ∫ y : Fin n → ℝ, (σ * y i) * (σ * y i) ∂gaussPi n := by
    refine integral_scl σ ?_
    exact (measurable_pi_apply i).aestronglyMeasurable.mul
      (measurable_pi_apply i).aestronglyMeasurable
  have h2 : (∫ x : Fin n → ℝ, x i ∂gaussPiVar σ n)
      = ∫ y : Fin n → ℝ, σ * y i ∂gaussPi n :=
    integral_scl σ (measurable_pi_apply i).aestronglyMeasurable
  have hsq : (∫ y : Fin n → ℝ, (σ * y i) * (σ * y i) ∂gaussPi n)
      = σ ^ 2 * ∫ y : Fin n → ℝ, y i * y i ∂gaussPi n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hlin : (∫ y : Fin n → ℝ, σ * y i ∂gaussPi n)
      = σ * ∫ y : Fin n → ℝ, y i ∂gaussPi n := integral_const_mul _ _
  obtain ⟨hvar, -, -⟩ := poincare_coord_textbook n i
  rw [h1, h2, hsq, hlin]
  nlinarith [hvar]

end

end TextbookSobolevPiScaled
