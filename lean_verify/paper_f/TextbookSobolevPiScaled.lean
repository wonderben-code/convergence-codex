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
  4. **`poincare_sobolevWeakPiVar`** — the same on the textbook side.
  5. **`smoothSteinPairPiVar_ofStd`** and **`poincare_sharp_var`** — the
     BACKWARD transport, and with it **σ² is SHARP**: on the coordinate
     function both sides of (3) equal σ², and the coordinate is exhibited as
     a member of the scaled class rather than assumed to be one. §5 of this
     file records that an earlier draft claimed sharpness without proving
     it; §6 discharges the retraction rather than leaving it standing.
  6. **`poincare_smoothSteinPairPiVar_all`** — and the `σ ≠ 0` hypothesis
     disappears. At `σ = 0` the measure is a point mass and the statement is
     `0 ≤ 0`. Getting there needed **`pi_dirac`**, that a `Measure.pi` of
     Dirac masses is a Dirac mass, which **Mathlib does not have** and
     `exact?` does not find — four lines from `Measure.pi_eq`, generic, and
     flagged as a plausible upstream contribution.

  WHAT THIS HEADER SAID IT DOES NOT DO, AND WHY BOTH CAVEATS ARE NOW GONE.
  The first draft named two residues: σ = 0, and the coefficient
  characterisation at variance σ². §7 closed the first. §8 closed the
  second, **and the caveat had overstated the difficulty** — it said a
  σ-indexed Hermite basis "would have to be built", when in fact §3 and §6
  together are a biconditional on membership, so the standard coefficient
  series of the RESCALED function decides it. That is ERRATUM 53's pattern
  for the fourth time, and both caveats are left visible above §7 and §8
  rather than deleted.

  **A NOTE ON SHARPNESS, kept because the drafting history is the point.**
  An earlier draft of this header claimed σ² sharp on the strength of
  `var_coord_scaled`, which computes only the LEFT-hand side. That was
  caught before pushing and the header was rewritten to say the constant was
  NOT proved sharp, naming the missing piece as a backward transport. §6 then
  built it, so sharpness is now a theorem (`poincare_sharp_var`). The
  retraction is left visible in §5 rather than erased: a claim that had to be
  withdrawn and was then earned is more informative than one that was always
  true.

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

/-! ## 5. The left-hand side reaches σ²

This section computes one side of the inequality on the coordinate function
and gets σ². **On its own that is NOT sharpness**, and an earlier draft of
this file's header said it was — the right-hand side also has to be σ², which
needs the coordinate to be a MEMBER of the scaled class, and §3's transport
runs the other way. §6 supplies the missing direction and finishes the
argument. The retraction is left recorded here on purpose.
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

/-! ## 6. The backward transport, and σ² IS sharp

§5 stopped at "the left-hand side reaches σ²" and the header routed the fix:
a transport running from variance `1` back to variance σ². It is §3's
computation with `σ⁻¹` in place of `σ`, and with it the coordinate function
becomes a member of the scaled class, so both sides can be computed and the
constant is attained.
-/

/-- The scaling run backwards is measure-preserving too. `Measure.map_map`
    on the composite, which is the identity. -/
theorem measurePreserving_scl_inv {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    MeasurePreserving (scl σ⁻¹ : (Fin n → ℝ) → Fin n → ℝ)
      (gaussPiVar σ n) (gaussPi n) := by
  refine ⟨(continuous_scl σ⁻¹).measurable, ?_⟩
  rw [← (measurePreserving_scl σ n).map_eq,
    Measure.map_map (continuous_scl σ⁻¹).measurable (continuous_scl σ).measurable]
  have hid : (scl σ⁻¹ ∘ scl σ : (Fin n → ℝ) → Fin n → ℝ) = id := by
    funext y
    funext j
    rw [Function.comp_apply, scl_apply, scl_apply, id_eq]
    field_simp
  rw [hid, Measure.map_id]

theorem memLp_comp_scl_inv {σ : ℝ} (hσ : σ ≠ 0) {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u 2 (gaussPi n)) :
    MemLp (fun x => u (scl σ⁻¹ x)) 2 (gaussPiVar σ n) := by
  have hmp := measurePreserving_scl_inv hσ n
  rw [← hmp.map_eq] at hu
  exact (memLp_map_measure_iff hu.aestronglyMeasurable hmp.measurable.aemeasurable).mp hu

/-- **THE BACKWARD TRANSPORT.** A standard pair becomes a σ-pair. -/
theorem smoothSteinPairPiVar_ofStd {σ : ℝ} (hσ : σ ≠ 0) {F : (Fin n → ℝ) → ℝ}
    {G : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPi n F G) :
    SmoothSteinPairPiVar σ n (fun x => F (scl σ⁻¹ x))
      (fun i x => σ⁻¹ * G i (scl σ⁻¹ x)) := by
  obtain ⟨hF, hG, hpair⟩ := h
  have hinv : ∀ y : Fin n → ℝ, scl σ⁻¹ (scl σ y) = y := by
    intro y; funext j; rw [scl_apply, scl_apply]; field_simp
  refine ⟨memLp_comp_scl_inv hσ hF,
    fun i => (memLp_comp_scl_inv hσ (hG i)).const_mul σ⁻¹, fun i φ hφ hcφ => ?_⟩
  -- run the standard pairing at the rescaled test function
  have hp := hpair i (fun z => φ (scl σ z)) (contDiff_comp_scl σ hφ)
    (hasCompactSupport_comp_scl hσ hcφ)
  have hL : (∫ x, (fun x => F (scl σ⁻¹ x)) x
        * (x i * φ x / σ ^ 2 - fderiv ℝ φ x (Pi.single i (1:ℝ))) ∂gaussPiVar σ n)
      = σ⁻¹ * ∫ y, F y * (y i * φ (scl σ y)
          - fderiv ℝ (fun z => φ (scl σ z)) y (Pi.single i (1:ℝ))) ∂gaussPi n := by
    rw [integral_scl σ (by
      refine (memLp_comp_scl_inv hσ hF).aestronglyMeasurable.mul ?_
      exact ((((continuous_apply i).mul hφ.continuous).div_const _).sub
        (continuous_partial n hφ i)).aestronglyMeasurable),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hinv y, fderiv_comp_scl σ hφ i y, scl_apply]
    field_simp
  have hR : (∫ x, (σ⁻¹ * G i (scl σ⁻¹ x)) * φ x ∂gaussPiVar σ n)
      = σ⁻¹ * ∫ y, G i y * φ (scl σ y) ∂gaussPi n := by
    rw [integral_scl σ (by
      exact ((memLp_comp_scl_inv hσ (hG i)).const_mul σ⁻¹).aestronglyMeasurable.mul
        hφ.continuous.aestronglyMeasurable),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hinv y]
    ring
  rw [hL, hR, hp]

/-- The class is closed under scalar multiples, which is what turns the
    transported coordinate `σ⁻¹xᵢ` back into `xᵢ`. -/
theorem smoothSteinPairPiVar_const_mul {σ : ℝ} (c : ℝ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPiVar σ n f g) :
    SmoothSteinPairPiVar σ n (fun x => c * f x) (fun i x => c * g i x) := by
  obtain ⟨hf, hg, hpair⟩ := h
  refine ⟨hf.const_mul c, fun i => (hg i).const_mul c, fun i φ hφ hcφ => ?_⟩
  have h1 : (∫ x, (c * f x) * (x i * φ x / σ ^ 2
        - fderiv ℝ φ x (Pi.single i (1:ℝ))) ∂gaussPiVar σ n)
      = c * ∫ x, f x * (x i * φ x / σ ^ 2
          - fderiv ℝ φ x (Pi.single i (1:ℝ))) ∂gaussPiVar σ n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only; ring
  have h2 : (∫ x, (c * g i x) * φ x ∂gaussPiVar σ n)
      = c * ∫ x, g i x * φ x ∂gaussPiVar σ n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only; ring
  rw [h1, h2, hpair i φ hφ hcφ]

/-- **THE COORDINATE IS A MEMBER AT EVERY VARIANCE**, with a unit gradient.
    This is what §5 was missing. -/
theorem coord_memVar {σ : ℝ} (hσ : σ ≠ 0) (i : Fin n) :
    SmoothSteinPairPiVar σ n (fun x => x i) (fun j _ => if j = i then (1:ℝ) else 0) := by
  classical
  have hstd : SmoothSteinPairPi n (fun y : Fin n → ℝ => y i)
      (fun j _ => if j = i then (1:ℝ) else 0) :=
    (smoothSteinPairPi_iff_sobolevWeakPi n _ _).mpr (coord_sobolevWeakPi n i)
  have h := smoothSteinPairPiVar_const_mul (σ := σ) σ
    (smoothSteinPairPiVar_ofStd hσ hstd)
  have hf : (fun x : Fin n → ℝ => σ * (scl σ⁻¹ x) i) = fun x : Fin n → ℝ => x i := by
    funext x; rw [scl_apply]; field_simp
  have hg : (fun (j : Fin n) (x : Fin n → ℝ) =>
        σ * (σ⁻¹ * (if j = i then (1:ℝ) else 0)))
      = fun (j : Fin n) (_ : Fin n → ℝ) => if j = i then (1:ℝ) else 0 := by
    funext j x
    rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]
  rw [hf, hg] at h
  exact h

/-- **σ² IS SHARP.** Both sides of the inequality equal σ² on the coordinate
    function — so the constant is attained and no smaller one can work. This
    discharges the retraction §5 was written to record. -/
theorem poincare_sharp_var {σ : ℝ} (hσ : σ ≠ 0) (i : Fin n) :
    ((∫ x : Fin n → ℝ, x i * x i ∂gaussPiVar σ n)
        - (∫ x : Fin n → ℝ, x i ∂gaussPiVar σ n) ^ 2 = σ ^ 2)
      ∧ (σ ^ 2 * ∑ j : Fin n, ∫ _x : Fin n → ℝ,
            (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0)
              ∂gaussPiVar σ n) = σ ^ 2
      ∧ SmoothSteinPairPiVar σ n (fun x => x i)
          (fun j _ => if j = i then (1:ℝ) else 0) := by
  classical
  refine ⟨var_coord_scaled σ i, ?_, coord_memVar hσ i⟩
  have hone : (∑ j : Fin n, ∫ _x : Fin n → ℝ,
      (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0)
        ∂gaussPiVar σ n) = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]; simp
    · intro j _ hj; rw [if_neg hj]; simp
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hone, mul_one]

/-! ## 7. σ = 0, and the hypothesis disappears

The 1-d chain handles the degenerate variance explicitly
(`PoincareSteinScaled.gaussSc_zero`, and `poincare_stein_scaled` carries no
`σ ≠ 0`). This section does the same in `n`, so every statement above can be
restated without the hypothesis.

**Mathlib has no `Measure.pi_dirac`** *(**FALSE — see the dated correction on the theorem below,
`ERRATUM 413`**: `infinitePi_dirac` composed with `infinitePi_eq_pi` gives it in two lines, and the
theorem is kept only to avoid a 53-job import)* — a product of Dirac masses is a Dirac
mass — and `exact?` does not find it. It is proved here from
`Measure.pi_eq`, four lines, and it is generic: no Gaussian content, no
cascade content. Flagged as a plausible upstream contribution alongside the
two `pderiv`/`finSuccEquiv` bridges already on the watchlist.
-/

/-- **A product of Dirac masses is a Dirac mass.** Absent from Mathlib.

**THAT CLAIM IS FALSE, CORRECTED 2026-09-01 (`ERRATUM 413`), AND IS KEPT ABOVE** (`ERRATUM 94`).
Mathlib has `MeasureTheory.Measure.infinitePi_dirac` and, **forty-five lines below it in the same
file**, `MeasureTheory.Measure.infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ`. Together
they give this statement — for an arbitrary `Fintype` index, arbitrary spaces and an arbitrary
point, not just `0` on `Fin n → ℝ` — in two lines, **compiled and checked before this note was
written**:

```
rw [← Measure.infinitePi_eq_pi]; exact Measure.infinitePi_dirac _
```

`ERRATUM 360` found `infinitePi_dirac` on 30 August, went looking for exactly that bridge, and
recorded *"No `Fintype` bridge was found and none is claimed absent"*. It was in the same file, and
the probe stopped short of it.

**WHY THIS THEOREM IS NEVERTHELESS KEPT AND NOT DELETED, and the reason is measured rather than
asserted**: the two-line proof needs `import Mathlib.Probability.ProductMeasure`, which this file
does not have and which costs **53 build jobs** (4491 → 4544, measured). Twelve lines of proof are
not worth fifty-three jobs on the Hermite chain. **It is kept as a local convenience, explicitly NOT
because Mathlib lacks the statement**, and it is **withdrawn as an upstreaming candidate**. -/
theorem pi_dirac (n : ℕ) :
    Measure.pi (fun _ : Fin n => Measure.dirac (0:ℝ)) = Measure.dirac (0 : Fin n → ℝ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  rw [Finset.prod_congr rfl fun i _ => Measure.dirac_apply' (0:ℝ) (hs i)]
  by_cases h : ∀ i, (0:ℝ) ∈ s i
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hnot : (0 : Fin n → ℝ) ∉ Set.univ.pi s := by
      simp only [Set.mem_univ_pi]
      exact fun hc => hi (hc i)
    rw [Set.indicator_of_notMem hnot]
    exact (Finset.prod_eq_zero (Finset.mem_univ i)
      (Set.indicator_of_notMem hi (1 : ℝ → ENNReal))).symm

/-- **At variance `0` the measure is the Dirac mass at the origin.** The
    n-dimensional twin of `PoincareSteinScaled.gaussSc_zero`. -/
theorem gaussPiVar_zero (n : ℕ) : gaussPiVar 0 n = Measure.dirac 0 := by
  have h0 : (⟨(0 : ℝ) ^ 2, sq_nonneg 0⟩ : NNReal) = 0 := by
    ext
    show (0:ℝ) ^ 2 = ((0 : NNReal) : ℝ)
    norm_num
  have hfun : (fun _ : Fin n => gaussianReal 0 (⟨(0:ℝ) ^ 2, sq_nonneg 0⟩ : NNReal))
      = fun _ : Fin n => Measure.dirac (0:ℝ) := by
    funext _
    rw [h0]
    exact gaussianReal_zero_var 0
  rw [gaussPiVar, hfun]
  exact pi_dirac n

/-- **THE INEQUALITY AT EVERY VARIANCE, WITH NO `σ ≠ 0` HYPOTHESIS.** At
    `σ = 0` the measure degenerates to a point mass, both sides are `0`, and
    the statement is `0 ≤ 0` — true, and worth having so that the theorem is
    a statement about all σ rather than about all nonzero σ. -/
theorem poincare_smoothSteinPairPiVar_all (σ : ℝ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SmoothSteinPairPiVar σ n f g) :
    (∫ x, f x * f x ∂gaussPiVar σ n) - (∫ x, f x ∂gaussPiVar σ n) ^ 2
      ≤ σ ^ 2 * ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPiVar σ n := by
  rcases eq_or_ne σ 0 with rfl | hσ
  · rw [gaussPiVar_zero, integral_dirac, integral_dirac]
    simp [pow_two]
  · exact poincare_smoothSteinPairPiVar hσ h

/-! ## 8. Membership at variance σ², decided by coefficients

**This section exists because the header's own caveat overstated the
difficulty**, which is ERRATUM 53's pattern for the fourth time. That caveat
said carrying `HermitePiCoeff` to variance σ² would need "a σ-indexed Hermite
basis to be built", because the coefficients are defined against `gaussPi n`
and the transport moves functions rather than coefficient systems.

Both halves of that are true and the conclusion does not follow. §3 and §6
together are a BICONDITIONAL: `f` has a σ-partner exactly when `f ∘ σ·` has a
standard one. So membership at variance σ² is decided by the STANDARD
coefficient series of the RESCALED function, and no new basis is needed. A
σ-indexed basis would state the same fact about `f`'s own coefficients
against σ-Hermite functions — which are the standard ones composed with the
scaling — so it would be a change of presentation, not of content.
-/

/-- The two transports of §3 and §6 combine into a biconditional on
    MEMBERSHIP: `f` has a σ-partner iff the rescaled `f` has a standard one. -/
theorem existsPairVar_iff_std {σ : ℝ} (hσ : σ ≠ 0) (f : (Fin n → ℝ) → ℝ) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SmoothSteinPairPiVar σ n f g)
      ↔ (∃ G : Fin n → ((Fin n → ℝ) → ℝ),
            SmoothSteinPairPi n (fun y => f (scl σ y)) G) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨_, smoothSteinPairPiVar_toStd hσ hg⟩
  · rintro ⟨G, hG⟩
    have hfun : (fun x : Fin n → ℝ => f (scl σ (scl σ⁻¹ x))) = f := by
      funext x
      congr 1
      funext j
      rw [scl_apply, scl_apply]
      field_simp
    exact ⟨_, by simpa only [hfun] using smoothSteinPairPiVar_ofStd hσ hG⟩

/-- **MEMBERSHIP AT VARIANCE σ², FROM COEFFICIENTS ALONE.** `f ∈ L²(γ_σⁿ)`
    has a gradient partner if and only if `Σ_k |k|·(∏ⱼkⱼ!)·c_k(f∘σ·)² < ∞` —
    the same series `HermitePiCoeff` uses, read off the rescaled function.
    The last residue of the n-dimensional line. -/
theorem smoothSteinPairPiVar_iff_summable {σ : ℝ} (hσ : σ ≠ 0)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (gaussPiVar σ n)) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SmoothSteinPairPiVar σ n f g)
      ↔ Summable (HermitePiCoeff.wt n (fun y => f (scl σ y))) := by
  rw [existsPairVar_iff_std hσ f]
  constructor
  · rintro ⟨G, hG⟩
    exact HermitePiCoeff.summable_total_of_steinPairPi
      ((steinPairPi_iff_smoothSteinPairPi n _ _).mpr hG)
  · intro hsum
    obtain ⟨g, hg⟩ :=
      HermitePiCoeff.exists_partner_of_summable (memLp_comp_scl σ hf) hsum
    exact ⟨g, (steinPairPi_iff_smoothSteinPairPi n _ _).mp hg⟩

end

end TextbookSobolevPiScaled
