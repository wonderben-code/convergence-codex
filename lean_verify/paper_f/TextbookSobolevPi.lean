/-
  TextbookSobolevPi.lean — **STAIR N5, the last stair of the 9 August
  staircase**: the `Cc^∞`-tested Gaussian pairing in n dimensions IS the
  textbook Lebesgue-weak-derivative Gaussian Sobolev space.

  WHAT IS PROVED. Two classes of `L²(γⁿ)` functions with a GRADIENT partner
  `g : Fin n → ((Fin n → ℝ) → ℝ)`:

  * **`SmoothSteinPairPi`** — for every coordinate `i` and every
    `φ ∈ Cc^∞(ℝⁿ)`, `∫ f·(xᵢφ − ∂ᵢφ) dγⁿ = ∫ gᵢ·φ dγⁿ`. Gaussian
    integration by parts, tested against smooth compactly supported
    functions, one coordinate at a time.
  * **`SobolevWeakPi`** — for every `i` and every `ψ ∈ Cc^∞(ℝⁿ)`,
    `∫ f·∂ᵢψ dx = −∫ gᵢ·ψ dx`. The textbook definition: `gᵢ` is the i-th
    LEBESGUE weak partial derivative of `f`.

  **`smoothSteinPairPi_iff_sobolevWeakPi` — they are the same class.** The
  n-dimensional twin of `TextbookSobolev.stein_iff_sobolevWeak`.

  THE "GENUINELY NEW SHAPE" WAS REAL BUT IT IS IN THE DEFINITION, NOT THE
  PROOF. The staircase called N5 the one genuinely new shape on the list
  because the pairing is a FAMILY indexed by the coordinate. That is true,
  and it is a fact about `SmoothSteinPairPi` and `SobolevWeakPi` — the
  partner is a gradient. **Once the definitions are written, every proof
  below is the one-dimensional proof with `i` carried along**, and nothing
  in §3 is new mathematics. Saying so is the point: the estate's habit is to
  over-estimate unprobed stairs, and this is the fourth time in five days
  that the honest answer was "less than predicted".

  WHERE MATHLIB'S INTEGRATION BY PARTS DOES AND DOES NOT APPEAR —
  **ERRATUM 51, and this file is the evidence for both halves.** The
  12 August probe concluded that
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` supplies N5's hard
  step. **It supplies no step of the bridge**: §3's two directions are the
  substitution `φ = ψ/ρₙ` and `ψ = φ·ρₙ` plus
  `GaussPiDensity.integral_gaussPi`, exactly as in one dimension, and
  neither mentions it. **It is used exactly once, in §5**, to prove
  `∫ ∂ᵢψ dx = 0` — the fact the constant witness needs. So the tool is real
  and the attribution was wrong, which is precisely what the erratum says.

  WHAT THIS DOES NOT DO. It exhibits no member of the class beyond §5's
  witnesses. In particular the n-dimensional analogue of
  `PoincareBeyondPolynomials.stein_general` — a differentiable function of
  polynomial growth IS a Stein pair with its gradient — is NOT here, and
  that is where Mathlib's integration by parts is genuinely wanted. Nor is
  Poincaré on this space (N6). **The n-dimensional "polynomial test
  functions only" fence does not fall until N6 lands.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GaussPiDensity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace TextbookSobolevPi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiPeel TextbookSobolev GaussPiDensity

noncomputable section

/-! ## 1. `φ ↦ φ·ρₙ` and `ψ ↦ ψ/ρₙ` are bijections of `Cc^∞(ℝⁿ)`

`ρₙ` is smooth and everywhere positive — `GaussPiDensity` — and positivity is
what makes the division legal.
-/

theorem mulRhoPi_smooth (n : ℕ) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => φ x * rhoPi n x := hφ.mul (rhoPi_smooth n)

theorem mulRhoPi_support (n : ℕ) {φ : (Fin n → ℝ) → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport fun x => φ x * rhoPi n x := hc.mul_right

theorem invRhoPi_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) fun x => (rhoPi n x)⁻¹ :=
  (rhoPi_smooth n).inv fun x => rhoPi_ne_zero n x

theorem divRhoPi_eq (n : ℕ) (ψ : (Fin n → ℝ) → ℝ) :
    (fun x => ψ x / rhoPi n x) = fun x => ψ x * (rhoPi n x)⁻¹ := by
  funext x
  rw [div_eq_mul_inv]

theorem divRhoPi_smooth (n : ℕ) {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => ψ x / rhoPi n x := by
  rw [divRhoPi_eq]
  exact hψ.mul (invRhoPi_smooth n)

theorem divRhoPi_support (n : ℕ) {ψ : (Fin n → ℝ) → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport fun x => ψ x / rhoPi n x := by
  rw [divRhoPi_eq]
  exact hc.mul_right

/-! ## 2. What each substitution does to a partial derivative

Both identities are the one-dimensional ones with `i` carried along, and both
rest on `GaussPiDensity.fderiv_rhoPi`.
-/

/-- `∂ᵢ(φ·ρₙ) = (∂ᵢφ − xᵢφ)·ρₙ`. -/
theorem fderiv_mulRhoPi (n : ℕ) {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y => φ y * rhoPi n y) x (Pi.single i (1:ℝ))
      = (fderiv ℝ φ x (Pi.single i (1:ℝ)) - x i * φ x) * rhoPi n x := by
  have hdφ : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
  rw [fderiv_fun_mul hdφ (rhoPi_differentiable n x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_rhoPi]
  ring

/-- **`xᵢ·(ψ/ρₙ) − ∂ᵢ(ψ/ρₙ) = −(∂ᵢψ)/ρₙ`** — the identity the forward
    direction runs on, and the exact analogue of
    `TextbookSobolev.transform_divRho`. -/
theorem transform_divRhoPi (n : ℕ) {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin n) (x : Fin n → ℝ) :
    x i * (ψ x / rhoPi n x)
        - fderiv ℝ (fun y => ψ y / rhoPi n y) x (Pi.single i (1:ℝ))
      = -(fderiv ℝ ψ x (Pi.single i (1:ℝ)) / rhoPi n x) := by
  -- No new derivative rule is needed: `ψ = (ψ/ρₙ)·ρₙ`, so `fderiv_mulRhoPi`
  -- applied to `φ = ψ/ρₙ` already computes what this identity asserts.
  have hne := rhoPi_ne_zero n x
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => ψ y / rhoPi n y) :=
    divRhoPi_smooth n hψ
  have hid : (fun y : Fin n → ℝ => ψ y / rhoPi n y * rhoPi n y) = ψ := by
    funext y
    have hy := rhoPi_ne_zero n y
    field_simp
  have hkey := fderiv_mulRhoPi n hφ i x
  rw [hid] at hkey
  rw [hkey]
  field_simp
  ring

/-! ## 3. The two classes, and STAIR N5 -/

/-- **The `Cc^∞`-tested Gaussian pairing in n dimensions.** The partner is a
    GRADIENT — a family indexed by the coordinate — which is the one place
    the n-dimensional statement genuinely differs in shape from the
    1-dimensional one. -/
def SmoothSteinPairPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) : Prop :=
  MemLp f 2 (gaussPi n) ∧ (∀ i, MemLp (g i) 2 (gaussPi n)) ∧
    ∀ (i : Fin n) (φ : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * (x i * φ x - fderiv ℝ φ x (Pi.single i (1:ℝ))) ∂gaussPi n
        = ∫ x, g i x * φ x ∂gaussPi n

/-- **The textbook n-dimensional Gaussian Sobolev space**: `gᵢ` is the i-th
    LEBESGUE weak partial derivative of `f`, and both are in `L²(γⁿ)`. -/
def SobolevWeakPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) : Prop :=
  MemLp f 2 (gaussPi n) ∧ (∀ i, MemLp (g i) 2 (gaussPi n)) ∧
    ∀ (i : Fin n) (ψ : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, f x * fderiv ℝ ψ x (Pi.single i (1:ℝ)) = -∫ x, g i x * ψ x

/-- **STAIR N5.** The two classes coincide. Both directions are one
    substitution and two applications of the change of measure — no
    integration by parts anywhere. -/
theorem smoothSteinPairPi_iff_sobolevWeakPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) :
    SmoothSteinPairPi n f g ↔ SobolevWeakPi n f g := by
  constructor
  · -- Gaussian pairing ⟹ Lebesgue weak derivative, by `φ = ψ/ρₙ`
    rintro ⟨hf, hg, hpair⟩
    refine ⟨hf, hg, fun i ψ hψ hcψ => ?_⟩
    have h := hpair i (fun x => ψ x / rhoPi n x) (divRhoPi_smooth n hψ)
      (divRhoPi_support n hcψ)
    rw [integral_gaussPi, integral_gaussPi] at h
    have hL : (∫ x, rhoPi n x * (f x * (x i * (ψ x / rhoPi n x)
          - fderiv ℝ (fun y => ψ y / rhoPi n y) x (Pi.single i (1:ℝ)))))
        = -∫ x, f x * fderiv ℝ ψ x (Pi.single i (1:ℝ)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [transform_divRhoPi n hψ i x]
      have hne := rhoPi_ne_zero n x
      field_simp
    have hR : (∫ x, rhoPi n x * (g i x * (ψ x / rhoPi n x)))
        = ∫ x, g i x * ψ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have hne := rhoPi_ne_zero n x
      field_simp
    rw [hL, hR] at h
    linarith [h]
  · -- Lebesgue weak derivative ⟹ Gaussian pairing, by `ψ = φ·ρₙ`
    rintro ⟨hf, hg, hweak⟩
    refine ⟨hf, hg, fun i φ hφ hcφ => ?_⟩
    have h := hweak i (fun x => φ x * rhoPi n x) (mulRhoPi_smooth n hφ)
      (mulRhoPi_support n hcφ)
    rw [integral_gaussPi, integral_gaussPi]
    have hL : (∫ x, f x * fderiv ℝ (fun y => φ y * rhoPi n y) x (Pi.single i (1:ℝ)))
        = -∫ x, rhoPi n x * (f x * (x i * φ x
            - fderiv ℝ φ x (Pi.single i (1:ℝ)))) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [fderiv_mulRhoPi n hφ i x]
      ring
    have hR : (∫ x, g i x * (φ x * rhoPi n x))
        = ∫ x, rhoPi n x * (g i x * φ x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      ring
    rw [hL, hR] at h
    linarith [h]

/-! ## 4. The partner is unique, so "the" gradient is earned

The 1-d file proved `sobolevWeak_unique` and ERRATUM 45 records why it
matters: a definite article is a uniqueness claim. The same is true one
coordinate at a time.
-/

theorem sobolevWeakPi_unique (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g h : Fin n → ((Fin n → ℝ) → ℝ)}
    (hgf : SobolevWeakPi n f g) (hhf : SobolevWeakPi n f h) (i : Fin n) :
    ∀ ψ : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, g i x * ψ x = ∫ x, h i x * ψ x := by
  intro ψ hψ hcψ
  have h1 := hgf.2.2 i ψ hψ hcψ
  have h2 := hhf.2.2 i ψ hψ hcψ
  rw [h1] at h2
  linarith [h2]

/-! ## 5. Non-vacuity, and the one place Mathlib's integration by parts
       actually belongs

A biconditional between two classes is uninteresting if both are empty. The
constants are in it with the zero gradient — and proving that needs exactly
one fact, `∫ ∂ᵢψ dx = 0` for a compactly supported smooth `ψ`, which is
**Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` at
`f ≡ 1`.** So the tool the 12 August probe found is genuinely used in this
file — for a witness, not for the bridge. ERRATUM 51 was about the
attribution, not about the tool.
-/

theorem continuous_partial (n : ℕ) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin n) :
    Continuous fun x => fderiv ℝ ψ x (Pi.single i (1:ℝ)) :=
  (hψ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_partial (n : ℕ) {ψ : (Fin n → ℝ) → ℝ}
    (hcψ : HasCompactSupport ψ) (i : Fin n) :
    HasCompactSupport fun x => fderiv ℝ ψ x (Pi.single i (1:ℝ)) :=
  (hcψ.fderiv ℝ).comp_left (g := fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i (1:ℝ)))
    (by simp)

theorem integrable_partial (n : ℕ) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) (i : Fin n) :
    Integrable (fun x => fderiv ℝ ψ x (Pi.single i (1:ℝ))) volume :=
  (continuous_partial n hψ i).integrable_of_hasCompactSupport
    (hasCompactSupport_partial n hcψ i)

/-- **`∫ ∂ᵢψ dx = 0`** for `ψ ∈ Cc^∞(ℝⁿ)` — Mathlib's several-variable
    integration by parts against the constant function `1`. -/
theorem integral_partial_eq_zero (n : ℕ) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) (i : Fin n) :
    ∫ x, fderiv ℝ ψ x (Pi.single i (1:ℝ)) = 0 := by
  have hone : ∀ x : Fin n → ℝ,
      fderiv ℝ (fun _ : Fin n → ℝ => (1:ℝ)) x (Pi.single i (1:ℝ)) = 0 := by
    intro x
    simp
  have h1 : Integrable (fun x : Fin n → ℝ =>
      fderiv ℝ (fun _ : Fin n → ℝ => (1:ℝ)) x (Pi.single i (1:ℝ)) * ψ x) volume := by
    refine (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hone x, zero_mul]
  have h2 : Integrable (fun x : Fin n → ℝ =>
      (1:ℝ) * fderiv ℝ ψ x (Pi.single i (1:ℝ))) volume := by
    refine (integrable_partial n hψ hcψ i).congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [one_mul]
  have h3 : Integrable (fun x : Fin n → ℝ => (1:ℝ) * ψ x) volume := by
    refine (hψ.continuous.integrable_of_hasCompactSupport hcψ).congr
      (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [one_mul]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Fin n → ℝ))) (f := fun _ : Fin n → ℝ => (1:ℝ)) (g := ψ)
    (v := Pi.single i (1:ℝ)) h1 h2 h3
    (fun x _ => differentiableAt_const 1)
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)
  have hR : (∫ x : Fin n → ℝ,
      fderiv ℝ (fun _ : Fin n → ℝ => (1:ℝ)) x (Pi.single i (1:ℝ)) * ψ x) = 0 := by
    have hz : (fun x : Fin n → ℝ =>
        fderiv ℝ (fun _ : Fin n → ℝ => (1:ℝ)) x (Pi.single i (1:ℝ)) * ψ x)
        = fun _ => (0:ℝ) := funext fun x => by rw [hone x, zero_mul]
    rw [hz, integral_zero]
  rw [hR, neg_zero] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [one_mul]

/-- **The constants are in the class**, with the zero gradient. -/
theorem const_mem (n : ℕ) (c : ℝ) :
    SobolevWeakPi n (fun _ => c) (fun _ _ => 0) := by
  refine ⟨memLp_const c, fun i => memLp_const 0, fun i ψ hψ hcψ => ?_⟩
  have hd : ∫ x : Fin n → ℝ, (0:ℝ) * ψ x = 0 := by simp
  rw [hd, neg_zero]
  have hc : (fun x : Fin n → ℝ => (fun _ : Fin n → ℝ => c) x
      * fderiv ℝ ψ x (Pi.single i (1:ℝ)))
      = fun x => c • fderiv ℝ ψ x (Pi.single i (1:ℝ)) := rfl
  rw [hc, integral_smul, integral_partial_eq_zero n hψ hcψ i, smul_zero]

/-- And therefore in the Gaussian-pairing class too, by stair N5. -/
theorem const_mem_stein (n : ℕ) (c : ℝ) :
    SmoothSteinPairPi n (fun _ => c) (fun _ _ => 0) :=
  (smoothSteinPairPi_iff_sobolevWeakPi n _ _).mpr (const_mem n c)

/-! ## 6. Review round 54 — the ways this could be hollow

**"The bridge could be the 1-d theorem with a decoration."** It is the 1-d
PROOF with `i` carried along, and the file says so rather than dressing it
up. What is not a decoration is the definitions: the partner is a gradient,
and `SobolevWeakPi` quantifies over coordinates as well as test functions.
A reader who wanted the n-dimensional textbook space would not accept the
1-d statement with `n` substituted anywhere.

**"Both classes could be empty."** §5 rules that out and does it by
computation: the constants are in both, with the zero gradient, and the
proof needs `∫ ∂ᵢψ dx = 0`, which is a real theorem about ℝⁿ and not a
triviality.

**"ERRATUM 51 might have thrown out a tool that was needed."** It did not,
and §5 is the check: Mathlib's several-variable integration by parts IS used
in this file, exactly once, to prove `integral_partial_eq_zero`. The erratum
was about attributing it to the bridge, and the bridge does not use it. Both
halves of that are now visible in one file.

**"Uniqueness might be missing."** §4 has it, one coordinate at a time,
because ERRATUM 45 records that a definite article is a uniqueness claim and
this file says "the i-th weak partial derivative".

**"This might close the fence."** It does not. Nothing here says a
differentiable function of polynomial growth belongs to the class — that is
the n-dimensional `stein_general` and it is not written — and nothing here
proves Poincaré on the class, which is N6. **The n-dimensional "polynomial
test functions only" fence stands until N6 lands.**
-/

end

end TextbookSobolevPi
