/-
  TextbookSobolev.lean — the last flagged identification, discharged.

  WHY. `SteinSmoothTest` proved the Stein class contained in the
  Cc^∞-tested GAUSSIAN pairing and `W6Converse` proved the two equal — and
  both files flagged, rather than absorbed, the step from that pairing to
  the way a textbook writes the Gaussian Sobolev space: with LEBESGUE weak
  derivatives, `∫ f·ψ′ dx = −∫ g·ψ dx`. The identification is the
  substitution `ψ = φ·ρ` with `ρ` the Gaussian density, it was written out
  in prose so a reader could check it, and it was named in Lean as
  `SteinSmoothTest.TextbookBridge` precisely so that it could not be
  quietly counted as proved.

  **It is proved here.** `textbookBridge : SteinSmoothTest.TextbookBridge`.

  WHAT MADE IT SHORT. `ProbabilityTheory.integral_gaussianReal_eq_integral_smul`
  transfers every Gaussian integral to a weighted Lebesgue integral with no
  integrability hypothesis at all, so the whole content is the two
  derivative computations: `(φ·ρ)′ = (φ′ − x·φ)·ρ` and
  `(ψ/ρ)′ = (ψ′ + x·ψ)/ρ`, both resting on `ρ′ = −x·ρ`. The map `φ ↦ φ·ρ`
  is a bijection of `Cc^∞` because `ρ` is smooth and nowhere zero, which is
  where `rho_pos` earns its place.

  WHAT THIS COMPLETES. With `W6Converse.stein_iff_smooth`, the chain now
  reads: Stein class = Cc^∞-tested Gaussian pairing = textbook
  Lebesgue-weak-derivative Gaussian Sobolev space. **WALLS W6 is answered
  in the form a reader coming from a textbook would ask it**, and the
  estate no longer carries a flagged identification underneath that claim.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import W6Converse

namespace TextbookSobolev

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass SteinCoefficients HermiteHilbertBasis SteinSmoothTest
open W6Converse

noncomputable section

/-! ## 1. The Gaussian density as a smooth, positive, nowhere-vanishing weight -/

/-- The standard Gaussian density. -/
def rho (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem rho_eq (x : ℝ) :
    rho x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  rw [rho, gaussianPDFReal_def]
  norm_num

theorem rho_pos (x : ℝ) : 0 < rho x := gaussianPDFReal_pos 0 1 x one_ne_zero

theorem rho_ne_zero (x : ℝ) : rho x ≠ 0 := ne_of_gt (rho_pos x)

theorem rho_funext : rho = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) :=
  funext rho_eq

theorem rho_smooth : ContDiff ℝ (⊤ : ℕ∞) rho := by
  rw [rho_funext]
  exact contDiff_const.mul (Real.contDiff_exp.comp (((contDiff_id.pow 2).neg).div_const 2))

/-- **`ρ′ = −x·ρ`** — the one identity the whole substitution rests on. -/
theorem hasDerivAt_rho (x : ℝ) : HasDerivAt rho (-x * rho x) x := by
  have hq : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-(2 * x ^ 1) / 2) x :=
      ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h using 1
    ring
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x := by
    simpa [Function.comp] using (Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x hq
  have hc := he.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  have hfin : HasDerivAt rho
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * (-x))) x := by
    rw [rho_funext]; exact hc
  convert hfin using 1
  rw [rho_eq]
  ring

theorem rho_differentiable : Differentiable ℝ rho :=
  fun x => (hasDerivAt_rho x).differentiableAt

/-! ## 2. The measure transfer

Mathlib supplies this with no integrability hypothesis, which is the
reason this file is short.
-/

theorem integral_gauss (F : ℝ → ℝ) : ∫ x, F x ∂gauss = ∫ x, rho x * F x := by
  rw [show (gauss : Measure ℝ) = gaussianReal 0 1 from rfl,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp [rho, smul_eq_mul]

/-! ## 3. `φ ↦ φ·ρ` is a bijection of `Cc^∞`, and what it does to derivatives -/

theorem mulRho_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => φ x * rho x := hφ.mul rho_smooth

theorem mulRho_support {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport fun x => φ x * rho x := hc.mul_right

/-- `(φ·ρ)′ = (φ′ − x·φ)·ρ`. -/
theorem deriv_mulRho {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ) :
    deriv (fun y => φ y * rho y) x = (deriv φ x - x * φ x) * rho x := by
  have hd : HasDerivAt φ (deriv φ x) x :=
    (hφ.differentiable (by simp) x).hasDerivAt
  have h := hd.mul (hasDerivAt_rho x)
  have hderiv : deriv (fun y => φ y * rho y) x
      = deriv φ x * rho x + φ x * (-x * rho x) := h.deriv
  rw [hderiv]
  ring

theorem support_divRho (ψ : ℝ → ℝ) :
    Function.support (fun x => ψ x / rho x) = Function.support ψ := by
  ext x
  simp [Function.mem_support, rho_ne_zero x]

theorem divRho_smooth {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => ψ x / rho x := hψ.div rho_smooth rho_ne_zero

theorem divRho_support {ψ : ℝ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport fun x => ψ x / rho x := by
  unfold HasCompactSupport tsupport at hc ⊢
  rwa [support_divRho]

/-- `(ψ/ρ)′ = (ψ′ + x·ψ)/ρ`. -/
theorem deriv_divRho {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : ℝ) :
    deriv (fun y => ψ y / rho y) x = (deriv ψ x + x * ψ x) / rho x := by
  have hd : HasDerivAt ψ (deriv ψ x) x :=
    (hψ.differentiable (by simp) x).hasDerivAt
  have h := hd.div (hasDerivAt_rho x) (rho_ne_zero x)
  have hderiv : deriv (fun y => ψ y / rho y) x
      = (deriv ψ x * rho x - ψ x * (-x * rho x)) / rho x ^ 2 := h.deriv
  rw [hderiv]
  have hne := rho_ne_zero x
  field_simp
  ring

/-- The composite the forward direction needs: for `φ = ψ/ρ`, the
    transformed test function is `−ψ′/ρ`. -/
theorem transform_divRho {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : ℝ) :
    x * (ψ x / rho x) - deriv (fun y => ψ y / rho y) x = -(deriv ψ x) / rho x := by
  rw [deriv_divRho hψ]
  have hne := rho_ne_zero x
  field_simp
  ring

/-! ## 4. The bridge -/

/-- **`SteinSmoothTest.TextbookBridge`, discharged.** The Cc^∞-tested
    Gaussian integration-by-parts pairing IS the Lebesgue-weak-derivative
    condition, so the class `W6Converse` proved equal to the Stein class is
    the textbook Gaussian Sobolev space. -/
theorem textbookBridge : SteinSmoothTest.TextbookBridge := by
  intro f g hf hg
  constructor
  · -- Gaussian pairing ⟹ Lebesgue weak derivative, by `φ = ψ/ρ`
    rintro ⟨-, -, hpair⟩ ψ hψ hcψ
    have h := hpair (fun x => ψ x / rho x) (divRho_smooth hψ) (divRho_support hcψ)
    rw [integral_gauss, integral_gauss] at h
    have hL : (∫ x, rho x * (f x * (x * (ψ x / rho x)
        - deriv (fun y => ψ y / rho y) x)))
        = -∫ x, f x * deriv ψ x := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [transform_divRho hψ]
      have hne := rho_ne_zero x
      field_simp
    have hR : (∫ x, rho x * (g x * (ψ x / rho x))) = ∫ x, g x * ψ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have hne := rho_ne_zero x
      field_simp
    rw [hL, hR] at h
    linarith [h]
  · -- Lebesgue weak derivative ⟹ Gaussian pairing, by `ψ = φ·ρ`
    intro hweak
    refine ⟨hf, hg, fun φ hφ hcφ => ?_⟩
    have h := hweak (fun x => φ x * rho x) (mulRho_smooth hφ) (mulRho_support hcφ)
    rw [integral_gauss, integral_gauss]
    have hL : (∫ x, f x * deriv (fun y => φ y * rho y) x)
        = -∫ x, rho x * (f x * (x * φ x - deriv φ x)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_mulRho hφ]
      ring
    have hR : (∫ x, g x * (φ x * rho x)) = ∫ x, rho x * (g x * φ x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [hL, hR] at h
    linarith [h]

/-! ## 5. WALLS W6, in the textbook's own words -/

/-- The textbook-defined Gaussian Sobolev pairing. -/
def SobolevWeak (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 gauss ∧ MemLp g 2 gauss ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, f x * deriv ψ x = -∫ x, g x * ψ x

theorem smoothSteinPair_iff_sobolevWeak (f g : ℝ → ℝ) :
    SmoothSteinPair f g ↔ SobolevWeak f g := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, (textbookBridge f g h.1 h.2.1).mp h⟩
  · rintro ⟨hf, hg, hw⟩
    exact (textbookBridge f g hf hg).mpr hw

/-- **THE FULL CHAIN.** The Stein class — Gaussian integration by parts
    against every POLYNOMIAL — is the textbook Gaussian Sobolev space,
    defined by LEBESGUE weak derivatives against `Cc^∞`. Three descriptions,
    two of them with incomparable test families (ERRATA 35), all equal. -/
theorem stein_iff_sobolevWeak (f g : ℝ → ℝ) :
    SteinPair f g ↔ SobolevWeak f g :=
  (W6Converse.stein_iff_smooth f g).trans (smoothSteinPair_iff_sobolevWeak f g)

/-- And with the coefficient characterisation, four descriptions: `f` lies
    in the textbook Gaussian Sobolev space exactly when its Hermite
    coefficients satisfy `Σ (n+1)·n!·cₙ(f)² < ∞`. -/
theorem sobolevWeak_iff_coeff {f : ℝ → ℝ} (hf : MemLp f 2 gauss) :
    (∃ g : ℝ → ℝ, SobolevWeak f g) ↔
      Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2 := by
  rw [← HermiteHilbertBasis.steinPair_iff_sobolev hf]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, (stein_iff_sobolevWeak f g).mpr hg⟩,
    fun ⟨g, hg⟩ => ⟨g, (stein_iff_sobolevWeak f g).mp hg⟩⟩

/-! ## 6. Review round 41 — the ways this could be hollow

**"`ρ` could be anything."** It is `Mathlib`'s own `gaussianPDFReal 0 1`,
and `integral_gauss` proves it is the density of the measure every other
file in the chain integrates against — not a hand-chosen weight that
happens to make the algebra work.

**"The bijection `φ ↦ φ·ρ` could fail to land in `Cc^∞`."** Both directions
are proved: `mulRho_smooth`/`mulRho_support` and
`divRho_smooth`/`divRho_support`, the latter needing `ρ` nowhere zero,
which is `rho_pos`. Without that the inverse map does not exist and only
one implication would survive.

**"The whole chain could be vacuous."** It is not: the class contains
`(X, 1)` and `(|x|, sgn)`, and by `HermiteHilbertBasis.sobolevGauss_proper`
it is a PROPER subset of `L²(γ)`, so the four equivalent descriptions
describe something that is neither empty nor everything.

**On integrability, stated because a reader will wonder.** `SobolevWeak`
is written with Lebesgue integrals and carries no integrability
hypothesis, which is the textbook's own phrasing. **The equivalence proved
here does not use one and does not need one**: every step is a pointwise
transformation of integrands closed by `integral_congr_ae`, plus
`integral_neg` and Mathlib's unconditional Gaussian-to-Lebesgue transfer.
So the theorem says what it appears to say whether or not a reader adds
the (true, unproved here) remark that `f ∈ L²(γ)` is locally
square-integrable for Lebesgue.
-/

/-- **The weak derivative is unique**, in the textbook's own formulation —
    inherited from `steinPartner_unique` through the chain. `PoincareSteinClass`
    called `g` "the derivative of `f`" before anything proved uniqueness
    (ERRATA 45); this is that fact, now transported to the space where a
    textbook would state it. -/
theorem sobolevWeak_unique {f g₁ g₂ : ℝ → ℝ} (h₁ : SobolevWeak f g₁)
    (h₂ : SobolevWeak f g₂) : g₁ =ᵐ[gauss] g₂ :=
  steinPartner_ae_eq ((stein_iff_sobolevWeak f g₁).mpr h₁)
    ((stein_iff_sobolevWeak f g₂).mpr h₂)

theorem sobolevWeak_witnesses :
    SobolevWeak (fun x : ℝ => x) (fun _ => 1)
      ∧ SobolevWeak (fun x => |x|) AbsSteinWitness.sgn :=
  ⟨(smoothSteinPair_iff_sobolevWeak _ _).mp SteinSmoothTest.smoothSteinPair_id_one,
    (smoothSteinPair_iff_sobolevWeak _ _).mp SteinSmoothTest.abs_smoothSteinPair⟩

theorem sobolevWeak_proper :
    ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ ¬ ∃ g : ℝ → ℝ, SobolevWeak f g := by
  obtain ⟨f, hf, hns⟩ := HermiteHilbertBasis.exists_memLp_not_steinPair
  exact ⟨f, hf, fun ⟨g, hg⟩ => hns ⟨g, (stein_iff_sobolevWeak f g).mpr hg⟩⟩

end

end TextbookSobolev
