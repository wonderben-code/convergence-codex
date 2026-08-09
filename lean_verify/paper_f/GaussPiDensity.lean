/-
  GaussPiDensity.lean — **stairs N5a and N5b**: the n-dimensional Gaussian
  density, and the one identity the whole `Cc^∞` bridge will rest on.

  WHY BOTH IN ONE FILE, AND WHY THIS FILE EXISTS AT ALL. The 12 August probe
  of N5 found that Mathlib supplies the hard analytic step —
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, integration by parts
  in a finite-dimensional real vector space, in exactly the directional form
  `fderiv ℝ g x v` that `v = Pi.single i 1` turns into the i-th partial
  derivative. But that theorem needs an **additive Haar measure**, and
  `gaussPi n` is not one. So the bridge must go through Lebesgue, and this
  file builds the two things that conversion needs:

  * **`integral_gaussPi`** (N5a) — `∫ f dγⁿ = ∫ ρₙ·f dx`. The n-dimensional
    twin of the estate's one-dimensional `TextbookSobolev.integral_gauss`.
  * **`fderiv_rhoPi`** (N5b) — `∂ᵢρₙ(x) = −xᵢ·ρₙ(x)`, in the
    `fderiv ℝ _ x (Pi.single i 1)` spelling the Mathlib theorem consumes.
    In one dimension the whole substitution rested on `ρ′ = −x·ρ`; here it
    rests on this, one coordinate at a time.

  THE MEASURE IDENTITY IS NOT FREE, AND THE PROBE SAID SO WRONGLY BY
  OMISSION. The watchlist's N5a said "the 1-d twin is `integral_gauss`",
  which is true and made it sound like a restatement. It is an induction on
  the dimension: the estate's `measurePreserving_peel` on the Gaussian side,
  Mathlib's `volume_pi` and the SAME peel on the Lebesgue side, and the 1-d
  identity applied to the inner integral at each step. **Three negative
  probes are behind that**: Mathlib has no `Measure.pi`/`withDensity`
  interaction, no Radon–Nikodym derivative of a `Measure.pi`, and no product
  formula for `lintegral` over a pi type — searched by SHAPE in
  `MeasureTheory/Constructions/Pi.lean` and `MeasureTheory/Measure/Prod.lean`.
  Had any of the three existed the identity would have been three lines.

  AND IT CARRIES AN INTEGRABILITY HYPOTHESIS, WHICH THE 1-d VERSION DOES NOT.
  `integral_gauss` is unconditional because
  `integral_gaussianReal_eq_integral_smul` is. The induction here goes
  through Fubini, which is not. That is a real difference from the 1-d file
  and it is stated rather than hidden. **My expectation is that it costs
  nothing** — the bridge's integrands are `L²` functions against compactly
  supported smooth test functions, so integrability is available on both
  sides — **but that is a PREDICTION about a file that does not exist yet,
  and this estate labels those.** If it turns out to bite, the fix is the
  unconditional measure-level identity
  `gaussPi n = volume.withDensity (ENNReal.ofReal ∘ rhoPi n)`, which the
  three negative probes above say would have to be proved from
  `Measure.pi_eq` by hand.

  WHAT THIS DOES NOT DO. It is not the bridge. N5c — that `ψ ↦ ψ/ρₙ`
  preserves `Cc^∞` and satisfies `xᵢ(ψ/ρₙ) − ∂ᵢ(ψ/ρₙ) = −(∂ᵢψ)/ρₙ` — and
  N5d, the assembly, are not here. Nor is the DEFINITION of the
  n-dimensional smooth Stein pairing, whose partner is a GRADIENT indexed by
  the coordinate rather than a single function.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiPeel
import TextbookSobolev
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace GaussPiDensity

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiPeel TextbookSobolev

noncomputable section

/-! ## 1. The density -/

/-- The n-dimensional standard Gaussian density, `ρₙ(x) = ∏ᵢ ρ(xᵢ)`. -/
def rhoPi (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, rho (x i)

theorem rhoPi_pos (n : ℕ) (x : Fin n → ℝ) : 0 < rhoPi n x :=
  Finset.prod_pos fun i _ => rho_pos (x i)

theorem rhoPi_ne_zero (n : ℕ) (x : Fin n → ℝ) : rhoPi n x ≠ 0 := ne_of_gt (rhoPi_pos n x)

theorem rhoPi_zero_dim (x : Fin 0 → ℝ) : rhoPi 0 x = 1 := by simp [rhoPi]

/-- Each coordinate factor is smooth, which is all `contDiff_prod` needs. -/
theorem rho_coord_smooth (n : ℕ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Fin n → ℝ => rho (x i) :=
  rho_smooth.comp (contDiff_apply ℝ ℝ i)

theorem rhoPi_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rhoPi n) :=
  contDiff_prod fun i _ => rho_coord_smooth n i

theorem rhoPi_differentiable (n : ℕ) (x : Fin n → ℝ) :
    DifferentiableAt ℝ (rhoPi n) x :=
  ((rhoPi_smooth n).differentiable (by simp)).differentiableAt

/-! ## 2. N5b: the partial derivatives of the density

`ρ′ = −x·ρ` is the estate's `hasDerivAt_rho`. Against the direction
`Pi.single i 1` the finite-product rule kills every factor but the `i`-th,
because the `j`-th factor's derivative in that direction is `ρ′(xⱼ)` times
the `j`-th coordinate of `Pi.single i 1`, which is zero unless `j = i`.
-/

theorem hasFDerivAt_rho_coord (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => rho (y i))
      ((-(x i) * rho (x i)) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have h := (hasDerivAt_rho (x i)).hasFDerivAt
  have := h.comp x (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
  convert this using 1
  ext v
  simp
  ring

theorem fderiv_rho_coord_single (n : ℕ) (i j : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => rho (y j)) x (Pi.single i (1:ℝ))
      = if j = i then -(x i) * rho (x i) else 0 := by
  rw [(hasFDerivAt_rho_coord n j x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp
  · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]

/-- **`∂ᵢρₙ(x) = −xᵢ·ρₙ(x)`.** Stair N5b, in the spelling Mathlib's
    integration-by-parts theorem consumes. -/
theorem fderiv_rhoPi (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (rhoPi n) x (Pi.single i (1:ℝ)) = -(x i) * rhoPi n x := by
  have hdiff : ∀ j ∈ Finset.univ, DifferentiableAt ℝ (fun y : Fin n → ℝ => rho (y j)) x :=
    fun j _ => (hasFDerivAt_rho_coord n j x).differentiableAt
  have hprod : rhoPi n = fun y : Fin n → ℝ => ∏ j ∈ Finset.univ, rho (y j) := rfl
  rw [hprod, fderiv_finset_prod hdiff]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [fderiv_rho_coord_single, if_pos rfl]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => rho (x j)) (Finset.mem_univ i)]
    ring
  · intro j _ hj
    rw [fderiv_rho_coord_single, if_neg hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## 3. N5a: the measure identity

An induction on the dimension. Both measures peel the same way — the
estate's `measurePreserving_peel` on the Gaussian side, and the same
equivalence on the Lebesgue side because `volume` on a pi type IS the pi of
`volume` (`volume_pi`) — and the one-dimensional `integral_gauss` handles the
coordinate that comes off.
-/

/-- The Lebesgue twin of `measurePreserving_peel`. -/
theorem measurePreserving_peel_volume (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
  rwa [← volume_pi, ← volume_pi] at h

theorem integral_peel_volume (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((volume : Measure ℝ).prod volume)
      = ∫ z, f z := by
  rw [← (measurePreserving_peel_volume n).integral_comp
    (MeasurableEquiv.measurableEmbedding _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [peel_apply, Fin.cons_self_tail]

theorem integrable_peel_volume (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f (volume : Measure (Fin (n + 1) → ℝ))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume : Measure ℝ).prod volume) := by
  rw [← (measurePreserving_peel_volume n).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  have hcomp : ((fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)) = f := by
    funext z
    simp only [Function.comp_apply, peel_apply, Fin.cons_self_tail]
  rw [hcomp]
  exact hf

/-- The density factorises along the peel, which is what makes the induction
    close. -/
theorem rhoPi_cons (n : ℕ) (x₀ : ℝ) (y : Fin n → ℝ) :
    rhoPi (n + 1) (Fin.cons x₀ y) = rho x₀ * rhoPi n y := by
  rw [rhoPi, rhoPi, Fin.prod_univ_succ, Fin.cons_zero]
  rfl

/-- **STAIR N5a: `∫ f dγⁿ = ∫ ρₙ·f dx`.** The n-dimensional twin of
    `TextbookSobolev.integral_gauss`, with the integrability hypothesis the
    1-d version does not need. -/
theorem integral_gaussPi : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    Integrable f (gaussPi n) → Integrable (fun x => rhoPi n x * f x) volume →
    ∫ x, f x ∂gaussPi n = ∫ x, rhoPi n x * f x := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    have hg : ∀ x : Fin 0 → ℝ, f x = f 0 := by
      intro x; congr 1; funext i; exact i.elim0
    have hr : ∀ x : Fin 0 → ℝ, rhoPi 0 x * f x = f 0 := by
      intro x; rw [rhoPi_zero_dim, one_mul, hg x]
    rw [integral_congr_ae (Filter.Eventually.of_forall hg),
      integral_congr_ae (Filter.Eventually.of_forall hr), integral_const, integral_const]
    have h1 : (gaussPi 0).real Set.univ = 1 := by rw [probReal_univ]
    have h2 : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
      rw [measureReal_def, volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ))]
      simp
    rw [h1, h2]
  | succ n ih =>
    intro f hf hrf
    -- both slice-integrabilities, transported to a.e. against LEBESGUE, which is
    -- the filter the right-hand side's outer integral runs over
    have hac : (volume : Measure ℝ) ≪ gaussianReal 0 1 :=
      gaussianReal_absolutelyContinuous' 0 one_ne_zero
    have hsl : ∀ᵐ x₀ ∂(volume : Measure ℝ),
        Integrable (fun y => f (Fin.cons x₀ y)) (gaussPi n) :=
      hac.ae_le (integrable_slice n hf)
    have hslv : ∀ᵐ x₀ ∂(volume : Measure ℝ),
        Integrable (fun y => rhoPi (n + 1) (Fin.cons x₀ y) * f (Fin.cons x₀ y))
          (volume : Measure (Fin n → ℝ)) :=
      (integrable_peel_volume n hrf).prod_right_ae
    -- the inductive hypothesis, applied inside, one slice at a time
    have hinner : ∀ᵐ x₀ ∂(volume : Measure ℝ),
        rho x₀ * (∫ y, f (Fin.cons x₀ y) ∂gaussPi n)
          = ∫ y, rhoPi (n + 1) (Fin.cons x₀ y) * f (Fin.cons x₀ y) := by
      filter_upwards [hsl, hslv] with x₀ h1 h2
      have hc : (fun y : Fin n → ℝ => rhoPi (n + 1) (Fin.cons x₀ y) * f (Fin.cons x₀ y))
          = fun y => rho x₀ * (rhoPi n y * f (Fin.cons x₀ y)) := by
        funext y
        rw [rhoPi_cons]
        ring
      rw [hc] at h2
      have h2' : Integrable (fun y : Fin n → ℝ => rhoPi n y * f (Fin.cons x₀ y)) volume := by
        refine (h2.const_mul (rho x₀)⁻¹).congr (Filter.Eventually.of_forall fun y => ?_)
        exact inv_mul_cancel_left₀ (rho_ne_zero x₀) _
      rw [ih _ h1 h2', ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [rhoPi_cons]
      ring
    rw [integral_peel_fubini n hf, integral_gauss,
      ← integral_peel_volume n (fun z => rhoPi (n + 1) z * f z),
      integral_prod _ (integrable_peel_volume n hrf)]
    exact integral_congr_ae hinner

end

end GaussPiDensity
