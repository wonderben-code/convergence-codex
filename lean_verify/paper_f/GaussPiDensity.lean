/-
  GaussPiDensity.lean — **stairs N5a and N5b**: the n-dimensional Gaussian
  density, and the one identity the whole `Cc^∞` bridge will rest on.

  WHY BOTH IN ONE FILE, AND WHY THIS FILE EXISTS AT ALL — **CORRECTED
  13 AUGUST, SEE ERRATUM 51.** As first written this header said the file
  existed because Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
  supplies "the hard analytic step of N5" and needs a Haar measure. **That
  attribution was false.** N5 is the `Cc^∞` bridge, and the bridge — in one
  dimension and in n — uses **no integration by parts at all**: it is the
  substitution `φ = ψ/ρ` in one direction and `ψ = φ·ρ` in the other, plus
  the change of measure, twice each. Read `TextbookSobolev.textbookBridge`
  and there is no FTC in it. The symptom was visible here and unnoticed:
  this file imported `LineDeriv.IntegrationByParts` and never used a single
  lemma from it, and it compiles with the import deleted.

  **The two theorems below are the right ones and are unchanged.** They are
  the exact twins of what the 1-d bridge consumes — `integral_gauss` and
  `hasDerivAt_rho` — and the bridge cannot be written without them. Only the
  stated reason was wrong. Where Mathlib's integration by parts is genuinely
  needed is a DIFFERENT and later stair: the n-dimensional analogue of
  `PoincareBeyondPolynomials.stein_general`, which shows that a
  differentiable function of polynomial growth actually IS a Stein pair with
  its gradient. That stair is not on the original staircase and is now on the
  watchlist under its own name.

  What this file builds, and what the bridge consumes:

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

  THE PREDICTION IN THIS HEADER WAS TESTED AND IT FAILED, AND THE FALLBACK IT
  NAMED IS WHAT IS NOW PROVED. As first written, `integral_gaussPi` carried
  two integrability hypotheses that the 1-d `integral_gauss` does not, and
  this header predicted that it would cost nothing downstream because the
  bridge's integrands are `L²` functions against compactly supported test
  functions. **That was wrong, and wrong in a way worth recording:** on the
  Lebesgue side the hypothesis is integrability of `ρₙ·f` against `volume`,
  and the only way to get it from `f ∈ L²(γⁿ)` is the change of measure
  itself. The prediction was circular and I did not see it until the bridge
  refused to typecheck.

  So the identity is now proved where Tonelli needs no hypotheses at all.
  **`lintegral_gaussPi`** does the induction with `∫⁻`; **`gaussPi_eq_withDensity`**
  turns it into the measure identity `γⁿ = volume.withDensity (ofReal ∘ ρₙ)`;
  and `integral_gaussPi` and `integrable_gaussPi_iff` fall out of Mathlib's
  `withDensity` API with NO hypotheses on `f` whatsoever. This is the
  unconditional fallback the earlier header named, and it is strictly
  stronger than what it replaces — `PROOF_STRATEGY` §7 rule 3, removing a
  restrictive hypothesis, arrived at by being forced rather than by
  choosing.

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

namespace GaussPiDensity

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiPeel TextbookSobolev
open scoped NNReal ENNReal

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

/-- **The product rule for a product of ONE-VARIABLE functions, one
    coordinate at a time.** Against `Pi.single i 1` every factor but the
    `i`-th dies, because the `j`-th factor's directional derivative carries
    the `j`-th coordinate of `Pi.single i 1`.

    Stated generally rather than for `ρ` alone: this argument was written
    inline for the density, and the multi-index Hermite recursion
    (`HermitePiStein.Hpi_succ`) needs the identical argument for a product of
    Hermite polynomials. `HermitePiPeel`'s standing lesson — machinery buried
    in a proof is machinery the next person rebuilds — fourth instance. -/
theorem fderiv_coordProd (n : ℕ) (u : Fin n → ℝ → ℝ)
    (hu : ∀ j, Differentiable ℝ (u j)) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => ∏ j, u j (y j)) x (Pi.single i (1:ℝ))
      = deriv (u i) (x i) * ∏ j ∈ Finset.univ.erase i, u j (x j) := by
  have hco : ∀ j : Fin n, HasFDerivAt (fun y : Fin n → ℝ => u j (y j))
      ((deriv (u j) (x j)) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    intro j
    have h := ((hu j) (x j)).hasDerivAt.hasFDerivAt
    have hc := h.comp x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt
    convert hc using 1
    ext v
    simp
    ring
  have hsingle : ∀ j : Fin n,
      fderiv ℝ (fun y : Fin n → ℝ => u j (y j)) x (Pi.single i (1:ℝ))
        = if j = i then deriv (u i) (x i) else 0 := by
    intro j
    rw [(hco j).fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]
  rw [fderiv_finset_prod (fun j _ => (hco j).differentiableAt)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [hsingle, if_pos rfl]
    ring
  · intro j _ hj
    rw [hsingle, if_neg hj, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem rho_differentiable : Differentiable ℝ rho :=
  TextbookSobolev.rho_differentiable

-- `dupname_scan.py` (ERRATUM 271): `rho` is defined once, in `TextbookSobolev`, and this file
-- imports it; the proof here was the same three tokens.
/-- **`∂ᵢρₙ(x) = −xᵢ·ρₙ(x)`.** Stair N5b, now the `u = ρ` instance of
    `fderiv_coordProd`. -/
theorem fderiv_rhoPi (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (rhoPi n) x (Pi.single i (1:ℝ)) = -(x i) * rhoPi n x := by
  have hprod : rhoPi n = fun y : Fin n → ℝ => ∏ j, rho (y j) := rfl
  have hprod' : rhoPi n x = ∏ j, rho (x j) := rfl
  rw [hprod, fderiv_coordProd n (fun _ => rho) (fun _ => rho_differentiable) i x,
    (hasDerivAt_rho (x i)).deriv]
  dsimp only
  rw [← Finset.mul_prod_erase Finset.univ (fun j => rho (x j)) (Finset.mem_univ i)]
  ring

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

/-- The density as an `ℝ≥0`-valued function, which is the shape `withDensity`
    and its integral lemmas want. -/
def rhoPiNN (n : ℕ) (x : Fin n → ℝ) : NNReal := (rhoPi n x).toNNReal

theorem rhoPiNN_coe (n : ℕ) (x : Fin n → ℝ) :
    ((rhoPiNN n x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (rhoPi n x) := rfl

theorem rhoPiNN_toReal (n : ℕ) (x : Fin n → ℝ) : ((rhoPiNN n x : ℝ≥0) : ℝ) = rhoPi n x :=
  Real.coe_toNNReal _ (le_of_lt (rhoPi_pos n x))

theorem measurable_rhoPi (n : ℕ) : Measurable (rhoPi n) :=
  (rhoPi_smooth n).continuous.measurable

theorem measurable_rhoPiNN (n : ℕ) : Measurable (rhoPiNN n) :=
  (measurable_rhoPi n).real_toNNReal

/-- `p ↦ Fin.cons p.1 p.2` is measurable. `fun_prop` has no `Fin.cons`
    theorem, so this is done coordinate by coordinate through `Fin.cases`. -/
theorem measurable_cons (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2 :
      ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simpa using measurable_fst
  · intro j
    simpa using measurable_snd.eval

/-- The one-dimensional lintegral identity, straight off Mathlib's definition
    of `gaussianReal` as a `withDensity`. -/
theorem lintegral_gauss_one {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, h x ∂(gaussianReal 0 1) = ∫⁻ x, ENNReal.ofReal (rho x) * h x := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hh]
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply]
  congr 1

/-- **THE UNCONDITIONAL IDENTITY, at the level where Tonelli needs no
    hypotheses.** This is what replaced an earlier Bochner-level statement
    that carried two integrability hypotheses; see the header. -/
theorem lintegral_gaussPi : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞), Measurable f →
    ∫⁻ x, f x ∂gaussPi n = ∫⁻ x, ENNReal.ofReal (rhoPi n x) * f x := by
  intro n
  induction n with
  | zero =>
    intro f _
    have hgd : gaussPi 0 = Measure.dirac (fun i : Fin 0 => (0:ℝ)) := by
      rw [gaussPi, Measure.pi_of_empty (fun _ : Fin 0 => gaussianReal 0 1)]
      congr 1
      funext i
      exact i.elim0
    have hvd : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (fun i : Fin 0 => (0:ℝ)) := by
      rw [volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ))]
      congr 1
      funext i
      exact i.elim0
    rw [hgd, hvd, lintegral_dirac, lintegral_dirac, rhoPi_zero_dim]
    simp
  | succ n ih =>
    intro f hf
    have hcons : Measurable fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2) :=
      hf.comp (measurable_cons n)
    have hrc : Measurable fun p : ℝ × (Fin n → ℝ) =>
        ENNReal.ofReal (rhoPi (n + 1) (Fin.cons p.1 p.2)) * f (Fin.cons p.1 p.2) :=
      (((measurable_rhoPi (n + 1)).comp (measurable_cons n)).ennreal_ofReal).mul hcons
    -- peel on the Gaussian side
    have hg : ∫⁻ x, f x ∂gaussPi (n + 1)
        = ∫⁻ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
            ∂((gaussianReal 0 1).prod (gaussPi n)) := by
      rw [← (measurePreserving_peel n).lintegral_comp hcons]
      refine lintegral_congr fun z => ?_
      simp only [peel_apply, Fin.cons_self_tail]
    -- peel on the Lebesgue side
    have hv : ∫⁻ x, ENNReal.ofReal (rhoPi (n + 1) x) * f x
        = ∫⁻ p : ℝ × (Fin n → ℝ),
            ENNReal.ofReal (rhoPi (n + 1) (Fin.cons p.1 p.2)) * f (Fin.cons p.1 p.2)
            ∂((volume : Measure ℝ).prod volume) := by
      rw [← (measurePreserving_peel_volume n).lintegral_comp hrc]
      refine lintegral_congr fun z => ?_
      simp only [peel_apply, Fin.cons_self_tail]
    rw [hg, hv, lintegral_prod _ hcons.aemeasurable,
      lintegral_prod _ hrc.aemeasurable]
    rw [lintegral_gauss_one hcons.lintegral_prod_right']
    refine lintegral_congr fun x₀ => ?_
    have hslice : Measurable fun y : Fin n → ℝ => f (Fin.cons x₀ y) :=
      hf.comp ((measurable_cons n).comp (measurable_const.prodMk measurable_id))
    rw [ih _ hslice, ← lintegral_const_mul _ (((measurable_rhoPi n).ennreal_ofReal).mul hslice)]
    refine lintegral_congr fun y => ?_
    rw [rhoPi_cons, ENNReal.ofReal_mul (le_of_lt (rho_pos x₀))]
    ring

/-- **`γⁿ` IS Lebesgue measure weighted by `ρₙ`.** The measure-level identity
    the earlier Bochner statement was a conditional shadow of. -/
theorem gaussPi_eq_withDensity (n : ℕ) :
    gaussPi n = volume.withDensity (fun x => ENNReal.ofReal (rhoPi n x)) := by
  refine Measure.ext fun s hs => ?_
  have h1 : gaussPi n s = ∫⁻ x, s.indicator (fun _ => (1:ℝ≥0∞)) x ∂gaussPi n := by
    rw [lintegral_indicator hs]; simp
  have h2 : (volume.withDensity (fun x => ENNReal.ofReal (rhoPi n x))) s
      = ∫⁻ x, ENNReal.ofReal (rhoPi n x) * s.indicator (fun _ => (1:ℝ≥0∞)) x := by
    rw [withDensity_apply _ hs, ← lintegral_indicator hs]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ s <;> simp [hx]
  rw [h1, h2, lintegral_gaussPi n _ (measurable_const.indicator hs)]

/-- **STAIR N5a, UNCONDITIONALLY: `∫ f dγⁿ = ∫ ρₙ·f dx`**, for EVERY `f`,
    exactly like the one-dimensional `TextbookSobolev.integral_gauss`. -/
theorem integral_gaussPi (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂gaussPi n = ∫ x, rhoPi n x * f x := by
  have hd : (fun x => ENNReal.ofReal (rhoPi n x))
      = fun x => ((rhoPiNN n x : ℝ≥0) : ℝ≥0∞) := rfl
  rw [gaussPi_eq_withDensity n, hd,
    integral_withDensity_eq_integral_smul (measurable_rhoPiNN n) f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [NNReal.smul_def, rhoPiNN_toReal, smul_eq_mul]

/-- And integrability transfers, which is what a consumer needs before it can
    use the identity on a function it only knows is `L²(γⁿ)`. -/
theorem integrable_gaussPi_iff (n : ℕ) {f : (Fin n → ℝ) → ℝ} :
    Integrable f (gaussPi n) ↔ Integrable (fun x => f x * rhoPi n x) volume := by
  rw [gaussPi_eq_withDensity n]
  rw [integrable_withDensity_iff ((measurable_rhoPi n).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  constructor <;> intro h <;>
    refine h.congr (Filter.Eventually.of_forall fun x => ?_) <;>
    dsimp only <;>
    rw [ENNReal.toReal_ofReal (le_of_lt (rhoPi_pos n x))]

end

end GaussPiDensity
