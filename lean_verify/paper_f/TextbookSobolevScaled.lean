/-
  TextbookSobolevScaled.lean — the σ = 1 restriction removed.

  WHY. Re-sweep #4 named this as the smallest open item on the watchlist,
  and the reason it is an item at all is a phrase: `TextbookSobolev` says
  "the textbook Gaussian Sobolev space", and every bridge in it was written
  at σ = 1. `PoincareSteinScaled` has proved the Stein-class inequality at
  EVERY variance since 2 August, with the σ² constant sharp — so the estate
  could say "every variance" about its own class and "the textbook space"
  about the standard Gaussian, and those two sentences sit two files apart.
  This closes the gap.

  WHAT THIS FILE PROVES:
  1. **`steinPairScaled_ofStd`** — the converse of the estate's
     `steinPairScaled_toStd`, so the transport of the Stein class along
     `x ↦ σx` is a BICONDITIONAL. That was the missing half.
  2. **`smoothSteinPairScaled_iff`** — the same transport for the Cc^∞
     class. The test function goes along too: `φ ↦ φ(σ·)` is a bijection
     of `Cc^∞`, and the derivative picks up the factor of `σ` that makes
     the two pairings correspond.
  3. **`steinPairScaled_iff_smooth`** — hence **the σ-analogue of W6**: at
     every variance, polynomial testing and `Cc^∞` testing define the same
     class.
  4. **`steinPairScaled_iff_sobolevWeakScaled`** — and the textbook form,
     with LEBESGUE weak derivatives against the σ-density. The density
     argument is `TextbookSobolev`'s, re-run with `ρ_σ′ = −(x/σ²)·ρ_σ`.
  5. **`poincare_sobolevWeakScaled`** — the Gaussian Poincaré inequality on
     the textbook Gaussian Sobolev space **at every variance**, constant
     `σ²`, proved sharp.

  WHAT IT COSTS, recorded because I estimated it a few hours ago and the
  rule is that estimates get checked against outcomes (ERRATA 43).
  Re-sweep #4 called this "routine, and the smallest open item on this
  list". **Routine it is. Small it is not**: 480 lines, because every
  statement needs its own change of variables and σ < 0 is carried rather
  than assumed away — `gaussSc σ` depends on σ², so σ and −σ give the same
  measure and the transport is still a bijection, but none of the algebra
  simplifies. "Smallest on the list" may well still be right, since the
  other open item is the n-dimensional build. What the phrase invited was
  the reading *quick*, and that reading was wrong. **A difficulty estimate
  should name the kind of work and the amount separately**, because a
  reader merges them and the merge is where the error lives.

  ONE DRAFTING ERROR, caught before commit and recorded rather than
  quietly fixed. The first version of this header named three theorems —
  `smoothSteinPairScaled_iff`, `steinPairScaled_iff_sobolevWeakScaled`,
  `poincare_sobolevWeakScaled` — that the file did not contain: I had
  written the `Cc^∞` half and stopped. That is ERRATUM 44's shape (a
  commit message naming files it did not touch) transplanted into a
  docstring, and it is worth saying that the thing which caught it was
  reading the header against the file rather than any tactic failing.
  **Folded back by writing the three theorems**, not by editing the list.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import TextbookSobolev
import PoincareSteinScaled

namespace TextbookSobolevScaled

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass PoincareSteinScaled SteinSmoothTest W6Converse TextbookSobolev

noncomputable section

/-! ## 1. The σ-rescaling of a test function -/

/-- `φ ↦ φ(σ·)`. -/
def scal (σ : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun y => φ (σ * y)

theorem scal_smooth {σ : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (scal σ φ) :=
  hφ.comp (contDiff_const.mul contDiff_id)

theorem scal_support {σ : ℝ} (hσ : σ ≠ 0) {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (scal σ φ) := by
  have h := hc.comp_smul (c := σ) hσ
  have heq : (fun y : ℝ => φ (σ • y)) = scal σ φ := by
    funext y; simp [scal, smul_eq_mul]
  rwa [heq] at h

theorem deriv_scal {σ : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : ℝ) :
    deriv (scal σ φ) y = σ * deriv φ (σ * y) := by
  have hd : HasDerivAt φ (deriv φ (σ * y)) (σ * y) :=
    (hφ.differentiable (by simp) (σ * y)).hasDerivAt
  have hinner : HasDerivAt (fun z : ℝ => σ * z) σ y := by
    simpa using (hasDerivAt_id y).const_mul σ
  have h := hd.comp y hinner
  have heq : φ ∘ (fun z : ℝ => σ * z) = scal σ φ := rfl
  rw [heq] at h
  rw [h.deriv]
  ring

/-- The inverse rescaling, so `scal σ` is a bijection of `Cc^∞`. -/
theorem scal_scal_inv {σ : ℝ} (hσ : σ ≠ 0) (φ : ℝ → ℝ) :
    scal σ (scal σ⁻¹ φ) = φ := by
  funext y
  simp only [scal]
  rw [show σ⁻¹ * (σ * y) = y by field_simp]

/-! ## 2. The Cc^∞ class at variance σ², and its transport -/

/-- The Cc^∞-tested σ-Gaussian pairing. -/
def SmoothSteinPairScaled (σ : ℝ) (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 (gaussSc σ) ∧ MemLp g 2 (gaussSc σ) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, f x * (x * φ x / σ ^ 2 - deriv φ x) ∂gaussSc σ
        = ∫ x, g x * φ x ∂gaussSc σ

/-- The transported pair. -/
def trF (σ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (σ * x)

/-- The transported partner, carrying the chain-rule factor. -/
def trG (σ : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := fun x => σ * g (σ * x)

theorem integral_transfer {σ : ℝ} (h : ℝ → ℝ)
    (hm : AEStronglyMeasurable h (gaussSc σ)) :
    ∫ x, h x ∂gaussSc σ = ∫ x, h (σ * x) ∂gauss :=
  integral_scaled_ae σ h hm

/-- **The Cc^∞ pairing transports.** One direction; the other follows by
    running it at `σ⁻¹`, which `smoothSteinPairScaled_iff` does. -/
theorem smoothSteinPair_of_scaled {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (h : SmoothSteinPairScaled σ f g) :
    SmoothSteinPair (trF σ f) (trG σ g) := by
  obtain ⟨hf, hg, hpair⟩ := h
  refine ⟨memLp_comp_scaled σ hf, (memLp_comp_scaled σ hg).const_mul σ, ?_⟩
  intro ϕ hϕ hcϕ
  -- test the σ-pairing against `φ = ϕ(σ⁻¹ ·)`
  set φ : ℝ → ℝ := scal σ⁻¹ ϕ with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := scal_smooth hϕ
  have hcφ : HasCompactSupport φ := scal_support (inv_ne_zero hσ) hcϕ
  have hp := hpair φ hφ hcφ
  have hinv : ∀ x : ℝ, σ⁻¹ * (σ * x) = x := fun x => by field_simp
  -- the left side
  have hL : ∫ x, f x * (x * φ x / σ ^ 2 - deriv φ x) ∂gaussSc σ
      = σ⁻¹ * ∫ y, trF σ f y * (y * ϕ y - deriv ϕ y) ∂gauss := by
    rw [integral_transfer (fun x => f x * (x * φ x / σ ^ 2 - deriv φ x))
      (hf.aestronglyMeasurable.mul (by
        have hc1 : Continuous fun x : ℝ => x * φ x / σ ^ 2 - deriv φ x :=
          ((continuous_id.mul hφ.continuous).div_const _).sub
            ((hφ.of_le (by exact_mod_cast le_top)).continuous_deriv_one)
        exact hc1.aestronglyMeasurable)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h1 : φ (σ * y) = ϕ y := by rw [hφdef]; simp [scal, hinv y]
    have h2 : deriv φ (σ * y) = σ⁻¹ * deriv ϕ y := by
      have hds := deriv_scal (σ := σ⁻¹) hϕ (σ * y)
      rw [hφdef, hds, hinv y]
    dsimp only
    rw [h1, h2]
    simp only [trF]
    field_simp
  -- the right side
  have hR : ∫ x, g x * φ x ∂gaussSc σ
      = σ⁻¹ * ∫ y, trG σ g y * ϕ y ∂gauss := by
    rw [integral_transfer (fun x => g x * φ x) (hg.aestronglyMeasurable.mul
      hφ.continuous.aestronglyMeasurable), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h1 : φ (σ * y) = ϕ y := by rw [hφdef]; simp [scal, hinv y]
    dsimp only
    rw [h1]
    simp only [trG]
    field_simp
  rw [hL, hR] at hp
  exact mul_left_cancel₀ (inv_ne_zero hσ) hp

/-! ## 3. The Stein class transports both ways -/

/-- **The converse of the estate's `steinPairScaled_toStd`.** -/
theorem steinPairScaled_ofStd {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ))
    (h : SteinPair (trF σ f) (trG σ g)) :
    SteinPairScaled σ f g := by
  refine ⟨hf, hg, fun r => ?_⟩
  obtain ⟨-, -, hpair⟩ := h
  set q : ℝ[X] := r.comp (Polynomial.C σ * Polynomial.X) with hqdef
  have hqeval : ∀ y : ℝ, q.eval y = r.eval (σ * y) := fun y => by
    simp [hqdef, Polynomial.eval_comp]
  have hqderiv : ∀ y : ℝ, (derivative q).eval y
      = σ * (derivative r).eval (σ * y) := fun y => by
    simp [hqdef, Polynomial.derivative_comp]
  have hp := hpair q
  have hL : ∫ y, trG σ g y * q.eval y ∂gauss
      = σ * ∫ x, g x * r.eval x ∂gaussSc σ := by
    rw [integral_transfer (fun x => g x * r.eval x)
      (hg.aestronglyMeasurable.mul (Polynomial.continuous r).aestronglyMeasurable),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hqeval]
    simp only [trG]
    ring
  have hR : ∫ y, trF σ f y * (X * q - derivative q).eval y ∂gauss
      = σ * ∫ x, f x * (x * r.eval x / σ ^ 2 - (derivative r).eval x) ∂gaussSc σ := by
    rw [integral_transfer (fun x => f x * (x * r.eval x / σ ^ 2
        - (derivative r).eval x))
      (hf.aestronglyMeasurable.mul (by fun_prop)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, trF]
    rw [hqeval, hqderiv]
    field_simp
  rw [hL, hR] at hp
  exact mul_left_cancel₀ hσ hp

theorem steinPairScaled_iff_std {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SteinPairScaled σ f g ↔ SteinPair (trF σ f) (trG σ g) :=
  ⟨steinPairScaled_toStd hσ, steinPairScaled_ofStd hσ hf hg⟩

/-! ## 4. The σ-analogue of W6 -/

/-- The Cc^∞ side, back from the standard case. -/
theorem smoothSteinPairScaled_of_std {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ))
    (h : SmoothSteinPair (trF σ f) (trG σ g)) :
    SmoothSteinPairScaled σ f g := by
  refine ⟨hf, hg, fun φ hφ hcφ => ?_⟩
  obtain ⟨-, -, hpair⟩ := h
  set ϕ : ℝ → ℝ := scal σ φ with hϕdef
  have hϕ : ContDiff ℝ (⊤ : ℕ∞) ϕ := scal_smooth hφ
  have hcϕ : HasCompactSupport ϕ := scal_support hσ hcφ
  have hp := hpair ϕ hϕ hcϕ
  have hL : ∫ y, trF σ f y * (y * ϕ y - deriv ϕ y) ∂gauss
      = σ * ∫ x, f x * (x * φ x / σ ^ 2 - deriv φ x) ∂gaussSc σ := by
    rw [integral_transfer (fun x => f x * (x * φ x / σ ^ 2 - deriv φ x))
      (hf.aestronglyMeasurable.mul (by
        have hc1 : Continuous fun x : ℝ => x * φ x / σ ^ 2 - deriv φ x :=
          ((continuous_id.mul hφ.continuous).div_const _).sub
            ((hφ.of_le (by exact_mod_cast le_top)).continuous_deriv_one)
        exact hc1.aestronglyMeasurable)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [trF, hϕdef, scal]
    rw [deriv_scal hφ y]
    field_simp
  have hR : ∫ y, trG σ g y * ϕ y ∂gauss = σ * ∫ x, g x * φ x ∂gaussSc σ := by
    rw [integral_transfer (fun x => g x * φ x)
      (hg.aestronglyMeasurable.mul hφ.continuous.aestronglyMeasurable),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [trG, hϕdef, scal]
    ring
  rw [hL, hR] at hp
  exact mul_left_cancel₀ hσ hp

/-- **THE σ-ANALOGUE OF W6.** At every nonzero variance, testing the
    Gaussian integration-by-parts pairing against polynomials and testing
    it against `Cc^∞` define the same class. -/
theorem steinPairScaled_iff_smooth {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SteinPairScaled σ f g ↔ SmoothSteinPairScaled σ f g := by
  rw [steinPairScaled_iff_std hσ hf hg]
  constructor
  · intro h
    exact smoothSteinPairScaled_of_std hσ hf hg (smoothSteinPair_of_steinPair h)
  · intro h
    exact steinPair_of_smoothSteinPair (smoothSteinPair_of_scaled hσ h)

/-- **The Cc^∞ transport, as a biconditional.** -/
theorem smoothSteinPairScaled_iff {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SmoothSteinPairScaled σ f g ↔ SmoothSteinPair (trF σ f) (trG σ g) :=
  ⟨smoothSteinPair_of_scaled hσ, smoothSteinPairScaled_of_std hσ hf hg⟩

/-! ## 4b. The Lebesgue form at variance σ²

The density argument of `TextbookSobolev`, re-run with `ρ_σ`. The only
change is the identity everything rests on: `ρ_σ′ = −(x/σ²)·ρ_σ`.
-/

/-- The σ-Gaussian density. -/
def rhoSc (σ : ℝ) (x : ℝ) : ℝ := gaussianPDFReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ x

theorem nnreal_sq_ne_zero {σ : ℝ} (hσ : σ ≠ 0) :
    (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) ≠ 0 := by
  intro hcon
  have : σ ^ 2 = 0 := congrArg NNReal.toReal hcon
  exact hσ (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

theorem rhoSc_eq {σ : ℝ} (x : ℝ) :
    rhoSc σ x = (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-x ^ 2 / (2 * σ ^ 2)) := by
  rw [rhoSc, gaussianPDFReal_def]
  norm_num

theorem rhoSc_pos {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) : 0 < rhoSc σ x :=
  gaussianPDFReal_pos 0 _ x (nnreal_sq_ne_zero hσ)

theorem rhoSc_ne_zero {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) : rhoSc σ x ≠ 0 :=
  ne_of_gt (rhoSc_pos hσ x)

theorem rhoSc_funext (σ : ℝ) : rhoSc σ
    = fun y : ℝ => (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-y ^ 2 / (2 * σ ^ 2)) :=
  funext (rhoSc_eq)

theorem rhoSc_smooth (σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rhoSc σ) := by
  rw [rhoSc_funext]
  exact contDiff_const.mul
    (Real.contDiff_exp.comp (((contDiff_id.pow 2).neg).div_const _))

/-- **`ρ_σ′ = −(x/σ²)·ρ_σ`.** -/
theorem hasDerivAt_rhoSc {σ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    HasDerivAt (rhoSc σ) (-(x / σ ^ 2) * rhoSc σ x) x := by
  have hs2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hq : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * σ ^ 2)) (-(x / σ ^ 2)) x := by
    have h : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * σ ^ 2))
        (-(2 * x ^ 1) / (2 * σ ^ 2)) x := ((hasDerivAt_pow 2 x).neg).div_const _
    convert h using 1
    field_simp
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / (2 * σ ^ 2)))
      (Real.exp (-x ^ 2 / (2 * σ ^ 2)) * (-(x / σ ^ 2))) x := by
    simpa [Function.comp] using
      (Real.hasDerivAt_exp (-x ^ 2 / (2 * σ ^ 2))).comp x hq
  have hc := he.const_mul ((Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹)
  have hfin : HasDerivAt (rhoSc σ)
      ((Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹
        * (Real.exp (-x ^ 2 / (2 * σ ^ 2)) * (-(x / σ ^ 2)))) x := by
    rw [rhoSc_funext]; exact hc
  convert hfin using 1
  rw [rhoSc_eq]
  ring

theorem integral_gaussSc {σ : ℝ} (hσ : σ ≠ 0) (F : ℝ → ℝ) :
    ∫ x, F x ∂gaussSc σ = ∫ x, rhoSc σ x * F x := by
  rw [show (gaussSc σ : Measure ℝ) = gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ from rfl,
    integral_gaussianReal_eq_integral_smul (nnreal_sq_ne_zero hσ)]
  simp [rhoSc, smul_eq_mul]

/-- The textbook-defined Gaussian Sobolev pairing at variance σ². -/
def SobolevWeakScaled (σ : ℝ) (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 (gaussSc σ) ∧ MemLp g 2 (gaussSc σ) ∧
    ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, f x * deriv ψ x = -∫ x, g x * ψ x

theorem deriv_mulRhoSc {σ : ℝ} (hσ : σ ≠ 0) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ) :
    deriv (fun y => φ y * rhoSc σ y) x
      = (deriv φ x - x * φ x / σ ^ 2) * rhoSc σ x := by
  have hd : HasDerivAt φ (deriv φ x) x := (hφ.differentiable (by simp) x).hasDerivAt
  have h := hd.mul (hasDerivAt_rhoSc hσ x)
  have hderiv : deriv (fun y => φ y * rhoSc σ y) x
      = deriv φ x * rhoSc σ x + φ x * (-(x / σ ^ 2) * rhoSc σ x) := h.deriv
  rw [hderiv]
  ring

theorem deriv_divRhoSc {σ : ℝ} (hσ : σ ≠ 0) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : ℝ) :
    deriv (fun y => ψ y / rhoSc σ y) x
      = (deriv ψ x + x * ψ x / σ ^ 2) / rhoSc σ x := by
  have hd : HasDerivAt ψ (deriv ψ x) x := (hψ.differentiable (by simp) x).hasDerivAt
  have h := hd.div (hasDerivAt_rhoSc hσ x) (rhoSc_ne_zero hσ x)
  have hderiv : deriv (fun y => ψ y / rhoSc σ y) x
      = (deriv ψ x * rhoSc σ x - ψ x * (-(x / σ ^ 2) * rhoSc σ x)) / rhoSc σ x ^ 2 :=
    h.deriv
  rw [hderiv]
  have hne := rhoSc_ne_zero hσ x
  field_simp
  ring

theorem support_divRhoSc {σ : ℝ} (hσ : σ ≠ 0) (ψ : ℝ → ℝ) :
    Function.support (fun x => ψ x / rhoSc σ x) = Function.support ψ := by
  ext x
  simp [Function.mem_support, rhoSc_ne_zero hσ x]

theorem divRhoSc_support {σ : ℝ} (hσ : σ ≠ 0) {ψ : ℝ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport fun x => ψ x / rhoSc σ x := by
  unfold HasCompactSupport tsupport at hc ⊢
  rwa [support_divRhoSc hσ]

/-- **The σ-textbook bridge.** -/
theorem smoothSteinPairScaled_iff_sobolevWeakScaled {σ : ℝ} (hσ : σ ≠ 0)
    {f g : ℝ → ℝ} (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SmoothSteinPairScaled σ f g ↔ SobolevWeakScaled σ f g := by
  have hs2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  constructor
  · rintro ⟨-, -, hpair⟩
    refine ⟨hf, hg, fun ψ hψ hcψ => ?_⟩
    have h := hpair (fun x => ψ x / rhoSc σ x)
      (hψ.div (rhoSc_smooth σ) (rhoSc_ne_zero hσ)) (divRhoSc_support hσ hcψ)
    rw [integral_gaussSc hσ, integral_gaussSc hσ] at h
    have hL : (∫ x, rhoSc σ x * (f x * (x * (ψ x / rhoSc σ x) / σ ^ 2
        - deriv (fun y => ψ y / rhoSc σ y) x))) = -∫ x, f x * deriv ψ x := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_divRhoSc hσ hψ]
      have hne := rhoSc_ne_zero hσ x
      field_simp
      ring
    have hR : (∫ x, rhoSc σ x * (g x * (ψ x / rhoSc σ x))) = ∫ x, g x * ψ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have hne := rhoSc_ne_zero hσ x
      field_simp
    rw [hL, hR] at h
    linarith [h]
  · rintro ⟨-, -, hweak⟩
    refine ⟨hf, hg, fun φ hφ hcφ => ?_⟩
    have h := hweak (fun x => φ x * rhoSc σ x) (hφ.mul (rhoSc_smooth σ)) hcφ.mul_right
    rw [integral_gaussSc hσ, integral_gaussSc hσ]
    have hL : (∫ x, f x * deriv (fun y => φ y * rhoSc σ y) x)
        = -∫ x, rhoSc σ x * (f x * (x * φ x / σ ^ 2 - deriv φ x)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [deriv_mulRhoSc hσ hφ]
      ring
    have hR : (∫ x, g x * (φ x * rhoSc σ x)) = ∫ x, rhoSc σ x * (g x * φ x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [hL, hR] at h
    linarith [h]

/-- **THE σ-ANALOGUE OF W6, IN THE TEXTBOOK'S OWN WORDS.** -/
theorem steinPairScaled_iff_sobolevWeakScaled {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SteinPairScaled σ f g ↔ SobolevWeakScaled σ f g :=
  (steinPairScaled_iff_smooth hσ hf hg).trans
    (smoothSteinPairScaled_iff_sobolevWeakScaled hσ hf hg)

/-! ## 5. Poincaré on the σ-textbook class

The inequality at every variance was proved on 2 August for the POLYNOMIAL
class. With §4 it holds on the `Cc^∞` class, which is the statement a
reader would recognise.
-/

/-- **THE GAUSSIAN POINCARÉ INEQUALITY ON THE Cc^∞-DEFINED SOBOLEV CLASS,
    AT EVERY VARIANCE.** -/
theorem poincare_smoothScaled {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (h : SmoothSteinPairScaled σ f g) :
    (∫ x, f x ^ 2 ∂gaussSc σ) - (∫ x, f x ∂gaussSc σ) ^ 2
      ≤ σ ^ 2 * ∫ x, g x ^ 2 ∂gaussSc σ :=
  poincare_stein_scaled σ ((steinPairScaled_iff_smooth hσ h.1 h.2.1).mpr h)

/-- Sharp at `(X, 1)`: the variance is exactly `σ²` and `∫1² = 1`. -/
theorem poincare_smoothScaled_sharp {σ : ℝ} (hσ : σ ≠ 0) :
    SmoothSteinPairScaled σ (fun x => x) (fun _ => 1)
      ∧ (∫ x, x ^ 2 ∂gaussSc σ) - (∫ x, x ∂gaussSc σ) ^ 2 = σ ^ 2 :=
  ⟨(steinPairScaled_iff_smooth hσ (steinPairScaled_id_one hσ).1
      (steinPairScaled_id_one hσ).2.1).mp (steinPairScaled_id_one hσ),
    var_id_scaled σ⟩

/-! ## 5b. Coefficients and uniqueness at every variance

Without these the σ story is lopsided: the estate would have the
inequality at every variance and the coefficient description and the
uniqueness of the derivative only at σ = 1, which is the same asymmetry
this file was written to remove.
-/

/-- **The coefficient characterisation at variance σ².** Stated about the
    transported pair, which is what the transport makes available without
    building a σ-Hermite system. -/
theorem steinPairScaled_iff_coeff {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SteinPairScaled σ f g ↔
      ∀ n : ℕ, HermiteBessel.coeff n (trG σ g)
        = (n + 1 : ℝ) * HermiteBessel.coeff (n + 1) (trF σ f) := by
  rw [steinPairScaled_iff_std hσ hf hg]
  exact SteinCoefficients.steinPair_iff_coeff (memLp_comp_scaled σ hf)
    ((memLp_comp_scaled σ hg).const_mul σ)

/-- The same in the textbook's language. -/
theorem sobolevWeakScaled_iff_coeff {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (gaussSc σ)) (hg : MemLp g 2 (gaussSc σ)) :
    SobolevWeakScaled σ f g ↔
      ∀ n : ℕ, HermiteBessel.coeff n (trG σ g)
        = (n + 1 : ℝ) * HermiteBessel.coeff (n + 1) (trF σ f) :=
  (steinPairScaled_iff_sobolevWeakScaled hσ hf hg).symm.trans
    (steinPairScaled_iff_coeff hσ hf hg)

/-- **The Sobolev summability is necessary at every variance.** -/
theorem summable_sobolev_scaled {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (h : SobolevWeakScaled σ f g) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ)
      * HermiteBessel.coeff n (trF σ f) ^ 2 :=
  SteinCoefficients.summable_sobolev_of_steinPair
    (steinPairScaled_toStd hσ ((steinPairScaled_iff_sobolevWeakScaled hσ h.1 h.2.1).mpr h))

/-- **The weak derivative is unique at every variance.** Proved through
    the integral rather than through an a.e. transport: the transported
    partners agree in L², the change of variables carries the integral of
    the squared difference across with a factor of σ², and σ ≠ 0 finishes. -/
theorem sobolevWeakScaled_unique {σ : ℝ} (hσ : σ ≠ 0) {f g₁ g₂ : ℝ → ℝ}
    (h₁ : SobolevWeakScaled σ f g₁) (h₂ : SobolevWeakScaled σ f g₂) :
    g₁ =ᵐ[gaussSc σ] g₂ := by
  have hs₁ := steinPairScaled_toStd hσ
    ((steinPairScaled_iff_sobolevWeakScaled hσ h₁.1 h₁.2.1).mpr h₁)
  have hs₂ := steinPairScaled_toStd hσ
    ((steinPairScaled_iff_sobolevWeakScaled hσ h₂.1 h₂.2.1).mpr h₂)
  have hzero := SteinCoefficients.steinPartner_unique hs₁ hs₂
  -- transport the vanishing integral back
  have hmeas : AEStronglyMeasurable (fun x => (g₁ x - g₂ x) ^ 2) (gaussSc σ) :=
    ((h₁.2.1.aestronglyMeasurable.sub h₂.2.1.aestronglyMeasurable).pow 2)
  have htr : ∫ x, (g₁ x - g₂ x) ^ 2 ∂gaussSc σ
      = ∫ y, (g₁ (σ * y) - g₂ (σ * y)) ^ 2 ∂gauss :=
    integral_transfer _ hmeas
  have hexp : ∫ y, (σ * g₁ (σ * y) - σ * g₂ (σ * y)) ^ 2 ∂gauss
      = σ ^ 2 * ∫ y, (g₁ (σ * y) - g₂ (σ * y)) ^ 2 ∂gauss := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [hexp] at hzero
  have hs2 : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hz : ∫ y, (g₁ (σ * y) - g₂ (σ * y)) ^ 2 ∂gauss = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hs2
    · exact h
  rw [hz] at htr
  -- and read off the a.e. equality
  have hint : Integrable (fun x => (g₁ x - g₂ x) ^ 2) (gaussSc σ) := by
    have hm : MemLp (fun x => g₁ x - g₂ x) 2 (gaussSc σ) := h₁.2.1.sub h₂.2.1
    have := hm.integrable_mul hm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hnn : 0 ≤ᵐ[gaussSc σ] fun x => (g₁ x - g₂ x) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 htr
  filter_upwards [hae] with x hx
  have hx2 : (g₁ x - g₂ x) ^ 2 = 0 := hx
  have hx3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx2
  linarith [hx3]

/-! ## 5c. What is NOT done at general σ, named

The EXISTENCE half of the coefficient characterisation — from a summable
sequence to a partner — is proved at σ = 1
(`HermiteHilbertBasis.steinPair_iff_sobolev`) and is NOT transported here.
The obstruction is specific and worth naming rather than glossing: the
transport produces a candidate `g(x) = G(x/σ)/σ` from a standard-Gaussian
`G`, and to place it in `MemLp _ 2 (gaussSc σ)` one needs `G` to be
a.e.-strongly-measurable for `gaussSc σ` rather than for `gauss`. The two
measures are mutually absolutely continuous — both have everywhere-positive
densities — but the estate has no lemma transporting a.e.-strong
measurability across a change of measure, and inventing one at the end of
this file would be the wrong place for it. **So `σ`-existence is open, the
reason is a missing general lemma and not a missing idea, and the
statement below is the necessary direction only.**
-/

/-! ## 6. Review round 42 — the ways this could be hollow

**"The transport could be one-directional and the `iff` cosmetic."** It is
not: `steinPairScaled_ofStd` is new here and is what makes §3 a
biconditional. The estate had only `toStd`, which on its own gives no
`iff` and no way back from the standard case.

**"σ < 0 could be quietly excluded."** It is not. `gaussSc σ` depends on
`σ²`, so `σ` and `−σ` give the same measure, and every statement here
carries `σ ≠ 0` rather than `0 < σ`. `scal σ` is a bijection of `Cc^∞`
for negative `σ` too, which is why `scal_scal_inv` is stated at `σ⁻¹`
rather than assuming a positive scaling.

**"σ = 0 could be a hidden hole."** It is excluded, and honestly: at
`σ = 0` the measure is a Dirac mass (`gaussSc_zero`, proved 2 August), the
pairing has no analytic content, and `not_steinPairScaled_zero_id_one`
already records that the witness fails there. Nothing here claims
otherwise.

**"The class could be empty at general σ."** `steinPairScaled_id_one`
gives `(X, 1)` at every `σ ≠ 0`, and §5 transports it.
-/

/-- The class is inhabited at every nonzero variance. -/
theorem smoothSteinPairScaled_id_one {σ : ℝ} (hσ : σ ≠ 0) :
    SmoothSteinPairScaled σ (fun x => x) (fun _ => 1) :=
  (poincare_smoothScaled_sharp hσ).1

/-- **THE GAUSSIAN POINCARÉ INEQUALITY ON THE TEXTBOOK GAUSSIAN SOBOLEV
    SPACE, AT EVERY VARIANCE.** For `f` in `W^{1,2}(γ_{σ²})` with weak
    derivative `g`, `Var(f) ≤ σ²·∫g² dγ_{σ²}`. -/
theorem poincare_sobolevWeakScaled {σ : ℝ} (hσ : σ ≠ 0) {f g : ℝ → ℝ}
    (h : SobolevWeakScaled σ f g) :
    (∫ x, f x ^ 2 ∂gaussSc σ) - (∫ x, f x ∂gaussSc σ) ^ 2
      ≤ σ ^ 2 * ∫ x, g x ^ 2 ∂gaussSc σ :=
  poincare_stein_scaled σ
    ((steinPairScaled_iff_sobolevWeakScaled hσ h.1 h.2.1).mpr h)

/-- Sharp at every variance, witnessed by `(X, 1)`. -/
theorem poincare_sobolevWeakScaled_sharp {σ : ℝ} (hσ : σ ≠ 0) :
    SobolevWeakScaled σ (fun x => x) (fun _ => 1)
      ∧ (∫ x, x ^ 2 ∂gaussSc σ) - (∫ x, x ∂gaussSc σ) ^ 2 = σ ^ 2 :=
  ⟨(smoothSteinPairScaled_iff_sobolevWeakScaled hσ
      (smoothSteinPairScaled_id_one hσ).1
      (smoothSteinPairScaled_id_one hσ).2.1).mp (smoothSteinPairScaled_id_one hσ),
    var_id_scaled σ⟩

end

end TextbookSobolevScaled
