/-
  SpinOrthochronous.lean — the spin image lies in SO⁺(1,3).

  WHAT THIS CLOSES. W7 step (d)'s first part, in full:

    **`spinToO13_mem_SOplus13 (g : spinGroup Q₁₃) : spinToO13 g ∈ SOplus13`**

  `SOplus13` is three conditions — `IsLorentzMat`, `det = 1`, and
  `0 < Λ⁰₀`. The first came with `spinToO13`'s construction, the second
  is `SpinDetOne`, and the third is this file. **The image of the spin
  representation is inside the proper orthochronous Lorentz group.**

  THE ARGUMENT, and it is the determinant argument again with one extra
  quantity carried. Orthochronicity is not a parity: a reflection in a
  TIMELIKE vector preserves the time direction and a reflection in a
  SPACELIKE vector reverses it, so the generators do not all agree and no
  count of them decides the answer. What decides it is the **spinor
  norm**. For a vector unit, `star (ι v) · ι v = −Q₁₃(v)`, and the sign
  of the reflection's `Λ⁰₀` is the sign of `Q₁₃(v)` — so the sign of
  `Λ⁰₀` is minus the sign of the spinor norm, generator by generator.
  Both are multiplicative, so the relation survives the induction, and a
  spin element has spinor norm exactly `1` because that is what
  `unitary` means. Combined with the determinant's `ε = −1` per
  generator, the invariant that goes through the induction is

    `0 < (det · n) · Λ⁰₀`,  where `star x · x = algebraMap n`,

  which reads on a generator as `Q₁₃(v) · Λ⁰₀ = p₀² + p₁² + p₂² + p₃² > 0`.

  WHAT MADE IT POSSIBLE. `LorentzOrthochronousSign.sign_mul` — the sign
  of `Λ⁰₀` is multiplicative, in all four cases rather than the one
  `LorentzGroup.orthochronous_mul` covered. Without it the induction
  cannot combine two factors whose signs are unknown, which is every
  step of it.

  WHY THE SPINOR NORM IS NOT OPTIONAL, added by review round 27 because
  the paragraph above asserts it and §5 would go through unchanged if it
  were false: **`generators_disagree`** — the reflection in the timelike
  `e₀` has `Λ⁰₀ = +1` and the one in the spacelike `e₁` has `Λ⁰₀ = −1`.
  A parity argument like `SpinDetOne`'s cannot see that difference.
  `vecUnit_e₁_not_mem_spinGroup` then gives a SECOND, independent reason
  no vector unit is a spin element, sharing nothing with the determinant
  route, and the two agree.

  WHAT REMAINS OF W7 STEP (d). Its three parts were: image inside
  SO⁺(1,3), surjectivity onto it, kernel exactly ±1. The kernel is
  `SpinKernel.kernel_iff`. The image is this file. **Surjectivity is
  untouched, and nothing here bears on it** — knowing where a map lands
  says nothing about whether it lands everywhere. The double-cover
  statement is not proved; ASSUMPTIONS 42 records the other reason, which
  is that `spinGroup Q₁₃` is Mathlib's algebraic object rather than a
  simply-connected cover.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinDetOne
import LorentzOrthochronousSign
import SpinMeetsSL2

namespace SpinOrthochronous

open SpinVectorRep SpinPair SpinToOrthogonal LipschitzVectorRep LorentzReflection
open MinkowskiSignature LorentzGroup SpinMinkowskiBridge SpinToLorentzMat
open SpinDetOne LorentzOrthochronousSign SpinMeetsSL2
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. The Lipschitz action as a matrix -/

/-- The action of a Lipschitz element, as a 4×4 matrix. -/
def lipMat {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix' ((coordEquiv : V →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ lipToEndo hx ∘ₗ
    (coordEquiv.symm : (Fin 4 → ℝ) →ₗ[ℝ] V))

theorem lipMat_congr {x y : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hy : y ∈ lipschitzGroup Q₁₃) (h : x = y) : lipMat hx = lipMat hy := by
  subst h; rfl

theorem lipMat_isLorentz {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    IsLorentzMat (lipMat hx) := by
  refine isLorentzMat_of_isometry _ fun v => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [minkowskiForm_coordEquiv, lipToEndo_preserves, ← minkowskiForm_coordEquiv,
    LinearEquiv.apply_symm_apply]

theorem lipMat_mul {x y : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hy : y ∈ lipschitzGroup Q₁₃) :
    lipMat (mul_mem hx hy) = lipMat hx * lipMat hy := by
  rw [lipMat, lipMat, lipMat, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [lipToEndo_mul]

theorem lipMat_one : lipMat (one_mem (lipschitzGroup Q₁₃)) = 1 := by
  rw [lipMat, ← LinearMap.toMatrix'_id]
  congr 1
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [lipToEndo_one, LinearEquiv.apply_symm_apply]

/-- A generator's matrix is the reflection matrix `LorentzReflection`
    already analysed. -/
theorem lipMat_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) :
    lipMat (vecUnit_mem v hv) = reflMat (coordEquiv v) := by
  ext i j
  rw [lipMat, LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [lipToEndo_vecUnit hv, coord_vreflect hv, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_single]
  simp

/-! ## 2. A generator's time-time entry, and its sign

The whole difference between this file and `SpinDetOne`: the generators
do NOT all behave the same way. A reflection in a timelike vector is
orthochronous and one in a spacelike vector is not, so the sign has to be
tracked by something other than counting.
-/

/-- **The sign of a reflection's `Λ⁰₀` is the sign of `Q` on the vector**,
    and the product is a sum of four squares, hence positive. -/
theorem minkowskiForm_mul_reflMat_zero_zero {p : Fin 4 → ℝ}
    (hp : minkowskiForm p ≠ 0) : 0 < minkowskiForm p * (reflMat p) 0 0 := by
  have hgv : (gram *ᵥ p) 0 = p 0 := by
    simp [gram, Matrix.mulVec_diagonal, mw]
  have hentry : (reflMat p) 0 0 = (2 / minkowskiForm p) * p 0 * p 0 - 1 := by
    rw [reflMat]
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.one_apply_eq,
      Pi.smul_apply, smul_eq_mul, hgv]
  have hQ : minkowskiForm p = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 :=
    minkowskiForm_apply p
  have hkey : minkowskiForm p * (reflMat p) 0 0
      = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [hentry]
    field_simp
    nlinarith [hQ]
  rw [hkey]
  rcases eq_or_lt_of_le (by positivity :
      (0 : ℝ) ≤ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) with h | h
  · exfalso
    refine hp ?_
    rw [hQ]
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  · exact h

/-! ## 3. The spinor norm

`star x · x` is a scalar for a Lipschitz element, and it is what
distinguishes a timelike generator from a spacelike one. The induction
carries it alongside the determinant.
-/

/-- A vector unit's spinor norm is `−Q₁₃(v)`. -/
theorem star_mul_self_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) :
    star ((vecUnit v hv : Clˣ) : Cl) * ((vecUnit v hv : Clˣ) : Cl)
      = algebraMap ℝ Cl (-(Q₁₃ v)) := by
  change star (ι Q₁₃ v) * ι Q₁₃ v = _
  rw [star_ι, neg_mul, ι_sq_scalar, map_neg]

/-- Inverting a Lipschitz element inverts its spinor norm. -/
theorem star_mul_self_inv {x : Clˣ} {n : ℝ} (hn : n ≠ 0)
    (h : star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = algebraMap ℝ Cl n) :
    star (((x⁻¹ : Clˣ)) : Cl) * (((x⁻¹ : Clˣ)) : Cl) = algebraMap ℝ Cl n⁻¹ := by
  have hstar : star ((x : Clˣ) : Cl) = algebraMap ℝ Cl n * ((x⁻¹ : Clˣ) : Cl) := by
    have := congrArg (fun a : Cl => a * ((x⁻¹ : Clˣ) : Cl)) h
    simpa [mul_assoc] using this
  have hstarinv : star (((x⁻¹ : Clˣ)) : Cl)
      = ((x : Clˣ) : Cl) * algebraMap ℝ Cl n⁻¹ := by
    have h2 := congrArg (star : Cl → Cl) hstar
    rw [star_star, star_mul, star_algebraMap] at h2
    have h3 := congrArg (fun a : Cl => a * algebraMap ℝ Cl n⁻¹) h2
    simp only [mul_assoc, ← map_mul, mul_inv_cancel₀ hn, map_one, mul_one] at h3
    exact h3.symm
  rw [hstarinv, mul_assoc, Algebra.commutes, ← mul_assoc, Units.mul_inv, one_mul]

/-! ## 4. The induction

Same shape as `SpinDetOne.parity`, with the spinor norm carried alongside
and the sign of `Λ⁰₀` combined into a single positivity statement.
-/

/-- **The determinant, the spinor norm and the time-time entry move
    together.** For every Lipschitz element,
    `0 < (det · n) · Λ⁰₀` where `n` is the spinor norm.

    The membership proof is universally quantified inside rather than
    fixed outside. Proof irrelevance makes that vacuous mathematically,
    but it lets each branch of the induction NAME the proof it was handed
    and transport along `lipToEndo_congr` / `lipMat_congr`, which a
    proof-indexed goal otherwise makes awkward. -/
theorem chronParity {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    ∃ n : ℝ, n ≠ 0 ∧ star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = algebraMap ℝ Cl n
      ∧ ∀ h : x ∈ lipschitzGroup Q₁₃,
          0 < (LinearMap.det (lipToEndo h) * n) * (lipMat h) 0 0 := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv⟩ := hy
    have hvne : Q₁₃ v ≠ 0 := generator_not_null hv.symm
    have hyeq : y = vecUnit v hvne := Units.ext hv.symm
    refine ⟨-(Q₁₃ v), neg_ne_zero.2 hvne, ?_, fun h => ?_⟩
    · rw [hyeq]; exact star_mul_self_vecUnit hvne
    · have hdet : LinearMap.det (lipToEndo h) = -1 :=
        Eq.trans (congrArg LinearMap.det
          (LinearMap.ext fun u => lipToEndo_congr h (vecUnit_mem v hvne) hyeq u))
          (det_lipToEndo_vecUnit hvne)
      have hmat : lipMat h = reflMat (coordEquiv v) :=
        Eq.trans (lipMat_congr h (vecUnit_mem v hvne) hyeq) (lipMat_vecUnit hvne)
      rw [hdet, hmat]
      have hpos := minkowskiForm_mul_reflMat_zero_zero (p := coordEquiv v)
        (by rwa [minkowskiForm_coordEquiv])
      rw [minkowskiForm_coordEquiv] at hpos
      calc (0 : ℝ) < Q₁₃ v * (reflMat (coordEquiv v)) 0 0 := hpos
        _ = -1 * -(Q₁₃ v) * (reflMat (coordEquiv v)) 0 0 := by ring
  | one =>
    refine ⟨1, one_ne_zero, by simp, fun h => ?_⟩
    have hdet : LinearMap.det (lipToEndo h) = 1 :=
      Eq.trans (congrArg LinearMap.det
        (LinearMap.ext fun u => lipToEndo_one u)) LinearMap.det_id
    have hmat : lipMat h = 1 := lipMat_one
    rw [hdet, hmat, Matrix.one_apply_eq]
    norm_num
  | mul y z hy hz ihy ihz =>
    obtain ⟨ny, hny, hsy, hpy⟩ := ihy
    obtain ⟨nz, hnz, hsz, hpz⟩ := ihz
    refine ⟨ny * nz, mul_ne_zero hny hnz, ?_, fun h => ?_⟩
    · rw [Units.val_mul, star_mul]
      calc star ((z : Clˣ) : Cl) * star ((y : Clˣ) : Cl)
              * (((y : Clˣ) : Cl) * ((z : Clˣ) : Cl))
          = star ((z : Clˣ) : Cl)
              * ((star ((y : Clˣ) : Cl) * ((y : Clˣ) : Cl)) * ((z : Clˣ) : Cl)) := by
            simp only [mul_assoc]
        _ = star ((z : Clˣ) : Cl) * (algebraMap ℝ Cl ny * ((z : Clˣ) : Cl)) := by
            rw [hsy]
        _ = algebraMap ℝ Cl ny * (star ((z : Clˣ) : Cl) * ((z : Clˣ) : Cl)) := by
            rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
        _ = algebraMap ℝ Cl (ny * nz) := by rw [hsz, ← map_mul]
    · have hdet : LinearMap.det (lipToEndo h)
          = LinearMap.det (lipToEndo hy) * LinearMap.det (lipToEndo hz) := by
        rw [show lipToEndo h = lipToEndo hy ∘ₗ lipToEndo hz from
          LinearMap.ext fun v => lipToEndo_mul hy hz v, LinearMap.det_comp]
      have hmat : lipMat h = lipMat hy * lipMat hz := lipMat_mul hy hz
      rw [hdet, hmat]
      have hcomb := sign_mul (lipMat_isLorentz hy) (lipMat_isLorentz hz)
        (hpy hy) (hpz hz)
      calc (0 : ℝ) < (LinearMap.det (lipToEndo hy) * ny)
              * (LinearMap.det (lipToEndo hz) * nz)
              * (lipMat hy * lipMat hz) 0 0 := hcomb
        _ = LinearMap.det (lipToEndo hy) * LinearMap.det (lipToEndo hz) * (ny * nz)
              * (lipMat hy * lipMat hz) 0 0 := by ring
  | inv y hy ihy =>
    obtain ⟨n, hn, hs, hpy⟩ := ihy
    refine ⟨n⁻¹, inv_ne_zero hn, star_mul_self_inv hn hs, fun h => ?_⟩
    have hp := hpy hy
    have hprod : lipMat h * lipMat hy = 1 := by
      rw [show lipMat h * lipMat hy = lipMat (mul_mem h hy) from (lipMat_mul h hy).symm]
      exact Eq.trans (lipMat_congr (mul_mem h hy) (one_mem (lipschitzGroup Q₁₃))
        (inv_mul_cancel y)) lipMat_one
    have hdetprod : LinearMap.det (lipToEndo h) * LinearMap.det (lipToEndo hy) = 1 := by
      rw [← LinearMap.det_comp]
      rw [show lipToEndo h ∘ₗ lipToEndo hy = LinearMap.id from
        LinearMap.ext fun v => lipToEndo_inv hy v]
      exact LinearMap.det_id
    set a := LinearMap.det (lipToEndo h) * n⁻¹ with ha
    set b := LinearMap.det (lipToEndo hy) * n with hb
    have hab : a * b = 1 := by
      rw [ha, hb]
      calc LinearMap.det (lipToEndo h) * n⁻¹ * (LinearMap.det (lipToEndo hy) * n)
          = (LinearMap.det (lipToEndo h) * LinearMap.det (lipToEndo hy))
              * (n⁻¹ * n) := by ring
        _ = 1 := by rw [hdetprod, inv_mul_cancel₀ hn, mul_one]
    obtain ⟨δ, hδ1, hδ⟩ := exists_sign (lipMat_isLorentz h)
    have hsgn : 0 < (δ * b) * (lipMat h * lipMat hy) 0 0 :=
      sign_mul (lipMat_isLorentz h) (lipMat_isLorentz hy) hδ hp
    rw [hprod, Matrix.one_apply_eq, mul_one] at hsgn
    rcases hδ1 with h1 | h1
    · subst h1
      rw [one_mul] at hδ hsgn
      have hapos : 0 < a := by nlinarith [hab, hsgn]
      exact mul_pos hapos hδ
    · subst h1
      have hmneg : (lipMat h) 0 0 < 0 := by nlinarith [hδ]
      have hbneg : b < 0 := by nlinarith [hsgn]
      have haneg : a < 0 := by nlinarith [hab, hbneg]
      exact mul_pos_of_neg_of_neg haneg hmneg

/-! ## 5. Spin elements are orthochronous -/

/-- **A spin element's Lorentz matrix has positive time-time entry.**
    Its determinant is `1` (`SpinDetOne`) and its spinor norm is `1`
    (that is what `unitary` means), so the invariant collapses. -/
theorem lipMat_zero_zero_pos {x : Clˣ} (hspin : (x : Cl) ∈ spinGroup Q₁₃) :
    0 < (lipMat (units_mem_lip hspin)) 0 0 := by
  obtain ⟨n, hn, hs, hpall⟩ := chronParity (units_mem_lip hspin)
  have hp := hpall (units_mem_lip hspin)
  have hunit : star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1 :=
    pinGroup.star_mul_self_of_mem (spinGroup.mem_pin hspin)
  have hn1 : n = 1 := by
    have : algebraMap ℝ Cl n = algebraMap ℝ Cl 1 := by rw [← hs, hunit, map_one]
    exact FaithfulSMul.algebraMap_injective ℝ Cl this
  have hdet : LinearMap.det (lipToEndo (units_mem_lip hspin)) = 1 := by
    rw [show lipToEndo (units_mem_lip hspin) = spinToEndo hspin from
      LinearMap.ext fun v => lipToEndo_eq_spinToEndo _ hspin v]
    exact det_spinToEndo_eq_one hspin
  rw [hdet, hn1] at hp
  simpa using hp

/-- The matrix `spinToO13` produces is the one the induction analysed. -/
theorem spinToO13_eq_lipMat (g : spinGroup Q₁₃) :
    ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ)
      = lipMat (units_mem_lip (toUnits_mem g)) := by
  rw [spinToO13_toMatrix]
  rfl

theorem spinToO13_zero_zero_pos (g : spinGroup Q₁₃) :
    0 < ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) 0 0 := by
  rw [spinToO13_eq_lipMat]
  exact lipMat_zero_zero_pos (toUnits_mem g)

/-- **W7 step (d), first part: the spin image lies in SO⁺(1,3).** -/
theorem spinToO13_mem_SOplus13 (g : spinGroup Q₁₃) :
    (spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) ∈ SOplus13 :=
  ⟨(spinToO13 g).2, det_spinToO13_eq_one g, spinToO13_zero_zero_pos g⟩

/-- Restated as a homomorphism into the proper orthochronous group,
    which is the form a downstream user wants. -/
def spinToSOplus : spinGroup Q₁₃ →* SOplus13 where
  toFun g := ⟨(spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    spinToO13_mem_SOplus13 g⟩
  map_one' := Subtype.ext (by
    change ((spinToO13 1 : O13) : Matrix.GeneralLinearGroup (Fin 4) ℝ) = 1
    rw [map_one]
    rfl)
  map_mul' g h := Subtype.ext (by
    change ((spinToO13 (g * h) : O13) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      = ((spinToO13 g : O13) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
        * ((spinToO13 h : O13) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
    rw [map_mul]
    rfl)

/-! ## 6. Orthochronicity is not a parity, and here is the proof

Review round 27's fold. The header asserts that the generators disagree —
a timelike reflection preserves the time direction and a spacelike one
reverses it — and that assertion is what forces the spinor norm into the
induction. §5 would go through unchanged if it were false and the sign
were a parity like the determinant, so it is worth being a theorem rather
than a paragraph.
-/

/-- The reflection in the TIMELIKE `e₀` is orthochronous. -/
theorem reflMat_e₀_zero_zero : (reflMat (coordEquiv e₀)) 0 0 = 1 := by
  have hgv : (gram *ᵥ coordEquiv e₀) 0 = (coordEquiv e₀) 0 := by
    simp [gram, Matrix.mulVec_diagonal, mw]
  rw [reflMat]
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.one_apply_eq,
    Pi.smul_apply, smul_eq_mul, hgv]
  simp [coordEquiv, e₀, minkowskiForm_apply]
  norm_num

/-- The reflection in the SPACELIKE `e₁` is ANTICHRONOUS. -/
theorem reflMat_e₁_zero_zero : (reflMat (coordEquiv e₁)) 0 0 = -1 := by
  rw [reflMat_e₁, Matrix.diagonal_apply_eq]
  norm_num

/-- **So the generators genuinely disagree**, and no count of them can
    decide orthochronicity. This is why §4 carries the spinor norm and
    `SpinDetOne`'s induction did not have to. -/
theorem generators_disagree :
    0 < (reflMat (coordEquiv e₀)) 0 0 ∧ (reflMat (coordEquiv e₁)) 0 0 < 0 := by
  rw [reflMat_e₀_zero_zero, reflMat_e₁_zero_zero]
  norm_num

/-- **A second, independent reason no vector unit is a spin element.**
    `SpinDetOne.vecUnit_not_mem_spinGroup` gets this from the
    determinant; for a SPACELIKE vector the time-time entry gives it by
    a route sharing nothing with that one, and the two agree. -/
theorem vecUnit_e₁_not_mem_spinGroup :
    ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl) ∉ spinGroup Q₁₃ := by
  intro hmem
  have h := lipMat_zero_zero_pos hmem
  rw [show lipMat (units_mem_lip hmem) = lipMat (vecUnit_mem e₁ Q₁₃_e₁_ne) from rfl,
    lipMat_vecUnit, reflMat_e₁_zero_zero] at h
  norm_num at h

/-- Two spacelike reflections compose to something orthochronous — the
    `(−1)(−1)` case, which is `LorentzOrthochronousSign`'s new one and is
    unreachable from `orthochronous_mul` alone. -/
theorem two_spacelike_chron :
    0 < ((reflMat (coordEquiv e₁)) * (reflMat (coordEquiv e₁))) 0 0 := by
  have hL : IsLorentzMat (reflMat (coordEquiv e₁)) := by
    rw [← lipMat_vecUnit Q₁₃_e₁_ne]
    exact lipMat_isLorentz _
  have hneg : (reflMat (coordEquiv e₁)) 0 0 < 0 := by
    rw [reflMat_e₁_zero_zero]; norm_num
  exact orthochronous_mul_neg_neg hL hL hneg hneg

/-- The general theorem states the same proposition the two hand
    computations in `SpinMeetsSL2` stated. Proof irrelevance makes the
    `rfl` trivial as a PROOF, which is the point: what it certifies is
    that the general result is about the same objects, not that the two
    arguments agree. -/
theorem agrees_with_hand_computation :
    spinToO13_mem_SOplus13 R₁₂' = spinToO13_R₁₂'_mem_SOplus
      ∧ spinToO13_mem_SOplus13 B' = spinToO13_B'_mem_SOplus :=
  ⟨rfl, rfl⟩

/-- And the homomorphism into SO⁺(1,3) is not the trivial one. -/
theorem spinToSOplus_nontrivial : spinToSOplus R₁₂' ≠ 1 := by
  intro h
  have hval : ((spinToO13 R₁₂' : O13) : Matrix.GeneralLinearGroup (Fin 4) ℝ) = 1 :=
    congrArg Subtype.val h
  exact spinToO13_R₁₂'_ne_one (Subtype.ext hval)

end

end SpinOrthochronous
