/-
  HermitePiRiesz.lean — **STAIR N4**: prescribed-coefficient Riesz–Fischer and
  polarised Parseval, in n dimensions.

  WHAT WAS MISSING AFTER N3b. The basis gives every `L²(γⁿ)` function a
  coefficient sequence and proves the sequence determines the function
  (`eq_of_coeffPi_eq`). That is UNIQUENESS. The other half — that a sequence
  given IN ADVANCE, subject only to the weighted summability, is the
  coefficient sequence of an honest `L²` function — is EXISTENCE, and the
  two are not the same half. `HermitePiBasis`'s header said so; this file is
  the other half.

  WHAT THIS FILE PROVES:
  * **`exists_of_summable_pi`** — Riesz–Fischer for a prescribed multi-index
    sequence. If `Σ_m (∏ᵢ(mᵢ)!)·a_m² < ∞` then some `F ∈ L²(γⁿ)` has
    `c_m(F) = a_m` for every multi-index `m`.
  * **`coeffPi_surjective_iff`** — the two halves combined into the statement
    a reader wants: a sequence is realisable **exactly when** it is weighted
    square-summable. Forward is Bessel-through-the-basis, backward is
    Riesz–Fischer.
  * **`integral_mul_eq_tsum_coeffPi`** — POLARISED Parseval,
    `∫ f·g dγⁿ = Σ_m (∏ᵢ(mᵢ)!)·c_m(f)·c_m(g)`. `HermitePiBasis` proved the
    diagonal case; this is the bilinear one, and it is the form every later
    stair actually consumes.
  * **`inner_eq_integral`**, **`coeffPi_congr_ae`** — the two dictionary
    lemmas the above need. `HermitePiBessel` already states `inner_toLpPi`
    for two `MemLp` FUNCTIONS; what it did inline, twice, is the
    `Lp.toLp_coeFn` round-trip needed to apply it to two `Lp` ELEMENTS, and
    `inner_eq_integral` is that round-trip stated once — `HermitePiPeel`'s
    standing lesson about machinery buried in proofs, for the third time
    this week. `coeffPi_congr_ae` is not an extraction; it is new, and it is
    what lets a statement about `Lp` elements be read as one about
    functions.

  ROUTE, AND IT IS NOT A DISCOVERY. §2 is `HermiteHilbertBasis` §4 with `ℕ`
  replaced by `Fin n → ℕ` and `n!` by `∏ᵢ(mᵢ)!`; §3 is the same
  substitution applied to `SteinSmoothTest.integral_mul_eq_tsum_coeff`. The
  staircase predicted exactly that ("all follow the 1-d file line for line
  once N3 exists") and for once the prediction was made AFTER the hard stair
  rather than before it. **The line-for-line claim is now checked rather
  than asserted**, which is the only reason it is worth restating.

  WHAT THIS DOES NOT DO. It says nothing about derivatives. N5 — the `Cc^∞`
  bridge — needs PARTIAL derivatives and is therefore a family of equations
  indexed by the coordinate, not one equation; it remains the only genuinely
  new shape on the n-dimensional list and it remains unprobed. N6, Poincaré
  on the n-dimensional textbook space, is downstream of N5. **The
  n-dimensional "polynomial test functions only" fence has NOT fallen**: in
  one dimension it needed completeness, the basis, AND the coefficient
  characterisation of a SOBOLEV class — and the third of those is about
  derivatives, which is N5, not this file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiBasis

namespace HermitePiRiesz

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiComplete HermitePiBasis
open scoped ENNReal

noncomputable section

/-! ## 1. Two dictionary lemmas, extracted rather than re-derived -/

/-- The `L²(γⁿ)` inner product of two `Lp` ELEMENTS is the integral of the
    product. `HermitePiBessel.inner_toLpPi` says this for two `MemLp`
    functions; getting from there to here is the `Lp.toLp_coeFn` round-trip,
    which that file performed inline in `norm_sq_eq_integral` and again in
    `inner_eHpi`. Stated once. -/
theorem inner_eq_integral (n : ℕ) (F G : Lp ℝ 2 (gaussPi n)) :
    inner ℝ F G
      = ∫ x, (F : (Fin n → ℝ) → ℝ) x * (G : (Fin n → ℝ) → ℝ) x ∂gaussPi n := by
  have hF : (Lp.memLp F).toLp ((F : (Fin n → ℝ) → ℝ)) = F := Lp.toLp_coeFn F (Lp.memLp F)
  have hG : (Lp.memLp G).toLp ((G : (Fin n → ℝ) → ℝ)) = G := Lp.toLp_coeFn G (Lp.memLp G)
  conv_lhs => rw [← hF, ← hG]
  rw [inner_toLpPi]

/-- Coefficients see only the a.e. class, which is what lets a statement
    about `Lp` elements be read as a statement about functions. -/
theorem coeffPi_congr_ae (n : ℕ) {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[gaussPi n] g) (m : Fin n → ℕ) :
    coeffPi n m f = coeffPi n m g := by
  rw [coeffPi, coeffPi]
  congr 1
  exact integral_congr_ae (h.mono fun x hx => by dsimp only; rw [hx])

/-! ## 2. Riesz–Fischer for a prescribed multi-index sequence -/

theorem memℓp_of_summable_pi (n : ℕ) {a : (Fin n → ℕ) → ℝ}
    (ha : Summable fun m : Fin n → ℕ => facPi n m * a m ^ 2) :
    Memℓp (fun m : Fin n → ℕ => Real.sqrt (facPi n m) * a m) 2 := by
  refine memℓp_gen ?_
  have hp : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hp]
  refine ha.congr fun m => ?_
  rw [Real.rpow_natCast, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (facPi_pos n m))]

/-- **RIESZ–FISCHER FOR A PRESCRIBED MULTI-INDEX HERMITE SEQUENCE.** Any
    sequence square-summable in the `∏ᵢ(mᵢ)!`-weighted sense is the
    coefficient sequence of an honest element of `L²(γⁿ)`. -/
theorem exists_of_summable_pi (n : ℕ) {a : (Fin n → ℕ) → ℝ}
    (ha : Summable fun m : Fin n → ℕ => facPi n m * a m ^ 2) :
    ∃ F : (Fin n → ℝ) → ℝ, MemLp F 2 (gaussPi n) ∧ ∀ m, coeffPi n m F = a m := by
  set b : lp (fun _ : Fin n → ℕ => ℝ) 2 :=
    ⟨fun m => Real.sqrt (facPi n m) * a m, memℓp_of_summable_pi n ha⟩ with hbdef
  refine ⟨(((hermitePiBasis n).repr.symm b : Lp ℝ 2 (gaussPi n)) : (Fin n → ℝ) → ℝ),
    Lp.memLp _, fun m => ?_⟩
  have hrepr : (hermitePiBasis n).repr ((hermitePiBasis n).repr.symm b) = b :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have h1 := repr_apply n ((hermitePiBasis n).repr.symm b) m
  rw [hrepr] at h1
  have h2 : (b : (Fin n → ℕ) → ℝ) m = Real.sqrt (facPi n m) * a m := rfl
  rw [h2] at h1
  exact (mul_left_cancel₀ (sqrt_facPi_ne_zero n m) h1).symm

/-- **THE COEFFICIENT MAP'S RANGE, EXACTLY.** A multi-index sequence is the
    Hermite coefficient sequence of some `L²(γⁿ)` function **if and only if**
    it is weighted square-summable. Forward is Bessel read through the basis;
    backward is Riesz–Fischer. -/
theorem coeffPi_surjective_iff (n : ℕ) (a : (Fin n → ℕ) → ℝ) :
    (∃ F : (Fin n → ℝ) → ℝ, MemLp F 2 (gaussPi n) ∧ ∀ m, coeffPi n m F = a m)
      ↔ Summable fun m : Fin n → ℕ => facPi n m * a m ^ 2 := by
  refine ⟨fun ⟨F, hF, hc⟩ => ?_, exists_of_summable_pi n⟩
  have hsum := summable_coeffPi_sq n (hF.toLp F)
  refine hsum.congr fun m => ?_
  rw [coeffPi_congr_ae n hF.coeFn_toLp m, hc m]

/-! ## 3. Polarised Parseval

`HermitePiBasis.parseval_pi` is the diagonal case. The bilinear one is what
every later stair consumes: it turns an integral pairing — which is how the
Stein-type classes are DEFINED — into a sum over coefficients.
-/

/-- **POLARISED PARSEVAL IN n DIMENSIONS.**
    `∫ f·g dγⁿ = Σ_m (∏ᵢ(mᵢ)!)·c_m(f)·c_m(g)`. -/
theorem integral_mul_eq_tsum_coeffPi (n : ℕ) {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussPi n)) (hg : MemLp g 2 (gaussPi n)) :
    ∫ x, f x * g x ∂gaussPi n
      = ∑' m : Fin n → ℕ, facPi n m * (coeffPi n m f * coeffPi n m g) := by
  have key := HilbertBasis.tsum_inner_mul_inner (hermitePiBasis n)
    (hf.toLp f) (hg.toLp g)
  rw [inner_eq_integral] at key
  have hint : ∫ x, f x * g x ∂gaussPi n
      = ∫ x, (hf.toLp f : (Fin n → ℝ) → ℝ) x * (hg.toLp g : (Fin n → ℝ) → ℝ) x
          ∂gaussPi n := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [hint, ← key]
  refine tsum_congr fun m => ?_
  rw [real_inner_comm ((hermitePiBasis n) m) (hf.toLp f), hermitePiBasis_apply,
    inner_eHpi, inner_eHpi,
    ← coeffPi_congr_ae n hf.coeFn_toLp m, ← coeffPi_congr_ae n hg.coeFn_toLp m]
  conv_rhs => rw [← sqrt_facPi_mul_self n m]
  ring

/-! ## 4. Non-vacuity

Riesz–Fischer would be uninteresting if the summability condition were only
satisfiable by the zero sequence. It is not: every finitely-supported
sequence qualifies, and the basis vectors realise the deltas.
-/

/-- A finitely supported sequence is always admissible, so the class of
    realisable sequences is infinite-dimensional. -/
theorem summable_facPi_of_finite_support (n : ℕ) {a : (Fin n → ℕ) → ℝ}
    (h : (Function.support a).Finite) :
    Summable fun m : Fin n → ℕ => facPi n m * a m ^ 2 := by
  refine summable_of_hasFiniteSupport ?_
  refine h.subset fun m hm => ?_
  by_contra hc
  simp only [Function.mem_support, not_not] at hc
  exact hm (by simp [hc])

/-- Every single prescribed coefficient is realised: for any multi-index `k`
    and any real `c`, some `L²(γⁿ)` function has `c_k = c` and every other
    coefficient zero. -/
theorem exists_delta_coeff (n : ℕ) (k : Fin n → ℕ) (c : ℝ) :
    ∃ F : (Fin n → ℝ) → ℝ, MemLp F 2 (gaussPi n) ∧
      ∀ m, coeffPi n m F = if m = k then c else 0 := by
  refine exists_of_summable_pi n (summable_facPi_of_finite_support n ?_)
  refine Set.Finite.subset (Set.finite_singleton k) fun m hm => ?_
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hm
  simpa using hm.1

/-! ## 5. Review round 52 — the ways this could be hollow

**"Riesz–Fischer could be `repr.symm` renamed."** It is `repr.symm` applied
to a specific `ℓ²` element, and the content is that the element EXISTS —
`memℓp_of_summable_pi` — and that unwinding `repr` at the produced vector
gives back the sequence you started from, which needs the scale factor
`√(∏(mᵢ)!)` cancelled and therefore needs it nonzero. Neither step is the
constructor.

**"`coeffPi_surjective_iff` could be vacuous in the forward direction."** It
is not: the forward direction is the ONLY place the hypothesis "`F` is in
`L²`" is used, and without it the statement is false — an arbitrary
measurable function has no reason to have summable weighted coefficients.
`summable_coeffPi_sq` is where that is discharged, and it comes from
orthonormality (N3a), not from this file.

**"Polarised Parseval could be the diagonal case with two letters."** Setting
`f = g` recovers `parseval_pi`, so the diagonal is a corollary of this and
not the other way round; the proof goes through
`HilbertBasis.tsum_inner_mul_inner`, which is a genuinely bilinear statement
about a basis. What makes it worth its own name is the consumer: the
Stein-type classes are DEFINED by an integral pairing of two functions, and
this is the theorem that turns such a pairing into coefficients.

**"The non-vacuity could be trivial."** `exists_delta_coeff` is the check
that the prescription is genuinely free at each index — it produces, for
every multi-index and every real number, a function whose expansion is that
single term. Without it, "any summable sequence is realised" is compatible
with the summable sequences being a very thin set.

**"This might close N5 or the fence."** It does not, and the header says so
in the strongest form available: N5 is about PARTIAL derivatives and is a
family of equations indexed by the coordinate rather than one equation, it
has not been probed, and the one-dimensional fence needed a coefficient
characterisation of a SOBOLEV class — a statement about derivatives — which
is nowhere in this file.
-/

end

end HermitePiRiesz
