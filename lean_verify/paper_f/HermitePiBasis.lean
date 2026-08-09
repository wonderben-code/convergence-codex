/-
  HermitePiBasis.lean — **STAIR N3b, and PARSEVAL in n dimensions.**

  WHY THIS IS A SEPARATE FILE FROM N2. `HermitePiComplete.hpi_complete` says
  that an `L²(γⁿ)` function orthogonal to every `Hpi n m` vanishes a.e.
  `HilbertBasis.mkOfOrthogonalEqBot` wants something that looks similar and
  is not the same statement: that the orthogonal complement of the CLOSED
  SPAN of the normalised family is the ZERO SUBMODULE of `Lp ℝ 2 (gaussPi n)`.
  Getting from one to the other is `Lp` bookkeeping — an element of the
  complement pairs to zero with each `eHpi n m`, that pairing is a
  coefficient up to `√(∏(mᵢ)!)`, the coefficient is an integral, and a
  function that is zero a.e. is the zero element of `Lp`. **That chain is
  short but it is not nothing, and folding it into N2's file would have been
  exactly the joint-between-two-files claim ERRATUM 48 is about.**

  WHAT THIS FILE PROVES:
  * **`orthogonal_eq_bot`** — the translation above. This is N3b's content.
  * **`hermitePiBasis`** — `HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 (gaussPi n))`.
    The multi-index Hermite system is a Hilbert basis of `L²(γⁿ)`, bundled
    as the Mathlib object with its whole API, in EVERY dimension.
  * **`repr_apply`** — what the abstract `repr` actually computes: the
    coefficient, scaled by `√(∏(mᵢ)!)`.
  * **`parseval_pi`** — and this is the one that was owed.
    `HermitePiBessel` proved `Σ_m (∏(mᵢ)!)·c_m(F)² ≤ ∫F²` and its header said
    in as many words that **Parseval is exactly what completeness buys**.
    Completeness now exists, so the inequality is an EQUALITY, stated in
    that file's own integral form (`parseval_pi_integral`) rather than left
    for a reader to notice.

  NOTHING HERE IS DEEP. Every ingredient was already exported: `Hpi_memLp`
  and `Hpi_orthogonal` from N1, `orthonormal_eHpi` / `inner_eHpi` /
  `integral_mul_Hpi` from N3a, `hpi_complete` from N2. **The honest
  accounting is that this file is the assembly, and the work was N2.** It is
  written out rather than skipped because "the basis follows" is a claim, and
  a claim that is never compiled is the kind this estate has been wrong about
  before.

  WHAT THIS DOES NOT DO. Riesz–Fischer for a PRESCRIBED coefficient sequence
  — the n-dimensional twin of `HermiteHilbertBasis.exists_of_summable` — is
  not here, and neither is the coefficient CHARACTERISATION of any Sobolev
  class. Those are N4. The `Cc^∞` bridge with partial derivatives (N5) and
  Poincaré on the n-dimensional textbook space (N6) are untouched, and the
  n-dimensional "polynomial test functions only" fence has NOT fallen.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiComplete
import HermitePiBessel
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace HermitePiBasis

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiComplete
open scoped ENNReal

noncomputable section

/-! ## 1. N3b: from "orthogonal to every `Hpi`" to "the complement is `⊥`"

The only content is the dictionary. An `F` in the orthogonal complement
pairs to zero with each `eHpi n m`; `inner_eHpi` turns that pairing into
`√(∏(mᵢ)!)·c_m(F)`, which forces `c_m(F) = 0` because the scalar is
nonzero; `integral_mul_Hpi` turns the coefficient back into the integral
`hpi_complete` speaks about; and `Lp.eq_zero_iff_ae_eq_zero` turns "zero
a.e." into "the zero vector".
-/

theorem orthogonal_eq_bot (n : ℕ) :
    (Submodule.span ℝ (Set.range (eHpi n)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  have hmem : ∀ m : Fin n → ℕ, eHpi n m ∈ Submodule.span ℝ (Set.range (eHpi n)) :=
    fun m => Submodule.subset_span ⟨m, rfl⟩
  have hz : ∀ m : Fin n → ℕ,
      ∫ x, (F : (Fin n → ℝ) → ℝ) x * Hpi n m x ∂gaussPi n = 0 := by
    intro m
    have h1 : inner ℝ (eHpi n m) F = (0:ℝ) :=
      (Submodule.mem_orthogonal _ _).mp hF _ (hmem m)
    rw [inner_eHpi] at h1
    have hc : coeffPi n m ((F : (Fin n → ℝ) → ℝ)) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (sqrt_facPi_ne_zero n m)
      · exact h
    rw [integral_mul_Hpi, hc, mul_zero]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (hpi_complete n _ (Lp.memLp F) hz)

/-- Density of the multi-index span in norm form — the classical phrasing,
    kept as an export. It is NOT on the critical path: Mathlib's
    `mkOfOrthogonalEqBot` consumes `orthogonal_eq_bot` directly. -/
theorem span_dense (n : ℕ) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (eHpi n))).topologicalClosure :=
  le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr (orthogonal_eq_bot n)).symm

/-! ## 2. The basis -/

/-- **THE MULTI-INDEX HERMITE SYSTEM IS A HILBERT BASIS OF `L²(γⁿ)`, IN
    EVERY DIMENSION.** Stair N3b. The one-dimensional twin is
    `HermiteHilbertBasis.hermiteBasis`; this is the same constructor fed the
    same two ingredients, orthonormality from N3a and completeness from
    N2. -/
def hermitePiBasis (n : ℕ) : HilbertBasis (Fin n → ℕ) ℝ (Lp ℝ 2 (gaussPi n)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_eHpi n) (orthogonal_eq_bot n)

theorem hermitePiBasis_apply (n : ℕ) (m : Fin n → ℕ) :
    hermitePiBasis n m = eHpi n m :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (orthonormal_eHpi n) (orthogonal_eq_bot n)) m

/-! ## 3. What the abstract representation computes -/

theorem repr_apply (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) (m : Fin n → ℕ) :
    ((hermitePiBasis n).repr F : (Fin n → ℕ) → ℝ) m
      = Real.sqrt (facPi n m) * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) := by
  rw [HilbertBasis.repr_apply_apply, hermitePiBasis_apply, inner_eHpi]

/-! ## 4. PARSEVAL — the equality `HermitePiBessel` said completeness buys -/

/-- **PARSEVAL'S IDENTITY IN n DIMENSIONS.**
    `‖F‖² = Σ_m (∏ᵢ(mᵢ)!)·c_m(F)²` for every `F ∈ L²(γⁿ)`. -/
theorem parseval_pi (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    ‖F‖ ^ 2 = ∑' m : Fin n → ℕ, facPi n m * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) ^ 2 := by
  have h0 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (by rw [h0]; norm_num) ((hermitePiBasis n).repr F)
  rw [h0] at hnorm
  simp only [Real.rpow_natCast] at hnorm
  rw [← (hermitePiBasis n).repr.norm_map F, hnorm]
  refine tsum_congr fun m => ?_
  rw [repr_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (facPi_pos n m))]

/-- The same identity written as an integral, which is the form the earlier
    n-dimensional results are stated in — and therefore **the statement that
    `HermitePiBessel.bessel_pi`'s inequality is an EQUALITY.** That file's
    header said only completeness could upgrade it; completeness now exists,
    and this is the upgrade rather than a remark about one. -/
theorem parseval_pi_integral (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    ∑' m : Fin n → ℕ, facPi n m * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) ^ 2
      = ∫ x, (F : (Fin n → ℝ) → ℝ) x ^ 2 ∂gaussPi n := by
  rw [← parseval_pi, norm_sq_eq_integral]

/-- **BESSEL IS NEVER STRICT.** The contrapositive form, which is what
    "the bound is tight for every `F`" means and is not the same sentence as
    the equality: it says no square-integrable function has any `L²` mass
    outside the multi-index Hermite system. -/
theorem not_bessel_strict (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    ¬ (∑' m : Fin n → ℕ, facPi n m * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) ^ 2
        < ∫ x, (F : (Fin n → ℝ) → ℝ) x ^ 2 ∂gaussPi n) := by
  rw [parseval_pi_integral]
  exact lt_irrefl _

/-- A vector is determined by its coefficients — the `Lp` form of
    `HermitePiComplete.eq_of_coeff_eq`, and the statement a reader wanting
    "the coefficients are a complete invariant" will look for. -/
theorem eq_of_coeffPi_eq (n : ℕ) {F F' : Lp ℝ 2 (gaussPi n)}
    (h : ∀ m : Fin n → ℕ, coeffPi n m ((F : (Fin n → ℝ) → ℝ))
        = coeffPi n m ((F' : (Fin n → ℝ) → ℝ))) :
    F = F' := by
  refine (hermitePiBasis n).repr.injective ?_
  ext m
  rw [repr_apply, repr_apply, h m]

/-! ## 5. Non-vacuity: the basis is the family we meant

`mkOfOrthogonalEqBot` produces a `HilbertBasis` whose underlying family is
`eHpi` by `hermitePiBasis_apply`, and the coefficients of a basis vector are
the delta. Both are checked rather than assumed, because a bundling that
silently indexed the wrong family would still compile.
-/

theorem repr_hermitePiBasis (n : ℕ) (m k : Fin n → ℕ) :
    ((hermitePiBasis n).repr (hermitePiBasis n m) : (Fin n → ℕ) → ℝ) k
      = if m = k then 1 else 0 := by
  rw [HilbertBasis.repr_apply_apply, hermitePiBasis_apply, hermitePiBasis_apply,
    orthonormal_iff_ite.mp (orthonormal_eHpi n) k m]
  simp [eq_comm]

/-- At `n = 0` the index type `Fin 0 → ℕ` is a singleton, so the basis has
    exactly ONE vector — every index names the same one. The degenerate case
    is stated as a theorem rather than left to the reader, which is what
    stair N1 did with `Hpi_zero_dim`. -/
theorem hermitePiBasis_zero_dim (m k : Fin 0 → ℕ) :
    hermitePiBasis 0 m = hermitePiBasis 0 k := by
  have : m = k := by funext i; exact i.elim0
  rw [this]

/-! ## 6. Review round 51 — the ways this could be hollow

**"`orthogonal_eq_bot` could be `hpi_complete` restated."** It consumes
`hpi_complete` and is not it: the hypothesis there is about integrals of raw
functions and the conclusion here is about a submodule of `Lp`. Three
dictionary steps sit between them (`inner_eHpi`, `integral_mul_Hpi`,
`Lp.eq_zero_iff_ae_eq_zero`), and the scalar `√(∏(mᵢ)!)` has to be known
nonzero or the first step fails. That the chain is short is a fact about how
well N3a was built, not evidence that the step is empty.

**"The bundling could index the wrong family."** `hermitePiBasis_apply`
pins the underlying family to `eHpi`, and `repr_hermitePiBasis` computes the
representation of a basis vector and gets the delta. A bundling that had
silently taken some other orthonormal family would compile and would fail
both.

**"Parseval could be a renaming of Bessel."** Bessel is `≤` and holds for
ANY orthonormal family — `HermitePiBessel` got it from
`Orthonormal.tsum_inner_products_le` with no completeness at all. The
equality needs the family to be a BASIS, which is what this file supplies,
and `parseval_pi_integral` is the upgrade stated in the earlier theorem's own
form, and `not_bessel_strict` says what tightness means, so that the earlier
theorem's honest limit is visibly retired rather than quietly outgrown.

**"This might close more of the staircase than it does."** It does not close
N4: Riesz–Fischer for a prescribed coefficient sequence is a different
theorem (`ℓ²`-summable coefficients produce an `L²` function), it is the
n-dimensional twin of `HermiteHilbertBasis.exists_of_summable`, and it is not
here. `eq_of_coeffPi_eq` is uniqueness, not existence, and the two are not
the same half.
-/

end

end HermitePiBasis
