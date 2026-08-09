/-
  HermitePiBessel.lean — stair N3a: the multi-index Hermite system as an
  ORTHONORMAL FAMILY in L²(γⁿ), and Bessel's inequality in n dimensions.

  WHY, and why this before N2. `PROOF_STRATEGY` §6.3 says that if the unit
  just finished was a B, retry B→C before touching the queue. `HermitePi`
  (stair N1) was a B, and asking §6.1's CAESAR question of it gives a
  clean answer: **orthonormality and Bessel need N1 and nothing else.**
  The staircase had bundled them into N3, behind completeness (N2), which
  is the stair that might be hard. They are not behind it. So the
  n-dimensional chain gains a rung today without N2 being touched.

  WHAT THIS FILE PROVES:
  * **`orthonormal_eHpi`** — `Hpi n m / √(∏ᵢ (mᵢ)!)` is an orthonormal
    family in `L²(γⁿ)`, indexed by multi-indices `Fin n → ℕ`. This is what
    N3 will feed to `HilbertBasis.mkOfOrthogonalEqBot`; the OTHER argument
    of that constructor is N2, and it is still missing.
  * **`bessel_pi`** — `Σ_m (∏ᵢ(mᵢ)!)·c_m(F)² ≤ ∫ F² dγⁿ` for every
    `F ∈ L²(γⁿ)`, with **`summable_coeffPi_sq`** the summability. The
    n-dimensional analogue of the estate's `HermiteBessel`, and the first
    quantitative statement about arbitrary L² functions in n dimensions.
    **That last clause was checked rather than remembered** (ERRATA 46):
    `GaussianProductMeasure.lean` contains no occurrence of `MemLp` or
    `Lp ℝ` at all, and no other file states anything n-dimensional about a
    non-polynomial function.
  * **`coeffPi_HpiL`** — the coefficients of a basis vector are the delta,
    so the coefficient map is not the zero map.

  WHAT THIS DOES NOT DO. Bessel is an INEQUALITY. Parseval — equality —
  is exactly the extra strength that completeness buys, and N2 is
  untouched. Nothing here says the family spans anything.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePi

namespace HermitePiBessel

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi

noncomputable section

/-! ## 1. The normalising constant -/

/-- `∏ᵢ (mᵢ)!` — the squared norm of `Hpi n m`, by `HermitePi.Hpi_norm_sq`. -/
def facPi (n : ℕ) (m : Fin n → ℕ) : ℝ := ∏ i, ((m i).factorial : ℝ)

theorem facPi_pos (n : ℕ) (m : Fin n → ℕ) : 0 < facPi n m := by
  refine Finset.prod_pos fun i _ => ?_
  exact_mod_cast (m i).factorial_pos

theorem facPi_ne_zero (n : ℕ) (m : Fin n → ℕ) : facPi n m ≠ 0 := ne_of_gt (facPi_pos n m)

theorem sqrt_facPi_pos (n : ℕ) (m : Fin n → ℕ) : 0 < Real.sqrt (facPi n m) :=
  Real.sqrt_pos.mpr (facPi_pos n m)

theorem sqrt_facPi_ne_zero (n : ℕ) (m : Fin n → ℕ) : Real.sqrt (facPi n m) ≠ 0 :=
  ne_of_gt (sqrt_facPi_pos n m)

theorem sqrt_facPi_mul_self (n : ℕ) (m : Fin n → ℕ) :
    Real.sqrt (facPi n m) * Real.sqrt (facPi n m) = facPi n m :=
  Real.mul_self_sqrt (le_of_lt (facPi_pos n m))

/-! ## 2. The vectors of `L²(γⁿ)` -/

/-- The `L²(γⁿ)` dictionary, the n-dimensional twin of the estate's
    `HermiteParseval.inner_toLp`. -/
theorem inner_toLpPi {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussPi n)) (hg : MemLp g 2 (gaussPi n)) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂gaussPi n := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  exact (RCLike.inner_apply (f x) (g x)).trans (by simp [mul_comm])

/-- `Hpi n m` as an element of `L²(γⁿ)`. -/
def HpiL (n : ℕ) (m : Fin n → ℕ) : Lp ℝ 2 (gaussPi n) := (Hpi_memLp n m).toLp _

/-- The NORMALISED multi-index system. -/
def eHpi (n : ℕ) (m : Fin n → ℕ) : Lp ℝ 2 (gaussPi n) :=
  (Real.sqrt (facPi n m))⁻¹ • HpiL n m

theorem inner_HpiL_HpiL (n : ℕ) (m k : Fin n → ℕ) :
    inner ℝ (HpiL n m) (HpiL n k) = if m = k then facPi n m else 0 := by
  simp only [HpiL]
  rw [inner_toLpPi]
  exact Hpi_orthogonal n m k

/-- **THE MULTI-INDEX HERMITE SYSTEM IS ORTHONORMAL IN `L²(γⁿ)`.** -/
theorem orthonormal_eHpi (n : ℕ) : Orthonormal ℝ (eHpi n) := by
  rw [orthonormal_iff_ite]
  intro m k
  rw [eHpi, eHpi, real_inner_smul_left, real_inner_smul_right, inner_HpiL_HpiL]
  split_ifs with h
  · subst h
    have hne := sqrt_facPi_ne_zero n m
    field_simp
    exact (Real.sq_sqrt (le_of_lt (facPi_pos n m))).symm
  · ring

/-! ## 3. Coefficients -/

/-- The multi-index Hermite coefficient. -/
def coeffPi (n : ℕ) (m : Fin n → ℕ) (F : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x, F x * Hpi n m x ∂gaussPi n) / facPi n m

theorem integral_mul_Hpi (n : ℕ) (m : Fin n → ℕ) (F : (Fin n → ℝ) → ℝ) :
    ∫ x, F x * Hpi n m x ∂gaussPi n = facPi n m * coeffPi n m F := by
  have h := facPi_ne_zero n m
  rw [coeffPi]
  field_simp

/-- The pairing of a basis vector with an arbitrary `L²` vector IS the
    coefficient, up to `√(∏(mᵢ)!)`. -/
theorem inner_eHpi (n : ℕ) (m : Fin n → ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    inner ℝ (eHpi n m) F
      = Real.sqrt (facPi n m) * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) := by
  have hF : (Lp.memLp F).toLp ((F : (Fin n → ℝ) → ℝ)) = F :=
    Lp.toLp_coeFn F (Lp.memLp F)
  have hinner : inner ℝ (HpiL n m) F
      = ∫ x, Hpi n m x * (F : (Fin n → ℝ) → ℝ) x ∂gaussPi n := by
    conv_lhs => rw [← hF]
    simp only [HpiL]
    rw [inner_toLpPi]
  have hcomm : ∫ x, Hpi n m x * (F : (Fin n → ℝ) → ℝ) x ∂gaussPi n
      = ∫ x, (F : (Fin n → ℝ) → ℝ) x * Hpi n m x ∂gaussPi n :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hne := sqrt_facPi_ne_zero n m
  have key : (Real.sqrt (facPi n m))⁻¹ * facPi n m = Real.sqrt (facPi n m) := by
    refine mul_left_cancel₀ hne ?_
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul, sqrt_facPi_mul_self]
  rw [eHpi, real_inner_smul_left, hinner, hcomm, integral_mul_Hpi, ← mul_assoc, key]

/-- The coefficients of a basis vector are the delta — so the coefficient
    map is not the zero map, which is what makes §4 say something. -/
theorem coeffPi_HpiL (n : ℕ) (m k : Fin n → ℕ) :
    coeffPi n k (Hpi n m) = if m = k then 1 else 0 := by
  rw [coeffPi, Hpi_orthogonal n m k]
  split_ifs with h
  · subst h
    exact div_self (facPi_ne_zero n m)
  · exact zero_div _

/-! ## 4. Bessel in n dimensions

Mathlib gives Bessel for any orthonormal family over any index type, so
§2 is the whole cost. The index type here is `Fin n → ℕ` — countably
infinite for `n ≥ 1` — and the summability is over all of it.
-/

theorem norm_sq_eq_integral (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    ‖F‖ ^ 2 = ∫ x, (F : (Fin n → ℝ) → ℝ) x ^ 2 ∂gaussPi n := by
  have hF : (Lp.memLp F).toLp ((F : (Fin n → ℝ) → ℝ)) = F :=
    Lp.toLp_coeFn F (Lp.memLp F)
  have h : inner ℝ F F
      = ∫ x, (F : (Fin n → ℝ) → ℝ) x * (F : (Fin n → ℝ) → ℝ) x ∂gaussPi n := by
    conv_lhs => rw [← hF]
    rw [inner_toLpPi]
  rw [← real_inner_self_eq_norm_sq, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **THE SUMMABILITY.** -/
theorem summable_coeffPi_sq (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    Summable fun m : Fin n → ℕ =>
      facPi n m * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) ^ 2 := by
  have h := (orthonormal_eHpi n).inner_products_summable F
  refine h.congr fun m => ?_
  rw [inner_eHpi, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (facPi_pos n m))]

/-- **BESSEL'S INEQUALITY IN n DIMENSIONS.** For every `F ∈ L²(γⁿ)`,
    `Σ_m (∏ᵢ(mᵢ)!)·c_m(F)² ≤ ∫ F² dγⁿ`. The first quantitative statement
    about ARBITRARY L² functions in n dimensions — every earlier
    n-dimensional result in the estate is about polynomials. -/
theorem bessel_pi (n : ℕ) (F : Lp ℝ 2 (gaussPi n)) :
    ∑' m : Fin n → ℕ, facPi n m * coeffPi n m ((F : (Fin n → ℝ) → ℝ)) ^ 2
      ≤ ∫ x, (F : (Fin n → ℝ) → ℝ) x ^ 2 ∂gaussPi n := by
  have h := (orthonormal_eHpi n).tsum_inner_products_le F
  rw [norm_sq_eq_integral] at h
  refine le_trans (le_of_eq ?_) h
  refine tsum_congr fun m => ?_
  rw [inner_eHpi, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (facPi_pos n m))]

/-! ## 5. Review round 44 — the ways this could be hollow

**"Bessel could be `0 ≤ something`."** It could, if every coefficient
vanished. `coeffPi_HpiL` computes the coefficients of a basis vector and
gets the delta, so the coefficient map is not the zero map and the sum is
not identically zero.

**"The family could be a single vector in disguise."** The index type is
`Fin n → ℕ`, which for `n ≥ 1` is countably infinite, and
`orthonormal_eHpi` gives distinct unit vectors at distinct multi-indices —
`eHpi_ne` records that they really are distinct.

**"This could be the 1-dimensional theorem relabelled."** It is derived
from the 1-dimensional orthogonality, but the statement is not the same
one: the sum runs over multi-indices, and the estate's `HermiteBessel`
does not imply it.

**"It might secretly need N2."** It does not, and that is the point of
the file. `Orthonormal` is a statement about pairwise inner products;
completeness is a statement about the orthogonal complement. Mathlib's
Bessel lemmas take the former only.
-/

/-- Distinct multi-indices give distinct unit vectors, so the family is
    genuinely infinite for `n ≥ 1`. -/
theorem eHpi_ne (n : ℕ) {m k : Fin n → ℕ} (h : m ≠ k) : eHpi n m ≠ eHpi n k := by
  intro hcon
  have h1 : inner ℝ (eHpi n m) (eHpi n k) = 0 := by
    have := (orthonormal_eHpi n).2 h
    exact this
  rw [hcon, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖eHpi n k‖ = 1 := (orthonormal_eHpi n).1 k
  rw [h2] at h1
  norm_num at h1

/-- Bessel is not vacuous: fed a basis vector, the left-hand side is that
    vector's squared norm. That the inequality is then an EQUALITY is
    `bessel_eq_at_basis` below — stated as a theorem rather than left as a
    sentence combining two facts, which is what ERRATA 46 was about. -/
theorem bessel_at_basis (n : ℕ) (m : Fin n → ℕ) :
    ∑' k : Fin n → ℕ, facPi n k * coeffPi n k (Hpi n m) ^ 2 = facPi n m := by
  have hfun : (fun k : Fin n → ℕ => facPi n k * coeffPi n k (Hpi n m) ^ 2)
      = fun k => if k = m then facPi n m else 0 := by
    funext k
    rw [coeffPi_HpiL]
    by_cases h : k = m
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
      ring
  rw [hfun, tsum_ite_eq]

theorem integral_Hpi_sq (n : ℕ) (m : Fin n → ℕ) :
    ∫ x, Hpi n m x ^ 2 ∂gaussPi n = facPi n m := by
  have h := Hpi_norm_sq n m
  rw [facPi, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **Bessel is SHARP at every basis vector**: the inequality of
    `bessel_pi` is an equality there, so the bound is attained and not
    merely true. -/
theorem bessel_eq_at_basis (n : ℕ) (m : Fin n → ℕ) :
    ∑' k : Fin n → ℕ, facPi n k * coeffPi n k (Hpi n m) ^ 2
      = ∫ x, Hpi n m x ^ 2 ∂gaussPi n := by
  rw [bessel_at_basis, integral_Hpi_sq]

end

end HermitePiBessel
