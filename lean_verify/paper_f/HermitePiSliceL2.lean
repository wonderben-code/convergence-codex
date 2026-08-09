/-
  HermitePiSliceL2.lean — residue (i) of the second route: the slice-integral
  is itself square-integrable, so the inductive call is legal.

  WHY. `HermitePiSlice` proved that the slice-integral

      `G_{m₀}(y) = ∫ F(cons x₀ y)·H_{m₀}(x₀) dγ(x₀)`

  inherits orthogonality to every `n`-variable Hermite product. That is one
  of the two hypotheses the inductive call needs. The other is that
  `G_{m₀}` is an `L²(γⁿ)` function at all — the inductive statement
  quantifies over square-integrable functions, and so far `G_{m₀}` was only
  known to be defined almost everywhere. This file supplies it, and the
  route is the one the previous header named: **Cauchy–Schwarz, plus Fubini
  on the square.**

  A NEGATIVE PROBE, RECORDED BECAUSE IT COST THE FIRST SECTION.
  Mathlib does **not** have Cauchy–Schwarz for the Bochner integral in the
  form this needs, `(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. Searched by SHAPE and not by
  name (ERRATA 40/42): Hölder exists as
  `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` but in `rpow` form with
  `(∫ ‖f‖^p)^(1/p)` factors; the abstract inequality exists as
  `abs_real_inner_le_norm` and `inner_mul_inner_self_le` for inner-product
  spaces, which `L²(μ)` is only after passing through `MemLp.toLp`; the
  discrete case is `Finset.sum_mul_sq_le_sq_mul_sq`, whose integral
  namesake does not exist. So §1 proves the squared form directly from the
  discriminant of `t ↦ ∫ (f + t·g)²`, and it is stated for an arbitrary
  measure and arbitrary real `L²` functions because nothing about this
  problem is in it.

  WHAT THIS FILE PROVES:
  * **`sq_integral_mul_le`** — the Cauchy–Schwarz inequality above, general.
  * **`memLp_G`** — the slice-integral is in `L²(γⁿ)`.
  * **`slice_hypothesis`** — the two facts packaged as the pair the
    inductive call consumes: `G_{m₀} ∈ L²(γⁿ)` **and** `G_{m₀}` is
    orthogonal to every `Hpi n m'`.
  * **`G_Hpi`** — non-vacuity with content: computed on a Hermite product,
    `G_{m₀}` is `k₀! · Hpi n k'` when `m₀ = k₀` and `0` otherwise. So the
    construction is not the zero map, and it picks out exactly the
    coordinate it is supposed to.

  WHAT THIS DOES NOT DO. It does not prove completeness. `HermitePiSlice`'s
  header named two outstanding pieces; this file discharges one of them, so
  the second one is what is left of that list: the a.e.-countable-
  intersection over `m₀` that turns "each `G_{m₀}` vanishes a.e." into "for
  a.e. `y`, ALL of them vanish". Beyond that list — named in
  `HermitePiPeel`'s header, not in `HermitePiSlice`'s — the induction still
  needs its two appeals to `hermite_complete`, once at dimension `n`
  through the inductive hypothesis and once at dimension 1 on the slices,
  and a final Fubini. Three things remain, not one.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiSlice

namespace HermitePiSliceL2

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiPeel HermitePiSlice

noncomputable section

/-! ## 1. Cauchy–Schwarz for the Bochner integral, squared form

Absent from Mathlib in this shape (see the header for what was searched).
The proof is the classical one: the quadratic `t ↦ ∫ (f + t·g)²` is
nonnegative, so its discriminant is nonpositive.
-/

/-- **Cauchy–Schwarz for the Bochner integral.** For real `L²` functions
    against any measure, `(∫ f·g)² ≤ (∫ f²)·(∫ g²)`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hg2 : Integrable (fun x => g x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have key : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (t * t)
      + (2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x ^ 2 ∂μ := by
    intro t
    have hnn : (0:ℝ) ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ :=
      integral_nonneg fun x => sq_nonneg _
    have hpt : ∀ x, (f x + t * g x) ^ 2
        = f x ^ 2 + (2 * t) * (f x * g x) + (t * t) * g x ^ 2 := fun x => by ring
    have hi1 : Integrable (fun x => (2 * t) * (f x * g x)) μ := hfg.const_mul _
    have hi2 : Integrable (fun x => (t * t) * g x ^ 2) μ := hg2.const_mul _
    have hi3 : Integrable (fun x => f x ^ 2 + (2 * t) * (f x * g x)) μ := hf2.add hi1
    have hexp : (∫ x, (f x + t * g x) ^ 2 ∂μ)
        = (∫ x, g x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x ^ 2 ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_add hi3 hi2, integral_add hf2 hi1, integral_const_mul, integral_const_mul]
      ring
    rw [hexp] at hnn
    exact hnn
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-! ## 2. The slice-integral -/

/-- The slice-integral `G_{m₀}(y) = ∫ F(cons x₀ y)·H_{m₀}(x₀) dγ(x₀)`, named
    so that the two facts about it can be stated together. -/
def G (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ) (m₀ : ℕ) (y : Fin n → ℝ) : ℝ :=
  ∫ x₀, F (Fin.cons x₀ y) * (H m₀).eval x₀ ∂(gaussianReal 0 1)

/-- The one-dimensional Hermite functions are in `L²(γ)` — the second
    argument of every Cauchy–Schwarz step below. -/
theorem memLp_H (j : ℕ) : MemLp (fun x : ℝ => (H j).eval x) 2 gauss :=
  (memLp_two_iff_integrable_sq (Polynomial.continuous (H j)).aestronglyMeasurable).mpr
    (integrable_H_sq j)

/-- `∫ H_{j}² dγ = j!`, which is `hermite_orthogonal_gauss` at `m = n` with
    the product written as a square. -/
theorem integral_H_sq (j : ℕ) : ∫ x, ((H j).eval x) ^ 2 ∂gauss = (j.factorial : ℝ) := by
  have h := hermite_orthogonal_gauss j j
  rw [if_pos rfl] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  exact pow_two _

/-- The multi-index system at the zero index is the constant `1`. -/
theorem Hpi_zero_index (n : ℕ) (y : Fin n → ℝ) : Hpi n (fun _ => 0) y = 1 := by
  simp [Hpi]

/-- The integrand of `G`, on the product measure. Obtained from
    `HermitePiSlice.integrable_cons_mul` at the zero multi-index rather than
    re-derived — the `Hpi n 0` factor is the constant `1`. -/
theorem integrable_cons_mul_H (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m₀ : ℕ) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) * (H m₀).eval p.1)
      ((gaussianReal 0 1).prod (gaussPi n)) := by
  have hz := integrable_cons_mul n hF m₀ (fun _ => 0)
  refine hz.congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [Hpi_zero_index, mul_one]

/-! ## 3. Residue (i): the slice-integral is square-integrable -/

/-- **The slices are in `L²(γ)` almost everywhere.** Stated rather than left
    inside `memLp_G`'s proof, because the induction consumes it directly and
    `HermitePiPeel` recorded the lesson: machinery buried in a proof is
    machinery the next person rebuilds.

    Both halves are needed and neither is enough — `F` integrable gives the
    slice a.e. strongly measurable, `F²` integrable gives its square a.e.
    integrable, and `L²` is exactly the conjunction. -/
theorem memLp_slice_ae (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) :
    ∀ᵐ y ∂gaussPi n, MemLp (fun x₀ => F (Fin.cons x₀ y)) 2 (gaussianReal 0 1) := by
  have hFint : Integrable F (gaussPi (n + 1)) := hF.integrable one_le_two
  have hF2 : Integrable (fun z => F z ^ 2) (gaussPi (n + 1)) :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  filter_upwards [(integrable_peel n hFint).prod_left_ae,
    (integrable_peel n hF2).prod_left_ae] with y h1 h2
  exact (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).mpr h2

/-- **THE MISSING HALF OF THE INDUCTIVE CALL'S HYPOTHESIS.** If `F` is in
    `L²(γⁿ⁺¹)` then each slice-integral `G_{m₀}` is in `L²(γⁿ)`.

    The bound is `G_{m₀}(y)² ≤ m₀! · ∫ F(cons x₀ y)² dγ(x₀)` — Cauchy–Schwarz
    in the first coordinate — and the right-hand side is integrable in `y`
    because `F²` is integrable on the product, which is Fubini on the
    square. -/
theorem memLp_G (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m₀ : ℕ) :
    MemLp (G n F m₀) 2 (gaussPi n) := by
  have hF2 : Integrable (fun z => F z ^ 2) (gaussPi (n + 1)) :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hPhi2 : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2) ^ 2)
      ((gaussianReal 0 1).prod (gaussPi n)) := integrable_peel n hF2
  -- a.e. in `y`, the slice is itself an L² function of one variable
  have hslice : ∀ᵐ y ∂gaussPi n,
      MemLp (fun x₀ => F (Fin.cons x₀ y)) 2 (gaussianReal 0 1) := memLp_slice_ae n hF
  -- Cauchy–Schwarz, pointwise in `y`
  have hCS : ∀ᵐ y ∂gaussPi n, G n F m₀ y ^ 2
      ≤ (∫ x₀, F (Fin.cons x₀ y) ^ 2 ∂(gaussianReal 0 1)) * (m₀.factorial : ℝ) := by
    filter_upwards [hslice] with y hy
    have hcs := sq_integral_mul_le hy (memLp_H m₀)
    rwa [integral_H_sq] at hcs
  -- Fubini on the square: the dominating function is integrable in `y`
  have hPsi : Integrable
      (fun y => ∫ x₀, F (Fin.cons x₀ y) ^ 2 ∂(gaussianReal 0 1)) (gaussPi n) :=
    hPhi2.integral_prod_right
  have hGaesm : AEStronglyMeasurable (G n F m₀) (gaussPi n) :=
    (integrable_cons_mul_H n hF m₀).integral_prod_right.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hGaesm).mpr ?_
  refine Integrable.mono' (hPsi.mul_const (m₀.factorial : ℝ)) (hGaesm.pow 2) ?_
  filter_upwards [hCS] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hy

/-- **THE INDUCTIVE CALL'S HYPOTHESIS, COMPLETE.** If `F` is orthogonal to
    every `(n+1)`-variable Hermite product, then for each `m₀` the
    slice-integral `G_{m₀}` is a square-integrable function on `ℝⁿ`
    orthogonal to every `n`-variable Hermite product — which is precisely
    what the inductive hypothesis is applied to. -/
theorem slice_hypothesis (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m₀ : ℕ)
    (h : ∀ m : Fin (n + 1) → ℕ, ∫ x, F x * Hpi (n + 1) m x ∂gaussPi (n + 1) = 0) :
    MemLp (G n F m₀) 2 (gaussPi n) ∧
      ∀ m' : Fin n → ℕ, ∫ y, G n F m₀ y * Hpi n m' y ∂gaussPi n = 0 :=
  ⟨memLp_G n hF m₀, fun m' => slice_orthogonality n hF m₀ m' (h (Fin.cons m₀ m'))⟩

/-! ## 4. Non-vacuity, with content

A construction that is identically zero would satisfy everything above.
Computing `G` on a Hermite product shows it is not, and shows it does the
job it was built for: it reads off the `m₀`-th one-dimensional coordinate
and leaves the rest alone.
-/

/-- `G_{m₀}` applied to the Hermite product indexed by `cons k₀ k'` is
    `k₀!·Hpi n k'` when `m₀ = k₀`, and `0` otherwise. -/
theorem G_Hpi (n : ℕ) (k₀ m₀ : ℕ) (k' : Fin n → ℕ) (y : Fin n → ℝ) :
    G n (Hpi (n + 1) (Fin.cons k₀ k')) m₀ y
      = (if k₀ = m₀ then (k₀.factorial : ℝ) else 0) * Hpi n k' y := by
  rw [G]
  have hpt : ∀ x₀ : ℝ,
      Hpi (n + 1) (Fin.cons k₀ k') (Fin.cons x₀ y) * (H m₀).eval x₀
        = ((H k₀).eval x₀ * (H m₀).eval x₀) * Hpi n k' y := by
    intro x₀
    rw [Hpi_cons' n k₀ k' x₀ y]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const,
    hermite_orthogonal_gauss]

/-- At the matching index the slice-integral is a nonzero multiple of the
    `n`-variable Hermite product, so `G` is genuinely not the zero map. -/
theorem G_Hpi_self (n : ℕ) (k₀ : ℕ) (k' : Fin n → ℕ) (y : Fin n → ℝ) :
    G n (Hpi (n + 1) (Fin.cons k₀ k')) k₀ y = (k₀.factorial : ℝ) * Hpi n k' y := by
  rw [G_Hpi, if_pos rfl]

/-- And at a non-matching index it vanishes identically — the two halves
    together are the statement that `G_{m₀}` extracts one coordinate. -/
theorem G_Hpi_ne (n : ℕ) {k₀ m₀ : ℕ} (h : k₀ ≠ m₀) (k' : Fin n → ℕ) (y : Fin n → ℝ) :
    G n (Hpi (n + 1) (Fin.cons k₀ k')) m₀ y = 0 := by
  rw [G_Hpi, if_neg h, zero_mul]

/-! ## 5. Review round 49 — the ways this could be hollow

**"The Cauchy–Schwarz lemma could be in Mathlib and I missed it."** It could
be, and the header records the SHAPE searched rather than a name, because
`exact?` is not a probe and a remembered absence decays (ERRATA 40/42). What
Mathlib has is the `rpow` Hölder form and the inner-product-space form; the
squared Bochner form is what §3 consumes, and §1 is twenty-eight lines, so
the cost of the duplication if it exists is small and the cost of the rpow
juggling if it does not is not. **Two citations in that header were checked
against the library rather than remembered, and one of them was wrong**: the
discrete Cauchy–Schwarz is `Finset.sum_mul_sq_le_sq_mul_sq`, not the
`inner_mul_le_norm_mul_norm` spelling first written. Corrected before push,
recorded here because a header citing a lemma that does not exist is the
defect ERRATUM 46 is about.

**"`memLp_G` could be vacuous because `G` is a.e. undefined."** The two
`prod_left_ae` facts are exactly what rules that out: `F` and `F²` are both
integrable on the product, so for a.e. `y` the slice is an honest `L²(γ)`
function and the integral defining `G y` converges. The a.e.-strong
measurability of `G` itself is separate and comes from
`Integrable.integral_prod_right`, not from the pointwise bound.

**"`slice_hypothesis` could be a restatement of its two conjuncts."** It is
a restatement, and the reason it earns a name is ERRATUM 48: the check on a
unit whose contribution is "this makes X possible" is to attempt X. `X` here
is the inductive call, and its hypothesis is a CONJUNCTION that no single
previous file stated. Writing it down is how one finds out whether the two
halves have the same `F`, the same `m₀`, and the same measure — they do.

**"The non-vacuity could be trivial."** `G_Hpi` is a computation, not an
existence claim, and it says something the construction was supposed to do
but had not been checked to do: `G_{m₀}` annihilates every Hermite product
whose first index is not `m₀` and rescales the one whose first index is.
That is the property the induction relies on, and it is now a theorem rather
than an expectation.
-/

end

end HermitePiSliceL2
