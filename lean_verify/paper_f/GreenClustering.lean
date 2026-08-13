import GreenDecay

/-!
# The free field clusters exponentially, at every order at once

`GreenDecay` bounds the **two-point** function and its header names what stops that being
clustering: the higher correlations, which the textbook obtains from the two-point function by
**Wick's moment formula**. That formula is not in this estate (`GreenDecay` §"What this is NOT")
and — probed against the pinned environment on 2026-08-13, by name and by shape — **it is not in
Mathlib either**: `grep -rli isserlis Mathlib/` returns zero files; `Wick` returns zero
declarations under `Mathlib/Probability/`; and `Gaussian/Real.lean` carries the
moment *generating* function, `variance_id_gaussianReal`, and
`memLp_id_gaussianReal` — *"all the moments are finite"* — but **no moment identity at all**, in
one variable or several. `Gaussian/Multivariate.lean` has the mean, the covariance bilinear form,
the entrywise covariance and the characteristic function, and nothing of higher order.

**So this file does not go through Wick.** `PROOF_STRATEGY` §3's rule — when B lands, re-attempt
B → C immediately — and the re-attempt found that the C is reachable by a different road, because
the estate already has the object that packages every order simultaneously.

## What is delivered

`LatticeGeneratingFunctional.generatingFunctional` says `Z(f) := ∫ exp ⟪f, ω⟫ = exp(½ · f·Cf)`.
Quadratic expansion is therefore an exact factorisation:

    Z(f + g)  =  Z(f) · Z(g) · exp (f · C g)          (`generatingFunctional_add`)

with **no hypothesis on the supports** — that is an identity, not an estimate. The estimate is the
cross term, and it is where `GreenDecay` enters: if every site where `f` lives is at least `N`
steps from every site where `g` lives, then

    |f · C g|  ≤  ‖f‖₁ · ‖g‖₁ · (Δ/(Δ+m²))^N · (m²)⁻¹   (`cross_abs_le`)

and the two statements together give

    |Z(f + g) − Z(f)·Z(g)|  ≤  Z(f)·Z(g) · (exp(that bound) − 1)   (`clustering`)

with `log_clustering` the same thing written additively, where the bound *is* the cross term and
no `exp` inequality is spent.

**Why this is "every order at once" and not a fourth statement about pairs, and exactly how far
that goes.** Exponentials of linear observables are the algebra the estate already states OS2 on —
though with a difference worth naming: `OS2Exponential.os2_exponential` and
`GraphOS2Exponential` work with `e^{iφ(t)}`, whose integrand has modulus one, and this file works
with the **real** exponential, whose integrability is `LatticeGeneratingFunctional`'s
`integrable_exp_inner` and is a fact about the tail. The bound below holds for **all** `f, g`
simultaneously, so it is a statement about the whole algebra rather than about one correlation.

**What is not claimed, and it is the honest boundary of "every order".** No individual higher
correlation is written down here. Recovering `E[ω_{p₁}⋯ω_{p_k}]` from `Z` means differentiating
under the integral sign `k` times, which is not done in this file and is not free; and the
resulting identity would *be* Wick's formula, which is the thing recorded above as absent. So the
correct reading is: **the generating functional clusters**, and every consequence that follows
from that *without* extracting coefficients follows. Extraction does not.

## Uniform in the volume, because `GreenDecay` was

`Δ` is a parameter, so on `boxGraph d n` and `torusGraph d n` the rate is `2d/(2d+m²)` at every
side length (`GreenDecay.boxGraph_green_abs_le`, `TorusDecay.torusGraph_green_abs_le`). The
constants `‖f‖₁‖g‖₁` are the test functions', not the volume's.

## What this is NOT

**It is still not OS4**, and the missing pieces are the ones `GreenDecay` listed minus one. The
higher-correlation gap is the one this file closes, in the generating-functional sense above and
in no other. **The infinite-volume limit and the continuum are untouched**, and no theorem here
should be recorded as OS4. The watchlist item keeps `OS4` open.

**And the separation hypothesis is stated on the sites, not on regions.** `hsep` says every `p`
with `f p ≠ 0` is at distance `≥ N` from every `q` with `g q ≠ 0`. There is no `Finset`-valued
notion of the distance between two regions anywhere in `paper_f` — grepped for `setDist`,
`regionDist`, and `Finset` next to `dist`, all zero — so introducing one here would be a
definition with a single user. A consumer that has two regions instantiates `hsep` by unfolding
its own supports.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenClustering

open GraphLaplacian GreenDecay MeasureTheory ProbabilityTheory Matrix Finset
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The quadratic form, expanded -/

omit [DecidableEq V] in
theorem dotProduct_mulVec_eq (M : Matrix V V ℝ) (x y : V → ℝ) :
    x ⬝ᵥ M *ᵥ y = ∑ p, ∑ q, x p * M p q * y q := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The Green form is symmetric in its two arguments, which is the one place `green_isSymm` is
spent below. -/
theorem green_swap (hm : m ≠ 0) (x y : V → ℝ) :
    x ⬝ᵥ green G m *ᵥ y = y ⬝ᵥ green G m *ᵥ x := by
  rw [dotProduct_mulVec_eq, dotProduct_mulVec_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [(green_isSymm G hm).apply q p]
  ring

/-- **THE CROSS TERM APPEARS ONCE, DOUBLED.** -/
theorem quad_add (hm : m ≠ 0) (f g : V → ℝ) :
    (f + g) ⬝ᵥ green G m *ᵥ (f + g)
      = f ⬝ᵥ green G m *ᵥ f + 2 * (f ⬝ᵥ green G m *ᵥ g) + g ⬝ᵥ green G m *ᵥ g := by
  have hgf : g ⬝ᵥ green G m *ᵥ f = f ⬝ᵥ green G m *ᵥ g := green_swap hm g f
  simp only [dotProduct_mulVec_eq, Pi.add_apply] at hgf ⊢
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  linarith [hgf]

/-! ## 2. The factorisation, which is exact -/

/-- **THE GENERATING FUNCTIONAL FACTORISES EXACTLY, WITH THE CROSS TERM AS THE ONLY DEFECT.** No
hypothesis on the supports of `f` and `g`: this is an identity. -/
theorem generatingFunctional_add (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    ∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m)
      = (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
          * (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m))
          * Real.exp (f ⬝ᵥ green G m *ᵥ g) := by
  rw [LatticeGeneratingFunctional.generatingFunctional hm (f + g),
    LatticeGeneratingFunctional.generatingFunctional hm f,
    LatticeGeneratingFunctional.generatingFunctional hm g,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  have h := quad_add (G := G) hm (WithLp.ofLp f) (WithLp.ofLp g)
  simp only [] at h ⊢
  rw [show ((f : V → ℝ) + (g : V → ℝ)) = ((f + g : EuclideanSpace ℝ V) : V → ℝ) from rfl] at h
  rw [h]; ring

/-- **THE ADDITIVE FORM.** `log Z` is exactly additive up to the cross term — no inequality is
spent here, so this is the sharpest statement in the file and the one an estimate should quote. -/
theorem log_generatingFunctional_add (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    Real.log (∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m))
        - Real.log (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
        - Real.log (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m))
      = f ⬝ᵥ green G m *ᵥ g := by
  rw [LatticeGeneratingFunctional.generatingFunctional hm (f + g),
    LatticeGeneratingFunctional.generatingFunctional hm f,
    LatticeGeneratingFunctional.generatingFunctional hm g,
    Real.log_exp, Real.log_exp, Real.log_exp]
  have h := quad_add (G := G) hm (WithLp.ofLp f) (WithLp.ofLp g)
  rw [show ((f : V → ℝ) + (g : V → ℝ)) = ((f + g : EuclideanSpace ℝ V) : V → ℝ) from rfl] at h
  rw [h]; ring

/-! ## 3. The cross term is small when the supports are far apart -/

/-- **THE ESTIMATE.** `GreenDecay` enters here and nowhere else. -/
theorem cross_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : V → ℝ) (hsep : ∀ p q, f p ≠ 0 → g q ≠ 0 → N ≤ G.dist p q) :
    |f ⬝ᵥ green G m *ᵥ g|
      ≤ (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  set C : ℝ := decayRate Δ m ^ N * (m ^ 2)⁻¹ with hC
  have hC0 : 0 ≤ C := by
    have := decayRate_nonneg Δ (m := m) hm
    positivity
  have hterm : ∀ p q : V, |f p * green G m p q * g q| ≤ |f p| * |g q| * C := by
    intro p q
    by_cases hfp : f p = 0
    · simp [hfp]
    by_cases hgq : g q = 0
    · simp [hgq]
    have hgreen : |green G m p q| ≤ C :=
      green_abs_le_pow hm hΔ N p q (hsep p q hfp hgq)
    calc |f p * green G m p q * g q| = |f p| * |green G m p q| * |g q| := by
          rw [abs_mul, abs_mul]
      _ ≤ |f p| * C * |g q| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgreen (abs_nonneg _)) (abs_nonneg _)
      _ = |f p| * |g q| * C := by ring
  calc |f ⬝ᵥ green G m *ᵥ g| = |∑ p, ∑ q, f p * green G m p q * g q| := by
        rw [dotProduct_mulVec_eq]
    _ ≤ ∑ p, |∑ q, f p * green G m p q * g q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |f p * green G m p q * g q| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |f p| * |g q| * C :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = (∑ p, |f p|) * (∑ q, |g q|) * C := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by
          rw [← Finset.sum_mul, ← Finset.mul_sum]

/-! ## 4. Clustering -/

/-- `|e^c − 1| ≤ e^{|c|} − 1`, which is the only inequality between §3 and the conclusion. The
negative branch is `e^c + e^{-c} ≥ 2`, i.e. `(e^c − 1)² ≥ 0`. -/
theorem abs_exp_sub_one_le (c : ℝ) : |Real.exp c - 1| ≤ Real.exp |c| - 1 := by
  by_cases hc0 : 0 ≤ c
  · rw [abs_of_nonneg hc0, abs_of_nonneg (by simpa using Real.one_le_exp hc0)]
  · have hc : c < 0 := not_le.mp hc0
    rw [abs_of_neg hc]
    have h1 : Real.exp c < 1 := Real.exp_lt_one_iff.mpr hc
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-c) = (Real.exp c)⁻¹ := Real.exp_neg c
    have h3 : (0 : ℝ) < Real.exp c := Real.exp_pos c
    rw [h2, le_sub_iff_add_le]
    have hinv : (Real.exp c)⁻¹ * Real.exp c = 1 := inv_mul_cancel₀ (ne_of_gt h3)
    nlinarith [sq_nonneg (Real.exp c - 1), h3, hinv]

/-- **EXPONENTIAL CLUSTERING OF THE FREE LATTICE FIELD.** For test functions living `N` steps
apart, the generating functional factorises up to an error that is geometric in `N` at a rate
depending only on the degree bound and the mass. -/
theorem clustering (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f p ≠ 0 → g q ≠ 0 → N ≤ G.dist p q) :
    |(∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m))
        - (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
          * (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m))|
      ≤ (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
          * (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m))
          * (Real.exp ((∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) - 1) := by
  set Zf : ℝ := ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) with hZf
  set Zg : ℝ := ∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m) with hZg
  set c : ℝ := (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) with hc
  set B : ℝ := (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) with hB
  have hZfpos : 0 < Zf := by
    rw [hZf, LatticeGeneratingFunctional.generatingFunctional hm f]; exact Real.exp_pos _
  have hZgpos : 0 < Zg := by
    rw [hZg, LatticeGeneratingFunctional.generatingFunctional hm g]; exact Real.exp_pos _
  have hfact : (∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m)) = Zf * Zg * Real.exp c :=
    generatingFunctional_add hm f g
  have hcb : |c| ≤ B := cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp g) hsep
  have hstep : |Real.exp c - 1| ≤ Real.exp B - 1 :=
    (abs_exp_sub_one_le c).trans (by
      have := Real.exp_le_exp.mpr hcb
      linarith)
  rw [hfact]
  have hrw : Zf * Zg * Real.exp c - Zf * Zg = (Zf * Zg) * (Real.exp c - 1) := by ring
  rw [hrw, abs_mul, abs_of_pos (mul_pos hZfpos hZgpos)]
  exact mul_le_mul_of_nonneg_left hstep (mul_pos hZfpos hZgpos).le

/-- **THE SAME, ADDITIVELY**, and here the bound is the cross term itself with no `exp` inequality
in the way. -/
theorem log_clustering (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f p ≠ 0 → g q ≠ 0 → N ≤ G.dist p q) :
    |Real.log (∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m))
        - Real.log (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
        - Real.log (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m))|
      ≤ (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) := by
  rw [log_generatingFunctional_add hm f g]
  exact cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp g) hsep

end GreenClustering
