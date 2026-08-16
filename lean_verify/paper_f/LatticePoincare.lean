import LatticeHigherClustering
import PoincareSteinScaled

/-!
# The Poincaré inequality for a CORRELATED Gaussian field

Every Poincaré inequality in this estate is for a **product** measure — independent coordinates,
built up one at a time through the `Hermite*` and `*Pi` chains. `gaussianField G m` is not a
product measure: its coordinates are correlated by the Green function, which is the entire point of
it. **So none of that machinery has ever applied to the lattice field.**

This removes that restriction along one direction at a time, and the removal is almost free,
because the bridge was already built and had never been used.

## The fence, and why nobody had noticed it was down

`LatticeGeneratingFunctional.map_pair` (`74db57b`, and it has been there since the generating
functional was written) says:

```
(gaussianField G m).map (pair f) = gaussianReal 0 (fᵀGf).toNNReal
```

**The smeared field is a centred real Gaussian whose variance is the Green quadratic form.** That
is a `B` in `PROOF_STRATEGY` §3's sense — and `grep` says it is consumed by **nothing outside its
own file**. It was proved on the way to the generating functional, used once, and never asked what
else it made true.

What it makes true is everything the estate knows about one real Gaussian variable. This file
takes the first of those: `PoincareSteinScaled.poincare_scaled_beyond_original`, the σ-scaled
Poincaré inequality for `C¹` functions of polynomial growth, which was proved for
`gaussianReal 0 ⟨σ²,_⟩` and never met a field.

## What is proved

* `sq_sqrt_linVar` — `√(fᵀGf)² = fᵀGf`, which needs `fᵀGf ≥ 0`; that is
  `LatticeHigherClustering.linVar_nonneg`, proved earlier today for an unrelated reason;
* `nnreal_linVar` — the two spellings of the variance agree, `⟨√(fᵀGf)², _⟩ = (fᵀGf).toNNReal`;
* `integral_comp_pair` — the transport, `∫ x, F x ∂(μ.map (pair f)) = ∫ ω, F ⟪f,ω⟫ ∂μ`, by
  `integral_map` with `pair f` a continuous linear map;
* **`poincare_smeared`** — the theorem:

  ```
  ∫ F(⟪f,ω⟫)² dμ − (∫ F(⟪f,ω⟫) dμ)²  ≤  (fᵀGf) · ∫ F′(⟪f,ω⟫)² dμ
  ```

  for every `C¹` `F : ℝ → ℝ` of polynomial growth, on **every** finite simple graph, at **every**
  nonzero mass. This is the first Poincaré inequality in the estate for a measure whose
  coordinates are not independent;
* `poincare_smeared_id` — the sharpness check: at `F = id` the inequality is an **equality**, both
  sides being `fᵀGf`, so the constant cannot be improved by any argument;
* **`memLp_comp_pair`** — the observable is square-integrable, so the left-hand side is a variance
  and not a formal difference. **This replaced a defect found in adversarial review:** the file's
  first draft carried a `var_smeared_le` that restated `poincare_smeared` character for character
  under a docstring claiming it was "the same in `Var` notation". The finding is folded back by
  proving the thing that was actually missing rather than by editing the docstring.

**The `Var`-notation restatement is deliberately not included.** With `memLp_comp_pair` in hand it
is a spelling change over `poincare_smeared`, and a declaration that only respells an adjacent one
is what the defect above was.

## What this is NOT

**It is one direction at a time.** `F(⟪f,ω⟫)` is a function of a *single* linear functional of the
field. The full Poincaré inequality for `gaussianField G m` bounds `Var F` for `F` a function of
**all** the coordinates, by `∫ ⟪∇F, G ∇F⟩`, and nothing here approaches that: the transport works
precisely because the pushforward along one functional is one-dimensional. **The correlated
multi-dimensional inequality is untouched and is not costed here** (`ERRATUM 183`).

**And no spectral gap is claimed for the field.** A gap statement quantifies over an algebra of
observables; this quantifies over `C¹` functions of one fixed smearing.

**OS4 does not move**, and nothing here is infinite-volume. **No published tag moves.**
-/

namespace LatticePoincare

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlisSmeared LatticeGeneratingFunctional LatticeHigherClustering
open LatticeIsserlis LatticeIsserlisFour

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The variance, in the two spellings the two sides use -/

/-- The Green quadratic form is a square, because it is nonnegative — which is
`LatticeHigherClustering.linVar_nonneg`, proved for the clustering bounds and reused here. -/
theorem sq_sqrt_linVar (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Real.sqrt (linVar G m f) ^ 2 = linVar G m f :=
  Real.sq_sqrt (linVar_nonneg hm f)

/-- `PoincareSteinScaled` indexes by `σ` and `map_pair` by `toNNReal`; these are the same. -/
theorem nnreal_linVar (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    (⟨Real.sqrt (linVar G m f) ^ 2, sq_nonneg _⟩ : NNReal)
      = (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal := by
  have h : Real.sqrt (linVar G m f) ^ 2 = f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp :=
    sq_sqrt_linVar hm f
  rw [Real.toNNReal_of_nonneg (h ▸ sq_nonneg _)]
  exact NNReal.coe_injective (by simpa using h)

/-! ## 2. The transport -/

/-- **THE BRIDGE, USED FOR THE FIRST TIME.** `pair f` is a continuous linear map, hence measurable,
so `integral_map` moves any integral against the pushforward back to one against the field. -/
theorem integral_comp_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ x, F x ∂(gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal)
      = ∫ ω, F (inner ℝ f ω : ℝ) ∂(gaussianField G m) := by
  rw [← map_pair hm f]
  rw [integral_map (pair f).continuous.measurable.aemeasurable hF.aestronglyMeasurable]
  rfl

/-! ## 3. The inequality -/

/-- **POINCARÉ FOR THE SMEARED LATTICE FIELD.**

`∫ F(⟪f,ω⟫)² − (∫ F(⟪f,ω⟫))² ≤ (fᵀGf)·∫ F′(⟪f,ω⟫)²`, on every finite simple graph, at every
nonzero mass, for every `C¹` `F` of polynomial growth.

**The measure is correlated and every previous Poincaré inequality in this estate was not.** What
makes it work is that the pushforward along one linear functional is one-dimensional, so the
one-dimensional theorem applies to it verbatim; the whole content is that `map_pair` identifies
that pushforward exactly, variance and all. -/
theorem poincare_smeared (hm : m ≠ 0) (f : EuclideanSpace ℝ V) {F F' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt F (F' x) x) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k)
    (hb' : ∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k) :
    (∫ ω, F (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, F (inner ℝ f ω : ℝ) ∂(gaussianField G m)) ^ 2
      ≤ linVar G m f * ∫ ω, F' (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m) := by
  have hFd : Differentiable ℝ F := fun x => (hderiv x).differentiableAt
  have hFc : Continuous F := hFd.continuous
  have hF'c : AEStronglyMeasurable F'
      (gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal) := by
    have hfd : F' = deriv F := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact (measurable_deriv F).aestronglyMeasurable
  have key := PoincareSteinScaled.poincare_scaled_beyond_original
    (Real.sqrt (linVar G m f)) hderiv hb hb'
  rw [nnreal_linVar hm f] at key
  rw [sq_sqrt_linVar hm f] at key
  -- move the three integrals across the pushforward
  rw [integral_comp_pair hm f (F := fun x => F x ^ 2) (hFc.pow 2),
    integral_comp_pair hm f hFc] at key
  have hlast : ∫ x, F' x ^ 2
      ∂(gaussianReal 0 (f.ofLp ⬝ᵥ (green G m).mulVec f.ofLp).toNNReal)
      = ∫ ω, F' (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m) := by
    rw [← map_pair hm f]
    rw [integral_map (pair f).continuous.measurable.aemeasurable
      (by rw [map_pair hm f]; exact (hF'c.pow 2))]
    rfl
  rw [hlast] at key
  exact key

/-- **THE OBSERVABLE IS SQUARE-INTEGRABLE**, which is what makes the left-hand side above a
variance rather than a formal difference. Polynomial growth composed with a smeared field is
dominated by one even power of that field, and `LatticeIsserlis.integrable_pow_pair` integrates
every one of those.

*A first draft of this section carried a `var_smeared_le` stating the theorem above verbatim, with
a docstring claiming it was "the same in `Var` notation". It was not — it was the same statement,
character for character, and the docstring was false. It is replaced by this lemma, which is the
hypothesis any genuine `Var` restatement needs and which the file did not have.* -/
theorem memLp_comp_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) {F : ℝ → ℝ}
    (hFc : Continuous F) {C : ℝ} {k : ℕ} (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k) :
    MemLp (fun ω => F (inner ℝ f ω : ℝ)) 2 (gaussianField G m) := by
  have hmeas : AEStronglyMeasurable (fun ω : EuclideanSpace ℝ V => F (inner ℝ f ω : ℝ))
      (gaussianField G m) :=
    (hFc.comp (LatticeIsserlisFour.continuous_pair f)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hbnd : Integrable (fun ω : EuclideanSpace ℝ V =>
      C ^ 2 * (2 ^ (2 * k) * (1 + (inner ℝ f ω : ℝ) ^ (4 * k)))) (gaussianField G m) := by
    have h1 : Integrable (fun _ : EuclideanSpace ℝ V => (1 : ℝ)) (gaussianField G m) :=
      integrable_const 1
    have h2 : Integrable (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ) ^ (4 * k))
        (gaussianField G m) := LatticeIsserlis.integrable_pow_pair (G := G) hm f _
    exact ((h1.add h2).const_mul _).const_mul _
  refine Integrable.mono' hbnd (hmeas.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
  set x : ℝ := (inner ℝ f ω : ℝ) with hx
  have hC : 0 ≤ C * (1 + x ^ 2) ^ k := le_trans (abs_nonneg _) (hb x)
  have hsq : F x ^ 2 ≤ C ^ 2 * (1 + x ^ 2) ^ (2 * k) := by
    have h := hb x
    have h2 : F x ^ 2 ≤ (C * (1 + x ^ 2) ^ k) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc F x ^ 2 ≤ (C * (1 + x ^ 2) ^ k) ^ 2 := h2
      _ = C ^ 2 * (1 + x ^ 2) ^ (2 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 2]
  have hsplit : (1 + x ^ 2) ^ (2 * k) ≤ 2 ^ (2 * k) * (1 + x ^ (4 * k)) := by
    have h := add_pow_le (zero_le_one (α := ℝ)) (sq_nonneg x) (2 * k)
    have hpow : ((x ^ 2) ^ (2 * k) : ℝ) = x ^ (4 * k) := by
      rw [← pow_mul]; ring_nf
    have hmono : (2 : ℝ) ^ (2 * k - 1) ≤ 2 ^ (2 * k) :=
      pow_le_pow_right₀ one_le_two (by omega)
    have hnn : (0 : ℝ) ≤ 1 ^ (2 * k) + (x ^ 2) ^ (2 * k) := by positivity
    calc (1 + x ^ 2) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (1 ^ (2 * k) + (x ^ 2) ^ (2 * k)) := h
      _ ≤ 2 ^ (2 * k) * (1 ^ (2 * k) + (x ^ 2) ^ (2 * k)) :=
          mul_le_mul_of_nonneg_right hmono hnn
      _ = 2 ^ (2 * k) * (1 + x ^ (4 * k)) := by rw [hpow, one_pow]
  have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  calc ‖F x ^ 2‖ = F x ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ C ^ 2 * (1 + x ^ 2) ^ (2 * k) := hsq
    _ ≤ C ^ 2 * (2 ^ (2 * k) * (1 + x ^ (4 * k))) := mul_le_mul_of_nonneg_left hsplit hC2

/-! ## 4. Sharpness -/

/-- **AT `F = id` IT IS AN EQUALITY**, both sides being `fᵀGf` — so the constant is sharp and
cannot be improved by any argument. `moment_two_of_general` and `moment_odd` supply both sides. -/
theorem poincare_smeared_id (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ∂(gaussianField G m)) ^ 2
      = linVar G m f * ∫ _, (1 : ℝ) ^ 2 ∂(gaussianField G m) := by
  have h1 := LatticeMomentsGeneral.moment_two_of_general (G := G) hm f
  have h2 := LatticeMomentsGeneral.moment_odd (G := G) hm f 0
  norm_num at h2
  rw [h1, h2]
  simp

end LatticePoincare
