import LatticeCorrelatedPoincare

/-!
# The variance bound that does not know how big the box is

`LatticeCorrelatedPoincare.poincare_correlated_general` proved

```
∫Φ² dμ − (∫Φ dμ)²  ≤  ∫ (∂Φ) ⬝ᵥ G *ᵥ (∂Φ) dμ
```

against `gaussianField K m`, at every finite vertex type. **The constant on the right is the
propagator's own quadratic form, so it grows with the graph.** That is the correct sharp
statement and it is useless for the one thing the estate most wants from it: an estimate that
survives taking the box to infinity.

This file trades the sharpness for uniformity:

```
∫Φ² dμ − (∫Φ dμ)²  ≤  m⁻² · ∫ ∑ⱼ (∂ⱼΦ)² dμ
```

**The constant is `m⁻²`. It does not mention the graph, its size, its degree, or its
geometry** — the same number serves `boxGraph` at side length 3 and at side length 3000.

## This is a WEAKENING, and saying otherwise would be a lie

`poincare_uniform` is a **corollary** of `poincare_correlated_general`, obtained by throwing
away everything the propagator knows and keeping only its largest eigenvalue. As an inequality
it is strictly weaker. It is recorded because a *weaker* bound with a *volume-independent*
constant is the useful object in an infinite-volume argument, and the strong version is kept in
its own file unchanged. **Nothing here improves on §4 of `LatticeCorrelatedPoincare`.**

## Why `m⁻²` and not something worse

The one input is `GreenLargeMass.green_le_smul_one`: `green K m ≼ m⁻²·1` in the Loewner order,
which is `massive = lapMatrix + m²·1 ≽ m²·1` inverted, the Laplacian being positive
semidefinite. **The graph enters only through a matrix that is being discarded**, which is
exactly why the surviving constant is graph-free. That lemma was already in the estate, proved
on 12 August for an unrelated purpose (the large-mass expansion), and had never been pointed at
a Poincaré inequality.

## What is proved

* `quadForm_nonneg`, `quadForm_mono` — a positive semidefinite matrix has a nonnegative
  quadratic form, and the Loewner order compares quadratic forms. Both are one unfolding of
  `Matrix.PosSemidef.dotProduct_mulVec_nonneg` and are stated here because the estate did not
  have either in this shape.
* `quadForm_green_le` — `w ⬝ᵥ G *ᵥ w ≤ m⁻² · ∑ wⱼ²`, every graph, every finite vertex type.
* `green_bot`, `quadForm_green_bot` — on the edgeless graph `green` *is* `m⁻²·1`, so the matrix
  step above is an equality.
* **`poincare_uniform`** — the displayed inequality.
* **`poincare_uniform_sharp`** — **the constant is attained by the inequality itself**, not just
  by the matrix step: on the edgeless graph the observable `ω ↦ ω j` makes `poincare_uniform` an
  equality, so no theorem of that shape valid at every graph can have a constant below `m⁻²`.
  *This was proved because the adversarial review of this file found `quadForm_green_bot`'s
  docstring inviting a claim about the Poincaré constant that only the matrix step supported.
  The fix was to prove the stronger statement, not to narrow the sentence.*
* **`poincare_uniform_of_bounded`** — if the gradient is bounded in `ℓ²` by `L` pointwise, then
  `Var Φ ≤ m⁻²·L²`, a bound with **no integral, no graph and no dimension in it at all**.

## What this is NOT

**`OS4` does not move and no infinite-volume limit is constructed here.** A variance bound
uniform in the volume is an *ingredient* of a tightness argument, not a tightness argument: this
file contains no sequence of measures, no limit, and no compactness. The gap between "the
constants do not blow up" and "the limit exists" is the whole of the remaining work, and it is
untouched.

**No spectral gap is claimed.** `m⁻²` is an upper bound on the propagator's norm, which is a
lower bound on the mass gap of the *free* field only; nothing here is stated about a spectrum.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeUniformPoincare

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeCorrelatedPoincare
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Quadratic forms and the Loewner order

Two facts that are each one unfolding away from `Matrix.PosSemidef.dotProduct_mulVec_nonneg`.
The only friction is that Mathlib states it with `star x ⬝ᵥ …` for a general `RCLike` scalar,
and over `ℝ` the `star` has to be discharged by hand. -/

omit [DecidableEq V] in
/-- A positive semidefinite matrix has a nonnegative quadratic form, over `ℝ` and without the
`star`.

*Named at length because `quadForm_nonneg` is already taken twice in this estate
(`OS2HigherDim`, and `OS2ProductField.quadForm_nonneg_all`), both about the Ornstein–Uhlenbeck
exponential covariance rather than about an arbitrary matrix. The estate's duplicated-name list
is a standing decision for the author and this unit declines to lengthen it.* -/
theorem quadForm_nonneg_of_posSemidef {A : Matrix V V ℝ} (hA : A.PosSemidef) (w : V → ℝ) :
    0 ≤ w ⬝ᵥ A *ᵥ w := by
  have hnn := hA.dotProduct_mulVec_nonneg w
  have hstar : (star w : V → ℝ) = w := by ext i; simp
  rwa [hstar] at hnn

omit [DecidableEq V] in
/-- **The Loewner order compares quadratic forms.** `A ≼ B` means `B − A` is positive
semidefinite, so the difference of the two forms is the form of the difference. -/
theorem quadForm_mono {A B : Matrix V V ℝ} (h : A ≤ B) (w : V → ℝ) :
    w ⬝ᵥ A *ᵥ w ≤ w ⬝ᵥ B *ᵥ w := by
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hnn := quadForm_nonneg_of_posSemidef hps w
  rw [Matrix.sub_mulVec, dotProduct_sub] at hnn
  linarith

/-! ## 2. The propagator's quadratic form, bounded by the mass alone -/

variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-- **`w ⬝ᵥ G *ᵥ w ≤ m⁻² · ∑ wⱼ²`.** The graph has been discarded; only the mass survives. -/
theorem quadForm_green_le (hm : m ≠ 0) (w : V → ℝ) :
    w ⬝ᵥ green K m *ᵥ w ≤ (m ^ 2)⁻¹ * ∑ j, w j ^ 2 := by
  refine (quadForm_mono (GreenLargeMass.green_le_smul_one K hm) w).trans (le_of_eq ?_)
  have hmul : ((m ^ 2)⁻¹ • (1 : Matrix V V ℝ)) *ᵥ w = (m ^ 2)⁻¹ • w := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul, dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, sq]

/-- **On the edgeless graph the propagator is exactly `m⁻²·1`.** The Laplacian vanishes, so
`massive` is `m²·1` and inverting is one `smul`. -/
theorem green_bot (hm : m ≠ 0) :
    green (⊥ : SimpleGraph V) m = (m ^ 2)⁻¹ • (1 : Matrix V V ℝ) := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hmassive : massive (⊥ : SimpleGraph V) m = (m ^ 2) • (1 : Matrix V V ℝ) := by
    have hEq : massive (⊥ : SimpleGraph V) m - (m ^ 2) • (1 : Matrix V V ℝ)
        = (⊥ : SimpleGraph V).lapMatrix ℝ := by
      rw [massive]
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have hlap : (⊥ : SimpleGraph V).lapMatrix ℝ = 0 := by
      ext i j
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
    rw [hlap] at hEq
    linear_combination (norm := module) hEq
  rw [green, hmassive]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- **AND THE CONSTANT IS SHARP AT THE LEVEL OF THE QUADRATIC FORM.** On the edgeless graph
`quadForm_green_le` holds with equality, so no bound of that shape valid on every graph can have
a constant below `m⁻²`.

*This is sharpness of the matrix step only. Sharpness of the Poincaré inequality itself — the
statement a reader actually cares about — is `poincare_uniform_sharp` in §3, which was proved
rather than asserted after review found this docstring inviting the stronger reading.* -/
theorem quadForm_green_bot (hm : m ≠ 0) (w : V → ℝ) :
    w ⬝ᵥ green (⊥ : SimpleGraph V) m *ᵥ w = (m ^ 2)⁻¹ * ∑ j, w j ^ 2 := by
  rw [green_bot hm]
  have hmul : ((m ^ 2)⁻¹ • (1 : Matrix V V ℝ)) *ᵥ w = (m ^ 2)⁻¹ • w := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul, dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, sq]

/-! ## 3. The Poincaré inequality with a volume-independent constant -/

variable {K}

/-- **THE POINCARÉ INEQUALITY FOR THE CORRELATED FIELD, WITH A CONSTANT THAT DOES NOT KNOW THE
GRAPH.**

```
∫Φ² dμ − (∫Φ dμ)²  ≤  m⁻² · ∫ ∑ⱼ (∂ⱼΦ)² dμ
```

against `gaussianField K m`, for every `C¹` observable of all the coordinates, at every finite
vertex type and every nonzero mass.

This is `poincare_correlated_general` composed with `quadForm_green_le`, and it is **weaker**
than that theorem. What it buys is that the right-hand side is the plain Dirichlet energy with a
graph-free constant, so the estimate is uniform over an increasing family of boxes. -/
theorem poincare_uniform (hm : m ≠ 0) {Φ : EuclideanSpace ℝ V → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ∫ ω, ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2
          ∂(gaussianField K m) := by
  refine (poincare_correlated_general hm hΦc hmem hgrad).trans ?_
  have hint : Integrable
      (fun ω => ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2)
      (gaussianField K m) :=
    integrable_finset_sum _ (fun j _ => (hgrad j).integrable_sq)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
    (hint.const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
  · exact quadForm_nonneg_of_posSemidef (green_posDef K hm).posSemidef _
  · exact quadForm_green_le K hm _

/-! ### Sharpness of the constant, at the level of the inequality itself

`quadForm_green_bot` shows the *matrix* step is tight. That is not the same as showing the
Poincaré constant is tight, and a reader is entitled to the latter. Here it is: on the edgeless
graph, a single coordinate is an observable for which `poincare_uniform` is an **equality**. So
`m⁻²` cannot be replaced by anything smaller in a statement quantified over graphs. -/

-- Scoped to this one declaration, not the file: the linter's report is correct about the
-- statement and unactionable because the proof needs the instance (see the docstring). A blanket
-- disable would blind the rest of the file to genuine reports, of which this family has had six.
set_option linter.unusedFintypeInType false in
omit [DecidableEq V] in
/-- The derivative of a coordinate is that coordinate of the direction.

*`DecidableEq` is genuinely unused and is omitted. **`Fintype` is not**, and the attempt to omit
it is recorded because it failed: the linter reports that a hypothesis is unused **in the type**,
and this one is — but the proof needs it, because `EuclideanSpace ℝ V` has no
`ContinuousSMul ℝ` instance without it. Six previous linter reports in this family were genuine
strengthenings and this one was read as a seventh without checking. The build refused it.
The general lesson is `ERRATUM 183`'s: an unverified reading of a tool's output is a guess.* -/
theorem fderiv_coord (j : V) (ω v : EuclideanSpace ℝ V) :
    fderiv ℝ (fun x : EuclideanSpace ℝ V => x j) ω v = v j := by
  have h : (fun x : EuclideanSpace ℝ V => x j) = ⇑(EuclideanSpace.proj (𝕜 := ℝ) j) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

/-- **THE CONSTANT `m⁻²` IS ATTAINED.** On the edgeless graph the field is a product of
independent centred Gaussians of variance `m⁻²`, and for the observable `ω ↦ ω j` both sides of
`poincare_uniform` equal `m⁻²`.

Consequently no theorem of the shape `Var Φ ≤ C · ∫ ∑ⱼ (∂ⱼΦ)²`, valid at every graph and every
finite vertex type, can hold with `C < m⁻²`. **The uniformity bought in this file costs nothing
that could have been kept.** -/
theorem poincare_uniform_sharp (hm : m ≠ 0) (j : V) :
    (∫ ω, (fun x : EuclideanSpace ℝ V => x j) ω * (fun x : EuclideanSpace ℝ V => x j) ω
        ∂(gaussianField (⊥ : SimpleGraph V) m))
      - (∫ ω, (fun x : EuclideanSpace ℝ V => x j) ω
          ∂(gaussianField (⊥ : SimpleGraph V) m)) ^ 2
      = (m ^ 2)⁻¹ * ∫ ω, ∑ i, (fderiv ℝ (fun x : EuclideanSpace ℝ V => x j) ω
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ^ 2
        ∂(gaussianField (⊥ : SimpleGraph V) m) := by
  have hlhs : (∫ ω, (fun x : EuclideanSpace ℝ V => x j) ω * (fun x : EuclideanSpace ℝ V => x j) ω
      ∂(gaussianField (⊥ : SimpleGraph V) m))
      - (∫ ω, (fun x : EuclideanSpace ℝ V => x j) ω
          ∂(gaussianField (⊥ : SimpleGraph V) m)) ^ 2 = (m ^ 2)⁻¹ := by
    rw [twoPoint (⊥ : SimpleGraph V) hm j j, integral_eval (⊥ : SimpleGraph V) m j,
      green_bot hm]
    simp
  have hgradpt : ∀ (ω : EuclideanSpace ℝ V) (i : V),
      (fderiv ℝ (fun x : EuclideanSpace ℝ V => x j) ω
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ^ 2 = if j = i then (1 : ℝ) else 0 := by
    intro ω i
    rw [fderiv_coord]
    simp only [Pi.single_apply]
    by_cases hij : j = i <;> simp [hij]
  have hsum : ∀ ω : EuclideanSpace ℝ V,
      ∑ i, (fderiv ℝ (fun x : EuclideanSpace ℝ V => x j) ω
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ^ 2 = 1 := by
    intro ω
    simp only [hgradpt ω]
    simp
  rw [hlhs]
  simp only [hsum]
  rw [integral_const]
  simp

/-! ## 4. The bounded-gradient form: no integral left at all -/

/-- **`Var Φ ≤ m⁻²·L²` for an observable whose gradient is bounded in `ℓ²` by `L`.**

The right-hand side contains no integral, no graph, no vertex count and no dimension. This is
the shape a uniform estimate takes when it is handed to a tightness argument — and, to be
explicit, **this file does not hand it to one.** -/
theorem poincare_uniform_of_bounded (hm : m ≠ 0) {Φ : EuclideanSpace ℝ V → ℝ}
    (hΦc : ContDiff ℝ 1 Φ)
    (hmem : MemLp Φ 2 (gaussianField K m))
    (hgrad : ∀ j, MemLp (fun ω => fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2
      (gaussianField K m))
    {L : ℝ} (hL : ∀ ω, ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2 ≤ L ^ 2) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * L ^ 2 := by
  refine (poincare_uniform hm hΦc hmem hgrad).trans ?_
  have hpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hint : Integrable
      (fun ω => ∑ j, (fderiv ℝ Φ ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) ^ 2)
      (gaussianField K m) :=
    integrable_finset_sum _ (fun j _ => (hgrad j).integrable_sq)
  have hle := integral_mono hint (integrable_const (L ^ 2)) hL
  simpa using hle

end LatticeUniformPoincare
