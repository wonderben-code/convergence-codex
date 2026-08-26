/-
  LatticeField.lean — the Gaussian field with the lattice Green function as
  its covariance, and a verdict on what "applies verbatim" was worth.

  WHY. `WALLS.md` W1 ends its account with: *"Then the OS2 packaging built
  this campaign (PosSemidef → multivariateGaussian → pairing) applies
  VERBATIM — that layer is done and waiting."* **That is a "this makes X
  possible" claim, made by this project about its own work, and ERRATUM 48
  says the check for such a claim is to attempt X.** `LatticeLaplacian`
  supplied the PosSemidef. This attempts X.

  WHAT THIS FILE PROVES:
  1. **`latticeField`** — the centred Gaussian measure on `EuclideanSpace ℝ
     (Site n)` with covariance `(−Δ + m²)⁻¹`. **The first lattice Gaussian
     field in the estate**; every previous field was the OU product.
  2. **`memLp_eval`, `integral_eval`** — coordinates are square-integrable
     and centred.
  3. **`twoPoint`** — **the two-point function IS the lattice Green
     function**: `∫ ω(p)·ω(q) = green n m p q`. That is the statement that
     makes this the field the physics names.
  4. **`twoPoint_diag_pos`** — and it is not the trivial field: the field at
     a site has strictly positive variance.

  THE VERDICT ON "APPLIES VERBATIM", which is the point of the file.
  **Half of it transferred, and the half that did not is the half W1 is
  about.** `OS2MeasureLevel.fieldMeasure` is `multivariateGaussian 0
  (prodCov Δ s)` — hard-wired to the OU product covariance, not generic in
  the kernel — so nothing could apply literally verbatim; the question was
  which proofs survive re-instantiation. §1–§2 here are its `memLp_eval`,
  `integral_eval` and `twoPoint` with `prodCov` replaced by `green`, and
  they went through unchanged in structure, because those proofs use only
  `IsGaussian` and `PosSemidef`. **`integral_pairing` and
  `os2_measure_level` did NOT transfer and are not attempted**: they consume
  the reflection, and

  **THERE IS NO REFLECTION ON `Site n` AT ALL.** `OS2MeasureLevel.theta` and
  `doubled` are built for the OU product's real-valued coordinates
  (`Fin (m+1) → ℝ`, reflecting the time coordinate); a finite box has no
  such map in the estate. So the "packaging" that was waiting turns out to
  be the Gaussian-moments layer, and the OS2 layer proper was waiting on
  something that does not exist yet.

  WHAT THIS DOES NOT DO. No OS2, no reflection positivity, no reflection, no
  chessboard estimate. W1's failing step is untouched and this file makes no
  progress on it whatever.

  **AMENDED 9 AUG 2026 — THE SENTENCE IN CAPITALS ABOVE IS NO LONGER TRUE,
  and the paragraph is kept because the verdict it records was correct.**
  `LatticeReflection.refl` is the reflection on `Site n`;
  `LatticeReflectionPositive.reflectionPositive_lattice` is the
  covariance-level positivity; and `GraphOS2.os2_lattice` is
  `integral_pairing` and `os2_measure_level` for THIS measure — the two
  theorems this header says "did NOT transfer and are not attempted". They
  transfer. **The diagnosis was right and so was the refusal to fake it**:
  the obstruction really was the missing reflection, it really was outside
  the packaging layer, and once it was built the packaging went through with
  nothing left over. Everything else in this header stands as written.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeLaplacian
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance

namespace LatticeField

open IsingFiniteVolume LatticeLaplacian MeasureTheory ProbabilityTheory Matrix Real Finset
open scoped RealInnerProductSpace

variable {n : ℕ} {m : ℝ}

/-! ## 1. The field -/

/-- The coordinate map as an inner product against a basis vector. Stated
    over an abstract index type on purpose: at the concrete `Site n` the
    `simp` set does not reduce `⟪·,·⟫` on `ℝ`, and this is the same lemma
    `OS2MeasureLevel` proves inline for its own abstract `ι`. -/
private theorem coord_eq_inner {ι : Type*} [Fintype ι]
    (a : ι) (ω : EuclideanSpace ℝ ι) :
    ω a = ⟪EuclideanSpace.basisFun ι ℝ a, ω⟫ :=
  (EuclideanSpace.basisFun_inner (ι := ι) (𝕜 := ℝ) ω a).symm


/-- **THE LATTICE GAUSSIAN FIELD**: the centred Gaussian on the box with
    covariance the massive lattice Green function `(−Δ + m²)⁻¹`. -/
noncomputable def latticeField (n : ℕ) (m : ℝ) :
    Measure (EuclideanSpace ℝ (Site n)) :=
  multivariateGaussian 0 (green n m)

instance isGaussian_latticeField (n : ℕ) (m : ℝ) : IsGaussian (latticeField n m) :=
  isGaussian_multivariateGaussian

/-- Each coordinate field `ω ↦ ω p` is square-integrable. -/
theorem memLp_eval (n : ℕ) (m : ℝ) (p : Site n) :
    MemLp (fun ω : EuclideanSpace ℝ (Site n) => ω p) 2 (latticeField n m) := by
  have h : (fun ω : EuclideanSpace ℝ (Site n) => ω p)
      = fun ω : EuclideanSpace ℝ (Site n) =>
          ⟪EuclideanSpace.basisFun (Site n) ℝ p, ω⟫ := by
    ext ω
    exact coord_eq_inner p ω
  rw [h]
  exact MemLp.const_inner _ IsGaussian.memLp_two_id

/-- Each coordinate field has mean zero. -/
theorem integral_eval (n : ℕ) (m : ℝ) (p : Site n) :
    ∫ ω, ω p ∂(latticeField n m) = 0 := by
  have h : (fun ω : EuclideanSpace ℝ (Site n) => ω p)
      = fun ω : EuclideanSpace ℝ (Site n) =>
          ⟪EuclideanSpace.basisFun (Site n) ℝ p, ω⟫ := by
    ext ω
    exact coord_eq_inner p ω
  rw [h]
  have hid : Integrable (fun ω : EuclideanSpace ℝ (Site n) => ω) (latticeField n m) :=
    IsGaussian.integrable_id
  rw [integral_inner hid]
  have hzero : ∫ ω, ω ∂(latticeField n m) = 0 := integral_id_multivariateGaussian
  rw [hzero, inner_zero_right]

/-! ## 2. The two-point function -/

/-- **THE TWO-POINT FUNCTION IS THE LATTICE GREEN FUNCTION.** This is the
    statement that makes `latticeField` the field the physics names, rather
    than some Gaussian measure with a convenient covariance. -/
theorem twoPoint (n : ℕ) {m : ℝ} (hm : m ≠ 0) (p q : Site n) :
    ∫ ω, ω p * ω q ∂(latticeField n m) = green n m p q := by
  have hcov : cov[fun ω : EuclideanSpace ℝ (Site n) => ω p,
      fun ω : EuclideanSpace ℝ (Site n) => ω q; latticeField n m] = green n m p q :=
    covariance_eval_multivariateGaussian (green_posDef n hm).posSemidef p q
  have hsub := covariance_eq_sub (memLp_eval n m p) (memLp_eval n m q)
  rw [integral_eval, integral_eval, mul_zero, sub_zero] at hsub
  rw [← hcov, hsub]
  simp only [Pi.mul_apply]

/-- **The field is not trivial**: every site has strictly positive variance,
    because a positive-definite matrix has positive diagonal. Without this
    the two-point theorem would be compatible with the zero measure. -/
theorem green_diag_pos (n : ℕ) {m : ℝ} (hm : m ≠ 0) (p : Site n) :
    0 < green n m p p := by
  simpa using (green_posDef n hm).2 (x := Finsupp.single p (1:ℝ)) (by simp)

theorem twoPoint_diag_pos (n : ℕ) {m : ℝ} (hm : m ≠ 0) (p : Site n) :
    0 < ∫ ω, ω p * ω p ∂(latticeField n m) := by
  rw [twoPoint n hm p p]
  exact green_diag_pos n hm p

/-! ## 3. Review round 72 — and the verdict this file was written to reach

**"Did the OS2 packaging apply verbatim?"** No, and the honest answer has
two halves.

*What transferred.* `OS2MeasureLevel.memLp_eval`, `integral_eval` and
`twoPoint` are reproduced here with `prodCov Δ s` replaced by `green n m`
and no other change of structure. That is a real transfer and it vindicates
the shape of the claim: those proofs never used anything about the OU
product beyond `IsGaussian` and `PosSemidef`.

*What did not, and it is the part W1 is about.* `integral_pairing` and
`os2_measure_level` consume a REFLECTION, and **the estate has no reflection
on `Site n`** — checked, not assumed: `OS2ProductField.theta` has type
`(Fin (m+1) → ℝ) → (Fin (m+1) → ℝ)` and negates a real time coordinate,
`doubled` builds a doubled site family out of it, and a grep for any
`Site n → Site n` map returns nothing. **So "that layer is done and waiting"
was true of the Gaussian-moments layer and false of the OS2 layer**, and the
second is the one W1 needs. `WALLS.md` is corrected rather than this
sentence softened.

*What this does NOT claim.* Nothing here says a reflection on the box would
be hard to write — a box has obvious ones. The finding is narrower and is
about the description rather than the difficulty: **"done and waiting"
described a layer that turns out to need an object nobody has built**, so
the distance to W1 was understated by one step, and that step is bookkeeping
rather than mathematics. The mathematics is still the positivity.

**"Could `latticeField` be the zero measure or otherwise degenerate?"**
`isGaussian_latticeField` makes it a probability measure, and
`twoPoint_diag_pos` gives every site strictly positive variance — which is
where `green_posDef` is used rather than merely `PosSemidef`, and is the
reason the previous file proved the stronger statement.

**"Could this be presented as progress on W1?"** It is not, and there is a
sharp way to say why. W1's failing step is the reflection positivity of this
covariance. To even STATE that, one needs a reflection on the box; §3 has
just established there is none in the estate. **So attempting X revealed a
prerequisite that "done and waiting" had concealed** — a small one, but the
point of ERRATUM 48's rule is that you find these by trying rather than by
rereading.

**A note on fragility, found while writing §1 and not worth an erratum.**
`OS2MeasureLevel` proves the coordinate-as-inner-product step with
`simp [PiLp.inner_apply]`. The identical statement fails here, and fails in
isolation too — `simp` cannot reduce `⟪·,·⟫` on `ℝ` without a lemma that
reaches `OS2MeasureLevel` only through its transitive imports. This file
uses `EuclideanSpace.basisFun_inner` instead, which is the lemma the step
actually wants. Both compile; one would survive an import change.
-/

end LatticeField
