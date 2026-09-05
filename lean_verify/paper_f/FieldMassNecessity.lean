import FieldOrthIsometry

/-!
# The mass hypothesis is NECESSARY, and this chain's prose had stopped saying so

**This file exists because of a defect in five files' prose, found by reading them and not by the
build** (`ERRATUM 455`). Every symmetry theorem in the rotation chain carries `m ≠ 0`, and
`FieldHouseholder`'s header says so — *"at every finite nonempty graph and `m ≠ 0`"*. The five
headers written after it dropped the hypothesis from the summary sentence while the theorems kept
it: `FieldRotation`, `FieldRotationInstance`, `FieldEigenGramSchmidt`, `FieldCycleRotation` and
`FieldBoxRotation` each say that some graph *"carries a genuine rotation of the Gaussian field"*
with no mass condition attached.

**The repair is not to add a word to five files and stop.** It is to say what the hypothesis is
doing, and that is a theorem: **at `m = 0` this estate's `gaussianField` is a point mass at the
origin.** `green G m` is `(massive G m)⁻¹`; `massive G 0` is the bare graph Laplacian; the Laplacian
is singular on every nonempty graph (`SimpleGraph.det_lapMatrix_eq_zero`, Mathlib's, because the
all-ones vector is in the kernel of every graph Laplacian); and Mathlib's inverse of a singular
matrix is `0`. A `multivariateGaussian` with zero covariance is `Measure.dirac`.

**So the omission was not a false sentence. It was worse.** The claim *"this graph carries a
rotation of the Gaussian field"*, read without the mass condition, is **true at `m = 0` as well**,
and trivially: every linear isometry fixes the origin, so every orthogonal matrix preserves a point
mass — on every graph, in every dimension, for reasons that have nothing to do with the graph, the
eigenvalue, or the eigenvectors the chain works to produce. A summary a reader cannot use to tell
the theorem apart from that is not summarising it.

**A SECOND FINDING, RECORDED BECAUSE IT WAS A NEAR MISS.** The first draft of this file proved the
Laplacian's determinant vanishes from `lapMatrix_mulVec_const_eq_zero` and
`Matrix.exists_mulVec_eq_zero_iff` — five lines that reconstruct Mathlib's own
`SimpleGraph.det_lapMatrix_eq_zero`, which is `@[simp]`. **What caught it was the
unused-simp-argument linter**: the
`simp` call below closed its goal without the new lemma, because Mathlib's was already firing. That
is the same linter that caught a redundant hypothesis in the previous unit, and it has now found
two different kinds of weakness in two consecutive units — neither of them an error the build would
ever have reported.

## What is proved

**`massive_zero`** and **`green_zero`** — `massive G 0` is the Laplacian, so `green G 0 = 0` on
every nonempty graph.

**`gaussianField_zero`** — hence `gaussianField G 0 = Measure.dirac 0`.

**`map_isometry_gaussianField_zero`** — **so at zero mass EVERY linear isometry is a symmetry of the
field**, orthogonal matrices included; `gaussianField_map_orthIsometry_zero` says it in the chain's
own vocabulary. This is the theorem that makes the hypothesis worth stating.

**`eq_zero_of_green_zero_smul`** and **`not_exists_eigenvector_zero`** — and the *route* the chain
takes is genuinely unavailable there: at `m = 0` the propagator has **no** non-zero eigenvector at
any non-zero eigenvalue, because it has no non-zero image at all. The chain does not merely fail to
apply at `m = 0`; its input is empty.

## What is NOT here

**No new symmetry of any field with `m ≠ 0`.** Nothing here adds a member to the commutant, counts
the rotations, or touches a graph the previous units did not.

**No claim that the five headers were false.** They were true and uninformative, which is a
different defect and the one `ERRATUM 455` records.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
statement about `m = 0` moves nothing: every OS statement in this estate is at `m ≠ 0`.

**Nothing about the torus at `d > 1`.** Still `TorusFibreOrbitPartition`'s orbits, still not
composed. **Not attempted, no cost claimed** (`ERRATUM 246`).
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 458`):
`FieldTorusRotation.exists_rotation_symmetry_torus` puts a rotation on the torus in **every**
dimension `d ≥ 1`, and needed no orbit bookkeeping at all —
`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank`, in the estate since 2026-08-31,
bounds the degeneracy below with **no hypotheses**, and the all-ones frequency has every axis
interior. **The route this sentence names was never necessary.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldMassNecessity

open Matrix GraphLaplacian FieldOrthIsometry MeasureTheory ProbabilityTheory
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The propagator at zero mass is the zero matrix -/

theorem massive_zero : massive G 0 = G.lapMatrix ℝ := by simp [massive]

/-- **THE PROPAGATOR AT ZERO MASS IS THE ZERO MATRIX.** The Laplacian is singular on every nonempty
graph — `SimpleGraph.det_lapMatrix_eq_zero`, Mathlib's, from the all-ones vector in its kernel —
and Mathlib's inverse of a singular matrix is `0`. -/
theorem green_zero [Nonempty V] : green G 0 = 0 := by
  rw [green, massive_zero]
  exact Matrix.nonsing_inv_apply_not_isUnit _ (by simp)

/-! ## 2. So the field is a point mass, and everything is a symmetry of it -/

/-- **AT ZERO MASS THE GAUSSIAN FIELD IS A POINT MASS AT THE ORIGIN.** -/
theorem gaussianField_zero [Nonempty V] : gaussianField G 0 = Measure.dirac 0 := by
  rw [gaussianField, green_zero, multivariateGaussian, CFC.sqrt_zero]
  simp

/-- **SO EVERY LINEAR ISOMETRY IS A SYMMETRY OF IT** — every graph, every dimension, for reasons
that have nothing to do with the graph. -/
theorem map_isometry_gaussianField_zero [Nonempty V]
    (f : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    Measure.map f (gaussianField G 0) = gaussianField G 0 := by
  rw [gaussianField_zero, Measure.map_dirac' f.continuous.measurable, map_zero]

/-- The same statement in this chain's own vocabulary. -/
theorem gaussianField_map_orthIsometry_zero [Nonempty V] {M : Matrix V V ℝ} (h : Mᵀ * M = 1) :
    Measure.map (orthIsometry h) (gaussianField G 0) = gaussianField G 0 :=
  map_isometry_gaussianField_zero _

/-! ## 3. And the route the chain takes is unavailable there -/

theorem eq_zero_of_green_zero_smul [Nonempty V] {u : V → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : green G 0 *ᵥ u = c • u) : u = 0 := by
  rw [green_zero, Matrix.zero_mulVec] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- **AT ZERO MASS THERE IS NO EIGENVECTOR TO ROTATE**: the chain's input is empty, not merely out
of reach. -/
theorem not_exists_eigenvector_zero [Nonempty V] {μ : ℝ} (hμ : μ ≠ 0) :
    ¬ ∃ u : V → ℝ, u ≠ 0 ∧ green G 0 *ᵥ u = μ⁻¹ • u := by
  rintro ⟨u, hu, hgu⟩
  exact hu (eq_zero_of_green_zero_smul (inv_ne_zero hμ) hgu)

end FieldMassNecessity
