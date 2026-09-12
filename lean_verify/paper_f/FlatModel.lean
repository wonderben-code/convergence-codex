import DensityCover
import FlatCurvature

/-!
# The density chain at the flat model space, where its integrand is zero

`DensityCover` closed 12 September's density chain with a theorem that **could not discharge its own
hypotheses**: `exists_partitionOfUnity_density` carries `[T2Space M]`, `[SigmaCompactSpace M]` and
`[IsManifold I ∞ M]`, and that file says in its own fence that it makes *"no claim that the three
hypotheses are satisfied by any manifold in this estate — they are hypotheses of a theorem, not
properties established of anything."* **None of the four density units of that day is ever applied
to a space.** This file applies them.

**The space is the one the estate already has.** `LeviCivitaFlat` and `FlatCurvature` (both
2026-09-07) work at a finite-dimensional real inner product space `F`, charted on itself, with the
constant inner product as its metric, and `FlatCurvature` computes its curvature: `riemann_flat`,
`ricci_flat`, `scalar_flat`, all zero. At that space the three hypotheses above are **found by
instance search rather than assumed** — `T2Space` and `SigmaCompactSpace` because a
finite-dimensional normed space is both, `IsManifold 𝓘(ℝ, F) ∞ F` because a vector space charted on
itself is smooth to every order — so the chain's last theorem becomes unconditional.

## What is proved

> **`exists_partitionOfUnity_density_model`** — `DensityCover.exists_partitionOfUnity_density` at
> the model space, with **nothing assumed but finite-dimensionality and completeness of `F`**: a
> smooth partition of unity subordinate to the chart cover, with a strictly positive `C^k` volume
> density on each piece. **The first application of the density chain to a space rather than to a
> context.**
>
> **`density_chartFrame_model_pos`** — and the density is strictly positive there, which is worth
> stating separately because of the next theorem.
>
> **`scalar_model_eq_zero`, `scalar_mul_density_model_eq_zero`** — **THE EINSTEIN–HILBERT INTEGRAND
> OF THE MODEL SPACE IS IDENTICALLY ZERO**, from `FlatCurvature.scalar_flat`. **The vanishing is the
> curvature's and not the density's** — that is what `density_chartFrame_model_pos` rules out — so
> this is the consistency check a chain that computes a curvature integrand has to pass, and it is
> the first value that chain has ever produced.

## What is NOT here, and the first item is the point

* **NO CURVED EXAMPLE, ANYWHERE IN THIS ESTATE.** No sphere, no torus, no graph of a function, no
  product of anything with anything. `FlatCurvature`'s own fence says *"no curvature has been
  computed that is not zero"*, and after this file no density has been computed on a space where
  the answer is not `√det g` of a constant metric. **The curvature and density chains have exactly
  one model between them and it is the trivial one**, so nothing here has been tested against a
  case that could distinguish a right definition from a wrong one. **Not attempted, no cost
  claimed** (`ERRATUM 246`), and it is the most useful thing this file says.
* **NO NON-CONSTANT METRIC ON `F`.** `KoszulVectorSpace` builds the Levi-Civita connection of a
  varying metric on the model space, and `LeviCivitaRegular.riemann` does not see it, being stated
  for the `RiemannianBundle` instance, which on `F` is the constant one. `FlatCurvature` says the
  same and it is unchanged here.
* **NO MEASURE, STILL.** Entry 48's two open objects stand: an integral on a manifold, and a
  finite-order partition of unity. Nothing here integrates anything, and a partition of unity whose
  pieces all carry integrand `0` integrates to `0` in any theory of integration, which is not an
  argument for anything.
* **NOTHING ABOUT `a₂`, THE WALL DOES NOT MOVE, AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup F]`,
`[InnerProductSpace ℝ F]`, `[FiniteDimensional ℝ F]`, `[CompleteSpace F]` — the hypotheses
`FlatCurvature`'s metric section already takes, and nothing else. **`T2Space`, `SigmaCompactSpace`
and `IsManifold 𝓘(ℝ, F) ∞ F` are not hypotheses here; they are found**, which is the whole content
of the first theorem.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FlatModel

open Bundle Manifold Set
open scoped ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]

/-! ## 1. The density chain applies to the model space -/

set_option maxHeartbeats 1000000 in
-- the whole chain's instance context, twenty files of it, is discharged in this one elaboration
omit [CompleteSpace F] in
/-- **`DensityCover`'S THEOREM, UNCONDITIONALLY.** Its three extra hypotheses — `T2Space`,
`SigmaCompactSpace`, `IsManifold ∞` — are found by instance search here rather than assumed. -/
theorem exists_partitionOfUnity_density_model (k : ℕ) :
    ∃ ρ : SmoothPartitionOfUnity F 𝓘(ℝ, F) F univ,
      ρ.IsSubordinate (fun x ↦ (chartAt F x).source) ∧
        ∀ x : F, ∀ y ∈ (chartAt F x).source,
          0 < VolumeDensity.density (DensityCover.chartFrame (I := 𝓘(ℝ, F)) x) y ∧
            ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) k
              (VolumeDensity.density (DensityCover.chartFrame (I := 𝓘(ℝ, F)) x)) y :=
  DensityCover.exists_partitionOfUnity_density

set_option maxHeartbeats 1000000 in
-- as above
omit [CompleteSpace F] in
/-- The volume density of a chart's frame is strictly positive at the model space. -/
theorem density_chartFrame_model_pos (x : F) {y : F} (hy : y ∈ (chartAt F x).source) :
    0 < VolumeDensity.density (DensityCover.chartFrame (I := 𝓘(ℝ, F)) x) y :=
  DensityCover.density_chartFrame_pos x hy

/-! ## 2. And its Einstein–Hilbert integrand vanishes -/

set_option maxHeartbeats 1000000 in
-- as above
/-- `FlatCurvature.scalar_flat`, in the name `ScalarOrder` and the density chain use. -/
theorem scalar_model_eq_zero (x : F) :
    RicciScalar.scalar
      (KoszulManifold.leviCivita :
        CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _)) x = 0 :=
  FlatCurvature.scalar_flat x

set_option maxHeartbeats 1000000 in
-- as above
/-- **THE EINSTEIN–HILBERT INTEGRAND OF THE MODEL SPACE IS IDENTICALLY ZERO**, and by
`density_chartFrame_model_pos` the vanishing is the curvature's and not the density's. -/
theorem scalar_mul_density_model_eq_zero (x y : F) :
    RicciScalar.scalar
        (KoszulManifold.leviCivita :
          CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _)) y
      * VolumeDensity.density (DensityCover.chartFrame (I := 𝓘(ℝ, F)) x) y = 0 := by
  rw [scalar_model_eq_zero, zero_mul]

end FlatModel
