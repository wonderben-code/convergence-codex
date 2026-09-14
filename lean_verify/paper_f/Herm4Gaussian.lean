/-
  Herm4Gaussian: the Boltzmann measure ON THE HERMITIAN SLICE, not on a stand-in

  SPINE LINK L20 ("Boltzmann measure exists").

  WHAT THE RECOMPUTE FOUND. L20 is rated PARTIAL. What is machine-checked is a
  16-dimensional Gaussian as a genuine Mathlib probability measure — `Measure.pi
  (gaussianReal 0 1)` on `Fin 16 → ℝ`, with every polynomial moment finite
  (`GaussianProductMeasure.lean`, `GaussPiDensity.lean`) — and the recompute's L20
  refuter recorded the residue precisely: **there is no declaration of type
  `Measure (selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ))` anywhere in the estate**, because
  there is no Frobenius inner product on the Hermitian slice, no isometry to `ℝ¹⁶`, and
  no pushforward. The 16 coordinates were a stand-in for a space nothing identified them
  with. This file removes that gap: the measure now lives on `Herm₄(ℂ)` itself and the
  16-coordinate description is a THEOREM about it rather than a substitute for it.

  A CORRECTION TO THE ROUTE MEMO, RECORDED BECAUSE IT WAS MINE TOO. The recompute's
  completeness critic reported that *"Mathlib has NO Frobenius inner product on Matrix
  (`grep -rn 'Inner (Matrix' Mathlib/` → no output)"*, and my own first query
  (`grep "instance.*Inner (Matrix\|Inner (Matrix"`) returned nothing either. **Both
  greps were wrong about the library.** `Matrix.toMatrixInnerProductSpace`
  (`Mathlib/Analysis/Matrix/Order.lean:306`) builds `InnerProductSpace 𝕜 (Matrix n n 𝕜)`
  from any positive-semidefinite `M` with `⟪x, y⟫ = Tr(y M xᴴ)`, and at `M = 1` that IS
  the Frobenius inner product — machine-checked here before this sentence was written.
  It was invisible to both queries because it is a `def` taking a hypothesis, not a bare
  `instance`, so the string `Inner (Matrix` never appears. **The lesson is specific and
  worth more than the finding: search for the STRUCTURE a library provides, not for the
  FIELD name of the class.** What this file still has to build is the REAL inner product
  on the self-adjoint slice, which Mathlib's `𝕜`-valued version does not give.

  WHY `Herm4` IS A TYPE SYNONYM AND NOT AN ABBREVIATION. `selfAdjoint A` is a subtype,
  and a subtype carries `instTopologicalSpaceSubtype` — which competes with the norm
  topology the Frobenius inner product induces. Written as an `abbrev`, every downstream
  instance resolved against the WRONG topology: `SecondCountableTopology` was reported
  missing while `BorelSpace` succeeded, and `stdGaussian`'s `IsProbabilityMeasure`
  instance could not fire at all. The synonym keeps the algebra (`AddCommGroup`,
  `Module ℝ` by `inferInstanceAs`) and blocks the topology. This is the same pattern as
  `SkolemNoether.Twisted`, and the failure mode is recorded because it is invisible from
  the statement and cost four probe files.

  WHAT IS PROVED.
  * **`frob`** — `⟪A, B⟫ = Re Tr(AB)`, the Frobenius inner product restricted to the
    Hermitian slice. On Hermitian matrices `Tr(AB)` is already real, so `Re` discards
    nothing (`conj_inner_symm` is `Matrix.trace_mul_comm`).
  * **`herm4Core`** — all six `InnerProductSpace.Core ℝ` conditions. Positive
    semidefiniteness is `Matrix.posSemidef_conjTranspose_mul_self` after
    `frob_self_eq` turns `A · A` into `Aᴴ · A`; definiteness is
    `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`. **Nothing is assumed: the inner
    product is the trace form and its properties are Mathlib's theorems about traces.**
  * **`finrank_herm4 = 16`** — the estate's own `SelfAdjointDimension.finrank_selfAdjoint_four`
    transports to the synonym by `rfl`. (An earlier draft of this header claimed that
    file had no consumer and dated it 2026-08-22. **Both were false and were caught by
    query before commit**: it landed 2026-08-17 and has four consumers —
    `F4_1e_SpectralTripleArithmetic`, `F4_1l_GaussianPartition`, `SkewBlockOffDiagonal`
    and `TracelessSkewDimension` — of which `F4_1l_GaussianPartition` uses this very
    theorem. Recorded rather than silently corrected, because a false "first consumer"
    claim is the shape `ERRATUM 563` is about.)
  * **`herm4Gaussian`** — `ProbabilityTheory.stdGaussian Herm4`: **a
    `Measure (Herm₄(ℂ))`, the declaration the L20 refuter reported absent.**
    `IsProbabilityMeasure` comes free from Mathlib.
  * **`herm4Basis`** — an orthonormal basis indexed by `Fin 16`, from
    `stdOrthonormalBasis` reindexed along `finrank_herm4`.
  * **`herm4Gaussian_eq_map_pi`** — **the bridge**: the measure on `Herm₄` is the
    pushforward of a 16-fold product of standard one-dimensional Gaussians along ANY
    orthonormal basis, and `herm4Gaussian_eq_map_pi_std` instantiates it at
    `herm4Basis`. So the estate's existing 16-coordinate Gaussian is now a description
    OF this measure rather than a stand-in FOR it, and the identification is
    basis-independent because Mathlib's `stdGaussian_eq_map_pi_orthonormalBasis` holds
    for every basis.

  WHAT IS **NOT** PROVED, stated plainly, because L20's rating does not move on this file
  alone.
  * **That this measure is the Boltzmann measure OF THE SPECTRAL ACTION.** What
    fluctuates and with what weight has never been written down in this estate: it is
    `DECISIONS NEEDED` 5 and `ASSUMPTIONS_LEDGER` 8, 26, 27. This file proves a canonical
    Gaussian exists on the right space with the right inner product; it does not identify
    it with `e^{-S}`.
  * **The closed form.** No `(2π)^{-8}` and no `Z = (πΛ²)⁸` appears in any statement
    here, and the L20 refuter's finding stands that the constant is missing even for the
    product measure at `n = 16` — `GaussPiDensity` states a `Finset.prod` at general `n`.
    The variance is `1`, not `Λ²`.
  * **Any connection to the cascade's `D`.** `Herm₄(ℂ)` is the self-adjoint part of
    `M₄(ℂ)`; that the cascade's Dirac operator lives there, and that `M₄(ℂ)` is the
    cascade's `D₂`, is `ASSUMPTIONS_LEDGER` 22 and 30.
  * **Moments.** `GaussianProductMeasure`'s polynomial-moment results are about the
    product measure and are not transported along the basis here.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import SelfAdjointDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace Herm4Gaussian

open Matrix
open scoped ComplexOrder

noncomputable section

/-! ## 1. The Hermitian slice as a type synonym -/

/-- The Hermitian (self-adjoint) part of `M₄(ℂ)`, as a **type synonym** rather than an
abbreviation. See the header: a subtype carries `instTopologicalSpaceSubtype`, which
competes with the norm topology of the Frobenius inner product and breaks every
measure-theoretic instance downstream. -/
def Herm4 : Type := selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ)

/-- The underlying matrix of a Hermitian element. -/
def Herm4.mat (A : Herm4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (id A : selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ))

instance : AddCommGroup Herm4 :=
  inferInstanceAs (AddCommGroup (selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ)))

instance : Module ℝ Herm4 :=
  inferInstanceAs (Module ℝ (selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ)))

theorem Herm4.mat_injective : Function.Injective Herm4.mat := fun _ _ h => Subtype.ext h

theorem Herm4.mat_add (A B : Herm4) : (A + B).mat = A.mat + B.mat := rfl

theorem Herm4.mat_smul (r : ℝ) (A : Herm4) : (r • A).mat = (r : ℂ) • A.mat := rfl

/-- The defining property: the underlying matrix is its own conjugate transpose. -/
theorem Herm4.mat_herm (A : Herm4) : A.matᴴ = A.mat :=
  (id A : selfAdjoint (Matrix (Fin 4) (Fin 4) ℂ)).2

/-! ## 2. The Frobenius inner product

`⟪A, B⟫ = Re Tr(AB)`. Every condition is a Mathlib theorem about traces of matrices:
symmetry is `trace_mul_comm`, positivity is `posSemidef_conjTranspose_mul_self` together
with `PosSemidef.trace_nonneg`, and definiteness is
`trace_conjTranspose_mul_self_eq_zero_iff`. Nothing is posited. -/

/-- The Frobenius inner product on the Hermitian slice. `Tr(AB)` is real for Hermitian
`A`, `B`, so taking the real part discards nothing. -/
def frob (A B : Herm4) : ℝ := (A.mat * B.mat).trace.re

/-- For a Hermitian matrix, `A · A` is `Aᴴ · A`, which is what makes the trace
nonnegative. -/
theorem frob_self_eq (A : Herm4) : A.mat * A.mat = A.matᴴ * A.mat := by
  rw [Herm4.mat_herm]

@[implicit_reducible]
def herm4Core : InnerProductSpace.Core ℝ Herm4 where
  inner := frob
  conj_inner_symm A B := by
    simp only [starRingEnd_apply, star_trivial, frob]
    rw [Matrix.trace_mul_comm]
  re_inner_nonneg A := by
    simp only [RCLike.re_to_real, frob]
    rw [frob_self_eq]
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self A.mat).trace_nonneg).1
  add_left A B C := by
    simp only [frob, Herm4.mat_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  smul_left A B r := by
    simp only [frob, starRingEnd_apply, star_trivial, Herm4.mat_smul, Matrix.smul_mul,
      Matrix.trace_smul]
    exact Complex.smul_re r _
  definite A hA := by
    simp only [frob] at hA
    rw [frob_self_eq] at hA
    have hps := Matrix.posSemidef_conjTranspose_mul_self A.mat
    have hz : (A.matᴴ * A.mat).trace = 0 :=
      Complex.ext hA ((Complex.nonneg_iff.mp hps.trace_nonneg).2).symm
    exact Herm4.mat_injective (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz)

attribute [local instance] herm4Core

@[implicit_reducible]
instance instNormedHerm4 : NormedAddCommGroup Herm4 :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ Herm4 _ _ _ herm4Core

@[implicit_reducible]
instance instIPHerm4 : InnerProductSpace ℝ Herm4 :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ Herm4)

/-! ## 3. Finite dimension, and the estate's own theorem as its first consumer -/

/-- The real-linear inclusion into the full matrix algebra. -/
def hermIncl : Herm4 →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := Herm4.mat
  map_add' := Herm4.mat_add
  map_smul' := Herm4.mat_smul

instance instFDMatrix : FiniteDimensional ℝ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Module.Finite.trans ℂ (Matrix (Fin 4) (Fin 4) ℂ)

instance : FiniteDimensional ℝ Herm4 :=
  FiniteDimensional.of_injective hermIncl Herm4.mat_injective

/-- `dim_ℝ Herm₄(ℂ) = 16`, from the estate's own `SelfAdjointDimension` (2026-08-17); the
transport to the synonym is `rfl`. `F4_1l_GaussianPartition` already consumes this same
theorem, for the partition-function count. -/
theorem finrank_herm4 : Module.finrank ℝ Herm4 = 16 :=
  SelfAdjointDimension.finrank_selfAdjoint_four

instance : ProperSpace Herm4 := FiniteDimensional.proper ℝ Herm4

instance : MeasurableSpace Herm4 := borel _

instance : BorelSpace Herm4 := ⟨rfl⟩

/-! ## 4. The measure, on the Hermitian slice itself -/

/-- **THE GAUSSIAN MEASURE ON `Herm₄(ℂ)`.** A `Measure (Herm₄(ℂ))`, which is the
declaration the L20 refuter reported absent from the whole estate. It is Mathlib's
`stdGaussian` at the Frobenius inner product, so it is canonical given that inner
product rather than a choice of coordinates. -/
def herm4Gaussian : MeasureTheory.Measure Herm4 := ProbabilityTheory.stdGaussian Herm4

instance : MeasureTheory.IsProbabilityMeasure herm4Gaussian :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.stdGaussian Herm4))

/-- An orthonormal basis of the Hermitian slice indexed by `Fin 16`. -/
def herm4Basis : OrthonormalBasis (Fin 16) ℝ Herm4 :=
  finrank_herm4 ▸ stdOrthonormalBasis ℝ Herm4

/-- **THE BRIDGE THE RESIDUE ASKED FOR.** The measure on `Herm₄(ℂ)` is the pushforward
of a 16-fold product of standard one-dimensional Gaussians along ANY orthonormal basis.
So the estate's existing 16-coordinate Gaussian is a description OF this measure rather
than a substitute FOR it, and the identification does not depend on which basis is
chosen — that independence is Mathlib's, not ours. -/
theorem herm4Gaussian_eq_map_pi (b : OrthonormalBasis (Fin 16) ℝ Herm4) :
    herm4Gaussian
      = (MeasureTheory.Measure.pi fun _ : Fin 16 => ProbabilityTheory.gaussianReal 0 1).map
          (fun x => ∑ i, x i • b i) :=
  ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis b

/-- The same at the basis this file constructs. -/
theorem herm4Gaussian_eq_map_pi_std :
    herm4Gaussian
      = (MeasureTheory.Measure.pi fun _ : Fin 16 => ProbabilityTheory.gaussianReal 0 1).map
          (fun x => ∑ i, x i • herm4Basis i) :=
  herm4Gaussian_eq_map_pi herm4Basis

end

end Herm4Gaussian
