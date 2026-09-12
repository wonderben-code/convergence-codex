import ScalarOrder
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The Riemannian volume density, and the Einstein–Hilbert integrand carrying it

`ScalarOrder` made the scalar curvature a `C^k` function of the point and fenced what it did not
give: *"**NO ACTION FUNCTIONAL, AND NO INTEGRAL OF ANY KIND.** The Einstein–Hilbert action is
`∫ S dvol`, and this file gives the **integrand** and nothing else."* `WALLS` §W5's twentieth
addendum, the same day, calls that the last rung of its kind — *"the Riemannian geometry under this
wall is now complete and differentiable end to end"* — and names the remaining obstruction as
measure theory: *"`∫ S dvol` needs a Riemannian volume measure, and this estate has no
measure-theoretic statement about a manifold at all."*

**The geometry was not quite complete.** Between the integrand and the measure sits one object that
is differential geometry and not measure theory: the **volume density** `√det g` of a local frame —
what a measure would integrate against, and the only factor of `∫ S dvol` that the estate could
have written and had not. It appears nowhere: no `Matrix.det` of a Gram matrix on a manifold, and
`volumeForm` matches **no file** under Mathlib's `Geometry/`, its only occurrences being on a fixed
oriented inner product space (`Analysis/InnerProductSpace/Orientation`) and the Haar measure built
from one.

**This file supplies it, and thereby sharpens the addendum rather than moving the wall**: what is
missing for `∫ S dvol` is now *exactly* measure theory — patching local densities into one measure
— with no differential geometry left in the way.

## What is proved

> **`gramMatrix`, `gramMatrix_isHermitian`, `dotProduct_gramMatrix`** — the Gram matrix
> `gᵢⱼ(y) = ⟪sᵢ y, sⱼ y⟫` of a family of sections, symmetric, with its quadratic form identified as
> `⟪∑ cᵢ sᵢ, ∑ cⱼ sⱼ⟫`. `FrameRegular.gram` is the same data as a continuous linear **operator**,
> which is what the inverse-Gram identities want; a **matrix** is what a determinant wants, and
> nothing had built one.
>
> **`gramMatrix_posDef`, `det_gramMatrix_pos`** — where the family is linearly independent the Gram
> matrix is **positive definite**, hence its determinant is **strictly positive**. The quadratic
> form is a squared norm and vanishes only at `c = 0`; `Matrix.PosDef.det_pos` does the rest.
>
> **`density`, `density_pos`** — so `√det g` is defined and **strictly positive** on a frame's
> domain. This is the local volume element.
>
> **`contMDiffAt_gramMatrix_entry`, `contMDiffAt_det_gramMatrix`, `contMDiffAt_density`** — and it
> is **`C^k`** for `C^k` sections and a `C^(k+2)` metric. The determinant is handled by
> `Matrix.det_apply'` — a finite sum of finite products of entries — so the smoothness is
> `ContMDiffAt.sum` over permutations and `ContMDiffAt.prod` over the row index, with no
> determinant-smoothness lemma needed, there being none in the pinned library.
>
> **`contMDiffAt_scalar_mul_density`** — **THE EINSTEIN–HILBERT INTEGRAND WITH ITS DENSITY**:
> `y ↦ S(y) · √det g(y)` is `C^k` at every point of a `C^(k+2)` local frame's domain. This is the
> function `∫ S dvol` integrates in a chart, and it is now a differentiable object.

## What is NOT here, and the list is the point

* **NO MEASURE, NO INTEGRAL, NO ACTION, NO FIELD EQUATIONS.** A density in a frame is not a
  measure. Turning these into one needs the **transformation law** — that a change of frame
  multiplies `√det g` by `|det A|`, so that the local densities agree where charts overlap — and a
  **partition of unity** to glue them. Neither is here. **Named, not attempted, no cost claimed**
  (`ERRATUM 246`), and `ScalarOrder`'s fence and `WALLS` §W5's twentieth addendum both stand
  unaltered on everything they say about the integral.
* **THE DENSITY IS FRAME-DEPENDENT AND THIS FILE DOES NOT SAY OTHERWISE.** Every statement carries
  its frame. `density s` is not an invariant of the metric and must not be read as one until the
  transformation law exists.
* **NO ORTHONORMAL FRAME**, in which `g` is the identity and the density is `1`. This estate has no
  smooth orthonormal frame and neither does the pinned library, which is why `FrameRegular` exists
  and why the identity above is stated in an **arbitrary** frame.
* **NOTHING ABOUT `a₂`, AND NO HEAT KERNEL.** `WALLS` §W5's rung 4 wants the curvature integral to
  come **out of** an expansion of `Tr f(D/Λ)`. Writing more of the integrand by hand is not a step
  on that rung. **The wall does not move**, and no published tag moves.
* **ONLY FINITE ORDERS**, inherited from `ScalarOrder` and everything under it: `k` is a natural
  number, so nothing here is a `C^∞` statement.
* **NO SHARPNESS.** `C^(k+2)` for a `C^k` answer is what the route costs and nothing here shows
  `C^(k+1)` would fail.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `ScalarOrder`'s context unchanged —
`[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`, a
`ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]`,
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`, the Riemannian bundle and its two smoothness
instances. The frame's index type takes `[Fintype ι]` and `[DecidableEq ι]` throughout, both
because `Matrix.det` asks for them; the algebraic statements need **no** manifold smoothness at all
and say so in their `omit` lines. **No orientation, no compactness, no completeness of `M`, and no
measure.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace VolumeDensity

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor FrameRegular
open scoped Bundle ContDiff Topology Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  {ι : Type*}

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self KoszulManifold.finDimTangent
  CurvatureTensor.contMDiffVectorBundle_two RicciOrder.contMDiffVectorBundle_add_two

local notation "⟪" x ", " y "⟫" => inner ℝ x y

local notation "LC" => (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))

/-! ## 1. The Gram matrix of a family of sections -/

noncomputable def gramMatrix (s : ι → Π x : M, TangentSpace I x) (y : M) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ⟪s i y, s j y⟫

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem gramMatrix_apply (s : ι → Π x : M, TangentSpace I x) (y : M) (i j : ι) :
    gramMatrix s y i j = ⟪s i y, s j y⟫ := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem gramMatrix_isHermitian {s : ι → Π x : M, TangentSpace I x} {y : M} :
    Matrix.IsHermitian (gramMatrix s y) := by
  ext i j
  simp [Matrix.conjTranspose_apply, gramMatrix_apply, real_inner_comm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem dotProduct_gramMatrix [Fintype ι] {s : ι → Π x : M, TangentSpace I x} {y : M}
    (c : ι → ℝ) : star c ⬝ᵥ (gramMatrix s y *ᵥ c)
      = ⟪∑ i, c i • s i y, ∑ j, c j • s j y⟫ := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, gramMatrix_apply, sum_inner,
    inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [real_inner_comm (s j y) (s i y)]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem gramMatrix_posDef [Finite ι] {s : ι → Π x : M, TangentSpace I x} {y : M}
    (hli : LinearIndependent ℝ (s · y)) : Matrix.PosDef (gramMatrix s y) := by
  cases nonempty_fintype ι
  refine Matrix.PosDef.of_dotProduct_mulVec_pos gramMatrix_isHermitian fun c hc ↦ ?_
  rw [dotProduct_gramMatrix]
  refine real_inner_self_pos.2 fun hzero ↦ hc ?_
  funext i
  exact Fintype.linearIndependent_iff.1 hli c hzero i

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem det_gramMatrix_pos [Fintype ι] [DecidableEq ι] {s : ι → Π x : M, TangentSpace I x} {y : M}
    (hli : LinearIndependent ℝ (s · y)) : 0 < Matrix.det (gramMatrix s y) :=
  (gramMatrix_posDef hli).det_pos

/-! ## 2. The volume density -/

noncomputable def density [DecidableEq ι] [Fintype ι] (s : ι → Π x : M, TangentSpace I x)
    (y : M) : ℝ :=
  Real.sqrt (Matrix.det (gramMatrix s y))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_pos [Fintype ι] [DecidableEq ι] {s : ι → Π x : M, TangentSpace I x} {y : M}
    (hli : LinearIndependent ℝ (s · y)) : 0 < density s y :=
  Real.sqrt_pos.2 (det_gramMatrix_pos hli)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_gramMatrix_entry {s : ι → Π x : M, TangentSpace I x} {x : M}
    (hs : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x) (i j : ι) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ gramMatrix s y i j) x := by
  haveI : IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1)
      (le_self_add.trans le_self_add)
  exact ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) (hs i) (hs j)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_det_gramMatrix [Fintype ι] [DecidableEq ι]
    {s : ι → Π x : M, TangentSpace I x} {x : M}
    (hs : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ Matrix.det (gramMatrix s y)) x := by
  simp only [Matrix.det_apply']
  refine ContMDiffAt.sum fun σ _ ↦ contMDiffAt_const.mul ?_
  exact ContMDiffAt.prod fun i _ ↦ contMDiffAt_gramMatrix_entry hs (σ i) i

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_density [Fintype ι] [DecidableEq ι]
    {s : ι → Π x : M, TangentSpace I x} {x : M}
    (hs : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x)
    (hli : LinearIndependent ℝ (s · x)) :
    ContMDiffAt I 𝓘(ℝ) k (density s) x := by
  have h : ContMDiffAt I 𝓘(ℝ) k
      (Real.sqrt ∘ fun y ↦ Matrix.det (gramMatrix s y)) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ Matrix.det (gramMatrix s y)) (x := x)
      (Real.contDiffAt_sqrt (det_gramMatrix_pos hli).ne') (contMDiffAt_det_gramMatrix hs)
  simpa [density, Function.comp_def] using h

/-! ## 3. The Einstein–Hilbert integrand, density included -/

theorem contMDiffAt_scalar_mul_density [Fintype ι] [DecidableEq ι]
    {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E ((k : WithTop ℕ∞) + 1 + 1) s u) {x : M} (hu : u ∈ 𝓝 x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ RicciScalar.scalar LC y * density s y) x := by
  have hsx : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x := fun i ↦
    ((hs.contMDiffOn i).contMDiffAt hu).of_le (le_self_add.trans le_self_add)
  exact (ScalarOrder.contMDiffAt_scalar_of_localFrame hs hu).mul
    (contMDiffAt_density hsx (hs.linearIndependent (mem_of_mem_nhds hu)))

end VolumeDensity
