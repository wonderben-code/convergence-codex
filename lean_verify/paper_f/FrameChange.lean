import VolumeDensity

/-!
# The volume density transforms by the Jacobian, and every second frame is a change of frame

`VolumeDensity` built `√det g` in a local frame, proved it positive and `C^k`, and fenced the one
thing that stops it being an object of the metric rather than of the frame: *"the density is
frame-dependent and this file does not say otherwise … turning these into one measure needs the
**transformation law** — that a change of frame multiplies `√det g` by `|det A|` … **named, not
attempted**."* This file is that law, and the half of it that was not named.

## What is proved

> **`changeOf`, `gramMatrix_changeOf`** — a pointwise linear change `s'ᵢ = ∑ⱼ Aᵢⱼ sⱼ` sends the Gram
> matrix to `A · g · Aᵀ`. Bilinearity of the metric and nothing else; no invertibility, no
> smoothness, no frame condition.
>
> **`det_gramMatrix_changeOf`, `density_changeOf`** — hence the determinant picks up `(det A)²` and
> **the density picks up `|det A|`**. This is the change-of-variables factor: a measure built by
> gluing local densities needs exactly this and nothing weaker, and `|det A|` rather than `det A` is
> why no orientation is required.
>
> **`density_changeOf_of_det_eq_one`, `density_changeOf_pos`** — so the density is **invariant**
> under unimodular changes, and stays strictly positive under any invertible one.
>
> **`mul_density_changeOf`, `mul_density_changeOf_of_det_eq_one`** — and so does anything integrated
> against it: for **every** `f : M → ℝ`, `f · density` transforms by `|det A|`. The
> Einstein–Hilbert integrand of `VolumeDensity.contMDiffAt_scalar_mul_density` is this at
> `f = RicciScalar.scalar LC`, and the statement is deliberately not specialised — **the density's
> transformation law does not see the curvature**, and saying it with `f` general is what makes that
> visible.
>
> **`changeOf_transition`, `density_eq_transition`** — **AND THE OTHER HALF, WHICH THE FENCE DID NOT
> NAME.** A transformation law is empty until two frames are known to be related by such an `A`.
> They are: the transition matrix is the frame's own coefficient functional,
> `Aᵢⱼ(y) = coeff_j(y)(s'ᵢ y)`, and `IsLocalFrameOn.coeff_sum_eq` says it works — so **any** second
> family `s'` on a frame's domain is a `changeOf` of it, and `density s' = |det A| · density s`
> there, with no hypothesis on `s'` at all. **`s'` is not assumed to be a frame**; if it is not, its
> transition matrix is singular and the identity reads `0 = 0`, which is the correct answer.

## What is NOT here

* **STILL NO MEASURE, NO INTEGRAL, NO ACTION.** What remains between these theorems and
  `∫ S dvol` is measure theory and only measure theory: a partition of unity subordinate to a cover
  by frame domains, a measure on each from its density, and the additivity that the law above makes
  consistent. **None of it is attempted, and no cost is claimed** (`ERRATUM 246`). Neither this
  estate nor the pinned library has a measure-theoretic statement about a manifold at all.
* **NO SMOOTHNESS OF THE TRANSITION MATRIX.** `changeOf_transition` is pointwise and algebraic.
  That `y ↦ A y` is `C^k` when both families are `C^k` frames is true by
  `FrameRegular.coeff_eq_inverse_gram` and `LeviCivitaOrder.contMDiffAt_gram`, and is **not proved
  here** — the gluing argument would want it and this file does not reach the gluing argument.
* **NO ORIENTATION AND NO SIGNED VOLUME.** `|det A|` is what a measure needs; a volume *form* would
  need `det A` and a consistent orientation, and neither appears.
* **NO CHART STATEMENT.** The law is stated for two families on one frame's domain, not for two
  charts overlapping. Relating a chart's frame to another chart's is a further step and is not
  taken.
* **NOTHING ABOUT `a₂`, AND THE WALL DOES NOT MOVE.** `WALLS` §W5's rung 4 wants the curvature
  integral to emerge from an expansion of `Tr f(D/Λ)`. No published tag moves.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype ι]` throughout and
`[DecidableEq ι]` wherever `Matrix.det` appears; `IsLocalFrameOn` at an arbitrary order `m` in §4,
which is the only place a frame is assumed at all. **Every theorem here omits the manifold
smoothness instances and says so in its `omit` line** — the transformation law is algebra, and the
file's `variable` block carries `ScalarOrder`'s context only so that `density` elaborates in the
same setting it was defined in. **No invertibility of `A` except where it is stated, no
orientation, no compactness, no measure.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FrameChange

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor FrameRegular VolumeDensity
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

/-! ## 1. A pointwise linear change of frame -/

noncomputable def changeOf [Fintype ι] (A : M → Matrix ι ι ℝ) (s : ι → Π x : M, TangentSpace I x) :
    ι → Π x : M, TangentSpace I x :=
  fun i y ↦ ∑ j, A y i j • s j y

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem gramMatrix_changeOf [Fintype ι] (A : M → Matrix ι ι ℝ)
    (s : ι → Π x : M, TangentSpace I x) (y : M) :
    gramMatrix (changeOf A s) y = A y * gramMatrix s y * (A y)ᵀ := by
  ext i j
  simp only [gramMatrix_apply, changeOf, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem det_gramMatrix_changeOf [Fintype ι] [DecidableEq ι] (A : M → Matrix ι ι ℝ)
    (s : ι → Π x : M, TangentSpace I x) (y : M) :
    Matrix.det (gramMatrix (changeOf A s) y)
      = Matrix.det (A y) ^ 2 * Matrix.det (gramMatrix s y) := by
  rw [gramMatrix_changeOf, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-! ## 2. So the density transforms by the Jacobian -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_changeOf [Fintype ι] [DecidableEq ι] (A : M → Matrix ι ι ℝ)
    (s : ι → Π x : M, TangentSpace I x) (y : M) :
    density (changeOf A s) y = |Matrix.det (A y)| * density s y := by
  rw [density, density, det_gramMatrix_changeOf, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_changeOf_of_det_eq_one [Fintype ι] [DecidableEq ι] {A : M → Matrix ι ι ℝ}
    (s : ι → Π x : M, TangentSpace I x) {y : M} (hA : |Matrix.det (A y)| = 1) :
    density (changeOf A s) y = density s y := by
  rw [density_changeOf, hA, one_mul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_changeOf_pos [Fintype ι] [DecidableEq ι] {A : M → Matrix ι ι ℝ}
    {s : ι → Π x : M, TangentSpace I x} {y : M} (hA : Matrix.det (A y) ≠ 0)
    (hli : LinearIndependent ℝ (s · y)) : 0 < density (changeOf A s) y := by
  rw [density_changeOf]
  exact mul_pos (abs_pos.2 hA) (density_pos hli)

/-! ## 3. And so does anything integrated against it, the integrand included -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem mul_density_changeOf [Fintype ι] [DecidableEq ι] (f : M → ℝ) (A : M → Matrix ι ι ℝ)
    (s : ι → Π x : M, TangentSpace I x) (y : M) :
    f y * density (changeOf A s) y = |Matrix.det (A y)| * (f y * density s y) := by
  rw [density_changeOf]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem mul_density_changeOf_of_det_eq_one [Fintype ι] [DecidableEq ι] (f : M → ℝ)
    {A : M → Matrix ι ι ℝ} (s : ι → Π x : M, TangentSpace I x) {y : M}
    (hA : |Matrix.det (A y)| = 1) :
    f y * density (changeOf A s) y = f y * density s y := by
  rw [mul_density_changeOf, hA, one_mul]

/-! ## 4. And any second frame on the same domain is such a change -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem changeOf_transition [Fintype ι] {m : WithTop ℕ∞}
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    (s' : ι → Π x : M, TangentSpace I x) {y : M} (hy : y ∈ u) (i : ι) :
    changeOf (fun z ↦ Matrix.of fun a b ↦ hs.coeff b z (s' a z)) s i y = s' i y :=
  (hs.coeff_sum_eq (s' i) hy).symm

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_eq_transition [Fintype ι] [DecidableEq ι] {m : WithTop ℕ∞}
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    (s' : ι → Π x : M, TangentSpace I x) {y : M} (hy : y ∈ u) :
    density s' y
      = |Matrix.det (Matrix.of fun a b ↦ hs.coeff b y (s' a y))| * density s y := by
  have hgram : gramMatrix s' y
      = gramMatrix (changeOf (fun z ↦ Matrix.of fun a b ↦ hs.coeff b z (s' a z)) s) y := by
    ext a b
    simp only [gramMatrix_apply]
    rw [show s' a y = _ from (changeOf_transition hs s' hy a).symm,
      show s' b y = _ from (changeOf_transition hs s' hy b).symm]
  rw [density, hgram, ← density, density_changeOf]

end FrameChange
