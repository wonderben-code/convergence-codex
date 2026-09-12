import FrameChange

/-!
# The transition matrix is `C^k`, and the change-of-frame Jacobian is a positive `C^k` function

`FrameChange` proved that a change of frame multiplies the volume density by `|det A|`, and that
**any** second family on a frame's domain is such a change — its transition matrix being the frame's
own coefficient functional. It fenced what it did not give: *"**NO SMOOTHNESS OF THE TRANSITION
MATRIX.** … true by `FrameRegular.coeff_eq_inverse_gram` and `LeviCivitaOrder.contMDiffAt_gram`, and
**not proved here**."* This file proves it, and the reason it looked harder than it is turns out to
be a naming defect rather than a mathematical one.

**THE FACT WAS ALREADY IN THE ESTATE, INSIDE A PROOF.**
`LeviCivitaOrder.contMDiffAt_of_contMDiffAt_inner` — the Gram-inverse leg — establishes exactly
*"the coefficients of a section in a `C^m` local frame are `C^k` when its pairings with the frame
are"* as an unnamed `have`, and then consumes it
immediately to feed `IsLocalFrameOn.contMDiffAt_of_coeff`. The coefficients are what a change of
frame **is**, and nothing downstream could reach them. It is now
`LeviCivitaOrder.contMDiffAt_coeff`, stated where it was proved, and that theorem's proof is three
lines shorter for it (`ERRATUM 517`).

## What is proved

> **`transition`** — the transition matrix of a second family against a frame, `Aₐᵦ(y) =
> coeff_b(y)(s'ₐ y)`, named so that the statements below can be read. `density_eq_transition'` is
> `FrameChange.density_eq_transition` in that name and proves nothing new.
>
> **`det_transition_ne_zero`** — where the second family is **independent**, the transition
> determinant is non-zero. Proved *through the density*, not by linear algebra: `density s' > 0`
> and `density s' = |det A| · density s`, so `det A = 0` is impossible. The previous unit's
> transformation law is doing the work.
>
> **`contMDiffAt_transition_entry`, `contMDiffAt_det_transition`** — every entry is `C^k` when both
> families are, by `LeviCivitaOrder.contMDiffAt_coeff` against `ContMDiffAt.inner_bundle`, and hence
> so is the determinant, by `VolumeDensity.contMDiffAt_det`.
>
> **`contMDiffAt_abs_det_transition`, `abs_det_transition_pos`** — **THE JACOBIAN IS A POSITIVE
> `C^k` FUNCTION.** `|t| = √(t²)`, and `√` is `C^k` away from zero, so the absolute value costs
> nothing once the determinant is known non-vanishing. **This is what a gluing argument consumes**:
> on the overlap of two frame domains the two local densities differ by a positive `C^k` factor, so
> a partition of unity can be applied to them without leaving the regularity class.

## What is NOT here

* **STILL NO MEASURE AND NO INTEGRAL**, and now the remaining gap is stated as narrowly as this
  estate can state it: a cover of the manifold by frame domains, a partition of unity subordinate
  to it, a measure on each piece built from its density, and the additivity that
  `FrameChange.density_eq_transition` together with this file's regularity makes consistent.
  Mathlib has the partition of unity (`Geometry/Manifold/PartitionOfUnity`) and **this estate has
  never used it**; what neither has is a measure on a manifold. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NO COCYCLE IDENTITY.** That the transition matrices of three frames compose —
  `A(s → s'') = A(s' → s'') · A(s → s')` — is true and is not proved. A gluing argument on a cover
  with triple overlaps would want it; a gluing argument on a partition of unity does not, which is
  why it is named rather than proved.
* **NO STATEMENT ON A SET.** Everything is at a point, with the frame's domain a neighbourhood of
  it. The `ContMDiffOn` versions are one `contMDiffAt` per point away and are not written.
* **NO ORIENTATION AND NO SIGNED JACOBIAN.** `|det A|` is what a measure wants; `det A` and a
  coherent sign would be a volume form, and neither appears.
* **NOTHING ABOUT `a₂`, THE WALL DOES NOT MOVE, AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype ι]` and `[DecidableEq ι]`;
`IsLocalFrameOn` at order `k + 2` for the frame and `CMDiffAt k` sections for the second family in
the regularity statements, and an arbitrary order `m` in the algebraic ones; linear independence of
the **second** family only where the determinant must not vanish. **The algebraic statements omit
every manifold-smoothness instance and say so.** No orientation, no compactness, no measure.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace TransitionRegular

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor FrameRegular VolumeDensity FrameChange
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

/-! ## 1. The transition matrix, named -/

noncomputable def transition [Fintype ι] {m : WithTop ℕ∞} {s : ι → Π x : M, TangentSpace I x}
    {u : Set M} (hs : IsLocalFrameOn I E m s u) (s' : ι → Π x : M, TangentSpace I x) (y : M) :
    Matrix ι ι ℝ :=
  Matrix.of fun a b ↦ hs.coeff b y (s' a y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_eq_transition' [Fintype ι] [DecidableEq ι] {m : WithTop ℕ∞}
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    (s' : ι → Π x : M, TangentSpace I x) {y : M} (hy : y ∈ u) :
    density s' y = |Matrix.det (transition hs s' y)| * density s y :=
  density_eq_transition hs s' hy

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem det_transition_ne_zero [Fintype ι] [DecidableEq ι] {m : WithTop ℕ∞}
    {s s' : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    {y : M} (hy : y ∈ u) (hli' : LinearIndependent ℝ (s' · y)) :
    Matrix.det (transition hs s' y) ≠ 0 := by
  intro hzero
  have hpos : 0 < density s' y := density_pos hli'
  rw [density_eq_transition' hs s' hy, hzero, abs_zero, zero_mul] at hpos
  exact lt_irrefl 0 hpos

/-! ## 2. And it is `C^k` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_transition_entry [Fintype ι]
    {s s' : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E ((k : WithTop ℕ∞) + 1 + 1) s u) {x : M} (hu : u ∈ 𝓝 x)
    (hs' : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s' i)) x) (a b : ι) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ transition hs s' y a b) x := by
  haveI : IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1)
      (le_self_add.trans le_self_add)
  have hsx : ∀ j, CMDiffAt (k : WithTop ℕ∞) (T% (s j)) x := fun j ↦
    ((hs.contMDiffOn j).contMDiffAt hu).of_le (le_self_add.trans le_self_add)
  exact LeviCivitaOrder.contMDiffAt_coeff (le_self_add.trans le_self_add) hs hu
    (fun j ↦ ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) (hs' a) (hsx j)) b

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_det_transition [Fintype ι] [DecidableEq ι]
    {s s' : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E ((k : WithTop ℕ∞) + 1 + 1) s u) {x : M} (hu : u ∈ 𝓝 x)
    (hs' : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s' i)) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ Matrix.det (transition hs s' y)) x :=
  contMDiffAt_det fun a b ↦ contMDiffAt_transition_entry hs hu hs' a b

/-! ## 3. So the Jacobian is a positive `C^k` function -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_abs_det_transition [Fintype ι] [DecidableEq ι]
    {s s' : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E ((k : WithTop ℕ∞) + 1 + 1) s u) {x : M} (hu : u ∈ 𝓝 x)
    (hs' : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s' i)) x)
    (hli' : LinearIndependent ℝ (s' · x)) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ |Matrix.det (transition hs s' y)|) x := by
  have hne : Matrix.det (transition hs s' x) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (det_transition_ne_zero hs (mem_of_mem_nhds hu) hli')
  have h : ContMDiffAt I 𝓘(ℝ) k
      (Real.sqrt ∘ fun y ↦ Matrix.det (transition hs s' y) ^ 2) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ Matrix.det (transition hs s' y) ^ 2) (x := x)
      (Real.contDiffAt_sqrt hne) ((contMDiffAt_det_transition hs hu hs').pow 2)
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using h

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem abs_det_transition_pos [Fintype ι] [DecidableEq ι] {m : WithTop ℕ∞}
    {s s' : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    {y : M} (hy : y ∈ u) (hli' : LinearIndependent ℝ (s' · y)) :
    0 < |Matrix.det (transition hs s' y)| :=
  abs_pos.2 (det_transition_ne_zero hs hy hli')

end TransitionRegular
