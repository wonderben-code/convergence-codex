import KoszulVectorSpace

/-!
# The Levi-Civita connection of a Riemannian manifold exists: the Koszul construction

`WALLS` §W5.1 §3 names one object between a library that has metrics and a library that has
curvature: **the Levi-Civita connection**. `LeviCivitaUnique` proved that a torsion-free
metric-compatible covariant derivative is unique; `LeviCivitaFlat` and `KoszulVectorSpace` built
it on the model space. This file builds it on a Riemannian manifold. For `M` a `C²` manifold
modelled on a finite-dimensional real normed space, whose tangent spaces carry inner products
(`RiemannianBundle`) depending `C¹` on the point (`IsContMDiffRiemannianBundle I 1`), **there is a
`CovariantDerivative` on the tangent bundle that is torsion-free and metric-compatible**
(`exists_leviCivita`), and by `LeviCivitaUnique` every such connection agrees with it on every
section differentiable at the point (`eq_leviCivita_of_torsionFree_of_compatible`).

The proof is the textbook one and it is coordinate-free. The Koszul expression
`⟨∇_X Y, Z⟩ = ½ (X⟨Y,Z⟩ + Y⟨X,Z⟩ − Z⟨X,Y⟩ + ⟨[X,Y],Z⟩ − ⟨[X,Z],Y⟩ − ⟨[Y,Z],X⟩)` is a bare
function of three sections (`koszulAux`). It is tensorial in `X` and in `Z`: under `X ↦ f • X`
the derivative terms and the bracket terms each produce a `df` term and the two cancel
(`koszulAux_tensorial₁`, `koszulAux_tensorial₂`). Mathlib's `TensorialAt.mkHom₂`, the device its
own `torsion` is built with, turns a function tensorial in two arguments into a bilinear form on
the fibre (`koszulForm`). The Riesz map of the fibre — `KoszulVectorSpace.toDualEquiv` for the
constant metric of the inner product space `TangentSpace I x` — turns the form in `Z` into the
vector `∇ᵥY(x)` (`riesz`, `leviCivitaFun`). Additivity and the Leibniz rule in `Y` are the same
bookkeeping (`koszulAux_add_Y`, `koszulAux_smul_Y`); torsion-freeness is the antisymmetrisation of
the expression in `X, Y` (`koszulAux_sub_swap`) and compatibility its symmetrisation in `Y, Z`
(`koszulAux_add_swap`). Every ingredient the standard proof consumes was present in the pinned
library and was named in §W5.1 §3 by 31 August; this file is the assembly.

## What is proved

**`extDerivFun_apply`, `extDerivFun_apply_add`, `extDerivFun_apply_mul`,
`extDerivFun_apply_add_dir`, `extDerivFun_apply_smul_dir`** — the exterior derivative of a scalar
function, applied to a vector: the sum and product rules, and linearity in the vector.

**`dInner`, `dInner_add_left`, `dInner_smul_left`, `dInner_symm`** — `X⟨Y, Z⟩`, the derivative of
the inner product of two sections along a third, and its linearity in `X`.

**`finDimTangent`, `riesz`, `inner_riesz`** — the Riesz map `(TangentSpace I x →L[ℝ] ℝ) →L
TangentSpace I x`, with `⟪riesz φ, w⟫ = φ w`.

**`koszulAux`, `koszulAux_sub_swap`, `koszulAux_add_swap`** — the Koszul expression, and its
antisymmetrisation in `X, Y` (the bracket) and symmetrisation in `Y, Z` (the derivative of the
metric).

**`mdiffAt_inner`, `dInner_smul_mid`, `dInner_smul_right`, `dInner_add_mid`, `dInner_add_right`**
— the differentiability of `⟨Y, Z⟩` (`MDifferentiableAt.inner_bundle`) and the product and sum
rules for `X⟨Y, Z⟩` in `Y` and in `Z`.

**`inner_bracket_smul_left`, `inner_bracket_smul_right`, `inner_bracket_add_left`,
`inner_bracket_add_right`** — the Leibniz and additivity rules of the bracket, inside an inner
product (`mlieBracket_smul_left` and its three companions).

**`koszulAux_tensorial₁`, `koszulAux_tensorial₂`** — **the Koszul expression is tensorial in `X`
and in `Z`**, for the other two sections differentiable at the point.

**`koszulAux_add_Y`, `koszulAux_smul_Y`** — additivity and the Leibniz rule in `Y`:
`koszulAux (f • Y) X Z = f • koszulAux Y X Z + df(X) ⟨Y, Z⟩`.

**`koszulForm`, `koszulForm_apply`** — the bilinear form `(v, w) ↦ ⟨∇ᵥY, w⟩` on the fibre, by
`TensorialAt.mkHom₂`, evaluating to `koszulAux` on differentiable sections.

**`leviCivitaFun`, `inner_leviCivitaFun`, `inner_leviCivitaFun_extend`** — `∇ᵥY(x)`, the Riesz
representative of the form, on sections differentiable at `x`, and `0` on the others.

**`leviCivita`, `leviCivita_apply`** — **the Levi-Civita connection as a `CovariantDerivative`**:
additivity and the Leibniz rule are `koszulAux_add_Y` and `koszulAux_smul_Y` read through
`ext_inner_right` against extended vectors.

**`leviCivita_torsion`** — **it is torsion-free**. **`leviCivita_compatible`** — **it is
metric-compatible** (`LeviCivitaUnique.IsMetricCompatible`).

**`exists_leviCivita`** — **EXISTENCE**: a torsion-free metric-compatible covariant derivative on
the tangent bundle of every Riemannian manifold under the hypotheses below.

**`eq_leviCivita_of_torsionFree_of_compatible`** — **AND UNIQUENESS**: every torsion-free
metric-compatible connection is `leviCivita` on every section differentiable at the point
(`LeviCivitaUnique.eq_of_torsionFree_of_compatible`).

**`leviCivita_eq_flatCov`** — **consistency**: on a Euclidean space with its constant metric,
`leviCivita` is `LeviCivitaFlat.flatCov` on every section differentiable at the point.

## What is NOT here

**A JUNK VALUE OFF THE DIFFERENTIABLE SECTIONS.** `leviCivitaFun Y x` is `0` when `Y` is not
differentiable at `x`. Mathlib's `CovariantDerivative` is a function on all sections and its axioms
constrain it only where a section is differentiable, so any other choice there would give a
different structure with the same theorems; this is `LeviCivitaUnique`'s fence *not equality of the
structures*, seen from the existence side. Nothing is claimed about `leviCivita` on a section not
differentiable at the point.

**NO REGULARITY OF THE CONNECTION.** The metric is asked to be `C¹` and the connection is built
from its first derivatives; that `leviCivita` is a `ContMDiffCovariantDerivativeOn` of any order is
not stated and not proved.

**NO CURVATURE.** `R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` can now be written on top of
`leviCivita`, and nothing here writes it: `WALLS` §W5.1's staircase names it as rung 3, still
absent from the pinned Mathlib (`curvature` matches no file under `Geometry/`, re-probed by
7 September). **Not attempted, no cost claimed** (`ERRATUM 246`). No heat kernel, no `a₂`.

**NO COMPARISON WITH `KoszulVectorSpace.VarMetric.cov`.** The consistency check against the
model space is `leviCivita_eq_flatCov`, through uniqueness; the variable-metric file's connection
is built on a `VarMetric` rather than a `RiemannianBundle` instance, and the two are not compared.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, a `ChartedSpace H M` and a model `I` throughout; the `Scalar` section takes
nothing more; `[RiemannianBundle (fun x ↦ TangentSpace I x)]` from `dInner` on;
`[FiniteDimensional ℝ E]` for the Riesz map and again from `koszulForm` on (Mathlib's hypothesis
for `TensorialAt.mkHom₂`); `[IsManifold I 2 M]` from `koszulAux` on (Mathlib's hypothesis for the
bracket's Leibniz rules and for `torsion`); `[IsContMDiffRiemannianBundle I 1 E (TangentSpace I)]`
wherever `⟨Y, Z⟩` is differentiated (Mathlib's `inner_bundle`); `[CompleteSpace E]` from the
bracket lemmas on (Mathlib's hypothesis there and for `torsion`, redundant given finite dimension
over `ℝ` and kept because Mathlib asks for it separately). So `exists_leviCivita` holds for a
`C²` manifold with corners modelled on a finite-dimensional real normed space, with a `C¹`
Riemannian metric; no compactness, no completeness of `M`, no dimension restriction. The
`VectorSpace` section takes a finite-dimensional complete real inner product space, with Mathlib's
own instances for its constant metric.

**ON THE PROOFS.** Two places needed the definitional identification of `TangentSpace 𝓘(ℝ) c` with
`ℝ` and of the tangent bundle's fibres with `E`, which `rw` and `simp` cannot see through: the
product rule `extDerivFun_apply_mul` states the derivative rule with every map at one type through
`id` and closes by `exact`, and `inner_bracket_smul_left`/`_right` restate one scalar by `change`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace KoszulManifold

open Bundle Manifold VectorField FiberBundle LeviCivitaUnique
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Scalar

theorem extDerivFun_apply (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ) f x v := rfl

theorem extDerivFun_apply_add {f g : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (v : TangentSpace I x) :
    extDerivFun (I := I) (f + g) x v = extDerivFun (I := I) f x v + extDerivFun (I := I) g x v := by
  rw [extDerivFun_add hf hg, ContinuousLinearMap.add_apply]

/-- The product rule for the exterior derivative of scalar functions. -/
theorem extDerivFun_apply_mul {f g : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (v : TangentSpace I x) :
    extDerivFun (I := I) (f * g) x v
      = f x * extDerivFun (I := I) g x v + g x * extDerivFun (I := I) f x v := by
  -- the derivative rule, stated with every map at the one type `TangentSpace I x →L[ℝ] ℝ`, and
  -- closed by `exact`: `rw` cannot see through `TangentSpace 𝓘(ℝ) _` to `ℝ`
  have h : @id (TangentSpace I x →L[ℝ] ℝ) (mfderiv I 𝓘(ℝ) (f * g) x)
      = f x • @id (TangentSpace I x →L[ℝ] ℝ) (mfderiv I 𝓘(ℝ) g x)
        + g x • @id (TangentSpace I x →L[ℝ] ℝ) (mfderiv I 𝓘(ℝ) f x) :=
    (hf.hasMFDerivAt.mul hg.hasMFDerivAt).mfderiv
  have h2 := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L v) h
  simp only [id, ContinuousLinearMap.add_apply] at h2
  exact h2

theorem extDerivFun_apply_add_dir (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    extDerivFun (I := I) f x (v + w) = extDerivFun (I := I) f x v + extDerivFun (I := I) f x w :=
  map_add _ v w

theorem extDerivFun_apply_smul_dir (f : M → ℝ) (x : M) (c : ℝ) (v : TangentSpace I x) :
    extDerivFun (I := I) f x (c • v) = c * extDerivFun (I := I) f x v := by
  rw [map_smul, smul_eq_mul]

end Scalar

section Riemannian

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `X⟨Y, Z⟩` at `x`: the derivative of the inner product of two sections along a third. -/
noncomputable def dInner (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  extDerivFun (I := I) (fun y ↦ ⟪Y y, Z y⟫) x (X x)

theorem dInner_add_left (X X' Y Z : Π x : M, TangentSpace I x) (x : M) :
    dInner (X + X') Y Z x = dInner X Y Z x + dInner X' Y Z x :=
  extDerivFun_apply_add_dir _ x _ _

theorem dInner_smul_left (f : M → ℝ) (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    dInner (f • X) Y Z x = f x * dInner X Y Z x :=
  extDerivFun_apply_smul_dir _ x _ _

theorem dInner_symm (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    dInner X Y Z x = dInner X Z Y x := by
  unfold dInner
  congr 3
  funext y
  exact real_inner_comm _ _

/-- The Koszul expression `⟨∇_X Y, Z⟩` at `x`, as a bare function of three sections. -/
noncomputable def koszulAux (Y X Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  (1 / 2 : ℝ) * (dInner X Y Z x + dInner Y X Z x - dInner Z X Y x
    + ⟪mlieBracket I X Y x, Z x⟫ - ⟪mlieBracket I X Z x, Y x⟫ - ⟪mlieBracket I Y Z x, X x⟫)

/-- Antisymmetrising the Koszul expression in `X, Y` gives the bracket: torsion-freeness. -/
theorem koszulAux_sub_swap (Y X Z : Π x : M, TangentSpace I x) (x : M) :
    koszulAux Y X Z x - koszulAux X Y Z x = ⟪mlieBracket I X Y x, Z x⟫ := by
  simp only [koszulAux]
  rw [dInner_symm Z X Y, mlieBracket_swap_apply (V := Y) (W := X), inner_neg_left]
  ring

/-- Symmetrising the Koszul expression in `Y, Z` gives the derivative of the metric:
compatibility. -/
theorem koszulAux_add_swap (Y X Z : Π x : M, TangentSpace I x) (x : M) :
    koszulAux Y X Z x + koszulAux Z X Y x = dInner X Y Z x := by
  simp only [koszulAux]
  rw [dInner_symm X Z Y, mlieBracket_swap_apply (V := Z) (W := Y), inner_neg_left]
  ring

section Manifold

variable [IsManifold I 2 M]

section Riesz

variable [FiniteDimensional ℝ E]

/-- Finite dimensionality of the tangent spaces, read off the vector bundle. -/
abbrev finDimTangent (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x

attribute [local instance] finDimTangent

variable (I) in
/-- The Riesz map of the tangent space at `x`: the inverse of `v ↦ ⟪v, ·⟫`, through the
constant metric `KoszulVectorSpace.ofInner` of the inner product space `TangentSpace I x`. -/
noncomputable def riesz (x : M) : (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x :=
  (((KoszulVectorSpace.ofInner (F := TangentSpace I x)).toDualEquiv 0).symm :
    (TangentSpace I x →L[ℝ] ℝ) ≃L[ℝ] TangentSpace I x)

theorem inner_riesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) (w : TangentSpace I x) :
    ⟪riesz I x φ, w⟫ = φ w := by
  have h := (KoszulVectorSpace.ofInner (F := TangentSpace I x)).g_symm_apply 0 φ
  have h2 := congrArg (fun ψ ↦ ψ w) h
  simpa [riesz, KoszulVectorSpace.ofInner_g] using h2

end Riesz

section Smooth

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

theorem mdiffAt_inner {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ ⟪Y y, Z y⟫) x :=
  MDifferentiableAt.inner_bundle (E := (TangentSpace I : M → Type _)) hY hZ

theorem dInner_smul_mid {f : M → ℝ} {X Z : Π x : M, TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x)
    (Y : Π x : M, TangentSpace I x) :
    dInner Y (f • X) Z x = f x * dInner Y X Z x + ⟪X x, Z x⟫ * extDerivFun (I := I) f x (Y x) := by
  have h : (fun y ↦ ⟪(f • X) y, Z y⟫) = f * (fun y ↦ ⟪X y, Z y⟫) := by
    funext y
    simp [real_inner_smul_left]
  unfold dInner
  rw [h, extDerivFun_apply_mul hf (mdiffAt_inner hX hZ)]

theorem dInner_smul_right {f : M → ℝ} {X Y : Π x : M, TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (Z : Π x : M, TangentSpace I x) :
    dInner Z X (f • Y) x = f x * dInner Z X Y x + ⟪X x, Y x⟫ * extDerivFun (I := I) f x (Z x) := by
  have h : (fun y ↦ ⟪X y, (f • Y) y⟫) = f * (fun y ↦ ⟪X y, Y y⟫) := by
    funext y
    simp [real_inner_smul_right]
  unfold dInner
  rw [h, extDerivFun_apply_mul hf (mdiffAt_inner hX hY)]

theorem dInner_add_mid {X X' Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hZ : MDiffAt (T% Z) x)
    (Y : Π x : M, TangentSpace I x) :
    dInner Y (X + X') Z x = dInner Y X Z x + dInner Y X' Z x := by
  have h : (fun y ↦ ⟪(X + X') y, Z y⟫) = (fun y ↦ ⟪X y, Z y⟫) + (fun y ↦ ⟪X' y, Z y⟫) := by
    funext y
    simp [inner_add_left]
  unfold dInner
  rw [h, extDerivFun_apply_add (mdiffAt_inner hX hZ) (mdiffAt_inner hX' hZ)]

theorem dInner_add_right {X Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (Z : Π x : M, TangentSpace I x) :
    dInner Z X (Y + Y') x = dInner Z X Y x + dInner Z X Y' x := by
  have h : (fun y ↦ ⟪X y, (Y + Y') y⟫) = (fun y ↦ ⟪X y, Y y⟫) + (fun y ↦ ⟪X y, Y' y⟫) := by
    funext y
    simp [inner_add_right]
  unfold dInner
  rw [h, extDerivFun_apply_add (mdiffAt_inner hX hY) (mdiffAt_inner hX hY')]

end Smooth

section Bracket

variable [CompleteSpace E]

theorem inner_bracket_smul_left {f : M → ℝ} {X : Π x : M, TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hX : MDiffAt (T% X) x)
    (Y Z : Π x : M, TangentSpace I x) :
    ⟪mlieBracket I (f • X) Y x, Z x⟫
      = f x * ⟪mlieBracket I X Y x, Z x⟫ - extDerivFun (I := I) f x (Y x) * ⟪X x, Z x⟫ := by
  rw [mlieBracket_smul_left hf hX, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  change (-(extDerivFun (I := I) f x (Y x))) * ⟪X x, Z x⟫ + _ = _
  ring

theorem inner_bracket_smul_right {f : M → ℝ} {Y : Π x : M, TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hY : MDiffAt (T% Y) x)
    (X Z : Π x : M, TangentSpace I x) :
    ⟪mlieBracket I X (f • Y) x, Z x⟫
      = f x * ⟪mlieBracket I X Y x, Z x⟫ + extDerivFun (I := I) f x (X x) * ⟪Y x, Z x⟫ := by
  rw [mlieBracket_smul_right hf hY, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  change (extDerivFun (I := I) f x (X x)) * ⟪Y x, Z x⟫ + _ = _
  ring

theorem inner_bracket_add_left {X X' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (Y Z : Π x : M, TangentSpace I x) :
    ⟪mlieBracket I (X + X') Y x, Z x⟫
      = ⟪mlieBracket I X Y x, Z x⟫ + ⟪mlieBracket I X' Y x, Z x⟫ := by
  rw [mlieBracket_add_left hX hX', inner_add_left]

theorem inner_bracket_add_right {Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (X Z : Π x : M, TangentSpace I x) :
    ⟪mlieBracket I X (Y + Y') x, Z x⟫
      = ⟪mlieBracket I X Y x, Z x⟫ + ⟪mlieBracket I X Y' x, Z x⟫ := by
  rw [mlieBracket_add_right hY hY', inner_add_left]

section Smooth

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- **The Koszul expression is tensorial in the direction `X`.** -/
theorem koszulAux_tensorial₁ {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X ↦ koszulAux Y X Z x) x where
  smul {f X} hf hX := by
    simp only [koszulAux, smul_eq_mul]
    rw [dInner_smul_left, dInner_smul_mid hf hX hZ, dInner_smul_mid hf hX hY,
      inner_bracket_smul_left hf hX, inner_bracket_smul_left hf hX, Pi.smul_apply',
      real_inner_smul_right]
    ring
  add {X X'} hX hX' := by
    simp only [koszulAux]
    rw [dInner_add_left, dInner_add_mid hX hX' hZ, dInner_add_mid hX hX' hY,
      inner_bracket_add_left hX hX', inner_bracket_add_left hX hX', Pi.add_apply, inner_add_right]
    ring

/-- **The Koszul expression is tensorial in the test section `Z`.** -/
theorem koszulAux_tensorial₂ {Y X : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) :
    TensorialAt I E (fun Z ↦ koszulAux Y X Z x) x where
  smul {f Z} hf hZ := by
    simp only [koszulAux, smul_eq_mul]
    rw [dInner_smul_right hf hY hZ, dInner_smul_right hf hX hZ, dInner_smul_left, Pi.smul_apply',
      real_inner_smul_right, inner_bracket_smul_right hf hZ, inner_bracket_smul_right hf hZ,
      real_inner_comm (Y x) (Z x), real_inner_comm (X x) (Z x)]
    ring
  add {Z Z'} hZ hZ' := by
    simp only [koszulAux]
    rw [dInner_add_right hY hZ hZ', dInner_add_right hX hZ hZ', dInner_add_left, Pi.add_apply,
      inner_add_right, inner_bracket_add_right hZ hZ', inner_bracket_add_right hZ hZ']
    ring

/-- Additivity of the Koszul expression in `Y`. -/
theorem koszulAux_add_Y {Y Y' X Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hX : MDiffAt (T% X) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulAux (Y + Y') X Z x = koszulAux Y X Z x + koszulAux Y' X Z x := by
  simp only [koszulAux]
  rw [dInner_add_mid hY hY' hZ, dInner_add_left, dInner_add_right hX hY hY',
    inner_bracket_add_right hY hY', Pi.add_apply, inner_add_right, inner_bracket_add_left hY hY']
  ring

/-- **The Leibniz rule of the Koszul expression in `Y`.** -/
theorem koszulAux_smul_Y {f : M → ℝ} {Y X Z : Π x : M, TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulAux (f • Y) X Z x
      = f x * koszulAux Y X Z x + extDerivFun (I := I) f x (X x) * ⟪Y x, Z x⟫ := by
  simp only [koszulAux]
  rw [dInner_smul_mid hf hY hZ, dInner_smul_left, dInner_smul_right hf hX hY,
    inner_bracket_smul_right hf hY, Pi.smul_apply', real_inner_smul_right,
    inner_bracket_smul_left hf hY, real_inner_comm (X x) (Y x)]
  ring

section Connection

variable [FiniteDimensional ℝ E]

/-- The Koszul form of `Y` at `x`, a bilinear form on the tangent space: `(v, w) ↦ ⟨∇ᵥY, w⟩`. -/
noncomputable def koszulForm (Y : Π x : M, TangentSpace I x) (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z ↦ koszulAux Y X Z x) x
    (fun _ hZ ↦ koszulAux_tensorial₁ hY hZ) (fun _ hX ↦ koszulAux_tensorial₂ hY hX)

theorem koszulForm_apply {Y X Z : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    koszulForm Y x hY (X x) (Z x) = koszulAux Y X Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hZ

/-- **The Levi-Civita connection**, as a function: `∇ᵥY(x)` is the Riesz representative of the
Koszul form where `Y` is differentiable at `x`, and `0` where it is not. -/
noncomputable def leviCivitaFun (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x := by
  classical
  exact if hY : MDiffAt (T% Y) x then riesz I x ∘L koszulForm Y x hY else 0

theorem inner_leviCivitaFun {Y X Z : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaFun Y x (X x), Z x⟫ = koszulAux Y X Z x := by
  classical
  simp only [leviCivitaFun, dif_pos hY, ContinuousLinearMap.comp_apply]
  rw [inner_riesz, koszulForm_apply hY hX hZ]

theorem inner_leviCivitaFun_extend {Y : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    ⟪leviCivitaFun Y x v, w⟫ = koszulAux Y (extend E v) (extend E w) x := by
  have h := inner_leviCivitaFun hY (mdifferentiableAt_extend (I := I) E v)
    (mdifferentiableAt_extend (I := I) E w)
  rwa [extend_apply_self, extend_apply_self] at h

/-- **THE LEVI-CIVITA CONNECTION OF A RIEMANNIAN MANIFOLD**, as a `CovariantDerivative`. -/
noncomputable def leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := leviCivitaFun
  isCovariantDerivativeOnUniv :=
    { add := by
        intro Y Y' x hY hY' _
        ext v
        apply ext_inner_right ℝ
        intro w
        rw [ContinuousLinearMap.add_apply, inner_add_left,
          inner_leviCivitaFun_extend (mdifferentiableAt_add_section hY hY'),
          inner_leviCivitaFun_extend hY, inner_leviCivitaFun_extend hY']
        exact koszulAux_add_Y hY hY' (mdifferentiableAt_extend (I := I) E v)
          (mdifferentiableAt_extend (I := I) E w)
      leibniz := by
        intro Y f x hY hf _
        ext v
        apply ext_inner_right ℝ
        intro w
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, inner_add_left, real_inner_smul_left,
          real_inner_smul_left, inner_leviCivitaFun_extend (hf.smul_section hY),
          inner_leviCivitaFun_extend hY,
          koszulAux_smul_Y hf hY (mdifferentiableAt_extend (I := I) E v)
            (mdifferentiableAt_extend (I := I) E w), extend_apply_self, extend_apply_self] }

theorem leviCivita_apply (Y : Π x : M, TangentSpace I x) (x : M) :
    leviCivita Y x = leviCivitaFun Y x := rfl

/-- **The Levi-Civita connection is torsion-free**: antisymmetrising the Koszul expression in its
first two sections gives the bracket. -/
theorem leviCivita_torsion :
    (leviCivita (I := I) (M := M)).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply ext_inner_right ℝ
  intro w
  have hZ := mdifferentiableAt_extend (I := I) E w
  have h1 := inner_leviCivitaFun hY hX hZ
  have h2 := inner_leviCivitaFun hX hY hZ
  rw [extend_apply_self] at h1 h2
  rw [inner_sub_left, leviCivita_apply, leviCivita_apply, h1, h2, koszulAux_sub_swap,
    extend_apply_self]

/-- **The Levi-Civita connection is metric-compatible**: symmetrising the Koszul expression in its
last two sections gives the derivative of the metric. -/
theorem leviCivita_compatible : IsMetricCompatible (leviCivita (I := I) (M := M)) := by
  intro X Y x hX hY v
  have hW := mdifferentiableAt_extend (I := I) E v
  have h1 := inner_leviCivitaFun hX hW hY
  have h2 := inner_leviCivitaFun hY hW hX
  rw [extend_apply_self] at h1 h2
  change extDerivFun (I := I) (fun y ↦ ⟪X y, Y y⟫) x v
    = ⟪leviCivitaFun X x v, Y x⟫ + ⟪X x, leviCivitaFun Y x v⟫
  rw [h1, ← real_inner_comm (X x) (leviCivitaFun Y x v), h2, koszulAux_add_swap]
  simp [dInner, extend_apply_self]

/-- **EXISTENCE OF THE LEVI-CIVITA CONNECTION**: every Riemannian manifold (with a `C¹` metric on
a `C²` manifold, modelled on a finite-dimensional space) carries a torsion-free metric-compatible
covariant derivative. -/
theorem exists_leviCivita :
    ∃ cov : CovariantDerivative I E (TangentSpace I : M → Type _),
      cov.torsion = 0 ∧ IsMetricCompatible cov :=
  ⟨leviCivita, leviCivita_torsion, leviCivita_compatible⟩

/-- **AND IT IS THE ONLY ONE** (`LeviCivitaUnique`): every torsion-free metric-compatible
connection is `leviCivita` on every section differentiable at the point. -/
theorem eq_leviCivita_of_torsionFree_of_compatible
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (h : cov.torsion = 0)
    (hc : IsMetricCompatible cov) {x : M} {σ : Π x : M, TangentSpace I x}
    (hσ : MDiffAt (T% σ) x) : cov σ x = leviCivita σ x :=
  eq_of_torsionFree_of_compatible cov leviCivita h leviCivita_torsion hc leviCivita_compatible hσ

end Connection

end Smooth

end Bracket

end Manifold

end Riemannian

section VectorSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

/-- **CONSISTENCY WITH `LeviCivitaFlat`**: on a Euclidean space with its constant metric, the
manifold construction is the flat connection on every section differentiable at the point. -/
theorem leviCivita_eq_flatCov {x : F} {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x) :
    leviCivita σ x = LeviCivitaFlat.flatCov σ x :=
  (eq_leviCivita_of_torsionFree_of_compatible LeviCivitaFlat.flatCov LeviCivitaFlat.flatCov_torsion
    LeviCivitaFlat.flatCov_compatible hσ).symm

end VectorSpace

end KoszulManifold
