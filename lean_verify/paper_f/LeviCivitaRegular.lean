import FrameRegular
import RicciScalar

/-!
# The Levi-Civita connection of a `C²` metric is `C¹`, and the curvature of a metric exists

`CurvatureTensor` and `RicciScalar` built the curvature endomorphism `R(v, w)`, the Ricci form and
the scalar curvature of any connection on `TM` that is `C¹` on every open set (`IsLocallyC1`), and
every fence since said that `KoszulManifold.leviCivita` was not shown to be one. `KoszulRegular`
proved that its pairings with `C²` test sections are `C¹`, and `FrameRegular` that `y ↦ ∇_Y Z(y)`
is a `C¹` section for each `C²` field `Y`. This file closes the statement: **the Levi-Civita
connection of a `C²` metric on a `C³` manifold is `C¹` on every open set**
(`isLocallyC1_leviCivita`, an instance), and so **the Riemann curvature, the Ricci curvature and
the scalar curvature of a `C²` metric exist in the estate** (`riemann`, `ricci`, `scalar`), with
`R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` on sections (`riemann_apply`).

The last leg is Mathlib's coordinate criterion for sections of the bundle `Hom(TM, TM)`
(`contMDiffAt_hom_bundle`): the section `y ↦ ∇Z(y)` is `C¹` at `x` when its coordinate matrix in
the chart at `x` is, and that matrix, applied to a basis vector `bᵢ` of the model space, is the
trivialised value of `∇_{sᵢ} Z` on the chart's local frame `sᵢ` (`inCoordinates_apply_localFrame`).
A map into `E →L[ℝ] E` is `C¹` when its values on a basis are (`contMDiffAt_clm_of_basis`, by the
expansion `A = ∑ᵢ bᵢ* ⊗ A(bᵢ)`), and the values are `C¹` by `FrameRegular`. Nothing else is
needed: the curvature of a metric is `CurvatureTensor.curvEndo` evaluated on `leviCivita`, once
the instance is in scope.

## What is proved

**`clm_eq_sum_smulRight`** — a continuous linear map out of a finite-dimensional space is the sum,
over a basis, of the coordinate functionals times the images of the basis vectors.

**`contMDiffAt_clm_of_basis`** — **a map into `E →L[ℝ] F` is `C^n` at a point as soon as its
values on a basis of `E` are.**

**`inCoordinates_apply_localFrame`** — in the chart at `x`, the coordinate matrix of a section `φ`
of `Hom(TM, TM)` has for columns the trivialised values of `φ` on the chart's local frame.

**`contMDiffAt_hom_of_localFrame`** — **a section of `Hom(TM, TM)` is `C¹` at `x` as soon as its
values on the chart's local frame are `C¹` sections of `TM`.**

**`contMDiffAt_leviCivita_hom`** — **`y ↦ ∇Z(y)` is a `C¹` section of `Hom(TM, TM)`** at every
point where `Z` is `C²`, for a `C²` metric on a `C³` manifold.

**`isLocallyC1_leviCivita`** — **THE LEVI-CIVITA CONNECTION OF A `C²` METRIC IS `IsLocallyC1`**,
as an instance; Mathlib's `ContMDiffCovariantDerivative leviCivita 1` follows by `CurvatureTensor`.

**`riemann`, `riemann_apply`, `riemann_swap`** — **THE RIEMANN CURVATURE OF A `C²` METRIC**,
`R(v, w) : T_xM → T_xM`, with `R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` for `X, Y`
differentiable and `Z` of class `C²` at the point, antisymmetric in `(v, w)`; a continuous linear
map in its third slot and bilinear in the first two, by `CurvatureTensor`.

**`ricci`, `scalar`, `scalar_eq_sum`** — **THE RICCI AND SCALAR CURVATURE OF A `C²` METRIC**,
`Ric(w, z) = tr (v ↦ R(v, w) z)` and `S = ∑ᵢ Ric(eᵢ, eᵢ)` in any orthonormal basis, by
`RicciScalar`.

## What is NOT here

**NO BIANCHI IDENTITY, NO PAIR SYMMETRY, NO SYMMETRY OF `Ric` — FOR THE CURVATURE OF A METRIC.**
That `Ric` of a metric is symmetric rests on `⟨R(v, w) z, u⟩ = ⟨R(z, u) v, w⟩`, which rests on the
first Bianchi identity `R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0` (torsion-freeness and the Jacobi
identity) and on `⟨R(v, w) z, u⟩ = −⟨R(v, w) u, z⟩` (metric compatibility); none of the three is
stated or proved for `riemann`. `AlgebraicCurvature` has the first Bianchi identity as an axiom of
`IsAlgCurv` and `pair_symm_of_bianchi` as its consequence, on an abstract tensor on `Fin n → ℝ`;
that `riemann` satisfies that axiom is exactly what is not proved. **Not attempted, no cost
claimed** (`ERRATUM 246`). ⚠ By entry 73, later the same day, the first Bianchi identity is
proved for every torsion-free locally `C¹` connection and so for `riemann`
(`CurvatureBianchi.riemann_cyclic`), with `Ric(w, z) − Ric(z, w) = −tr R(w, z)`
(`CurvatureBianchi.ricci_sub_swap`); the skew-symmetry, the pair symmetry and the symmetry of
`Ric` are exactly as unproved as the paragraph says. ⚠ And by entry 74 they are not:
`CurvatureSkew.riemann_inner_skew`, `CurvatureSkew.riemann_inner_pair_symm` and
`CurvatureSkew.ricci_metric_symm`.

**NO SECTIONAL CURVATURE, NO EINSTEIN TENSOR, NO LOCAL FORMULA — FOR `riemann`**, and no bridge to
the algebraic vocabulary: `AlgebraicCurvature.einstein` and the sectional curvature of the Lovelock
files are stated on components of an abstract algebraic tensor, and `KoszulVectorSpace.chris` is
the Christoffel form of a metric on the model space, not of a metric on a manifold; relating
`riemann` to any of them is a modelling decision that belongs to the author.

**NO EXAMPLE, NOT EVEN THE FLAT ONE.** That the curvature of a Euclidean space vanishes —
`riemann` for the constant metric on `F`, where the connection is the ordinary derivative
(`KoszulManifold.leviCivita_eq_flatCov`) and `R` is an antisymmetrised second derivative — is not
proved. ⚠ By entry 75, later the same day, it is: `FlatCurvature.riemann_flat`, with
`FlatCurvature.ricci_flat` and `FlatCurvature.scalar_flat`, exactly by that antisymmetrised
second derivative (`FlatCurvature.curvAux_flatCov`).

**ONLY `C¹`.** The connection is shown `C¹`, which is what one derivative of it costs and what
curvature needs; the class of the connection of a `C^{k+1}` metric for `k ≥ 2`, and with it any
regularity of `riemann` as the point moves, is not stated. ⚠ By entry 78 the first half is:
`LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita` is Mathlib's
`ContMDiffCovariantDerivativeOn E k` for the Levi-Civita connection of a `C^(k+1)` metric on a
`C^(k+2)` manifold, of which this file's `isLocallyC1_leviCivita` is the case `k = 1`. **The
regularity of `riemann` is exactly as unstated as the sentence says.** ⚠ By entry 81 it is stated:
`RicciOrder.contMDiffAt_riemann` is `y ↦ R(X y, W y)(Z y)` as a `C^k` section for `C^(k+2)` fields
and a `C^(k+2)` metric, and `RicciOrder.contMDiffAt_ricci'` is `ricci` as a `C^k` function.
**`scalar` is still not a function of the point.** ⚠ By entry 82 it is:
`ScalarOrder.contMDiffAt_scalar'` is `scalar` as a `C^k` function of the point, with no hypothesis
beyond the metric and the manifold.

**`W5`'S RUNG 4 IS WHERE IT WAS.** The heat-kernel expansion of `Tr f(D/Λ)` and the identification
of `a₂` as a curvature integral are untouched: the curvature that `a₂` integrates now exists, and
the expansion that produces `a₂` does not. **No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `clm_eq_sum_smulRight` and
`contMDiffAt_clm_of_basis` take `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`,
`[FiniteDimensional ℝ E]`, a normed space `F`, a `Fintype ι` (the first) or `Finite ι` (the
second), and a `ChartedSpace H M` with model `I` for the second; `inCoordinates_apply_localFrame`
and `contMDiffAt_hom_of_localFrame` take `[IsManifold I 2 M]` (the tangent bundle as a `C¹`
bundle, for `contMDiffAt_hom_bundle`) and the latter `[FiniteDimensional ℝ E]`, no metric;
everything from `contMDiffAt_leviCivita_hom` on takes what
`FrameRegular.contMDiffAt_leviCivita_apply` takes — `[IsManifold I 3 M]`, `[CompleteSpace E]`,
`[FiniteDimensional ℝ E]`, `[RiemannianBundle (fun x ↦ TangentSpace I x)]` and
`[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]`, a `C²` metric.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace LeviCivitaRegular

open Bundle Manifold VectorField FiberBundle Set KoszulManifold KoszulRegular FrameRegular
open scoped Bundle ContDiff Topology

section CLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} (b : Module.Basis ι ℝ E)

/-- A continuous linear map out of a finite-dimensional space is the sum, over a basis, of the
coordinate functionals times the images of the basis vectors. -/
theorem clm_eq_sum_smulRight [Fintype ι] (A : E →L[ℝ] F) :
    A = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (A (b i)) := by
  ext v
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into `E →L[ℝ] F` is `C^n` at a point as soon as its values on a basis of `E` are. -/
theorem contMDiffAt_clm_of_basis [Finite ι] {n : WithTop ℕ∞}
    {Φ : M → E →L[ℝ] F} {x : M} (h : ∀ i, ContMDiffAt I 𝓘(ℝ, F) n (fun y ↦ Φ y (b i)) x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) n Φ x := by
  cases nonempty_fintype ι
  have hΦ : Φ = fun y ↦
      ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (Φ y (b i)) :=
    funext fun y ↦ clm_eq_sum_smulRight b (Φ y)
  rw [hΦ]
  exact ContMDiffAt.sum fun i _ ↦
    (ContinuousLinearMap.smulRightL ℝ E F
      (LinearMap.toContinuousLinearMap (b.coord i))).contMDiffAt.comp x (h i)

end CLM

section Hom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {ι : Type*}

/-- In the chart at `x`, the coordinate matrix of a section `φ` of `Hom(TM, TM)` has for columns
the trivialised values of `φ` on the chart's local frame. -/
theorem inCoordinates_apply_localFrame (φ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    {x y : M} (hy : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (b : Module.Basis ι ℝ E) (i : ι) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x y x y (φ y) (b i) =
      (trivializationAt E (TangentSpace I : M → Type _) x
        ⟨y, φ y ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y)⟩).2 := by
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply, Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hy,
    Trivialization.localFrame_apply_of_mem_baseSet _ b hy,
    Trivialization.basisAt, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply]

variable [FiniteDimensional ℝ E]

/-- **A section of `Hom(TM, TM)` is `C¹` at `x` as soon as its values on the chart's local frame
are `C¹` sections of `TM`.** -/
theorem contMDiffAt_hom_of_localFrame [Finite ι]
    (φ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) {x : M} (b : Module.Basis ι ℝ E)
    (h : ∀ i, CMDiffAt 1 (T% (fun y ↦
      φ y ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (φ y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, contMDiffAt_clm_of_basis b fun i ↦ ?_⟩
  refine ((contMDiffAt_section x).1 (h i)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  exact inCoordinates_apply_localFrame φ hy b i

end Hom

section LeviCivita

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- **THE LEVI-CIVITA CONNECTION OF A `C²` METRIC IS A `C¹` SECTION OF `Hom(TM, TM)`** at every
point where the section it is applied to is `C²`. -/
theorem contMDiffAt_leviCivita_hom {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (leviCivita Z y)) x := by
  refine contMDiffAt_hom_of_localFrame (leviCivita Z) (Module.finBasis ℝ E) fun i ↦ ?_
  exact contMDiffAt_leviCivita_apply (contMDiffAt_localFrame_of_mem 2 _ _ i
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)) hZ

/-- **`IsLocallyC1 leviCivita`**: on every open set, the Levi-Civita connection of a `C²` metric
is `C¹` in Mathlib's sense, so the curvature machinery of `CurvatureTensor` and `RicciScalar`
applies to it. -/
instance isLocallyC1_leviCivita :
    CurvatureTensor.IsLocallyC1
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) where
  on_open u hu := ⟨fun {Z} hZ x hx ↦ by
    have hZx : CMDiffAt 2 (T% Z) x := by simpa using hZ.contMDiffAt (hu.mem_nhds hx)
    exact (contMDiffAt_leviCivita_hom hZx).contMDiffWithinAt⟩

section Curvature

variable (I) in
/-- **THE RIEMANN CURVATURE OF A `C²` METRIC**: `R(v, w) : T_xM → T_xM`, the curvature
endomorphism of the Levi-Civita connection. -/
noncomputable abbrev riemann (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  CurvatureTensor.curvEndo
    (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) x v w

/-- **`R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`** for the Levi-Civita connection, `X, Y`
differentiable and `Z` of class `C²` at `x`. -/
theorem riemann_apply {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    riemann I x (X x) (Y x) (Z x) =
      leviCivita (fun y ↦ leviCivita Z y (Y y)) x (X x)
        - leviCivita (fun y ↦ leviCivita Z y (X y)) x (Y x)
        - leviCivita Z x (mlieBracket I X Y x) :=
  CurvatureTensor.curvEndo_apply leviCivita hX hY hZ

/-- The Riemann curvature is antisymmetric in its two directions. -/
theorem riemann_swap (x : M) (v w : TangentSpace I x) : riemann I x v w = - riemann I x w v :=
  CurvatureTensor.curvEndo_swap leviCivita x v w

variable (I) in
/-- **THE RICCI CURVATURE OF A `C²` METRIC**, `Ric(w, z) = tr (v ↦ R(v, w) z)`. -/
noncomputable abbrev ricci (x : M) (w z : TangentSpace I x) : ℝ :=
  RicciScalar.ricci (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) x w z

variable (I) in
/-- **THE SCALAR CURVATURE OF A `C²` METRIC**, the trace of the Ricci form. -/
noncomputable abbrev scalar (x : M) : ℝ :=
  RicciScalar.scalar (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) x

/-- The scalar curvature of a metric, in any orthonormal basis of the tangent space. -/
theorem scalar_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    scalar I x = ∑ i, ricci I x (b i) (b i) :=
  RicciScalar.scalar_eq_sum _ x b

end Curvature

end LeviCivita

end LeviCivitaRegular
