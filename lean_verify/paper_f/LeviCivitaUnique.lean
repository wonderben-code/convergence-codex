import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Metric compatibility named, and the Levi-Civita connection is unique

`WALLS` §W5.1 §3 says what stands between this estate and curvature: *the Levi-Civita connection
is missing, and it is the single object between a library that has metrics and a library that
has curvature*. It then inventories what the pinned Mathlib already holds — `CovariantDerivative`,
`addOneForm`, `difference`, `torsion` with its antisymmetry — and names the two absences exactly:
**metric compatibility has no name in the library**, and **the existence-and-uniqueness theorem
for the torsion-free compatible connection is absent**.

This file supplies the name and the uniqueness half. Both cost only algebra, because the library
has done the analysis: two covariant derivatives differ by a tensor
(`CovariantDerivative.difference`), torsion-freeness is a symmetry of that tensor, compatibility
is a skew-symmetry of it, and a tensor that is symmetric in one pair of slots and skew in another
is zero.

## What is proved

**`IsMetricCompatible`** — a covariant derivative `∇` on the tangent bundle of a manifold whose
tangent spaces carry inner products (`RiemannianBundle`) is metric-compatible when, for every
point `x`, every two sections `X, Y` differentiable at `x`, and every direction `v`,
`d⟨X, Y⟩(v) = ⟨∇ᵥX, Y⟩ + ⟨X, ∇ᵥY⟩` at `x`, the left side being `mfderiv`.

**`difference_apply'`** — the bundled difference tensor, evaluated on a section differentiable at
the point, is the difference of the two derivatives there.

**`difference_symm`** — two **torsion-free** connections differ by a tensor symmetric in its two
slots (`Mathlib`'s `torsion_eq_zero_iff`, on the extension of two tangent vectors to sections).

**`difference_skew`** — two **metric-compatible** connections differ by a tensor skew in the
metric: `⟨D(u, w), v⟩ + ⟨u, D(v, w)⟩ = 0`.

**`difference_eq_zero`** — **the Levi-Civita connection is unique**: two torsion-free,
metric-compatible connections have zero difference tensor. The proof is the six-step braid
`B(w;u,v) = B(u;w,v) = −B(u;v,w) = −B(v;u,w) = B(v;w,u) = B(w;v,u) = −B(w;u,v)`, closed by
`linarith` once the six identities are in `ℝ`.

**`eq_of_torsionFree_of_compatible`** — and so they agree on every section differentiable at the
point.

## What is NOT here

**EXISTENCE.** No connection is shown to be torsion-free and metric-compatible — not on a
Riemannian manifold, and not even on a vector space with its constant metric. The Koszul
construction needs the derivative of the metric along vector fields and the Lie bracket's
Leibniz rules, and it is the analysis this file did not need; it is the remaining object of
`WALLS` §W5.1 §3, and it stays that. **Not attempted, no cost claimed** (`ERRATUM 246`).

⚠ **THE FLAT CASE IS DONE THE SAME DAY, AND THE PARAGRAPH ABOVE IS KEPT AS WRITTEN**
(`ERRATUM 94`). `LeviCivitaFlat.exists_leviCivita`: on a finite-dimensional complete real inner
product space with its constant metric, the ordinary derivative is torsion-free and
metric-compatible, so `IsMetricCompatible` is inhabited, and
`eq_fderiv_of_torsionFree_of_compatible` makes it the only such connection there through this
file's uniqueness. **The manifold case — the Koszul construction — is exactly as untouched as
the paragraph says.**

**NOT EQUALITY OF THE CONNECTIONS AS STRUCTURES.** A `CovariantDerivative` is a function on all
sections and is constrained only where a section is differentiable; two such structures may
differ on sections differentiable nowhere. What is proved is the vanishing of the difference
tensor and agreement at every point of differentiability, which is everything the geometry uses.

**NO SMOOTHNESS OF THE METRIC IS ASSUMED OR USED.** `IsMetricCompatible` quantifies `mfderiv` over
sections differentiable at a point; it does not ask the inner product to be differentiable, and
`IsContMDiffRiemannianBundle` is not among the hypotheses. That is what makes the definition
usable here and is also why nothing here says the definition is inhabited.

**NOTHING ABOUT CURVATURE.** No curvature is defined; §W5.1 §3's *single object* is existence, and
`W5`'s rung 4 — the heat-kernel expansion — is untouched. **No wall moves. No published tag
moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[IsManifold I 2 M]`,
`[FiniteDimensional ℝ E]` and `[CompleteSpace E]` are Mathlib's own hypotheses for `difference` and
`torsion`; `[RiemannianBundle (fun x : M ↦ TangentSpace I x)]` supplies the inner products; nothing
else — no metric space structure on `M`, no `IsRiemannianManifold`, no smoothness of the metric.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace LeviCivitaUnique

open Bundle Manifold VectorField FiberBundle
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section Compatible

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **Metric compatibility** of a covariant derivative on the tangent bundle: the Leibniz rule
for the metric, at every point, for every pair of sections differentiable there, in every
direction. -/
def IsMetricCompatible (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {X Y : Π x : M, TangentSpace I x} {x : M}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
    ∀ v : TangentSpace I x,
      mfderiv I 𝓘(ℝ) (fun y ↦ ⟪X y, Y y⟫) x v = ⟪cov X x v, Y x⟫ + ⟪X x, cov Y x v⟫

end Compatible

variable (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The bundled difference, evaluated on a section differentiable at the point. -/
theorem difference_apply' {x : M} {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x) :
    cov.difference cov' x (σ x) = cov σ x - cov' σ x :=
  IsCovariantDerivativeOn.difference_apply _ _ (Set.mem_univ x) hσ

section TorsionFree

variable [CompleteSpace E]

/-- **Two torsion-free connections differ by a symmetric tensor.** -/
theorem difference_symm (h : cov.torsion = 0) (h' : cov'.torsion = 0) (x : M)
    (u v : TangentSpace I x) :
    cov.difference cov' x u v = cov.difference cov' x v u := by
  have hu := mdifferentiableAt_extend (I := I) E u
  have hv := mdifferentiableAt_extend (I := I) E v
  have e1 := (cov.torsion_eq_zero_iff.mp h) hu hv
  have e2 := (cov'.torsion_eq_zero_iff.mp h') hu hv
  have hd1 := difference_apply' cov cov' hu
  have hd2 := difference_apply' cov cov' hv
  simp only [extend_apply_self] at hd1 hd2 e1 e2
  rw [hd1, hd2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  exact (sub_eq_sub_iff_sub_eq_sub.mp (e1.trans e2.symm)).symm

end TorsionFree

section Skew

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **Two metric-compatible connections differ by a tensor that is skew in the metric.** -/
theorem difference_skew (hc : IsMetricCompatible cov) (hc' : IsMetricCompatible cov') (x : M)
    (u v w : TangentSpace I x) :
    ⟪cov.difference cov' x u w, v⟫ + ⟪u, cov.difference cov' x v w⟫ = 0 := by
  have hu := mdifferentiableAt_extend (I := I) E u
  have hv := mdifferentiableAt_extend (I := I) E v
  have e1 := hc hu hv w
  have e2 := hc' hu hv w
  have hd1 := difference_apply' cov cov' hu
  have hd2 := difference_apply' cov cov' hv
  simp only [extend_apply_self] at hd1 hd2 e1 e2
  rw [hd1, hd2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, inner_sub_left,
    inner_sub_right]
  -- `e1` and `e2` are equations in `TangentSpace 𝓘(ℝ) _`, which is `ℝ` by definition and not by
  -- syntax; restate their consequence in `ℝ` so linear arithmetic can see it.
  have key : (⟪(cov (extend E u) x) w, v⟫ + ⟪u, (cov (extend E v) x) w⟫ : ℝ) =
      ⟪(cov' (extend E u) x) w, v⟫ + ⟪u, (cov' (extend E v) x) w⟫ := e1.symm.trans e2
  linear_combination key

end Skew

section Unique

variable [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **UNIQUENESS OF THE LEVI-CIVITA CONNECTION**: two torsion-free, metric-compatible covariant
derivatives on the tangent bundle have zero difference tensor. -/
theorem difference_eq_zero (h : cov.torsion = 0) (h' : cov'.torsion = 0)
    (hc : IsMetricCompatible cov) (hc' : IsMetricCompatible cov') :
    cov.difference cov' = 0 := by
  funext x
  ext u w
  refine ext_inner_right ℝ fun v ↦ ?_
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_left]
  set D := cov.difference cov' x with hD
  have S : ∀ a b : TangentSpace I x, D a b = D b a := difference_symm cov cov' h h' x
  have K : ∀ a b c : TangentSpace I x, ⟪D a c, b⟫ + ⟪a, D b c⟫ = 0 :=
    difference_skew cov cov' hc hc' x
  have s1 : ⟪D u w, v⟫ = ⟪D w u, v⟫ := by rw [S u w]
  have s2 : ⟪D v u, w⟫ = ⟪D u v, w⟫ := by rw [S v u]
  have s3 : ⟪D w v, u⟫ = ⟪D v w, u⟫ := by rw [S w v]
  have k1 : ⟪D w u, v⟫ + ⟪D v u, w⟫ = 0 := by
    have := K w v u; rwa [real_inner_comm (D v u) w] at this
  have k2 : ⟪D u v, w⟫ + ⟪D w v, u⟫ = 0 := by
    have := K u w v; rwa [real_inner_comm (D w v) u] at this
  have k3 : ⟪D v w, u⟫ + ⟪D u w, v⟫ = 0 := by
    have := K v u w; rwa [real_inner_comm (D u w) v] at this
  linarith

/-- **AND SO THEY AGREE ON EVERY SECTION DIFFERENTIABLE AT THE POINT.** -/
theorem eq_of_torsionFree_of_compatible (h : cov.torsion = 0) (h' : cov'.torsion = 0)
    (hc : IsMetricCompatible cov) (hc' : IsMetricCompatible cov') {x : M}
    {σ : Π x : M, TangentSpace I x} (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  have hd := difference_apply' cov cov' hσ
  rw [difference_eq_zero cov cov' h h' hc hc'] at hd
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply] at hd
  exact (sub_eq_zero.mp hd.symm)

end Unique

end LeviCivitaUnique
