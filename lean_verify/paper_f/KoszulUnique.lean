import KoszulVectorSpace

/-!
# The Koszul connection is the Levi-Civita connection: uniqueness for a variable metric

`KoszulVectorSpace` built, for a metric `m` on a finite-dimensional real vector space that varies
with the point, a torsion-free `m`-compatible connection `m.cov`, and said in its fence that it had
not shown it to be the only one: `LeviCivitaUnique`'s uniqueness is stated for
`IsMetricCompatible`, the constant metric of a `RiemannianBundle` instance, and reaches `m` only in
the constant case. This file proves uniqueness for `m` itself: **two torsion-free `m`-compatible
connections have zero difference tensor, they agree on every section differentiable at the point,
and so every such connection is `m.cov` there.** With `KoszulVectorSpace.exists_leviCivita` this
is existence and uniqueness of the Levi-Civita connection of a variable metric on the model space.

The proof is `LeviCivitaUnique`'s braid with `g x` in place of the inner product — a tensor
symmetric in its two slots (torsion-free, `difference_symm`, reused as it stands) and skew in the
metric (compatibility) vanishes — and it is shorter in one respect: on a vector space the sections
with a prescribed value at a point are the constant sections, so `FiberBundle.extend` is not
needed and the skew identity is read off `IsGCompatible` on two constants. One thing costs a lemma
of its own: the difference tensor's values live in a tangent space while `g x` is a map on `F`, and
carrying the linearity of `g x` across that definitional equality is `g_difference_left` and
`g_difference_right`, proved by `exact` where `simp` cannot see through `TangentSpace`.

## What is proved

**`constSec`, `mdiffAt_const`** — the constant section at `u`, differentiable as a section.

**`difference_const`** — on a constant section the difference tensor is the difference of the two
connections (`LeviCivitaUnique.difference_apply'`).

**`g_difference_left`, `g_difference_right`** — `g x` through that difference, in either slot.

**`difference_skew_g`** — **two `m`-compatible connections have a skew difference tensor**:
`g(D(u, v), w) + g(u, D(w, v)) = 0`, from `IsGCompatible` on the constant sections at `u` and `w`.

**`difference_eq_zero_of_gCompatible`** — **UNIQUENESS**: torsion-free and `m`-compatible force
`cov.difference cov' = 0` — `difference_symm`, `difference_skew_g`, the six-step braid closed by
`linarith`, and `injective_g` to pass from `g x (D u v) = 0` to `D u v = 0`.

**`eq_of_torsionFree_of_gCompatible`** — and so `cov σ x = cov' σ x` on every section
differentiable at `x`.

**`eq_koszul_of_torsionFree_of_gCompatible`** — **every torsion-free `m`-compatible connection is
`m.cov`** on every section differentiable at the point.

## What is NOT here

**NOT EQUALITY OF THE STRUCTURES.** As in `LeviCivitaUnique`: a `CovariantDerivative` is a
function on all sections and is constrained only where a section is differentiable, so two such
structures may differ on sections differentiable nowhere. The conclusions are `difference = 0` and
agreement on sections differentiable at the point, and nothing stronger is claimed.

**A MANIFOLD.** The constant sections are what a vector space has and a manifold does not; there
the skew identity needs `FiberBundle.extend`, as `LeviCivitaUnique` already does, and existence
needs the Koszul construction in charts. `WALLS` §W5.1 §3's object — existence on a Riemannian
manifold — stays where it was; what the model space now has is existence and uniqueness together.
**Not attempted, no cost claimed** (`ERRATUM 246`).

**NO GENERALISATION TO A NONDEGENERATE FORM.** The only property of `g` used beyond symmetry is
`injective_g`, so the same proof would run for a pseudo-Riemannian `VarMetric`; `VarMetric` asks
for positivity and the generalisation is not made.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `constSec` and `mdiffAt_const` take
`[NormedAddCommGroup F]` and `[NormedSpace ℝ F]`; the `Difference` section adds
`[FiniteDimensional ℝ F]`, Mathlib's hypothesis for `difference`; the `Unique` section adds
`[CompleteSpace F]`, Mathlib's hypothesis for `torsion`, redundant given finite dimension over `ℝ`
and kept because Mathlib asks for it separately. **No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace KoszulUnique

open Bundle Manifold VectorField FiberBundle LeviCivitaUnique LeviCivitaFlat KoszulVectorSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The constant section at `u`, typed as a section of the tangent bundle. -/
abbrev constSec (u : F) : Π x : F, TangentSpace 𝓘(ℝ, F) x := fun _ ↦ u

/-- A constant section is differentiable as a section. -/
theorem mdiffAt_const (u x : F) :
    MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
      (fun y ↦ TotalSpace.mk' F y (constSec u y)) x :=
  mdiffAt_section_iff.mpr (differentiableAt_const u)

variable (m : VarMetric F)
variable (cov cov' : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _))

section Difference

variable [FiniteDimensional ℝ F]

/-- The difference tensor on a constant section is the difference of the connections on it. -/
theorem difference_const (x u v : F) :
    cov.difference cov' x u v = cov (constSec u) x v - cov' (constSec u) x v :=
  congrArg (fun L ↦ L v) (difference_apply' cov cov' (mdiffAt_const u x))

/-- The metric on the difference tensor, first slot: the subtraction lives in a tangent space,
and the linearity of `g x` is applied through the definitional equality with `F`. -/
theorem g_difference_left (x u v w : F) :
    m.g x (cov.difference cov' x u v) w
      = m.g x (cov (constSec u) x v) w - m.g x (cov' (constSec u) x v) w := by
  have d := congrArg (fun L ↦ L w)
    (map_sub (m.g x) (cov (constSec u) x v) (cov' (constSec u) x v))
  rw [difference_const]
  exact d

/-- The metric on the difference tensor, second slot. -/
theorem g_difference_right (x u v w : F) :
    m.g x u (cov.difference cov' x w v)
      = m.g x u (cov (constSec w) x v) - m.g x u (cov' (constSec w) x v) := by
  have d := map_sub (m.g x u) (cov (constSec w) x v) (cov' (constSec w) x v)
  rw [difference_const]
  exact d

/-- **Two `m`-compatible connections have a skew difference tensor**, on constant sections: no
extension of tangent vectors is needed on a vector space. -/
theorem difference_skew_g (hc : m.IsGCompatible cov) (hc' : m.IsGCompatible cov') (x u v w : F) :
    m.g x (cov.difference cov' x u v) w + m.g x u (cov.difference cov' x w v) = 0 := by
  have e1 := hc (constSec u) (constSec w) x (differentiableAt_const u) (differentiableAt_const w) v
  have e2 := hc' (constSec u) (constSec w) x (differentiableAt_const u) (differentiableAt_const w) v
  dsimp only [constSec] at e1 e2
  rw [g_difference_left, g_difference_right]
  linarith

end Difference

section Unique

variable [FiniteDimensional ℝ F] [CompleteSpace F]

/-- **UNIQUENESS OF THE LEVI-CIVITA CONNECTION FOR A VARIABLE METRIC**: two torsion-free
`m`-compatible connections have zero difference tensor. -/
theorem difference_eq_zero_of_gCompatible (h : cov.torsion = 0) (h' : cov'.torsion = 0)
    (hc : m.IsGCompatible cov) (hc' : m.IsGCompatible cov') : cov.difference cov' = 0 := by
  funext x
  ext u v
  apply m.injective_g x
  change m.g x (cov.difference cov' x u v) = m.g x (0 : F)
  rw [map_zero]
  ext w
  simp only [ContinuousLinearMap.zero_apply]
  have sym : ∀ a b, cov.difference cov' x a b = cov.difference cov' x b a :=
    fun a b ↦ difference_symm cov cov' h h' x a b
  have sk := difference_skew_g m cov cov' hc hc'
  have gs : ∀ a b c, m.g x a (cov.difference cov' x c b) = m.g x (cov.difference cov' x c b) a :=
    fun a b c ↦ m.symm x a _
  have k1 := sk x u v w
  have k2 := sk x w u v
  have k3 := sk x v w u
  rw [gs] at k1 k2 k3
  rw [sym w v] at k1
  rw [sym v u] at k2
  rw [sym u w] at k3
  linarith

/-- **And so they agree on every section differentiable at the point.** -/
theorem eq_of_torsionFree_of_gCompatible (h : cov.torsion = 0) (h' : cov'.torsion = 0)
    (hc : m.IsGCompatible cov) (hc' : m.IsGCompatible cov') {x : F}
    {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x) :
    cov σ x = cov' σ x := by
  have e := difference_apply' cov cov' hσ
  rw [difference_eq_zero_of_gCompatible m cov cov' h h' hc hc'] at e
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply] at e
  exact sub_eq_zero.mp e.symm

/-- **THE KOSZUL CONNECTION IS THE LEVI-CIVITA CONNECTION OF `m`**: every torsion-free
`m`-compatible connection is `m.cov` on every section differentiable at the point. -/
theorem eq_koszul_of_torsionFree_of_gCompatible (h : cov.torsion = 0) (hc : m.IsGCompatible cov)
    {x : F} {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x) :
    cov σ x = m.cov σ x :=
  eq_of_torsionFree_of_gCompatible m cov m.cov h m.cov_torsion hc m.cov_gCompatible hσ

end Unique

end KoszulUnique
