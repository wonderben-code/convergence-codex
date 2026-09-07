import LeviCivitaFlat

/-!
# The Levi-Civita connection of a variable metric on a vector space: the Koszul construction

`LeviCivitaFlat` said in its fence: *not even a non-constant metric on `F`*. This file does the
non-constant metric on `F`. It is the Koszul construction in the case where there are coordinates
everywhere: for a metric `g` on a finite-dimensional real vector space `F` — at each point a
symmetric positive definite bilinear form, differentiable in the point (`VarMetric`) — **the flat
connection plus the Christoffel one-form is a covariant derivative, it is torsion-free, and it
satisfies the Leibniz rule for `g`.** So a torsion-free `g`-compatible connection exists for every
such `g` (`exists_leviCivita`), which is what `LeviCivitaFlat` could not say.

The construction is what a textbook does after choosing coordinates, without the coordinates.
`A := Dg` is the derivative of the metric, a trilinear form symmetric in its last two slots
(`A_symm`). The Koszul functional is
`kos x u v : w ↦ ½ ((∂ᵤg)(v, w) + (∂ᵥg)(u, w) − (∂_w g)(u, v))`, symmetric and bilinear in
`u, v`. The Christoffel vector `chris x u v` is the vector representing it through the metric's own
isomorphism `F ≃ F*` (`toDualEquiv`, and this is where finite dimension enters: injectivity is
positivity, surjectivity is a rank count). Then `cov := flatCov.addOneForm chrisForm`, so the
connection axioms are Mathlib's (`CovariantDerivative.addOneForm`) and are not re-proved here.
Torsion-freeness is `chris_symm`; compatibility is the product rule `fderiv_g_XY`, whose third
term `A x v (X x) (Y x)` is exactly what the two Koszul terms produce.

## What is proved

**`VarMetric F`** — the structure: `g : F → F →L[ℝ] F →L[ℝ] ℝ`, `symm`, `pos`,
`diff : Differentiable ℝ g`. **`injective_g`** — `g x` is injective, from `pos` alone.
**`toDualEquiv`, `toDualEquiv_apply`, `g_symm_apply`** — `g x : F ≃L[ℝ] F*` (finite dimension).

**`A`, `fderiv_g_apply`, `A_symm`** — the derivative of the metric and its symmetry.

**`kos`, `kos_apply`, `kos_symm`, `kos_add_left`, `kos_smul_left`** — the Koszul functional.

**`chris`, `g_chris`, `chris_symm`, `chris_add_left`, `chris_smul_left`, `chris_add_right`,
`chris_smul_right`** — the Christoffel map, defined by `g x (chris x u v) w = kos x u v w`,
symmetric and bilinear. **`chrisCLM`, `chrisForm`** and their `_apply`, `_add`, `_smul` — the
same map bundled as a one-form with values in endomorphisms, the shape `addOneForm` takes.

**`cov`, `cov_apply`** — **the connection**: `∇ᵥσ(x) = Dσ(x)(v) + Γₓ(v, σ(x))`.

**`IsGCompatible`** — the Leibniz rule for `g` along every direction, for sections differentiable
at the point: `LeviCivitaUnique.IsMetricCompatible` written with `g` in place of the tangent-space
inner product. **`fderiv_g_XY`** — the product rule for `g(X, Y)` with the metric's own derivative
as its third term. **`cov_gCompatible`** — **`cov` is `g`-compatible.**

**`cov_torsion`** — **`cov` is torsion-free** (`torsion_eq_zero_iff` and `chris_symm`).

**`exists_leviCivita`** — **EXISTENCE**: for every `m : VarMetric F` there is a torsion-free
`m`-compatible covariant derivative on the tangent bundle of `F`.

**`ofInner`, `ofInner_g`, `A_ofInner`, `chris_ofInner`, `cov_ofInner_apply`, `cov_ofInner`,
`isGCompatible_ofInner_iff`** — the check that the construction is the right one: the constant
metric of an inner product space is a `VarMetric` (so the structure is inhabited), its Christoffel
map is zero, **its `cov` is `flatCov`**, and for it `IsGCompatible` is exactly
`IsMetricCompatible`. So `LeviCivitaFlat.exists_leviCivita` is the constant case of this file's.

## What is NOT here

**UNIQUENESS FOR A VARIABLE METRIC.** That `cov` is the *only* torsion-free `m`-compatible
connection is not proved here; `LeviCivitaUnique.eq_of_torsionFree_of_compatible` is stated for
`IsMetricCompatible`, that is for the constant metric of a `RiemannianBundle` instance, and applies
to `m` only through `isGCompatible_ofInner_iff`, in the constant case. The variable-metric
uniqueness is the same braid with `g x` in place of the inner product and constant sections in
place of `extend`, and it is the next object, not this file's. ⚠ By 7 September, the same day, it
is `KoszulUnique`: `difference_eq_zero_of_gCompatible`, `eq_koszul_of_torsionFree_of_gCompatible`.

**A MANIFOLD.** This is the model space with global coordinates. On a Riemannian manifold the
Koszul construction needs the metric's derivative along vector fields and charts, and `WALLS`
§W5.1 §3's object — existence there — stays where it was. **Not attempted, no cost claimed**
(`ERRATUM 246`). What this file removes from that object is the formula: `cov_apply`,
`cov_gCompatible` and `cov_torsion` are its chart-local content.

**NO `RiemannianBundle` INSTANCE FOR A VARIABLE METRIC**, and so no use of Mathlib's
`IsMetricCompatible` for one. Compatibility is `IsGCompatible`, stated against `g` directly; the
two notions are shown equal only for the constant metric (`isGCompatible_ofInner_iff`).

**NO REGULARITY OF `cov`.** `diff` asks `g` to be differentiable once; the connection is built
from `Dg` and nothing is claimed about its continuity or smoothness
(`ContMDiffCovariantDerivativeOn` is not proved). **NO CURVATURE**, undefined in this estate and
in the pinned Mathlib. **No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `VarMetric`, `injective_g`, `A`,
`fderiv_g_apply`, `A_symm`, the `kos` lemmas, `IsGCompatible` and `fderiv_g_XY` take
`[NormedAddCommGroup F]` and `[NormedSpace ℝ F]`; `toDualEquiv`, `chris`, `chrisCLM`,
`chrisForm`, `cov`, `cov_apply` and `cov_gCompatible` add `[FiniteDimensional ℝ F]`;
`cov_torsion` and `exists_leviCivita` add `[CompleteSpace F]` as well, which is Mathlib's
hypothesis for `torsion` (redundant given finite dimension over `ℝ`, and kept because Mathlib asks
for it separately, as in `LeviCivitaFlat`). The `Constant` section takes `[InnerProductSpace ℝ F]`,
and `[FiniteDimensional ℝ F]` from `chris_ofInner` on. Positivity (`pos`) is used only through
`injective_g`; a nondegenerate symmetric form would do, and that generalisation is not made.

One `set_option synthInstance.maxHeartbeats 100000`, scoped to the one declaration
(`fderiv_g_apply`) whose nested continuous-linear-map instances `F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ`
exceed the default synthesis budget; no `maxHeartbeats` on any proof.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace KoszulVectorSpace

open Bundle Manifold VectorField FiberBundle LeviCivitaUnique LeviCivitaFlat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A (variable) Riemannian metric on the vector space `F`: at each point a symmetric positive
definite bilinear form, differentiable in the point. -/
structure VarMetric (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  g : F → F →L[ℝ] F →L[ℝ] ℝ
  symm : ∀ x u v, g x u v = g x v u
  pos : ∀ x v, v ≠ 0 → 0 < g x v v
  diff : Differentiable ℝ g

namespace VarMetric

variable (m : VarMetric F)

theorem injective_g (x : F) : Function.Injective (m.g x) := by
  intro u v huv
  by_contra hne
  have h : m.g x (u - v) (u - v) = 0 := by
    have h1 : m.g x u = m.g x v := huv
    simp [map_sub, h1]
  exact absurd h (ne_of_gt (m.pos x (u - v) (sub_ne_zero.mpr hne)))

theorem finrank_dual [FiniteDimensional ℝ F] :
    Module.finrank ℝ F = Module.finrank ℝ (F →L[ℝ] ℝ) := by
  rw [← (LinearMap.toContinuousLinearMap : (F →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (F →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq.symm

section Dual
variable [FiniteDimensional ℝ F]

/-- The metric at `x` as a continuous linear equivalence `F ≃ F*` (finite dimension). -/
noncomputable def toDualEquiv (x : F) : F ≃L[ℝ] (F →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (m.g x : F →ₗ[ℝ] (F →L[ℝ] ℝ))
    ⟨m.injective_g x,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_dual (F := F))).mp
        (m.injective_g x)⟩).toContinuousLinearEquiv

theorem toDualEquiv_apply (x u : F) : m.toDualEquiv x u = m.g x u := rfl

theorem g_symm_apply (x : F) (φ : F →L[ℝ] ℝ) : m.g x ((m.toDualEquiv x).symm φ) = φ := by
  rw [← toDualEquiv_apply]
  exact (m.toDualEquiv x).apply_symm_apply φ

end Dual

/-- `A := Dg(x)`, the derivative of the metric at `x`: `A v u w = (∂ᵥ g)(u, w)`. -/
noncomputable abbrev A (x : F) : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ := fderiv ℝ m.g x

set_option synthInstance.maxHeartbeats 100000 in
-- the nested `F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ` instances exceed the default synthesis budget
/-- The derivative of the scalar function `y ↦ g y u w` is the derivative of `g` applied. -/
theorem fderiv_g_apply (x u w v : F) :
    fderiv ℝ (fun y ↦ m.g y u w) x v = m.A x v u w := by
  have h1 := (m.diff x).hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have h2 := h1.clm_apply (hasFDerivAt_const w x)
  rw [h2.fderiv]
  simp

/-- The last two slots of `A` are symmetric, because `g` is. -/
theorem A_symm (x v u w : F) : m.A x v u w = m.A x v w u := by
  rw [← fderiv_g_apply, ← fderiv_g_apply]
  congr 2
  funext y
  exact m.symm y u w

/-- The Koszul functional `w ↦ ½ ((∂ᵤg)(v, w) + (∂ᵥg)(u, w) − (∂_w g)(u, v))`. -/
noncomputable def kos (x u v : F) : F →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (m.A x u v + m.A x v u - ((m.A x).flip u).flip v)

theorem kos_apply (x u v w : F) :
    m.kos x u v w = (1 / 2 : ℝ) * (m.A x u v w + m.A x v u w - m.A x w u v) := by
  simp [kos]

theorem kos_symm (x u v : F) : m.kos x u v = m.kos x v u := by
  ext w
  rw [kos_apply, kos_apply, m.A_symm x w u v]
  ring

theorem kos_add_left (x u₁ u₂ v : F) : m.kos x (u₁ + u₂) v = m.kos x u₁ v + m.kos x u₂ v := by
  ext w
  simp only [kos_apply, map_add, ContinuousLinearMap.add_apply]
  ring

theorem kos_smul_left (x : F) (c : ℝ) (u v : F) : m.kos x (c • u) v = c • m.kos x u v := by
  ext w
  simp only [kos_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

section Chris
variable [FiniteDimensional ℝ F]

/-- The Christoffel map: `Γ(u, v)` is the vector representing the Koszul functional. -/
noncomputable def chris (x u v : F) : F := (m.toDualEquiv x).symm (m.kos x u v)

theorem g_chris (x u v w : F) : m.g x (m.chris x u v) w = m.kos x u v w := by
  rw [chris, g_symm_apply]

theorem chris_symm (x u v : F) : m.chris x u v = m.chris x v u := by
  rw [chris, chris, kos_symm]

theorem chris_add_left (x u₁ u₂ v : F) :
    m.chris x (u₁ + u₂) v = m.chris x u₁ v + m.chris x u₂ v := by
  rw [chris, chris, chris, kos_add_left, map_add]

theorem chris_smul_left (x : F) (c : ℝ) (u v : F) : m.chris x (c • u) v = c • m.chris x u v := by
  rw [chris, chris, kos_smul_left, map_smul]

theorem chris_add_right (x u v₁ v₂ : F) :
    m.chris x u (v₁ + v₂) = m.chris x u v₁ + m.chris x u v₂ := by
  rw [m.chris_symm x u, chris_add_left, m.chris_symm x v₁ u, m.chris_symm x v₂ u]

theorem chris_smul_right (x : F) (c : ℝ) (u v : F) : m.chris x u (c • v) = c • m.chris x u v := by
  rw [m.chris_symm x u, chris_smul_left, m.chris_symm x v u]

/-- `Γ(·, s)` as a continuous linear map. -/
noncomputable def chrisCLM (x s : F) : F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ m.chris x v s
      map_add' := fun u₁ u₂ ↦ m.chris_add_left x u₁ u₂ s
      map_smul' := fun c u ↦ m.chris_smul_left x c u s }

theorem chrisCLM_apply (x s v : F) : m.chrisCLM x s v = m.chris x v s := rfl

theorem chrisCLM_add (x s t : F) : m.chrisCLM x (s + t) = m.chrisCLM x s + m.chrisCLM x t := by
  ext v
  simp only [chrisCLM_apply, ContinuousLinearMap.add_apply, chris_add_right]

theorem chrisCLM_smul (x : F) (c : ℝ) (s : F) : m.chrisCLM x (c • s) = c • m.chrisCLM x s := by
  ext v
  simp only [chrisCLM_apply, ContinuousLinearMap.smul_apply, chris_smul_right]

/-- `Γ` as a one-form with values in the endomorphisms of the fibre: `chrisForm x s v = Γ(v, s)`,
the shape Mathlib's `CovariantDerivative.addOneForm` takes. -/
noncomputable def chrisForm (x : F) : F →L[ℝ] F →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun s ↦ m.chrisCLM x s
      map_add' := m.chrisCLM_add x
      map_smul' := m.chrisCLM_smul x }

theorem chrisForm_apply (x s v : F) : m.chrisForm x s v = m.chris x v s := rfl

/-- **The Levi-Civita connection of `m`**: the flat connection plus the Christoffel one-form,
`∇ᵥσ(x) = Dσ(x)(v) + Γₓ(v, σ(x))`. -/
noncomputable def cov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
  flatCov.addOneForm m.chrisForm

theorem cov_apply (σ : Π x : F, TangentSpace 𝓘(ℝ, F) x) (x v : F) :
    m.cov σ x v = fderiv ℝ (σ : F → F) x v + m.chris x v (σ x) := rfl

end Chris

/-- Metric compatibility with respect to `m`, in the vector-space form: the Leibniz rule for
`g(X, Y)` along every direction, for sections differentiable at the point. -/
def IsGCompatible (cov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _)) :
    Prop :=
  ∀ (X Y : F → F) (x : F), DifferentiableAt ℝ X x → DifferentiableAt ℝ Y x → ∀ v : F,
    fderiv ℝ (fun y ↦ m.g y (X y) (Y y)) x v = m.g x (cov X x v) (Y x) + m.g x (X x) (cov Y x v)

/-- The product rule for `g(X, Y)`: the derivative of the metric appears as a third term. -/
theorem fderiv_g_XY (X Y : F → F) (x : F) (hX : DifferentiableAt ℝ X x)
    (hY : DifferentiableAt ℝ Y x) (v : F) :
    fderiv ℝ (fun y ↦ m.g y (X y) (Y y)) x v
      = m.A x v (X x) (Y x) + m.g x (fderiv ℝ X x v) (Y x) + m.g x (X x) (fderiv ℝ Y x v) := by
  have hc : DifferentiableAt ℝ (fun y ↦ m.g y (X y)) x := (m.diff x).clm_apply hX
  have h1 := fderiv_clm_apply (m.diff x) hX
  have h2 := fderiv_clm_apply hc hY
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, h1]
  ring

section Compatible
variable [FiniteDimensional ℝ F]

/-- **The Levi-Civita connection of `m` is `m`-compatible**: the Koszul formula was built for
it. -/
theorem cov_gCompatible : m.IsGCompatible m.cov := by
  intro X Y x hX hY v
  rw [fderiv_g_XY m X Y x hX hY v, cov_apply, cov_apply]
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [g_chris, m.symm x (X x) (m.chris x v (Y x)), g_chris, kos_apply, kos_apply,
    m.A_symm x v (Y x) (X x)]
  ring

end Compatible

section Finite
variable [FiniteDimensional ℝ F] [CompleteSpace F]

/-- **The Levi-Civita connection of `m` is torsion-free**: the Christoffel map is symmetric. -/
theorem cov_torsion : m.cov.torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  rw [cov_apply, cov_apply, m.chris_symm x (X x) (Y x)]
  unfold lieBracket
  abel

/-- **EXISTENCE**: every differentiable Riemannian metric on a finite-dimensional real vector space
has a torsion-free, metric-compatible connection. -/
theorem exists_leviCivita :
    ∃ c : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _),
      c.torsion = 0 ∧ m.IsGCompatible c :=
  ⟨m.cov, m.cov_torsion, m.cov_gCompatible⟩

end Finite

end VarMetric

section Constant

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The constant metric of an inner product space, as a `VarMetric`: the definition is
inhabited. -/
noncomputable def ofInner : VarMetric F where
  g _ := innerSL ℝ
  symm _ u v := real_inner_comm v u
  pos _ _ hv := real_inner_self_pos.mpr hv
  diff := differentiable_const _

theorem ofInner_g (x u v : F) : (ofInner (F := F)).g x u v = ⟪u, v⟫ := rfl

/-- A constant metric has no derivative. -/
theorem A_ofInner (x : F) : (ofInner (F := F)).A x = 0 := by
  simp [VarMetric.A, ofInner]

/-- **For a constant metric, `IsGCompatible` is `LeviCivitaUnique.IsMetricCompatible`**: the new
notion agrees with the old one where both are defined. -/
theorem isGCompatible_ofInner_iff
    (cov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _)) :
    (ofInner (F := F)).IsGCompatible cov ↔ IsMetricCompatible cov := by
  constructor
  · intro h X Y x hX hY v
    rw [mdiffAt_section_iff] at hX hY
    rw [mfderiv_eq_fderiv]
    exact h X Y x hX hY v
  · intro h X Y x hX hY v
    have := h (mdiffAt_section_iff.mpr hX) (mdiffAt_section_iff.mpr hY) v
    rw [mfderiv_eq_fderiv] at this
    exact this

variable [FiniteDimensional ℝ F]

/-- **The Christoffel map of a constant metric vanishes.** -/
theorem chris_ofInner (x u v : F) : (ofInner (F := F)).chris x u v = 0 := by
  apply (ofInner (F := F)).injective_g x
  ext w
  rw [VarMetric.g_chris, VarMetric.kos_apply, A_ofInner]
  simp

/-- **For a constant metric the construction returns the flat connection**, on every section. -/
theorem cov_ofInner_apply (σ : Π x : F, TangentSpace 𝓘(ℝ, F) x) (x : F) :
    (ofInner (F := F)).cov σ x = flatCov σ x := by
  ext v
  rw [VarMetric.cov_apply, chris_ofInner, add_zero]
  rfl

/-- **For a constant metric the construction returns the flat connection**, as connections. -/
theorem cov_ofInner : (ofInner (F := F)).cov = flatCov :=
  CovariantDerivative.ext (funext fun σ ↦ funext fun x ↦ cov_ofInner_apply σ x)

end Constant

end KoszulVectorSpace
