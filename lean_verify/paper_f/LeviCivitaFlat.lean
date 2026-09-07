import LeviCivitaUnique

/-!
# The Levi-Civita connection of a Euclidean space is the flat connection

`LeviCivitaUnique` named metric compatibility and proved that a torsion-free, metric-compatible
connection is unique, and said in its own fence that nothing there showed the definition
inhabited — *not even the flat one on a vector space*. This file does that case: on a real inner
product space `F`, with the tangent spaces carrying `F`'s own inner product (Mathlib's
`riemannianMetricVectorSpace` instance), **the ordinary derivative is a covariant derivative, it is
torsion-free, it is metric-compatible, and by uniqueness it is the only such connection.**

Each half is a translation. A section of the tangent bundle of `F` is a map `F → F`, and
Mathlib's manifold differentiability of the section is differentiability of the map
(`mdiffAt_section_iff`, one `simp`). Torsion-freeness is the definition of the Lie bracket on a
vector space, `[X, Y] = DY(X) − DX(Y)`. Compatibility is the product rule for the inner product,
`fderiv_inner_apply`.

## What is proved

**`mdiffAt_section_iff`** — on a vector space, a section of the tangent bundle is differentiable
at a point as a section exactly when it is as a map.

**`inner_tangentSpace`** — the inner product on a tangent space of `F` is that of `F`, by `rfl`.

**`extDerivFun_eq_fderiv`** — Mathlib's exterior derivative of a scalar function on `F` is its
derivative.

**`flatCov`, `flatCov_apply`** — the flat connection `∇ᵥσ(x) = Dσ(x)(v)`, packaged as a
`CovariantDerivative`: additive (`fderiv_add`) and Leibniz (`fderiv_smul`).

**`flatCov_torsion`** — its torsion vanishes: `torsion_eq_zero_iff` asks for
`DY(X) − DX(Y) = [X, Y]`, which is `VectorField.lieBracket` unfolded.

**`flatCov_compatible`** — it is metric-compatible, by `fderiv_inner_apply`.

**`exists_leviCivita`** — **so a torsion-free metric-compatible connection exists on every real
inner product space that is finite-dimensional and complete**, and `IsMetricCompatible` is
inhabited.

**`eq_fderiv_of_torsionFree_of_compatible`** — **and it is the only one**: any torsion-free
metric-compatible connection on `F` is the ordinary derivative on every section differentiable at
the point (`LeviCivitaUnique.eq_of_torsionFree_of_compatible` against `flatCov`).

## What is NOT here

**A MANIFOLD.** Everything here is on the model space `F` with its constant metric, where the
connection is the derivative and the Koszul formula is never needed. Existence on a Riemannian
manifold — `WALLS` §W5.1 §3's single object — is untouched: it needs the Koszul construction,
with the derivative of a non-constant metric along vector fields and the Lie bracket's Leibniz
rules, and nothing here starts it. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NOT EVEN A NON-CONSTANT METRIC ON `F`.** The tangent-space inner product used is `F`'s own, at
every point; a Riemannian metric on `F` that varies with the point is a different `RiemannianBundle`
instance, and the flat connection is not compatible with it.

**NO CURVATURE**, and no statement that the flat connection's curvature vanishes, curvature being
undefined in this estate and in the pinned Mathlib. **No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `flatCov`, `flatCov_apply`,
`flatCov_compatible` and the three translation lemmas take only `[NormedAddCommGroup F]` and
`[InnerProductSpace ℝ F]`; `flatCov_torsion`, `exists_leviCivita` and the uniqueness corollary
add `[FiniteDimensional ℝ F]` and `[CompleteSpace F]`, which are Mathlib's hypotheses for
`torsion` and `difference`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace LeviCivitaFlat

open Bundle Manifold VectorField FiberBundle LeviCivitaUnique
open scoped Bundle ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- On a vector space, a section of the tangent bundle is a map `F → F`, and manifold
differentiability of the section is differentiability of the map. -/
theorem mdiffAt_section_iff {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F} :
    MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x ↔
      DifferentiableAt ℝ (σ : F → F) x := by
  rw [mdifferentiableAt_section, mdifferentiableAt_iff_differentiableAt]
  simp

/-- The inner product on a tangent space of a vector space is the inner product of the space. -/
theorem inner_tangentSpace (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    ⟪v, w⟫ = @inner ℝ F _ v w := rfl

/-- On a vector space the exterior derivative of a scalar function is its derivative. -/
theorem extDerivFun_eq_fderiv (g : F → ℝ) (x : F) :
    extDerivFun (I := 𝓘(ℝ, F)) g x = fderiv ℝ g x := by
  ext v
  simp [extDerivFun, mfderiv_eq_fderiv]
  rfl

/-- **The flat connection**: the ordinary derivative of a map `F → F`, as a covariant derivative
on the tangent bundle of `F`. -/
noncomputable def flatCov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _) where
  toFun σ x := fderiv ℝ (σ : F → F) x
  isCovariantDerivativeOnUniv :=
    { add := by
        intro σ σ' x hσ hσ' _
        rw [mdiffAt_section_iff] at hσ hσ'
        exact fderiv_add hσ hσ'
      leibniz := by
        intro σ g x hσ hg _
        rw [mdiffAt_section_iff] at hσ
        rw [mdifferentiableAt_iff_differentiableAt] at hg
        rw [extDerivFun_eq_fderiv]
        exact fderiv_smul hg hσ }

theorem flatCov_apply (σ : Π x : F, TangentSpace 𝓘(ℝ, F) x) (x : F) :
    flatCov σ x = fderiv ℝ (σ : F → F) x := rfl

/-- **The flat connection is metric-compatible**: the product rule for the inner product. -/
theorem flatCov_compatible : IsMetricCompatible (flatCov (F := F)) := by
  intro X Y x hX hY v
  rw [mdiffAt_section_iff] at hX hY
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun y ↦ @inner ℝ F _ (X y) (Y y)) x v
    = @inner ℝ F _ (fderiv ℝ X x v) (Y x) + @inner ℝ F _ (X x) (fderiv ℝ Y x v)
  rw [fderiv_inner_apply ℝ hX hY v, add_comm]

section Finite

variable [FiniteDimensional ℝ F] [CompleteSpace F]

/-- **The flat connection is torsion-free**: its torsion is the Lie bracket's own definition. -/
theorem flatCov_torsion : (flatCov (F := F)).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  rfl

/-- **EXISTENCE ON A EUCLIDEAN SPACE**: the flat connection is a torsion-free, metric-compatible
covariant derivative, so `IsMetricCompatible` is inhabited. -/
theorem exists_leviCivita :
    ∃ cov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _),
      cov.torsion = 0 ∧ IsMetricCompatible cov :=
  ⟨flatCov, flatCov_torsion, flatCov_compatible⟩

/-- **AND IT IS THE ONLY ONE**: on a Euclidean space, every torsion-free metric-compatible
connection is the ordinary derivative on every section differentiable at the point. -/
theorem eq_fderiv_of_torsionFree_of_compatible
    (cov : CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _))
    (h : cov.torsion = 0) (hc : IsMetricCompatible cov) {x : F}
    {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hσ : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x) :
    cov σ x = fderiv ℝ (σ : F → F) x :=
  eq_of_torsionFree_of_compatible cov flatCov h flatCov_torsion hc flatCov_compatible hσ

end Finite

end LeviCivitaFlat
