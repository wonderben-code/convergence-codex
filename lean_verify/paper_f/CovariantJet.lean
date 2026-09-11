import CovariantOrderMono

/-!
# A covariant derivative depends only on the 1-jet of the section

Mathlib's `CovariantDerivative/Basic.lean` states, in its implementation notes, what it does and
does not prove about locality: *"This file proves that `(∇_X σ) x` depends only on the germ of `σ`
at `x`, but not the stronger statement that it depends only the 1-jet of `σ` at `x`. This will be
proved in a later file."* `CovariantOrderMono.eq_of_localFrame_coeff_eq` got the **frame** form of
that sentence as a two-line corollary of the local frame expansion, and the `UNLOCK_WATCHLIST` item
filed by the same unit named what was missing: the step from equal derivatives of the section to
equal derivatives of its frame coefficients. **This file takes that step, and the statement is
intrinsic** — no frame and no trivialisation appears in it.

## What is proved

**`coeffFun`** and **`contMDiffAt_coeffFun`** — reading one coordinate of a point of the total
space in a trivialisation, as a function **on the total space** rather than on the base, and its
`C^n` regularity on that trivialisation's source. Mathlib's own coefficient lemmas
(the root-level `contMDiffAt_localFrame_coeff` and its relatives) are `iff`s about sections and
give regularity, not derivatives; this is the same reading as a map, which is what a chain rule
can be applied to.

**`extDerivFun_localFrame_coeff_congr`** — **THE STEP.** If `σ` and `σ'` are differentiable at `y`,
take the same value there and have the same `mfderiv` there, then for each `i` the coefficient
functions `y' ↦ cᵢ(σ y')` and `y' ↦ cᵢ(σ' y')` have the same value and the same `extDerivFun` at
`y`. It is `mfderiv_comp` through the trivialisation, with `Filter.EventuallyEq.mfderiv_eq` to
replace the coefficient by the composite on the trivialisation's base set, where the two agree.

**`eq_of_mfderiv_eq`** — **A COVARIANT DERIVATIVE DEPENDS ONLY ON THE 1-JET OF THE SECTION**, in
the intrinsic form: `σ y = σ' y` and `mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) y = … (T% σ') y` give
`∇σ y = ∇σ' y`. The frame is chosen inside the proof — the trivialisation at `y` and
`Module.finBasis` of the model fibre — so the statement a reader sees has neither in it.

**`eq_zero_of_mfderiv_eq`** — the form the statement gets used in: a section whose value and
`mfderiv` at `y` agree with the zero section's has zero covariant derivative there.

## Two things a reader should know about the statement

**WHY THE TWO `mfderiv`S CAN BE COMPARED AT ALL.** `mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) y` has type
`TangentSpace I y →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ((T% σ) y)`, whose codomain depends on the
point `(T% σ) y` — so the equation in `hder` looks ill-typed before one knows the points agree. It
type-checks because `TangentSpace` is a **type synonym for the model space**: both sides live in
`E →L[𝕜] E × F` whatever the base points are. The value hypothesis is therefore not redundant
bookkeeping — it is what makes the derivative comparison mean *the same chart at the same point*,
and the proof uses it in exactly that way (`hT`, rewritten into the chain rule).

**NO REGULARITY HYPOTHESIS ON THE BASE, AND THE LINTER SETTLED IT.** The file was written under
`[IsManifold I 1 M]`, as everything in this estate is. The unused-variable report named it in all
five declarations, so it was **removed from the file** rather than `omit`ted: the 1-jet dependence
needs a charted space over the model, a `C¹` vector bundle, a finite-dimensional model fibre and a
complete scalar field, and nothing about the base's own smoothness.

## What is NOT here

* **NO JET OBJECT.** There is no 1-jet bundle or jet space to factor the statement through:
  checked 2026-09-11, `JetSpace`, `OneJet` and `jetSpace` match nothing in the pinned Mathlib, and
  `grep -ril jet` under `Mathlib/Geometry/Manifold/` hits two files in which the word is in a
  comment. So the hypothesis is spelled as *equal values and equal `mfderiv`*, which is what a
  1-jet is, rather than as an equation between jets. **A statement about a jet object is not
  stated**, and it is not clear it should be until the library has one.
* **NOTHING ABOUT THE CURVATURE 3-TENSOR.** `CurvatureTensorial`'s *what is NOT here* paragraph
  wants two `C²` sections with **the same value** at `x` to give the same `R(X, Y)Z(x)` — a
  **0-jet** statement, which is strictly stronger than anything here and is false for a covariant
  derivative. That is `CurvatureTensor.curvAux_congr_of_eq_Z`'s job and it is already done; this
  file does not touch it, and no wall or watchlist item moves through it.
* **NO SECOND-ORDER VERSION.** That `∇∇σ` depends only on the 2-jet is not stated; the expansion
  this rests on is first-order and a second application would need the induced connection on
  `Hom(TM, V)`, which the pinned library does not have — `CurvatureOrder` records the
  `Hom(TM, TM)` case of the same absence, and says there why its route never needs it. **Not
  attempted, no cost claimed** (`ERRATUM 246`). ⚠ **The absence is still the pinned library's and
  is no longer this estate's**: `HomCovariant.homCovariantDerivative` (entry 107) is the induced
  connection on `Hom(TM, TM)`, for an arbitrary covariant derivative on the tangent bundle. **The
  second-order statement is still not stated** — that is what this clause claims and it stands —
  but the reason given for not attempting it is now only about Mathlib.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a normed space `E` over a nontrivially
normed field `𝕜` with `[CompleteSpace 𝕜]`, a `ChartedSpace H M` with model `I` and **no
`IsManifold` instance**, a finite-dimensional model fibre `F`, and a vector bundle `V` over `M`
with `[FiberBundle F V]`, `[VectorBundle 𝕜 F V]` and `[ContMDiffVectorBundle 1 F V I]`, plus
`[∀ x, IsTopologicalAddGroup (V x)]` and `[∀ x, ContinuousSMul 𝕜 (V x)]` — Mathlib's own binders
for `IsCovariantDerivativeOn`. `contMDiffAt_coeffFun` takes its own order `n` with
`[ContMDiffVectorBundle n F V I]` and `omit`s four binders it does not use;
`extDerivFun_localFrame_coeff_congr` `omit`s three. The unused-variable linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantJet

open Bundle Manifold VectorField FiberBundle Set Module
open scoped Bundle ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι]

/-- The `i`-th coordinate of a point of the total space, read in a trivialisation `e` against a
basis `b` of the model fibre. This is the frame coefficient of `Trivialization.localFrame_coeff`
seen as a function **on the total space** rather than on the base. -/
noncomputable def coeffFun
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) (b : Basis ι 𝕜 F) (i : ι) :
    TotalSpace F V → 𝕜 := fun p ↦ b.repr (e p).2 i

omit [Fintype ι] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [ContMDiffVectorBundle 1 F V I] in
/-- Reading one coordinate in a trivialisation is `C^n` on that trivialisation's source. -/
theorem contMDiffAt_coeffFun {n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I]
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (i : ι) {p : TotalSpace F V} (hp : p ∈ e.source) :
    ContMDiffAt (I.prod 𝓘(𝕜, F)) 𝓘(𝕜) n (coeffFun e b i) p := by
  let breprl : F →ₗ[𝕜] 𝕜 :=
    { toFun v := b.repr v i
      map_add' m m' := by simp
      map_smul' c m := by simp }
  have hout : ContMDiffAt (I.prod 𝓘(𝕜, F)) 𝓘(𝕜) n
      (fun q : M × F ↦ breprl.toContinuousLinearMap q.2) (e p) := by
    refine ContMDiffAt.comp (I' := 𝓘(𝕜, F)) _ ?_ contMDiffAt_snd
    exact contMDiffAt_iff_contDiffAt.mpr (by fun_prop)
  exact hout.comp p ((e.contMDiffOn (n := n)).contMDiffAt (e.open_source.mem_nhds hp))

omit [Fintype ι] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
/-- **THE FRAME COEFFICIENTS INHERIT THE SECTION'S 1-JET.** If two sections differentiable at `y`
have the same value there and the same `mfderiv` there, then for each `i` the coefficient functions
have the same value and the same exterior derivative at `y`. This is the chain rule through the
trivialisation, and it is the whole step between the frame form of the 1-jet statement and the
intrinsic one. -/
theorem extDerivFun_localFrame_coeff_congr
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {σ σ' : Π x : M, V x} {y : M} (hy : y ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) y) (hσ' : MDiffAt (T% σ') y) (hval : σ y = σ' y)
    (hder : mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) y = mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ') y) (i : ι) :
    extDerivFun (I := I) (fun y' ↦ (e.localFrame_coeff I b i y') (σ y')) y
      = extDerivFun (I := I) (fun y' ↦ (e.localFrame_coeff I b i y') (σ' y')) y := by
  have hT : (T% σ) y = (T% σ') y := by simp [hval]
  have hmem : ∀ τ : Π x : M, V x, (T% τ) y ∈ e.source := by
    intro τ; simp [Trivialization.mem_source, hy]
  have hΦ : ∀ τ : Π x : M, V x,
      MDifferentiableAt (I.prod 𝓘(𝕜, F)) 𝓘(𝕜) (coeffFun e b i) ((T% τ) y) := fun τ ↦
    (contMDiffAt_coeffFun (n := 1) e b i (hmem τ)).mdifferentiableAt one_ne_zero
  have heq : ∀ τ : Π x : M, V x,
      (fun y' ↦ (e.localFrame_coeff I b i y') (τ y')) =ᶠ[𝓝 y] (coeffFun e b i ∘ (T% τ)) := by
    intro τ
    filter_upwards [e.open_baseSet.mem_nhds hy] with y' hy'
    simpa [coeffFun] using Trivialization.localFrame_coeff_eq_coeff e hy'
  have hd : ∀ τ : Π x : M, V x, MDiffAt (T% τ) y →
      mfderiv I 𝓘(𝕜) (fun y' ↦ (e.localFrame_coeff I b i y') (τ y')) y
        = (mfderiv (I.prod 𝓘(𝕜, F)) 𝓘(𝕜) (coeffFun e b i) ((T% τ) y)).comp
            (mfderiv I (I.prod 𝓘(𝕜, F)) (T% τ) y) := by
    intro τ hτ
    rw [(heq τ).mfderiv_eq]
    exact mfderiv_comp y (hΦ τ) hτ
  simp only [extDerivFun]
  rw [hd σ hσ, hd σ' hσ', hder, hT, hval]
  rfl

/-! ## The intrinsic statement -/

/-- **A COVARIANT DERIVATIVE DEPENDS ONLY ON THE 1-JET OF THE SECTION.** If `σ` and `σ'` are
differentiable at `y`, take the same value there and have the same `mfderiv` there — which is what
Mathlib's own sentence means by *the 1-jet of `σ` at `y`* — then `∇σ y = ∇σ' y`. **No frame and no
trivialisation appear in the statement**; the frame is chosen inside the proof, as the
trivialisation at `y` and `Module.finBasis` of the model fibre.

Mathlib's `CovariantDerivative/Basic.lean` proves germ-dependence and says of this: *"This file
proves that `(∇_X σ) x` depends only on the germ of `σ` at `x`, but not the stronger statement that
it depends only the 1-jet of `σ` at `x`. This will be proved in a later file."* -/
theorem eq_of_mfderiv_eq
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {σ σ' : Π x : M, V x} {y : M}
    (hσ : MDiffAt (T% σ) y) (hσ' : MDiffAt (T% σ') y) (hys : s ∈ 𝓝 y) (hval : σ y = σ' y)
    (hder : mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) y = mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ') y) :
    cov σ y = cov σ' y :=
  CovariantOrderMono.eq_of_localFrame_coeff_eq hcov (trivializationAt F V y)
    (Module.finBasis 𝕜 F) hσ hσ' (FiberBundle.mem_baseSet_trivializationAt F V y) hys
    (fun i ↦ by rw [hval])
    (fun i ↦ extDerivFun_localFrame_coeff_congr _ _
      (FiberBundle.mem_baseSet_trivializationAt F V y) hσ hσ' hval hder i)

/-- **A SECTION WHOSE 1-JET AGREES WITH THE ZERO SECTION'S HAS ZERO COVARIANT DERIVATIVE**, which
is the form a reader uses the statement above in. -/
theorem eq_zero_of_mfderiv_eq
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {σ : Π x : M, V x} {y : M}
    (hσ : MDiffAt (T% σ) y) (hys : s ∈ 𝓝 y) (hval : σ y = 0)
    (hder : mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) y
      = mfderiv I (I.prod 𝓘(𝕜, F)) (T% (0 : Π x : M, V x)) y) :
    cov σ y = 0 := by
  rw [eq_of_mfderiv_eq hcov hσ (mdifferentiableAt_zeroSection 𝕜 V) hys hval hder]
  exact hcov.zero (mem_of_mem_nhds hys)

end CovariantJet
