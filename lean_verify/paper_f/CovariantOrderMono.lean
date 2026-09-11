import KoszulOrder
import LeviCivitaOrder
import CovariantOrderClass

/-!
# Lowering the order of a covariant derivative

`CovariantOrderClass` added the class `IsLocallyCk k cov` and recorded, as the first thing it did
not do, that the class is **not** monotone in the order: `ContMDiffCovariantDerivativeOn`'s field
takes a section of class `C^(k+1)` as its hypothesis, so lowering `k` weakens the conclusion and
the available hypothesis together. Mathlib defers the same implication in its own words, twice —
*"We will prove in a later file that any `C^(k+1)` covariant derivative is `C^k`."* This file
proves a form of it.

## The one thing to read first: this is not Mathlib's sentence

Mathlib states that sentence above two declarations: `ContMDiffCovariantDerivativeOn F k cov u`,
about a **fixed** set `u`, and `ContMDiffCovariantDerivative cov k`, about `u = univ`. **Neither of
those two implications is proved here.** What is proved is the *all-open-sets* form: a connection
that is `C^n` **on every open set** is `C^j` on every open set, for every natural `j ≤ n`. That is
exactly the shape of this estate's own class `IsLocallyCk`, which quantifies over all open sets,
and it is why the class comes out monotone while the single-set predicate does not.

**Why the hypothesis has to be available on small sets, measured rather than asserted.** The proof
expands the section in a local frame, and the only local frames the pinned library has are the ones
a trivialisation carries (`Trivialization.localFrame`), which are regular on that trivialisation's
base set and are the junk value 0 outside it. That was checked and not assumed: `IsLocalFrameOn`
occurs in one Mathlib file, `VectorBundle/LocalFrame.lean`, whose only constructor is
`Trivialization.isLocalFrameOn_localFrame_baseSet`, and the `OrthonormalFrame.lean` its comments
point at is described there as **planned** and is not in the pinned library. This estate produces
none either — every other use of `IsLocalFrameOn` here takes one as a hypothesis. So the order-`n`
hypothesis is applied to a section that is regular only on `u ∩ e.baseSet`, and a hypothesis about
sections regular across the whole of `u` cannot be applied to such a section at all. Closing that
gap needs a cutoff — a section regular on `u`, of class `C^(n+1)`, agreeing with the frame near the
point — and a bump function of
finite regularity on a `C^(n+2)` manifold is not in this estate or in the pinned library.
**The fixed-set form is not attempted and no cost is claimed** (`ERRATUM 246`). There is also a
reason not to expect it for free: its hypothesis constrains `cov` only on sections regular across
all of `u`, while its conclusion constrains `cov` on the strictly larger supply of sections that
are only `C^(j+1)`. **That is an obstruction identified, not a counterexample**; no counterexample
is offered, and nothing here says the fixed-set form is false.

## What is proved

**`sum_of_isCovariantDerivativeOn`** — a covariant derivative commutes with finite sums of
sections differentiable at the point. Mathlib has the binary case as a field and the finite case
for *tensorial* operations; a covariant derivative is not tensorial, so this is proved here by the
same induction.

**`eq_sum_localFrame_of_isCovariantDerivativeOn`** — **THE LOCAL FRAME EXPANSION.** On a
trivialisation's base set, `∇σ = ∑ᵢ (cᵢσ) ∇sᵢ + ∑ᵢ d(cᵢσ) ⊗ sᵢ` with `sᵢ` the frame and `cᵢ` its
coefficient functionals. This is the structural lemma the rest of the file rests on, and it is
stated for **an arbitrary vector bundle over an arbitrary field**, not just the tangent bundle: it
needs only Mathlib's germ-locality (`IsCovariantDerivativeOn.congr_of_eventuallyEq`), the Leibniz
rule and the sum rule above. It is the reason the order can be lowered at all — the section's own
regularity is consumed once, by the exterior derivative in the second sum.

**`eq_of_localFrame_coeff_eq`** — **AND SO A COVARIANT DERIVATIVE DEPENDS ONLY ON THE 1-JET OF THE
SECTION, IN A FRAME**, two lines from the expansion. Mathlib defers this too, in the same file:
*"This file proves that `(∇_X σ) x` depends only on the germ of `σ` at `x`, but not the stronger
statement that it depends only the 1-jet of `σ` at `x`. This will be proved in a later file."*
**This is the frame form and not the intrinsic one**, and the difference is the same kind as the
one above: the hypothesis is on the coefficients in one trivialisation's frame, not on the 1-jet of
the section as an object. The intrinsic form — equal values and equal `mfderiv` of `T% σ` — is
**not derived here**, and the step it needs is the chain rule through the trivialisation.
`UNLOCK_WATCHLIST` carries it as its own item. ⚠ It carried it for one unit:
`CovariantJet.eq_of_mfderiv_eq` (11 September, entry 106) is the intrinsic form, by exactly that
chain rule, and the item is closed. **The sentence above is true of this file and false of the
estate**; what it says about the shape of the two statements is unchanged.

**`contMDiffAt_localFrame`**, **`contMDiffAt_sum_extDerivFun_smulRight`**,
**`contMDiffVectorBundle_add_one`** — the tangent-bundle pieces. The second is the half of the
expansion that costs a derivative: for coefficients of class `C^(j+1)` the sum `∑ᵢ dcᵢ ⊗ sᵢ` is a
`C^j` section of `Hom(TM, TM)`, through `KoszulOrder.contMDiffAt_extDerivFun_apply` and
`LeviCivitaOrder.contMDiffAt_hom_of_localFrame`.

**`contMDiffCovariantDerivativeOn_of_le`** — **THE ORDER CAN BE LOWERED.** For `j : ℕ` and
`(j : WithTop ℕ∞) ≤ n`, a covariant derivative on the tangent bundle of a `C^(n+2)` manifold that
is `C^n` on every open set is `C^j` on every open set, in Mathlib's own
`ContMDiffCovariantDerivativeOn E j`.

**`isLocallyCk_of_le`** — the same statement as the class: `IsLocallyCk n cov → IsLocallyCk j cov`.
This is the sentence `CovariantOrderClass`'s *What is NOT here* section reported as unproved.

**`isLocallyC1_of_isLocallyCk`** — **AND SO A CONNECTION KNOWN `C^n` FOR ANY `n ≥ 1` SATISFIES THE
CLASS THE WHOLE CURVATURE CHAIN IS WRITTEN AGAINST.** `CurvatureTensor.IsLocallyC1 cov` from
`IsLocallyCk n cov`, with no file restated and no binder dropped from one.

## What is NOT here

* **THE FIXED-SET AND GLOBAL FORMS**, as above — which is why this file does not claim to have
  proved Mathlib's deferred theorem, only an all-open-sets form of it.
* **ONLY THE TARGET ORDER IS RESTRICTED, AND THIS ESTATE CANNOT FEED THE REST.** `j : ℕ` is
  finite — the exterior-derivative step is `KoszulOrder`'s, which is finite-order for the reason
  that file gives — while the hypothesis order `n : WithTop ℕ∞` may be infinite or analytic.
  **The infinite cases are stated and unfed here**: the only connection this estate knows to be
  `C^n` at high order is the Levi-Civita connection, through
  `LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita`, which is stated for `k : ℕ` and is
  blocked above the finite orders by `contMDiffAt_iff_contMDiffOn_nhds`. So `n = ∞` costs nothing
  to state and nothing in this estate satisfies it.
* **NO GAIN FOR THE LEVI-CIVITA CONNECTION, AND IT IS WORTH SAYING PLAINLY.** Its order-one
  instance is proved directly (`LeviCivitaRegular.isLocallyC1_leviCivita`, a `C³` manifold with a
  `C²` metric), so `isLocallyC1_of_isLocallyCk` gives nothing there that was not already available
  under weaker hypotheses. The theorem's content is for a connection whose regularity is **only**
  known at a high order — which is the position any consumer of an order-`n` construction is in,
  and the position `CurvatureTensor`'s order-one class put them in.
* **THE WATCHLIST ITEM'S RESIDUE (i) IS STILL NOT DISCHARGED.** No curvature statement is
  restated: `curvEndo` is still built at one derivative, the twelve other files that mention
  `IsLocallyC1` are untouched, and the literal-order binders `OrderBridge` measured are still
  there — they are the connection's existence conditions, not slack. What this file changes is
  that a consumer holding the order-`n` class no longer has to re-run the order-one theorem under
  its own hypotheses to reach the chain. **The item stays open on both residues**; residue (ii),
  whether a `C^(k+1)` metric would suffice, is untouched and needs a counterexample.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix**, which `WALLS` §W5.1 §4 prices as a
  research project and which rung 4 also needs.

**No wall moves.** `W5`'s rung 4 is unchanged. **No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`). Section `Sum`: a normed space `E` over a
nontrivially normed field `𝕜`, a `ChartedSpace H M` with model `I`, a model fibre `F` and a vector
bundle `V` over `M` with `F`'s topological and module structure. Section `Frame` adds
`[CompleteSpace 𝕜]`, `[FiniteDimensional 𝕜 F]`, `[ContMDiffVectorBundle 1 F V I]` and a `Fintype`
index for the frame, with `[IsManifold I 1 M]` present in the section and `omit`ted from the
expansion, which does not use it. Sections `Halves` and `Mono` are over `ℝ` on the tangent bundle:
`[CompleteSpace E]` (Mathlib's hypothesis for pulled-back fields, inherited from `KoszulOrder`),
`[FiniteDimensional ℝ E]`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, and the order binder —
`[IsManifold I ((j : WithTop ℕ∞) + 1 + 1) M]` in `Halves`, `[IsManifold I (n + 1 + 1) M]` in
`Mono`, from which the `j` one is derived inside the proof — plus `[IsManifold I 3 M]` in section
`ToOne`, which `CovariantOrderClass` measured to be needed to **state** anything mentioning
`IsLocallyC1`. The unused-variable linter reports nothing anywhere in this file, so every binder
every theorem here carries — after the three `omit` lines — is load-bearing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderMono

open Bundle Manifold VectorField FiberBundle Set Module
open scoped Bundle ContDiff Topology

/-! ## 1. Finite additivity of a covariant derivative -/

section Sum

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- A covariant derivative commutes with finite sums of sections. -/
theorem sum_of_isCovariantDerivativeOn
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s) {ι : Type*} (t : Finset ι)
    (σ : ι → Π x : M, V x) {x : M} (hσ : ∀ i, MDiffAt (T% (σ i)) x) (hx : x ∈ s) :
    cov (fun y ↦ ∑ i ∈ t, σ i y) x = ∑ i ∈ t, cov (σ i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hcov.zero hx
  | insert a t ha h =>
    simp only [Finset.sum_insert ha, ← h]
    exact hcov.add (hσ a) (.sum_section fun i ↦ hσ i) hx

end Sum

/-! ## 2. The local frame expansion -/

section Frame

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι]

omit [IsManifold I 1 M] in
/-- **THE LOCAL FRAME EXPANSION OF A COVARIANT DERIVATIVE.** -/
theorem eq_sum_localFrame_of_isCovariantDerivativeOn
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {σ : Π x : M, V x} {y : M}
    (hσ : MDiffAt (T% σ) y) (hy : y ∈ e.baseSet) (hys : s ∈ 𝓝 y) :
    cov σ y = ∑ i, ((e.localFrame_coeff I b i y) (σ y) • cov (e.localFrame b i) y
      + (extDerivFun (I := I) (fun y' ↦ (e.localFrame_coeff I b i y') (σ y')) y).smulRight
          (e.localFrame b i y)) := by
  classical
  set g : ι → M → 𝕜 := fun i y' ↦ (e.localFrame_coeff I b i y') (σ y') with hgdef
  have hgd : ∀ i, MDiffAt (g i) y := fun i ↦ by
    simpa [hgdef] using mdifferentiableAt_localFrame_coeff b hy hσ i
  have hsd : ∀ i, MDiffAt (T% (e.localFrame b i)) y := fun i ↦
    ((e.isLocalFrameOn_localFrame_baseSet I 1 b).contMDiffAt e.open_baseSet hy i).mdifferentiableAt
      one_ne_zero
  have hmem : ∀ i, MDiffAt (T% (g i • e.localFrame b i)) y := fun i ↦
    (hgd i).smul_section (hsd i)
  have hsum : MDiffAt (T% (fun y' ↦ ∑ i, g i y' • e.localFrame b i y')) y :=
    MDifferentiableAt.sum_section fun i ↦ hmem i
  have heq : ∀ᶠ y' in 𝓝 y, σ y' = ∑ i, g i y' • e.localFrame b i y' := by
    filter_upwards [e.open_baseSet.mem_nhds hy] with y' hy'
    exact Trivialization.eq_sum_localFrame_coeff_smul hy'
  have hsplit : cov (fun y' ↦ ∑ i, g i y' • e.localFrame b i y') y
      = ∑ i, cov (g i • e.localFrame b i) y :=
    sum_of_isCovariantDerivativeOn hcov Finset.univ _ hmem (mem_of_mem_nhds hys)
  rw [hcov.congr_of_eventuallyEq hσ hsum hys heq, hsplit]
  exact Finset.sum_congr rfl fun i _ ↦ hcov.leibniz (hsd i) (hgd i) (mem_of_mem_nhds hys)

omit [IsManifold I 1 M] [Fintype ι] in
/-- **AND SO A COVARIANT DERIVATIVE DEPENDS ONLY ON THE 1-JET OF THE SECTION, IN A FRAME.** If two
sections differentiable at `y` have the same frame coefficients at `y` **and** the same exterior
derivatives of those coefficients at `y`, then `∇σ y = ∇σ' y`. Mathlib's `CovariantDerivative`
file proves germ-dependence and says of this, in its own words, *"This file proves that `(∇_X σ) x`
depends only on the germ of `σ` at `x`, but not the stronger statement that it depends only the
1-jet of `σ` at `x`. This will be proved in a later file."* **This is the frame form of that
statement and not the intrinsic one** — the hypothesis is on the coefficients in one
trivialisation's frame, not on the 1-jet of the section as an object — and the intrinsic form,
which would ask for equal values and equal `mfderiv` of `T% σ`, is not derived here. It is two
lines from the expansion above, which is the point.
**⚠ The intrinsic form is `CovariantJet.eq_of_mfderiv_eq`, proved one unit later from this lemma
and a chain rule through the trivialisation; *not derived here* remains true of this file.** -/
theorem eq_of_localFrame_coeff_eq [Finite ι]
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {σ σ' : Π x : M, V x} {y : M}
    (hσ : MDiffAt (T% σ) y) (hσ' : MDiffAt (T% σ') y) (hy : y ∈ e.baseSet) (hys : s ∈ 𝓝 y)
    (hval : ∀ i, (e.localFrame_coeff I b i y) (σ y) = (e.localFrame_coeff I b i y) (σ' y))
    (hder : ∀ i, extDerivFun (I := I) (fun y' ↦ (e.localFrame_coeff I b i y') (σ y')) y
      = extDerivFun (I := I) (fun y' ↦ (e.localFrame_coeff I b i y') (σ' y')) y) :
    cov σ y = cov σ' y := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [eq_sum_localFrame_of_isCovariantDerivativeOn hcov e b hσ hy hys,
    eq_sum_localFrame_of_isCovariantDerivativeOn hcov e b hσ' hy hys]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hval i, hder i]

end Frame

/-! ## 3. The two halves of the expansion, on the tangent bundle -/

section Halves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {j : ℕ} [IsManifold I ((j : WithTop ℕ∞) + 1 + 1) M]

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The chart's local frame is `C^(j+1)` at `x`, hence `C^n` there for every `n ≤ j + 1`. -/
theorem contMDiffAt_localFrame {ι : Type*} (b : Basis ι ℝ E) {x : M}
    {n : WithTop ℕ∞} (hn : n ≤ (j : WithTop ℕ∞) + 1) (i : ι) :
    CMDiffAt n
      (T% ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i)) x :=
  (((trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet I
      ((j : WithTop ℕ∞) + 1) b).contMDiffAt
    (trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x) i).of_le hn

/-- **THE `df ⊗ s` HALF OF THE EXPANSION IS A `C^j` SECTION OF `Hom(TM, TM)`**, for coefficient
functions of class `C^(j+1)`. This is the half that costs a derivative, and the only place the
expansion's order is limited by the section rather than by the connection. -/
theorem contMDiffAt_sum_extDerivFun_smulRight {ι : Type*} [Fintype ι] (b : Basis ι ℝ E)
    (g : ι → M → ℝ) {x : M}
    (hg : ∀ i, ContMDiffAt I 𝓘(ℝ) ((j : WithTop ℕ∞) + 1) (g i) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (j : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (∑ i, (extDerivFun (I := I) (g i) y).smulRight
          ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y))) x := by
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ b fun i₀ ↦ ?_
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContMDiffAt.sum_section fun i _ ↦
    (KoszulOrder.contMDiffAt_extDerivFun_apply (hg i)
      (contMDiffAt_localFrame b le_self_add i₀)).smul_section
      (contMDiffAt_localFrame b le_self_add i)

end Halves

/-! ## 4. Lowering the order -/

section Mono

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {j : ℕ} {n : WithTop ℕ∞} [IsManifold I (n + 1 + 1) M]

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The tangent bundle of a `C^(n+2)` manifold is a `C^(n+1)` vector bundle, at every order `n`
including the infinite ones (Mathlib registers this only for `n + 1 ∈ {1, ∞, ω}`). -/
theorem contMDiffVectorBundle_add_one :
    ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_add_one

/-- **THE ORDER OF A COVARIANT DERIVATIVE ON THE TANGENT BUNDLE CAN BE LOWERED**, which is the
implication Mathlib states it will prove in a later file and has not. -/
theorem contMDiffCovariantDerivativeOn_of_le (hjn : (j : WithTop ℕ∞) ≤ n)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : ∀ v : Set M, IsOpen v → ContMDiffCovariantDerivativeOn E n cov.toFun v)
    (u : Set M) (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E (j : WithTop ℕ∞) cov.toFun u := by
  classical
  haveI : IsManifold I ((j : WithTop ℕ∞) + 1 + 1) M :=
    IsManifold.of_le (n := n + 1 + 1) (by gcongr)
  constructor
  intro σ hσ x hx
  have hxe : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  set e := trivializationAt E (TangentSpace I : M → Type _) x with he
  set b := Module.finBasis ℝ E with hb
  set w := u ∩ e.baseSet with hw
  have hwo : IsOpen w := hu.inter e.open_baseSet
  have hxw : x ∈ w := ⟨hx, hxe⟩
  set g : Fin (finrank ℝ E) → M → ℝ := fun i y ↦ (e.localFrame_coeff I b i y) (σ y) with hg
  -- the frame is `C^(m+1)` on `w`, so the connection applied to it is `C^m` there, hence `C^j`
  have hframe : ∀ i, CMDiff[w] (n + 1) (T% (e.localFrame b i)) := fun i ↦
    ((e.isLocalFrameOn_localFrame_baseSet I (n + 1) b).mono
      inter_subset_right).contMDiffOn i
  have hcovframe : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (j : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (cov.toFun (e.localFrame b i) y)) x :=
    fun i ↦ (((h w hwo).contMDiff (hframe i)).contMDiffAt (hwo.mem_nhds hxw)).of_le hjn
  -- and the coefficients of `σ` are `C^(j+1)` at `x`
  have hgk : ∀ i, ContMDiffAt I 𝓘(ℝ) ((j : WithTop ℕ∞) + 1) (g i) x := fun i ↦ by
    simpa [hg] using contMDiffAt_localFrame_coeff (k := (j : WithTop ℕ∞) + 1) b hxe
      (hσ.contMDiffAt (hu.mem_nhds hx)) i
  -- the two halves of the expansion are `C^j` sections of `Hom(TM, TM)`
  have hsmul : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (j : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (g i y • cov.toFun (e.localFrame b i) y)) x :=
    fun i ↦ ((hgk i).of_le le_self_add).smul_section (hcovframe i)
  have hsum : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (j : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        ((∑ i, g i y • cov.toFun (e.localFrame b i) y)
          + ∑ i, (extDerivFun (I := I) (g i) y).smulRight (e.localFrame b i y))) x :=
    (ContMDiffAt.sum_section fun i _ ↦ hsmul i).add_section
      (contMDiffAt_sum_extDerivFun_smulRight b g hgk)
  -- and their sum is the covariant derivative near `x`
  have hEq : ∀ᶠ y in 𝓝 x, cov.toFun σ y
      = (∑ i, g i y • cov.toFun (e.localFrame b i) y)
        + ∑ i, (extDerivFun (I := I) (g i) y).smulRight (e.localFrame b i y) := by
    filter_upwards [hwo.mem_nhds hxw] with y hy
    rw [← Finset.sum_add_distrib]
    exact eq_sum_localFrame_of_isCovariantDerivativeOn
      (cov.isCovariantDerivativeOn (s := univ)) e b
      ((hσ.contMDiffAt (hu.mem_nhds hy.1)).mdifferentiableAt (by simp)) hy.2 Filter.univ_mem
  refine (hsum.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hEq] with y hy
  simp [hy]

/-- **THE CLASS IS MONOTONE IN THE ORDER**: `IsLocallyCk m → IsLocallyCk j` for `j ≤ m`. -/
theorem isLocallyCk_of_le (hjn : (j : WithTop ℕ∞) ≤ n)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : CovariantOrderClass.IsLocallyCk n cov) :
    CovariantOrderClass.IsLocallyCk (j : WithTop ℕ∞) cov :=
  ⟨fun u hu ↦ contMDiffCovariantDerivativeOn_of_le hjn (fun v hv ↦ h.on_open v hv) u hu⟩

section ToOne

variable [IsManifold I 3 M]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- **A CONNECTION OF CLASS `C^m` FOR ANY `m ≥ 1` SATISFIES THE CLASS THE WHOLE CURVATURE CHAIN IS
WRITTEN AGAINST.** -/
theorem isLocallyC1_of_isLocallyCk (hn : 1 ≤ n)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (h : CovariantOrderClass.IsLocallyCk n cov) :
    CurvatureTensor.IsLocallyC1 cov := by
  haveI : CovariantOrderClass.IsLocallyCk (1 : WithTop ℕ∞) cov := by
    simpa using isLocallyCk_of_le (j := 1) (by simpa using hn) h
  exact CovariantOrderClass.IsLocallyCk.isLocallyC1

end ToOne

end Mono

end CovariantOrderMono
