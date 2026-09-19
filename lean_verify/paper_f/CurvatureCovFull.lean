import CurvatureCovBundle

/-!
# The four-deep object, and the `k`-free core the chain says it does not have

`CurvatureCovTensor`'s header names an object it did not build — ***what is still not built, as of
2026-09-11, is the four-deep object* with the direction bundled in as well** — because
`CurvatureCovBundle.covRiemannHom` bundles only the two curvature slots and leaves the direction
`u` as a plain argument. **`covRiemannFull` is that object.**

Building it meant reading the chain's binders, and the reading found something else.

## The claim three headers make, and what the binders say

`CurvatureCovDeriv`'s binder paragraph says that every theorem there additionally takes the
non-zero-order hypothesis, and concludes from that that nothing in the file says anything at order
zero. The first clause is **true** — all **six** of its theorems take `hk`. The conclusion drawn
from it is **false**, and the counterexample is the file's own seventh declaration: **`covRiemann`
is a definition, not a theorem, and it has no `k` binder at all.** The object whose absence at
`k = 0` the sentence asserts is *defined* at `k = 0`. (The sentences are described rather than
quoted here, and the same below: a quoted claim reads to `binderclaim_scan.py` as a live one, which
is the rule `--residues` already imposes on the registers.)

`CurvatureCovTensor` inherits that sentence, says so in those words, and broadens it from *every
theorem there* to every theorem **about `covRiemann`**. Broadened, it is false outright: of the
**five** theorems there whose names begin `covRiemann`, **two** — `covRiemann_congr_left` and
`covRiemann_zero_left` — take no `hk`, and neither carries a `k` binder of any kind.

`CurvatureCovCyclic` then counts across the file boundary — ***four* of `CurvatureCovTensor`'s
eight declarations do**. The denominator is right and the numerator is not: **three** of the eight
take `hk` (`covRiemann_sum_left`, `covRiemann_congr_of_eq_left`, `covRiemann_congr_of_eq_right`).

**The measurement, read from `#check` and not from any header** (`ERRATUM 455`'s own rule, applied
to the files that cite it): across the chain's five files — `CurvatureCovDeriv`,
`CurvatureCovBundle`, `CurvatureCovTensor`, `CurvatureCovCyclic`, `CurvatureEndoOrder` — there are
**36** named declarations, of which **15 carry no `k` binder at all**. That is not a corner: it is
the object `covRiemann`, the pointwise object `covRiemannAt`, all four direction laws, the two germ
lemmas, and **every one of `CurvatureCovCyclic`'s four declarations**, the cyclic sum among them.

## Why this is not `ERRATUM 455` again

`ERRATUM 455` is a header that **drops** a hypothesis its theorems carry, so its sentences come out
true for the wrong reason. This is the **inverse**: a header that **attributes** a hypothesis to
theorems that do not carry it. It does not make a sentence true for the wrong reason — it makes it
**false**, and false in the direction that **understates what the estate has proved**. The three
sentences above claim the chain is silent at `k = 0` when fifteen of its declarations speak there.
`ERRATUM 659` records the species; `ERRATUM 660` records that the error travelled, degrading at
each step — true premise, false conclusion, false universal, false count — across three headers
written on three different days.

## What is proved

**`covRiemannSecDir`**, **`covRiemannDir`** — **THE DIRECTION SLOT, BUNDLED, WITH NO LOWER BOUND ON
`k`**: `u ↦ (∇_u R)(Y, Z)` as a continuous linear map, on fields and then on tangent vectors
through their extensions. Built from `covRiemann_add_dir` and `covRiemann_smul_dir`, which take no
`hk`, so neither does this. Continuity is automatic: the tangent space is finite-dimensional.

**`covRiemannSecDir_congr_left`**, **`covRiemannSecDir_zero_left`** — the bundled map depends only
on the germ of `Y`, and vanishes on the zero field. Also **`k`-free**, from the two theorems
`CurvatureCovTensor`'s own fence says do not exist.

**`covRiemannFull`** — **THE FOUR-DEEP OBJECT**:
`(∇R)_x : T_xM →L T_xM →L T_xM →L (T_xM →L T_xM)`, direction outermost, which is what
`CurvatureCovTensor`'s fence asks for. It takes `hk`, because it is built over `covRiemannHom`,
which does.

**`covRiemannFull_apply_field`** — **THE CHECK AGAINST THE ORIGINAL**: on fields of class
`C^(k+2)` the four-deep object returns `covRiemann Y Z x u`, via `covRiemannAt_eq`. Without this
the bundling could be any linear map at all.

**`covRiemannFull_eq_dir`**, **`covRiemannSecDir_eq_dir`** — the joints. The four-deep object's
direction slot **is** the `k`-free object, definitionally; and on fields of the right class the
section-level and vector-level direction maps agree.

**`covRiemannFull_swap`**, **`covRiemannFull_cyclic`** — antisymmetry in the two curvature slots
and **the second Bianchi identity**, transported to the bundled object.

## What is NOT here

* **NO REGULARITY OF THE BUNDLED OBJECT.** Nothing here says `x ↦ covRiemannFull hk x` is a
  section of anything. **As of 2026-09-19** the nearest thing the estate has is
  `CurvatureCovOrder.contMDiffAt_covRiemann_hom`, which regularises the *values* —
  `y ↦ (∇_X R)(Y, Z)(y)` as a `C^k` section of `Hom(TM, TM)` — and bundling the direction does not
  carry that across, because the bundled object varies over `x` in a space that changes with `x`.
  The shift is **not attempted, no cost claimed** (`ERRATUM 246`).
* **NO TENSORIALITY OF `covRiemannSecDir` IN `Y` OR `Z` WITHOUT `hk`.** The `k`-free half is the
  **direction** slot only. Additivity and `f`-homogeneity in the two curvature slots go through
  `CurvatureEndoOrder.mdiffHomAt_riemann`, which needs `k ≠ 0` because a `C²` metric gives a `C⁰`
  curvature. **The three corrected sentences were wrong about which slot, not about whether a
  hypothesis is needed somewhere**, and that distinction is the whole of this file's §1.
* **NOTHING IS CLAIMED TO BE SHARP AT `k = 0`.** That six declarations here have no `k` binder says
  they hold at every `k`; it does not say `covRiemann` is *interesting* at `k = 0`, and no example
  computes it on a `C²` metric. Whether the `k = 0` theory is non-trivial is open and not costed.
* **NO CONTRACTED FORM, NO DIVERGENCE OF THE EINSTEIN TENSOR.** `CurvatureCovDeriv`'s fence stands
  unchanged.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and this paragraph is the one the unit
is about, so it is written from `#check` and its arithmetic is checkable**: the section context is
`CurvatureCovBundle`'s, unchanged and unrelaxed — a normed space `E` over `ℝ` with
`[CompleteSpace E]` and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, the four
`IsManifold` instances, `[RiemannianBundle …]` and the two `IsContMDiffRiemannianBundle`
instances, and the seven names on the `attribute [local instance]` line, copied from
it unchanged. Of the **13** declarations, **7** take
`hk : k ≠ 0` — `covRiemannSecDir_eq_dir` and the six `covRiemannFull*` — and those same 7 are
exactly the ones carrying a `k` binder at all. The other **6** carry neither: `covRiemannSecDir`,
`covRiemannSecDir_apply`, `covRiemannSecDir_congr_left`, `covRiemannSecDir_zero_left`,
`covRiemannDir`, `covRiemannDir_apply`. There is no `omit` and no `set_option` in this file, and
the unused-variable linter reports nothing. Four statements pin the model with `(I := I)` because
a four-deep coercion is applied before `I` is unified; that is elaboration order, not a hypothesis.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovFull

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CurvatureCovDeriv CurvatureCovBundle

open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self KoszulManifold.finDimTangent
  CurvatureTensor.contMDiffVectorBundle_two RicciOrder.contMDiffVectorBundle_add_two

/-! ## 1. The direction slot on fields, bundled -/

/-- **THE DIRECTION SLOT OF `∇R` ON FIELDS, BUNDLED.** -/
noncomputable def covRiemannSecDir (Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ covRiemann Y Z x u
      map_add' := fun u u' ↦ covRiemann_add_dir u u'
      map_smul' := fun c u ↦ by simpa using covRiemann_smul_dir c u }

@[simp] theorem covRiemannSecDir_apply (Y Z : Π x : M, TangentSpace I x) (x : M)
    (u : TangentSpace I x) : covRiemannSecDir Y Z x u = covRiemann Y Z x u := rfl

/-- Germ dependence. -/
theorem covRiemannSecDir_congr_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (h : ∀ᶠ y in 𝓝 x, Y y = Y' y) :
    covRiemannSecDir Y Z x = covRiemannSecDir Y' Z x :=
  ContinuousLinearMap.ext fun u ↦ CurvatureCovTensor.covRiemann_congr_left hY hY' h u

/-- Vanishing on the zero field. -/
theorem covRiemannSecDir_zero_left (Z : Π x : M, TangentSpace I x) (x : M) :
    covRiemannSecDir (0 : Π x : M, TangentSpace I x) Z x = 0 :=
  ContinuousLinearMap.ext fun u ↦ CurvatureCovTensor.covRiemann_zero_left u

/-! ## 2. The direction slot on tangent vectors -/

/-- **THE DIRECTION SLOT ON TANGENT VECTORS.** -/
noncomputable def covRiemannDir (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  covRiemannSecDir (extend E v) (extend E w) x

@[simp] theorem covRiemannDir_apply (x : M) (u v w : TangentSpace I x) :
    covRiemannDir x v w u = covRiemannAt x u v w := rfl

/-- The bridge. -/
theorem covRiemannSecDir_eq_dir (hk : k ≠ 0) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    covRiemannSecDir Y Z x = covRiemannDir x (Y x) (Z x) :=
  ContinuousLinearMap.ext fun u ↦ (covRiemannAt_eq hk hY hZ u).symm

/-! ## 3. The four-deep object -/

/-- **THE FOUR-DEEP OBJECT.** -/
noncomputable def covRiemannFull (hk : k ≠ 0) (x : M) :
    TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ covRiemannHom hk x u
      map_add' := fun u u' ↦ by
        refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_add_dir u u' v w
      map_smul' := fun c u ↦ by
        refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_smul_dir c u v w }

@[simp] theorem covRiemannFull_apply (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannFull (I := I) hk x u v w = covRiemannAt x u v w := rfl

/-- The joint. -/
theorem covRiemannFull_eq_dir (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannFull (I := I) hk x u v w = covRiemannDir x v w u := rfl

/-- The check against the original. -/
theorem covRiemannFull_apply_field (hk : k ≠ 0) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemannFull (I := I) hk x u (Y x) (Z x) = covRiemann Y Z x u :=
  covRiemannAt_eq hk hY hZ u

/-- Antisymmetry. -/
theorem covRiemannFull_swap (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannFull (I := I) hk x u v w = - covRiemannFull (I := I) hk x u w v :=
  covRiemannAt_swap hk u v w

/-- The second Bianchi identity. -/
theorem covRiemannFull_cyclic (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannFull (I := I) hk x u v w + covRiemannFull (I := I) hk x v w u
      + covRiemannFull (I := I) hk x w u v = 0 :=
  covRiemannAt_cyclic hk u v w

end CurvatureCovFull
