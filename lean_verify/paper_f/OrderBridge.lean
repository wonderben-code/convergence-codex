import ScalarOrder

/-!
# The order hypotheses of the curvature chain, and why four of them cannot be dropped

The headline theorems of `CurvatureOrder`, `RicciOrder` and `ScalarOrder` carry seven instance
binders, and four of them name **literal** orders — `[IsManifold I 2 M]`, `[IsManifold I 3 M]`,
`[IsContMDiffRiemannianBundle I 2 …]`, `[IsContMDiffRiemannianBundle I 1 …]` — while the geometric
content is carried by two `k`-indexed ones, a `C^(k+3)` manifold and a `C^(k+2)` metric. Since
`2 ≤ k+1+1+1` and `2 ≤ k+1+1` for every natural `k`, the four look like redundant strength, which
is the kind of thing `ERRATUM 455` exists to make a reader check. **This file checks it, and the
answer is in two halves.**

**The propositions are derivable, in three lines each** (`isManifold_two`, `isManifold_three`,
`isContMDiffRiemannianBundle_two`, `isContMDiffRiemannianBundle_one`), from Mathlib's own `of_le`
lemmas, with `k` pulled into each statement by `include` because the conclusion does not mention
it.

**But they cannot be registered as instances, and the binders cannot be removed.** Two separate
obstacles, both measured:

* `attribute [local instance]` on any of them is refused — *cannot find synthesization order* —
  because `k` occurs only in the hypothesis, so instance search would have to invert
  `↑?k + 1 + 1 + 1` to use them. A derived instance is unavailable exactly where an instance is
  what is wanted.
* More decisively, the literal-order binders are needed to **state** the theorems, not merely to
  prove them. `KoszulManifold.leviCivita` is declared under `[IsManifold I 2 M]` and
  `[IsContMDiffRiemannianBundle I 1 …]`, so a context carrying only `[IsManifold I 1 M]` and the
  two `k`-indexed binders **cannot even name `leviCivita`**; and `CurvatureTensor.curvEndo` needs
  `IsLocallyC1` and so the `C²` metric. **A `C²` manifold with a `C¹` metric is what makes a
  Levi-Civita connection definable at all** — those hypotheses are the object's existence
  conditions, not slack.

**What the derivations are good for anyway.** A user who has the two `k`-indexed hypotheses and
nothing else can reach the conclusions with one `haveI` per instance, because inside a proof `k` is
fixed and the synthesization-order problem does not arise. `contMDiff_scalar_of_order` is that,
packaged: its **type** carries the three `haveI`s, so a reader of the binders sees that the scalar
curvature is `C^k` on the strength of a `C^(k+3)` manifold, its `C^(k+2)` metric and
finite-dimensionality, and nothing else.

## What is proved

**`isManifold_two`, `isManifold_three`** — a `C^(k+3)` manifold is `C²` and `C³`.

**`isContMDiffRiemannianBundle_two`, `isContMDiffRiemannianBundle_one`** — a `C^(k+2)` metric is
`C²` and `C¹`.

**`contMDiff_scalar_of_order`** — **THE SCALAR CURVATURE IS `C^k` FROM THE TWO ORDER HYPOTHESES
ALONE**, with the three derivations carried in the statement's own type.

## What is NOT here

**NO BINDER IS ACTUALLY REMOVED FROM ANY EXISTING FILE.** `CurvatureOrder`, `RicciOrder` and
`ScalarOrder` are untouched and still take the literal-order instances as section hypotheses,
because as the second bullet above shows they must. What this file adds is the bridge and the
reason, not a weakening. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NO ORDER-PARAMETRISED REWRITE.** Removing the literal orders from the chain means restating
`KoszulManifold` and `CurvatureTensor` against `ContMDiffCovariantDerivativeOn E k` with the order
a variable, so that no definition mentions a literal order. That is the rewrite the curvature-
regularity watchlist item has asked for since it was filed, it is two files that eleven depend on,
and no estimate for it is offered (`ERRATUM 194`).

**NOTHING ABOUT SHARPNESS.** That a `C^(k+2)` metric is what a `C^k` curvature costs by this route
is unchanged; whether `C^(k+1)` would do is the other residue of that item and is not touched here.

**ONLY FINITE ORDERS**, inherited from the whole chain: `k` is a natural number, and the `of_le`
casts above are statements about naturals.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with
model `I`, `[IsManifold I 1 M]` — which cannot be dropped either, being what gives the total space
of the tangent bundle its topology and so what lets the metric binder be written down at all —
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`, the Riemannian bundle, and
`[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I)]`. **Four binders
fewer than the files below**, with `omit` on each derivation lemma.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace OrderBridge

open Bundle Manifold Set KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)] in
include k in
/-- A `C^(k+3)` manifold is a `C²` manifold, for every natural `k`. `k` is `include`d because the
conclusion does not mention it, which is also why this cannot be an instance. -/
theorem isManifold_two : IsManifold I 2 M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1)
    (by exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 + 1 by omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)] in
include k in
/-- A `C^(k+3)` manifold is a `C³` manifold, for every natural `k`. -/
theorem isManifold_three : IsManifold I 3 M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1)
    (by exact_mod_cast (show (3 : ℕ) ≤ k + 1 + 1 + 1 by omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] in
include k in
/-- A `C^(k+2)` metric is a `C²` metric, for every natural `k`. -/
theorem isContMDiffRiemannianBundle_two :
    IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1)
    (by exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega))

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] in
include k in
/-- A `C^(k+2)` metric is a `C¹` metric, for every natural `k` — the hypothesis under which
`KoszulManifold.leviCivita` is declared. -/
theorem isContMDiffRiemannianBundle_one :
    IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1)
    (by exact_mod_cast (show (1 : ℕ) ≤ k + 1 + 1 by omega))

/-- **THE SCALAR CURVATURE IS `C^k` FROM THE TWO ORDER HYPOTHESES ALONE.** The type carries the
three derivations, so a reader of the binders sees that nothing is assumed beyond a `C^(k+3)`
manifold, its `C^(k+2)` metric, and finite-dimensionality: the literal-order instances
`ScalarOrder.contMDiff_scalar`'s statement mentions are all supplied here. -/
theorem contMDiff_scalar_of_order :
    haveI := isManifold_two (I := I) (M := M) (k := k)
    haveI := isManifold_three (I := I) (M := M) (k := k)
    haveI := isContMDiffRiemannianBundle_two (I := I) (M := M) (k := k)
    ContMDiff I 𝓘(ℝ) k (fun y : M ↦ RicciScalar.scalar
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) y) := by
  haveI := isManifold_two (I := I) (M := M) (k := k)
  haveI := isManifold_three (I := I) (M := M) (k := k)
  haveI := isContMDiffRiemannianBundle_two (I := I) (M := M) (k := k)
  exact ScalarOrder.contMDiff_scalar

end OrderBridge
