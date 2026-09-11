import LeviCivitaOrder
import CurvatureTensor

/-!
# The connection's regularity class, parametrised by the order

`CurvatureTensor.IsLocallyC1` is the class the whole curvature chain is written against. Its single
field is *`ContMDiffCovariantDerivativeOn E 1 cov.toFun u` for every open `u`* — the order fixed at
one. `LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita` proves that statement at **every**
finite order, so the connection side has been order-free since 2026-09-10 while the class it is
consumed through has not. The `UNLOCK_WATCHLIST` item *the regularity of the curvature of a metric*
has asked for the order-parametrised form since it was filed and prices it as a rewrite of two
files with eleven dependents.

**This file does not do that rewrite.** It adds the class beside the existing one, so that a later
statement can be written against `IsLocallyCk k cov` without any existing file changing, and it
supplies the Levi-Civita instance at every order. **No existing file is touched and no binder is
dropped from one** — which is the same discipline `OrderBridge` used for the literal-order binders,
and for the same reason: the rewrite is the expensive half and this is the half that can be had
without it.

## What is proved

**`IsLocallyCk`** — the class, with `k : WithTop ℕ∞` so that it matches Mathlib's
`ContMDiffCovariantDerivativeOn` argument exactly rather than restricting to `ℕ`.

**`IsLocallyCk.isLocallyC1`** and **`IsLocallyC1.isLocallyCk_one`** — the two bridges at `k = 1`,
each one field projection, so `IsLocallyCk 1 cov` and `IsLocallyC1 cov` are interchangeable and the
thirteen files written against the old class keep working unchanged.

**`isLocallyCk_leviCivita`** — **the Levi-Civita connection is `IsLocallyCk k` at every finite
`k`**, on a `C^(k+2)` manifold with a `C^(k+1)` metric. This is
`LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita` packaged, and it is the statement that
makes the class non-empty at orders above one.

## What is NOT here

* **NO MONOTONICITY IN THE ORDER, AND IT IS NOT AN OVERSIGHT.** `IsLocallyCk k → IsLocallyCk j` for
  `j ≤ k` is **not** a projection: `ContMDiffCovariantDerivativeOn`'s field takes a section of class
  `C^(k+1)` as its hypothesis, so lowering `k` weakens the conclusion **and** weakens the available
  hypothesis, and the implication has to be proved rather than read off. **Mathlib defers exactly
  this**, in its own words in that file: *"We will prove in a later file that any `C^(k+1)`
  covariant derivative is `C^k`."* It is not proved there yet and it is not proved here. **Not
  attempted, 11 September 2026**, and no cost is claimed (`ERRATUM 246`). The consequence for a
  reader: `isLocallyCk_leviCivita` at order `k` does **not** give `IsLocallyC1` for free — that
  comes from the same theorem at `k = 1`, under its own hypotheses, which is why both are
  available and neither is derived from the other.
* **NO CURVATURE STATEMENT IS RESTATED.** `CurvatureTensor`, `CurvatureSkew`, `CurvatureBianchi`,
  `CurvatureTensorial`, `RicciScalar`, `TraceFrame` and the seven other files that mention
  `IsLocallyC1` are untouched, and the curvature results still fix one derivative. **The item's
  residue (i) is not discharged** — this is its first piece, not the piece.
* **NO ANSWER TO RESIDUE (ii).** Whether a `C^(k+1)` metric would suffice where the chain currently
  asks for `C^(k+2)` is untouched. Proving a hypothesis cannot be weakened needs a counterexample,
  not a class.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix**, which `WALLS` §W5.1 §4 prices as a
  research project and which rung 4 also needs.

**No wall moves.** `W5`'s rung 4 is unchanged.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderClass

open Bundle Manifold VectorField FiberBundle Set KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- A covariant derivative on the tangent bundle that is of class `C^k` on every open set:
Mathlib's `ContMDiffCovariantDerivativeOn E k cov u` for every open `u`. The order-parametrised
form of `CurvatureTensor.IsLocallyC1`, which is this class at `k = 1`. -/
class IsLocallyCk (k : WithTop ℕ∞)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop where
  on_open : ∀ u : Set M, IsOpen u → ContMDiffCovariantDerivativeOn E k cov.toFun u

/-! ## 1. The two bridges at order one -/

section Bridges

/-! **`IsManifold I 3 M` IS NEEDED TO STATE THESE, NOT TO PROVE THEM.**
`CurvatureTensor.IsLocallyC1` is declared under `contMDiffVectorBundle_two` — the tangent bundle as
a `C²` vector bundle — which needs a `C³` manifold, so the old class cannot be NAMED without it
while `IsLocallyCk` above can. That is `OrderBridge`'s finding in a second place: a literal-order
binder here is an existence condition for the object, not slack.
**AND THE LINTER CHECKED WHICH BINDER IT IS, rather than this file asserting it**: the two bridges
`omit` `[CompleteSpace E]` and `[IsManifold I 2 M]`, both reported unused, and the unused-variable
report does **not** name `[IsManifold I 3 M]` — so the `C³` binder is load-bearing for STATING them
and the `C²` one is not. -/
variable [IsManifold I 3 M]

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- At `k = 1` the new class gives the old one, by a field projection. -/
theorem IsLocallyCk.isLocallyC1
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)} [h : IsLocallyCk 1 cov] :
    CurvatureTensor.IsLocallyC1 cov :=
  ⟨h.on_open⟩

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- And the old class gives the new one at `k = 1`, the same way. **So nothing written against
`IsLocallyC1` has to change.** -/
theorem IsLocallyC1.isLocallyCk_one
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [h : CurvatureTensor.IsLocallyC1 cov] : IsLocallyCk 1 cov :=
  ⟨h.on_open⟩

end Bridges

/-! ## 2. What the class delivers: Mathlib's global notion at every order -/

/-- **`IsLocallyCk k` GIVES MATHLIB'S GLOBAL `ContMDiffCovariantDerivative cov k`**, by taking the
open set to be everything. `CurvatureTensor` has this at order one, as an unnamed instance; this is
the same one line at every order, and it is what makes the class a statement about the connection
rather than a repackaging of its own field. -/
instance contMDiffCovariantDerivative_of_isLocallyCk {k : WithTop ℕ∞}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)} [h : IsLocallyCk k cov] :
    CovariantDerivative.ContMDiffCovariantDerivative cov k :=
  ⟨h.on_open univ isOpen_univ⟩

/-! ## 3. The Levi-Civita connection, at every finite order -/

section LeviCivita

variable {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- **THE LEVI-CIVITA CONNECTION IS `IsLocallyCk k` AT EVERY FINITE ORDER**, on a `C^(k+2)`
manifold with a `C^(k+1)` metric. This is what makes the class non-empty above order one, and it
is `LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita` packaged. -/
instance isLocallyCk_leviCivita :
    IsLocallyCk (k : WithTop ℕ∞)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) :=
  ⟨fun u hu ↦ LeviCivitaOrder.contMDiffCovariantDerivativeOn_leviCivita u hu⟩

end LeviCivita

end CovariantOrderClass
