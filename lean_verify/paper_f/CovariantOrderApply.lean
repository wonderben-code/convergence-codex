import CovariantOrderClass
import CurvatureTensorial
import KoszulOrder

/-!
# The covariant derivative of a section at order `k`, for ANY connection of that class

**`CovariantOrderClass.IsLocallyCk` had no consumer, and this file is its first.** Entry 104 built
the order-parametrised class — a covariant derivative that is `C^k` on every open set — and proved
the Levi-Civita connection satisfies it at every finite order. Measured today: the class is named
in five other files of the estate and **not one declaration takes it as a hypothesis**; the two
below are the first. `HomCovariantOrder`'s own fence says as much in its own words — the abstract
statement *would need the hypothesis in the form `CovariantOrderClass.IsLocallyCk` — which exists —
but no such statement is made*.

**What it buys is the foundation stone of the abstract chain.** Every order-`k` regularity result in
this estate's geometry chain is stated for the **Levi-Civita** connection, because the one lemma
they all rest on — `∇_Y Z` is `C^k` when the fields are — was proved from the Koszul formula.
That lemma is not about the Koszul formula: it is Mathlib's `ContMDiffCovariantDerivativeOn`
unfolded on a neighbourhood, and the class supplies it for **any** connection. The two theorems
here are that lemma, abstractly, and the Levi-Civita corollary below shows the specialisation is
strictly better than what the estate had: it asks the direction field for `C^k` where
`LeviCivitaOrder.contMDiffAt_leviCivita_apply` asks `C^(k+1)`.

## What is proved

**`contMDiffAt_cov_hom`** — **`∇Z` IS A `C^k` SECTION OF `Hom(TM, TM)`** for `Z` of class `C^(k+1)`
at the point, for any `IsLocallyCk k` connection. The proof is `mdiffAt_covApply'`'s, one order up
and with the connection abstract: take a neighbourhood on which `Z` is `C^(k+1)`, apply the class's
field there, and restrict.

**`contMDiffAt_covApply`** — **AND `∇_Y Z` IS A `C^k` SECTION OF `TM`**, by Mathlib's
`ContMDiffAt.clm_bundle_apply`.

**`contMDiffAt_leviCivita_apply'`** — the Levi-Civita case, **with one hypothesis weaker than the
estate's own version of it**. Not a second proof: the instance is
`CovariantOrderClass.isLocallyCk_leviCivita`.

## What is NOT here

* **THE REST OF THE ABSTRACT CHAIN.** The curvature at order `k`, the induced connection on
  `Hom(TM, TM)` at order `k`, and `∇R` are all still stated for the Levi-Civita connection only.
  That is the `UNLOCK_WATCHLIST` residue **(R-REWRITE)** on the curvature-regularity item, and it
  is the same job it was: the files below this one quote `LeviCivitaOrder`'s theorem by name, and
  re-pointing them at this one is a rewrite of each. **Not attempted, no cost claimed**
  (`ERRATUM 246`); what changes is that the target of that rewrite now exists.
* **NO REPLACEMENT OF `LeviCivitaOrder.contMDiffAt_leviCivita_apply`.** That theorem stays: it is
  quoted by four files, and `ERRATUM 465`'s rule is to compare what each establishes rather than
  only its hypotheses — the Levi-Civita proof is self-contained where this one routes through a
  class with an instance to discharge.
* **NOTHING ABOUT `ω`.** `k` is a natural number here, because the neighbourhood characterisation
  `contMDiffAt_iff_contMDiffOn_nhds` is not available at the analytic order.
⚠ **`∞` IS REACHED ON 2026-09-11 AND `ω` IS NOT, kept as written** (`ERRATUM 505`):
`CovariantOrderInfty` states this chain's results at the **smooth** order, on the strength of
Mathlib's *`C^∞` is `C^n` for every natural `n`* characterisation. **The sentence is still true of
`ω`**, which has no such characterisation — which is the reason this very paragraph gives — and true
of this file, which proves nothing at either.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a normed space `E` over `ℝ` with
`[CompleteSpace E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`
and `[IsManifold I 3 M]`, `{k : ℕ}` with `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]`, and the
connection. `KoszulOrder.isManifold_succ` and `contMDiffVectorBundle_succ` are the two local
instances — the `C^(k+1)` manifold and the `C^(k+1)` tangent bundle, which the total space's own
manifold structure needs. The two abstract theorems take `[IsLocallyCk k cov]`; the Levi-Civita
corollary takes the metric instances instead and no class hypothesis, because the instance is
found. Three declarations, three `omit` lines, and the linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderApply

open Bundle Manifold VectorField FiberBundle Set CurvatureTensorial CovariantOrderClass
  KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two
  KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M] in
/-- **`∇Z` IS A `C^k` SECTION OF `Hom(TM, TM)`** for `Z` of class `C^(k+1)` at the point, for
**any** connection of class `C^k` on every open set. -/
theorem contMDiffAt_cov_hom [IsLocallyCk (k : WithTop ℕ∞) cov]
    {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (cov Z y)) x := by
  obtain ⟨u, hu, hZu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hZ
  have hZ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' E y (Z y)) (interior u) := hZu.mono interior_subset
  have h := (IsLocallyCk.on_open (k := (k : WithTop ℕ∞)) (cov := cov) (interior u)
    isOpen_interior).contMDiff hZ'
  exact h.contMDiffAt (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hu))

omit [CompleteSpace E] [IsManifold I 3 M] in
/-- **AND `∇_Y Z` IS A `C^k` SECTION OF `TM`**, for `Y` of class `C^k` and `Z` of class `C^(k+1)`
at the point. -/
theorem contMDiffAt_covApply [IsLocallyCk (k : WithTop ℕ∞) cov]
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt (k : WithTop ℕ∞) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (covApply cov Y Z)) x :=
  ContMDiffAt.clm_bundle_apply (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (contMDiffAt_cov_hom cov hZ) hY

section LeviCivita

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

omit [IsManifold I 3 M] in
/-- **THE LEVI-CIVITA CASE, AND IT ASKS LESS OF THE DIRECTION FIELD THAN THE ESTATE'S OWN
VERSION**: `LeviCivitaOrder.contMDiffAt_leviCivita_apply` wants both fields at `C^(k+1)`, and the
abstract theorem above wants the direction at `C^k` only. The Levi-Civita connection satisfies the
class by `CovariantOrderClass.isLocallyCk_leviCivita`, so this is a specialisation and not a second
proof. -/
theorem contMDiffAt_leviCivita_apply' {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt (k : WithTop ℕ∞) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (covApply (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) Y Z)) x :=
  contMDiffAt_covApply _ hY hZ

end LeviCivita

end CovariantOrderApply
