import CovariantOrderEndo
import CovariantOrderHom
import CurvatureCovDeriv

/-!
# `∇R` for ANY connection of class `C^(k+1)`, and its six slot laws

**This is the first file of the job `ERRATUM 498` priced, and the erratum's point was that it is a
RE-DEFINITION and not a re-pointing.** `CurvatureCovDeriv.covRiemann` is
`(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)` with `A y = R(Y y, Z y)`, and the Levi-Civita
connection is written into its **body** — three times — rather than quoted from a lemma. So the
generalisation cannot re-point anything: the object has to be defined again over an arbitrary
connection, and every theorem about it re-proved. That is done here for the definition and all six
of its slot laws.

**AND THE RE-PROVING WAS FREE, WHICH IS THE MEASUREMENT WORTH RECORDING — AND IT IS A MEASUREMENT,
NOT A RECOLLECTION.** Extracted from `CurvatureCovDeriv`'s declarations with a script: they use
**ten** estate-level names, besides Mathlib's `ContinuousLinearMap` and `Pi` lemmas, and the
connection itself. **Four are Levi-Civita-specific** — `CurvatureEndoOrder.mdiffHomAt_riemann`,
`CurvatureEndoOrder.homCovFun_riemann_apply`, `LeviCivitaRegular.riemann` and
`LeviCivitaRegular.riemann_swap` — and each is already answered: the first two are exactly what
**entry 122**, two units earlier, made abstract (`CovariantOrderEndo.mdiffHomAt_curvEndo` and
`.homCovFun_curvEndo_apply`), `riemann` is an `abbrev` for `curvEndo leviCivita` so the object was
never specific, and `riemann_swap`'s general form `CurvatureTensor.curvEndo_swap` has existed all
along. The remaining six — the four `curvEndo` slot laws, `HomCovariant.homCovFun` and its
`isCovariantDerivativeOn_homCovFun` — never mentioned a metric, nor does the connection's own
`isCovariantDerivativeOn`. **So the six proofs below are the six above with three LEMMA
names substituted** — plus the object's own spelling, which the generalisation forces and which is
the `abbrev` — and the file priced as the expensive half of the residue cost a substitution, because
entry 122 had done the work.

**AND ENTRY 123 CONTRIBUTED NOTHING TO THIS FILE**, which is worth saying rather than implying: its
theorem is the regularity of the induced connection, and what this file needs from that direction is
the induced connection's *algebra* — `isCovariantDerivativeOn_homCovFun`, which `HomCovariant` has
had all along. 123 is a prerequisite for `∇R`'s REGULARITY, which is not proved here.

## What is proved

**`covRiemann`** — the definition, over an arbitrary `cov`: the induced derivative of the curvature
field minus the two correction terms. It asks only `CurvatureTensor.IsLocallyC1 cov`, which is what
`curvEndo` is defined under.

**`covRiemann_eq`** — **THE IDENTIFICATION, AND IT IS `rfl`**: at `cov = leviCivita` this is
`CurvatureCovDeriv.covRiemann`, because `LeviCivitaRegular.riemann` is an `abbrev` for
`curvEndo leviCivita`. So the general object is not merely *analogous* to the estate's `∇R` — it is
the same term, and the specialisation is checked by the elaborator rather than asserted in prose.

**`covRiemann_swap`** — antisymmetry in the two directions.

**`covRiemann_smul_left`**, **`covRiemann_add_left`**, **`covRiemann_smul_right`**,
**`covRiemann_add_right`** — additive and `f`-homogeneous in each direction field **as an operation
on sections**, with the Leibniz terms cancelling: the `df ⊗ ·` the induced connection produces is
exactly the one the correction term produces, which is why those two subtractions are the right
ones. This is the content, and it is what makes the object a candidate for a tensor.

**`covRiemann_apply`** — **THE CLASSICAL FORMULA**, the line a reader checks against a textbook:
`(∇_u R)(Y, Z)W = ∇_u (R(Y, Z)W) − R(Y, Z)(∇_u W) − R(∇_u Y, Z)W − R(Y, ∇_u Z)W`, for any
connection of class `C^(k+1)` with `k ≠ 0`.

## What is NOT here

* **TENSORIALITY IS NOT PROVED HERE.** That `(∇_u R)(Y, Z)` depends on `Y` and `Z` only through
  `Y x` and `Z x` is a separate statement — `CurvatureCovTensor`'s, for the Levi-Civita connection —
  and it is the next file of this re-definition, not this one. The slot laws below are the
  hypotheses that statement consumes, so what is here is its input and not the statement itself.
  **Not attempted, no cost claimed** (`ERRATUM 246`).
* **NOTHING ON VECTORS RATHER THAN FIELDS**, which is `CurvatureCovBundle`'s, and nothing bundled as
  a continuous multilinear map.
* **NO SECOND BIANCHI IDENTITY**, which is `CurvatureBianchiSecond`'s and needs the cyclic sum.
* **NO REGULARITY OF `∇R`, AND THE SHIFT IT NEEDS IS NOT MISSING — IT IS LEVI-CIVITA-ONLY**
  (`ERRATUM 499`, which corrects three of this campaign's own sentences on the point).
  `CurvatureCovOrder.contMDiffAt_covRiemann_hom` makes `y ↦ (∇_X R)(Y, Z)(y)` a `C^k` section of
  `Hom(TM, TM)` for a `C^(k+3)` metric on a `C^(k+4)` manifold, doing precisely the order
  bookkeeping that `HomCovariantOrder` named as what stood in the way. What does **not** exist is
  the abstract version, and entries 122, 123 and this file are its three legs: the curvature's
  `Hom`-regularity, the induced connection's regularity, and `∇R` itself. **Not attempted here, no
  cost claimed** (`ERRATUM 246`) — it is the next unit.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.

**No wall moves. No published tag moves.**

**THE NAMES COLLIDE WITH `CurvatureCovDeriv`'S ON PURPOSE**, all seven of them, and `covRiemann_eq`
is the reason it is safe: the two are the same object, this one more general, and the identification
is proved by `rfl` rather than described. `newnames_scan.py` asks the question for each; the answer
is that theorem, and it is recorded in `newnames_accepted.txt` with this sentence.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`, from the signatures because entry 122 found
a header and its binders disagreeing): `E` normed over `ℝ` with `[CompleteSpace E]` and
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]`, `[IsManifold I 3 M]`, `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`,
`[CurvatureTensor.IsLocallyC1 cov]` and — for the six slot laws, **not** the definition and **not**
the identification — `[CovariantOrderClass.IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]` with `k ≠ 0`.
The `C³` binder is `curvEndo`'s existence condition, as in entry 122. **The definition takes no
order class and no `k` at all**, and **the identification takes the metric only at literal order
`2`** — its proof is `rfl`, so it needs the two objects to exist and nothing more, which is why the
`C^(k+2)`-metric binder was removed from that section rather than carried.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCovDeriv

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CurvatureTensor.IsLocallyC1 cov]

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureTensor.contMDiffVectorBundle_two KoszulManifold.finDimTangent

/-- **THE COVARIANT DERIVATIVE OF THE CURVATURE OF AN ARBITRARY CONNECTION, ON TWO DIRECTION
FIELDS**: `(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)` where `A y = R(Y y, Z y)`. The two
subtractions are what differentiating the composite does not have: that carries `Y` and `Z` inside
it. `CurvatureCovDeriv.covRiemann` is this with the Levi-Civita connection written into the body;
`covRiemann_eq` below is the identification, by `rfl`. -/
noncomputable def covRiemann (Y Z : Π x : M, TangentSpace I x) (x : M) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (Y y) (Z y)) x u
    - curvEndo cov x (cov Y x u) (Z x)
    - curvEndo cov x (Y x) (cov Z x u)

variable [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]

/-- **ANTISYMMETRY IN THE TWO DIRECTIONS.** -/
theorem covRiemann_swap {Y Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann cov Y Z x u = - covRiemann cov Z Y x u := by
  have hA := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hZ hY
  have hfield : (fun y ↦ curvEndo cov y (Y y) (Z y))
      = -(fun y ↦ curvEndo cov y (Z y) (Y y)) := by
    funext y
    exact curvEndo_swap cov y (Y y) (Z y)
  simp only [covRiemann, hfield]
  rw [show (-(fun y ↦ curvEndo cov y (Z y) (Y y)))
      = ((-1 : ℝ) • fun y ↦ curvEndo cov y (Z y) (Y y)) by
    funext y; simp,
    (HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).smul_const
      (-1 : ℝ) hA (mem_univ x)]
  rw [curvEndo_swap cov x (cov Y x u) (Z x), curvEndo_swap cov x (Y x) (cov Z x u)]
  ext w
  simp
  abel

/-- **THE LEIBNIZ TERMS CANCEL IN THE FIRST DIRECTION**, which is why the two subtractions in
`covRiemann` are the right ones: the `df ⊗ ·` the induced connection produces is exactly the one the
first correction term produces. -/
theorem covRiemann_smul_left {Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M} (hk : k ≠ 0)
    (hf : MDiffAt f x) (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann cov (f • Y) Z x u = f x • covRiemann cov Y Z x u := by
  have hA := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY hZ
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ curvEndo cov y ((f • Y) y) (Z y))
      = f • fun y ↦ curvEndo cov y (Y y) (Z y) := by
    funext y
    exact curvEndo_smul_left cov y (f y) (Y y) (Z y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).leibniz hA hf
      (mem_univ x),
    cov.isCovariantDerivativeOn.leibniz hYd hf (mem_univ x)]
  have h3 : curvEndo cov x ((f • Y) x) (cov Z x u)
      = f x • curvEndo cov x (Y x) (cov Z x u) :=
    curvEndo_smul_left cov x (f x) (Y x) (cov Z x u)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, curvEndo_add_left, curvEndo_smul_left, h3]
  ext w
  simp
  module

/-- **ADDITIVITY IN THE FIRST DIRECTION.** -/
theorem covRiemann_add_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hY' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y') x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann cov (Y + Y') Z x u = covRiemann cov Y Z x u + covRiemann cov Y' Z x u := by
  have hA := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY hZ
  have hA' := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY' hZ
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have hYd' : MDiffAt (T% Y') x := hY'.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ curvEndo cov y ((Y + Y') y) (Z y))
      = (fun y ↦ curvEndo cov y (Y y) (Z y)) + fun y ↦ curvEndo cov y (Y' y) (Z y) := by
    funext y
    exact curvEndo_add_left cov y (Y y) (Y' y) (Z y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).add hA hA'
      (mem_univ x),
    cov.isCovariantDerivativeOn.add hYd hYd' (mem_univ x)]
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, curvEndo_add_left]
  ext w
  simp
  abel

/-- **THE CLASSICAL FORMULA**, which is what a reader checks against a textbook:
`(∇_u R)(Y, Z)W = ∇_u (R(Y, Z)W) − R(Y, Z)(∇_u W) − R(∇_u Y, Z)W − R(Y, ∇_u Z)W`. -/
theorem covRiemann_apply {Y Z W : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (hW : MDiffAt (T% W) x)
    (u : TangentSpace I x) :
    covRiemann cov Y Z x u (W x)
      = cov (fun y ↦ curvEndo cov y (Y y) (Z y) (W y)) x u
        - curvEndo cov x (Y x) (Z x) (cov W x u)
        - curvEndo cov x (cov Y x u) (Z x) (W x)
        - curvEndo cov x (Y x) (cov Z x u) (W x) := by
  simp only [covRiemann, ContinuousLinearMap.sub_apply,
    CovariantOrderEndo.homCovFun_curvEndo_apply cov hk hY hZ hW u]

/-- **THE SAME CANCELLATION IN THE SECOND DIRECTION.** -/
theorem covRiemann_smul_right {Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M} (hk : k ≠ 0)
    (hf : MDiffAt f x) (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann cov Y (f • Z) x u = f x • covRiemann cov Y Z x u := by
  have hA := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY hZ
  have hZd : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ curvEndo cov y (Y y) ((f • Z) y))
      = f • fun y ↦ curvEndo cov y (Y y) (Z y) := by
    funext y
    exact curvEndo_smul_right cov y (f y) (Y y) (Z y)
  have h3 : curvEndo cov x (cov Y x u) ((f • Z) x)
      = f x • curvEndo cov x (cov Y x u) (Z x) :=
    curvEndo_smul_right cov x (f x) (cov Y x u) (Z x)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).leibniz hA hf
      (mem_univ x),
    cov.isCovariantDerivativeOn.leibniz hZd hf (mem_univ x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, curvEndo_add_right, curvEndo_smul_right, h3]
  ext w
  simp
  module

/-- **ADDITIVITY IN THE SECOND DIRECTION.** -/
theorem covRiemann_add_right {Y Z Z' : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hZ' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z') x) (u : TangentSpace I x) :
    covRiemann cov Y (Z + Z') x u = covRiemann cov Y Z x u + covRiemann cov Y Z' x u := by
  have hA := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY hZ
  have hA' := CovariantOrderEndo.mdiffHomAt_curvEndo cov hk hY hZ'
  have hZd : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  have hZd' : MDiffAt (T% Z') x := hZ'.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ curvEndo cov y (Y y) ((Z + Z') y))
      = (fun y ↦ curvEndo cov y (Y y) (Z y)) + fun y ↦ curvEndo cov y (Y y) (Z' y) := by
    funext y
    exact curvEndo_add_right cov y (Y y) (Z y) (Z' y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).add hA hA'
      (mem_univ x),
    cov.isCovariantDerivativeOn.add hZd hZd' (mem_univ x)]
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, curvEndo_add_right]
  ext w
  simp
  abel

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- **THE IDENTIFICATION, AND IT IS `rfl`**: at the Levi-Civita connection this object is
`CurvatureCovDeriv.covRiemann`, because `LeviCivitaRegular.riemann` is an `abbrev` for
`curvEndo leviCivita`. So the general definition is not analogous to the estate's `∇R` — it is the
same term, and every theorem above specialises to that file's by rewriting along this. -/
theorem covRiemann_eq (Y Z : Π x : M, TangentSpace I x) (x : M) (u : TangentSpace I x) :
    covRiemann (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) Y Z x u
      = CurvatureCovDeriv.covRiemann Y Z x u := rfl

end LeviCivita

end CovariantOrderCovDeriv
