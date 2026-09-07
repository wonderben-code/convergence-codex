import CurvatureTensor
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Ricci and scalar curvature of a locally `C¹` connection: the traces of `R(v, w)`

`CurvatureTensor` built the curvature endomorphism `R(v, w) : T_xM → T_xM` of any covariant
derivative on the tangent bundle that is `C¹` on every open set, and said in its fence that no
trace was taken. This file takes the two traces. **The Ricci curvature** is the trace of the first
slot, `Ric(w, z) = tr (v ↦ R(v, w) z)` (`ricci`), bilinear in `(w, z)`; in any orthonormal basis
it is `∑ᵢ ⟪eᵢ, R(eᵢ, w) z⟫` (`ricci_eq_sum_inner`). **The scalar curvature** is the metric trace of
the Ricci form (`scalar`), defined in the standard orthonormal basis of the tangent space and
shown to be **independent of the orthonormal basis** (`scalar_eq_sum`): it is the trace of the
Ricci endomorphism `w ↦ Ric(w, ·)♯` (`ricciEndo`, `scalar_eq_trace`), the metric raising one
index through `KoszulManifold.riesz`. The trace is Mathlib's `LinearMap.trace`, and the sum
formulas are its `trace_eq_sum_inner`; nothing else is needed, which is why this file is short.

## What is proved

**`curvLeft`, `curvLeft_apply`** — `v ↦ R(v, w) z` as a linear map, from `CurvatureTensor`'s
bilinearity; **`curvLeft_add_left`** and three companions — its bilinearity in `(w, z)`.

**`ricci`** — **the Ricci curvature** `Ric(w, z) = tr (v ↦ R(v, w) z)`; **`ricci_add_left`**,
**`ricci_smul_left`**, **`ricci_add_right`**, **`ricci_smul_right`** — bilinear.

**`ricci_eq_sum_inner`** — `Ric(w, z) = ∑ᵢ ⟪eᵢ, R(eᵢ, w) z⟫` for every orthonormal basis.

**`ricciCLM`, `ricciEndo`, `inner_ricciEndo`** — `Ric(w, ·)` as a continuous linear form and its
metric dual, with `⟪Ric(w, ·)♯, z⟫ = Ric(w, z)`.

**`sum_ricci_diag_eq_trace`** — `∑ᵢ Ric(eᵢ, eᵢ)` is the trace of the Ricci endomorphism, for
every orthonormal basis.

**`scalar`, `scalar_eq_trace`, `scalar_eq_sum`** — **the scalar curvature**, its expression as a
trace, and **its independence of the orthonormal basis**.

## What is NOT here

**NO SYMMETRY OF THE RICCI FORM.** `Ric(w, z) = Ric(z, w)` needs the pair symmetry of the
curvature of a metric connection, which needs the first Bianchi identity, which is not in the
estate; `ricci` here is a bilinear form with no symmetry claimed, and for a connection that is
not metric it need not be symmetric.

**NOTHING ABOUT `leviCivita`, AND SO NO RICCI OR SCALAR CURVATURE OF A METRIC.** The connection is
any `IsLocallyC1` one, and `KoszulManifold.leviCivita` is not shown to be one. The scalar
curvature here is the metric trace of the Ricci form of an arbitrary such connection, with the
metric and the connection unrelated; the geometer's scalar curvature is the case
`cov = leviCivita`, which this estate cannot yet write. **Not attempted, no cost claimed**
(`ERRATUM 246`). ⚠ By entry 72, later the same day, the estate writes it:
`LeviCivitaRegular.ricci` and `LeviCivitaRegular.scalar` are `ricci leviCivita` and
`scalar leviCivita` under `LeviCivitaRegular.isLocallyC1_leviCivita`, so the geometer's scalar
curvature of a `C²` metric is in the estate; the sentence is kept as written (`ERRATUM 94`).

**NO BRIDGE TO THE ALGEBRAIC VOCABULARY.** `AlgebraicCurvature.ricci` and `scal` (the Lovelock
files, `WALLS` §W5.1 §5h) are traces of an abstract algebraic curvature on `Fin n → ℝ`; no
declaration relates them to `ricci` and `scalar` here.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): those of `CurvatureTensor` —
`[IsManifold I 3 M]`, `[IsLocallyC1 cov]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]` —
throughout, finite dimension now for the trace itself;
`[RiemannianBundle (fun x ↦ TangentSpace I x)]` from `ricci_eq_sum_inner` on. One new Mathlib
import, the file of `LinearMap.trace_eq_sum_inner`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace RicciScalar

open Bundle Manifold VectorField FiberBundle Set CurvatureTensorial CurvatureTensor
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) [IsLocallyC1 cov]

attribute [local instance] KoszulManifold.finDimTangent

/-- `v ↦ R(v, w) z`, as a linear map on the tangent space. -/
noncomputable def curvLeft (x : M) (w z : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := curvEndo cov x v w z
  map_add' v v' := by rw [curvEndo_add_left, ContinuousLinearMap.add_apply]
  map_smul' c v := by rw [curvEndo_smul_left, ContinuousLinearMap.smul_apply, RingHom.id_apply]

theorem curvLeft_apply (x : M) (w z v : TangentSpace I x) :
    curvLeft cov x w z v = curvEndo cov x v w z := rfl

/-- **The Ricci curvature** `Ric(w, z) = tr (v ↦ R(v, w) z)`. -/
noncomputable def ricci (x : M) (w z : TangentSpace I x) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (curvLeft cov x w z)

theorem curvLeft_add_left (x : M) (w w' z : TangentSpace I x) :
    curvLeft cov x (w + w') z = curvLeft cov x w z + curvLeft cov x w' z := by
  ext v
  simp only [curvLeft_apply, LinearMap.add_apply, curvEndo_add_right,
    ContinuousLinearMap.add_apply]

theorem curvLeft_smul_left (x : M) (c : ℝ) (w z : TangentSpace I x) :
    curvLeft cov x (c • w) z = c • curvLeft cov x w z := by
  ext v
  simp only [curvLeft_apply, LinearMap.smul_apply, curvEndo_smul_right,
    ContinuousLinearMap.smul_apply]

theorem curvLeft_add_right (x : M) (w z z' : TangentSpace I x) :
    curvLeft cov x w (z + z') = curvLeft cov x w z + curvLeft cov x w z' := by
  ext v
  simp only [curvLeft_apply, LinearMap.add_apply, map_add]

theorem curvLeft_smul_right (x : M) (c : ℝ) (w z : TangentSpace I x) :
    curvLeft cov x w (c • z) = c • curvLeft cov x w z := by
  ext v
  simp only [curvLeft_apply, LinearMap.smul_apply, map_smul]

theorem ricci_add_left (x : M) (w w' z : TangentSpace I x) :
    ricci cov x (w + w') z = ricci cov x w z + ricci cov x w' z := by
  simp only [ricci, curvLeft_add_left, map_add]

theorem ricci_smul_left (x : M) (c : ℝ) (w z : TangentSpace I x) :
    ricci cov x (c • w) z = c • ricci cov x w z := by
  simp only [ricci, curvLeft_smul_left, map_smul]

theorem ricci_add_right (x : M) (w z z' : TangentSpace I x) :
    ricci cov x w (z + z') = ricci cov x w z + ricci cov x w z' := by
  simp only [ricci, curvLeft_add_right, map_add]

theorem ricci_smul_right (x : M) (c : ℝ) (w z : TangentSpace I x) :
    ricci cov x w (c • z) = c • ricci cov x w z := by
  simp only [ricci, curvLeft_smul_right, map_smul]

section Riemannian

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The Ricci curvature as a sum over an orthonormal basis: `Ric(w, z) = ∑ᵢ ⟪eᵢ, R(eᵢ, w) z⟫`. -/
theorem ricci_eq_sum_inner {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (w z : TangentSpace I x) :
    ricci cov x w z = ∑ i, ⟪b i, curvEndo cov x (b i) w z⟫ :=
  LinearMap.trace_eq_sum_inner _ b

/-- `Ric(w, ·)` as a continuous linear form. -/
noncomputable def ricciCLM (x : M) (w : TangentSpace I x) : TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ ricci cov x w z
      map_add' := fun z z' ↦ ricci_add_right cov x w z z'
      map_smul' := fun c z ↦ ricci_smul_right cov x c w z }

theorem ricciCLM_apply (x : M) (w z : TangentSpace I x) : ricciCLM cov x w z = ricci cov x w z :=
  rfl

/-- The Ricci endomorphism `w ↦ Ric(w, ·)♯`, the metric raising one index of the Ricci form. -/
noncomputable def ricciEndo (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun w := KoszulManifold.riesz I x (ricciCLM cov x w)
  map_add' w w' := by
    have h : ricciCLM cov x (w + w') = ricciCLM cov x w + ricciCLM cov x w' := by
      ext z
      simp only [ricciCLM_apply, ContinuousLinearMap.add_apply, ricci_add_left]
    rw [h, map_add]
  map_smul' c w := by
    have h : ricciCLM cov x (c • w) = c • ricciCLM cov x w := by
      ext z
      simp only [ricciCLM_apply, ContinuousLinearMap.smul_apply, ricci_smul_left]
    rw [h, map_smul, RingHom.id_apply]

theorem inner_ricciEndo (x : M) (w z : TangentSpace I x) :
    ⟪ricciEndo cov x w, z⟫ = ricci cov x w z :=
  KoszulManifold.inner_riesz x _ z

/-- **The metric trace of the Ricci form is independent of the orthonormal basis**: for every
orthonormal basis `b`, `∑ᵢ Ric(bᵢ, bᵢ)` is the trace of the Ricci endomorphism. -/
theorem sum_ricci_diag_eq_trace {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, ricci cov x (b i) (b i) = LinearMap.trace ℝ (TangentSpace I x) (ricciEndo cov x) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, inner_ricciEndo]

/-- **The scalar curvature**: the metric trace of the Ricci form, `S = ∑ᵢ Ric(eᵢ, eᵢ)` in the
standard orthonormal basis, which is the trace of the Ricci endomorphism. -/
noncomputable def scalar (x : M) : ℝ :=
  ∑ i, ricci cov x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

theorem scalar_eq_trace (x : M) :
    scalar cov x = LinearMap.trace ℝ (TangentSpace I x) (ricciEndo cov x) :=
  sum_ricci_diag_eq_trace cov x _

/-- **The scalar curvature in any orthonormal basis.** -/
theorem scalar_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    scalar cov x = ∑ i, ricci cov x (b i) (b i) := by
  rw [scalar_eq_trace, sum_ricci_diag_eq_trace]

end Riemannian

end RicciScalar
