import FieldSignReflection
import SymmetricEigenOrthogonal

/-!
# Distinct eigenvalues give distinct symmetries, which is the count the chain has been missing

`FieldEigenReflection` gives one reflection per eigenvector of `green`; `FieldSignReflection` added
a second concrete one and closed on the same gap both units named: **two is not a count.** The
missing statement was never about producing more eigenvectors. It is that **different eigenvectors
give different reflections** — without that, a family indexed by eigenvectors could collapse to a
single map.

**It does not collapse, and the reason is orthogonality.** A reflection fixes its own axis; a
reflection along a vector orthogonal to that axis negates it. So two reflections along orthogonal
non-zero vectors are different maps, and `SymmetricEigenOrthogonal.dotProduct_eq_zero_of_eigen_ne`
makes eigenvectors at different eigenvalues orthogonal.

`PROOF_STRATEGY` §6 question 3 again: the previous unit was a `B` and this is the `B → C` retry.

## What is proved

**`eigenRefl_mulVec`** — `eigenRefl v *ᵥ x = (2⟪v,x⟫/⟪v,v⟫) · v − x`, the reflection acting on a
vector. **`eigenRefl_mulVec_self`** — it fixes its own axis, and
**`eigenRefl_mulVec_of_orthogonal`** — it negates anything orthogonal to it.

**`eigenRefl_ne_of_orthogonal`** — so reflections along orthogonal non-zero vectors are **distinct
matrices**.

**`eigenRefl_ne_of_eigen_ne`** — hence reflections along eigenvectors of `green` at **different
eigenvalues** are distinct, at every finite graph and every `m ≠ 0`.

**`gaussianField_symmetries_of_eigen_ne`** — the statement in the form the chain wanted: two
different eigenvalues give two **different** isometries, each leaving the Gaussian field invariant.

## What is NOT here

**No cardinality is computed.** This gives an injection from distinct eigenvalues to distinct
symmetries; turning that into a number on a named graph means counting the spectrum, which for the
torus is `MassiveTorusSpectrum.spectrum_real_eq_range_nuR` and for the box is `BoxLapSpectrum`.
**That instantiation is not attempted and no cost is claimed** (`ERRATUM 246`).
⚠ **THE GOAL WAS REACHED BY ANOTHER ROUTE, 2026-09-05/06, and this paragraph is kept as written**
(`ERRATUM 94`). `FieldLineCount.card_symmetries` counts the isometric symmetries on a line at
`2^(m+1)` and `FieldSignGroup.signMulEquiv` makes that group `(ℤ/2)^(m+1)`. **Neither goes through
this file's injection**, and the instantiation disclaimed above — counting the spectrum and pushing
it through these reflections — **is still not attempted.** Both sentences are true; they are about
different routes to the same number.

**Distinct eigenvectors at the SAME eigenvalue are not separated.** Two independent eigenvectors in
one eigenspace are generally not orthogonal, and this argument says nothing about them — which is
also why it cannot see the rotations that live inside a degenerate eigenspace. **The commutant is
still not described.**

> ⚠ **THE PAIR THIS PARAGRAPH SAYS NOTHING ABOUT IS NOW EXHIBITED, AND THE PARAGRAPH IS KEPT AS
> WRITTEN** (`ERRATUM 94`, 2026-09-05).
> `FieldComponentEigen.exists_orthogonal_eigenpair_of_not_reachable` gives two **orthogonal**
> non-zero eigenvectors of `green` at the same eigenvalue `m⁻²` on any disconnected graph — the
> indicators of a component and its complement. **Every word above stays true**: this file's
> argument still separates nothing inside an eigenspace, and it is the pair that is new, not a
> repair to the argument. The commutant is still not described and no rotation is built.
> ⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 459`):
> `FieldCommutantSpectral.mul_green_comm_iff` describes it — a matrix commutes with `green` **iff**
> it carries every eigenvector to an eigenvector at the same eigenvalue — and
> `FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` makes that a description of
> the symmetries of the measure and not of a subset of them. What is still missing is the
> `∏ᵢ O(dᵢ)` packaging, not a characterisation.

**No new symmetry.** Every map here is one `FieldEigenReflection` already supplied; what is new is
that they are pairwise different.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldReflectionCount

open Matrix GraphLaplacian FieldEigenReflection

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The reflection, acting on a vector -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem vecMulVec_mulVec (v x : V → ℝ) (i : V) :
    (Matrix.vecMulVec v v *ᵥ x) i = v i * (v ⬝ᵥ x) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableRel G.Adj] in
theorem eigenRefl_mulVec (v x : V → ℝ) :
    eigenRefl v *ᵥ x = (2 / (v ⬝ᵥ v) * (v ⬝ᵥ x)) • v - x := by
  ext i
  simp only [eigenRefl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, vecMulVec_mulVec]
  ring

omit [DecidableRel G.Adj] in
/-- **A REFLECTION FIXES ITS OWN AXIS.** -/
theorem eigenRefl_mulVec_self {v : V → ℝ} (hv : v ⬝ᵥ v ≠ 0) : eigenRefl v *ᵥ v = v := by
  rw [eigenRefl_mulVec, div_mul_cancel₀ _ hv]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableRel G.Adj] in
/-- **AND NEGATES ANYTHING ORTHOGONAL TO IT.** -/
theorem eigenRefl_mulVec_of_orthogonal {v x : V → ℝ} (h : v ⬝ᵥ x = 0) :
    eigenRefl v *ᵥ x = -x := by
  rw [eigenRefl_mulVec, h, mul_zero]
  ext i
  simp

/-! ## 2. So orthogonal axes give different reflections -/

omit [DecidableRel G.Adj] in
/-- **REFLECTIONS ALONG ORTHOGONAL NON-ZERO VECTORS ARE DIFFERENT MATRICES.** One fixes `v`; the
other negates it. -/
theorem eigenRefl_ne_of_orthogonal {u v : V → ℝ} (hv : v ⬝ᵥ v ≠ 0) (horth : u ⬝ᵥ v = 0) :
    eigenRefl u ≠ eigenRefl v := by
  intro hcontra
  have h1 : eigenRefl v *ᵥ v = v := eigenRefl_mulVec_self hv
  have h2 : eigenRefl u *ᵥ v = -v := eigenRefl_mulVec_of_orthogonal horth
  rw [hcontra, h1] at h2
  have hzero : v = 0 := by
    funext i
    have hi := congrFun h2 i
    simp only [Pi.neg_apply] at hi
    change v i = 0
    linarith
  exact hv (by rw [hzero]; simp)

/-! ## 3. And different eigenvalues give orthogonal axes -/

/-- **REFLECTIONS ALONG EIGENVECTORS AT DIFFERENT EIGENVALUES ARE DISTINCT.** -/
theorem eigenRefl_ne_of_eigen_ne (hm : m ≠ 0) {u v : V → ℝ} {a b : ℝ}
    (hu : green G m *ᵥ u = a • u) (hv : green G m *ᵥ v = b • v) (hab : a ≠ b)
    (hv0 : v ⬝ᵥ v ≠ 0) : eigenRefl u ≠ eigenRefl v :=
  eigenRefl_ne_of_orthogonal hv0
    (SymmetricEigenOrthogonal.dotProduct_eq_zero_of_eigen_ne (green_isSymm G hm) hu hv hab)

/-- **THE STATEMENT THE CHAIN WANTED**: two different eigenvalues of the propagator give two
**different** isometries, each leaving the Gaussian field invariant. -/
theorem gaussianField_symmetries_of_eigen_ne (hm : m ≠ 0) {u v : V → ℝ} {a b : ℝ}
    (hu : green G m *ᵥ u = a • u) (hv : green G m *ᵥ v = b • v) (hab : a ≠ b)
    (hu0 : u ⬝ᵥ u ≠ 0) (hv0 : v ⬝ᵥ v ≠ 0) :
    eigenRefl u ≠ eigenRefl v ∧
      MeasureTheory.Measure.map
          (FieldHouseholder.reflIsometry (eigenRefl_isSymm u) (eigenRefl_mul_self hu0))
          (gaussianField G m) = gaussianField G m ∧
      MeasureTheory.Measure.map
          (FieldHouseholder.reflIsometry (eigenRefl_isSymm v) (eigenRefl_mul_self hv0))
          (gaussianField G m) = gaussianField G m :=
  ⟨eigenRefl_ne_of_eigen_ne hm hu hv hab hv0,
    gaussianField_map_eigenRefl hm hu0 hu, gaussianField_map_eigenRefl hm hv0 hv⟩

end FieldReflectionCount
