import MassiveSpectrumRange

/-!
# The propagator's spectrum, both ends, at every finite graph

`GreenNormExact` settled `‖green G m‖ = (m²)⁻¹` and fenced the other end in its own words:

> *"**AND IT SAYS NOTHING ABOUT `(√green)⁻¹`.** `SqrtGreenOpNorm` bounds
> `‖(CFC.sqrt (green G m))⁻¹‖`, which is governed by the SMALLEST eigenvalue of `green`; this is
> the largest. **The two ends of the spectrum are different questions and only one of them is
> settled here.**"*

The other end is settled here, and it is the previous unit read through the inverse:

```
IsLeast     {μ | ∃ x ≠ 0, green G m *ᵥ x = μ • x}  (‖massive G m‖)⁻¹
IsGreatest  {μ | ∃ x ≠ 0, green G m *ᵥ x = μ • x}  (m²)⁻¹
```

at every finite nonempty graph and every `m ≠ 0`, with no spectrum computed anywhere. The upper end
agrees with `GreenNormExact.norm_green_eq` — `(m²)⁻¹` is `‖green G m‖` — and the lower end is the
reciprocal of `OpNormTopEigenvalue`'s top, which on a `Δ`-regular graph with a two-colourable
component is `(2Δ + m²)⁻¹` by `LaplacianNormSharp`.

## The transfer lemma, which is what was actually missing

**`mulVec_smul_inv_iff`** — for an invertible `A` and `μ ≠ 0`, `x` is an eigenvector of `A` at
`μ` **iff** it is an eigenvector of `A⁻¹` at `μ⁻¹`. Probed 2026-09-03 before this file was
written: `μ⁻¹` occurred in **no** `paper_f/` statement, `nonsing_inv` never met `mulVec … smul`
in one, and every spectral statement in this estate is about `massive`, `lapMatrix`,
`signlessLap`, an adjacency matrix or a transfer matrix — **none about an inverse**.
`CycleLaplacianSpectrum.cx_green_mulVec_chi` computes the propagator's eigenvalues on the cycle
from the characters, which is a family and a computation rather than a transfer.

## What is NOT here

**No multiplicity, and no claim that these are the only two ends worth having.** The set is
bracketed and not enumerated; nothing here counts eigenvalues or identifies eigenvectors beyond
the constants that `GreenExpansion.green_mulVec_one` already supplies at the top.

**Nothing about `(√green)⁻¹`.** The fence quoted above is about `SqrtGreenOpNorm`'s object, which is
a norm of an operator built by continuous functional calculus; this bounds the propagator's own
spectrum. **The two are related by a square root that is not taken here**, and `SqrtGreenOpNorm` is
neither used nor superseded.

**Not about a measure or a field**, and **no wall moves** — `W1` asks for a lower bound on the cross
form (`WALLS.md` §W1.5), a different object on a different operator.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenSpectrumRange

open Matrix GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Eigenvectors transfer to the inverse, at the reciprocal eigenvalue -/

/-- **AN EIGENVECTOR OF `A` AT `μ ≠ 0` IS AN EIGENVECTOR OF `A⁻¹` AT `μ⁻¹`**, and conversely. No
symmetry and no positivity; only invertibility and `μ ≠ 0`. -/
theorem mulVec_smul_inv_iff {A : Matrix V V ℝ} (hA : IsUnit A.det) {μ : ℝ} (hμ : μ ≠ 0)
    (x : V → ℝ) : A *ᵥ x = μ • x ↔ A⁻¹ *ᵥ x = μ⁻¹ • x := by
  constructor
  · intro h
    have h1 : A⁻¹ *ᵥ (A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun v : V → ℝ => μ⁻¹ • v) h1
    simpa [smul_smul, inv_mul_cancel₀ hμ] using h2
  · intro h
    have h1 : A *ᵥ (A⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun v : V → ℝ => μ • v) h1
    simpa [smul_smul, mul_inv_cancel₀ hμ] using h2

/-! ## 2. Both ends for the propagator -/

/-- **THE GREATEST EIGENVALUE OF THE PROPAGATOR IS `(m²)⁻¹`**, at every finite nonempty graph.
It is `‖green G m‖` by `GreenNormExact.norm_green_eq`, and it is the reciprocal of
`MassiveSpectrumRange.isLeast_eigenvalue_massive`. -/
theorem isGreatest_eigenvalue_green [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℝ} (hm : m ≠ 0) :
    IsGreatest {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ green G m *ᵥ x = μ • x} ((m ^ 2)⁻¹) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hdet : IsUnit (massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit G hm)
  obtain ⟨⟨x, hx0, hx⟩, hub⟩ := MassiveSpectrumRange.isLeast_eigenvalue_massive G m
  refine ⟨⟨x, hx0, ?_⟩, ?_⟩
  · simpa [GraphLaplacian.green] using (mulVec_smul_inv_iff hdet (ne_of_gt hm2) x).mp hx
  · rintro μ ⟨y, hy0, hy⟩
    have hyy : 0 < y ⬝ᵥ y := by
      refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hy0 (dotProduct_self_eq_zero.1 h0))
      rw [dotProduct]
      exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
    have hquad : 0 < y ⬝ᵥ green G m *ᵥ y :=
      (Matrix.posDef_iff_dotProduct_mulVec.mp (green_posDef G hm)).2 hy0
    rw [hy, dotProduct_smul, smul_eq_mul] at hquad
    have hμpos : 0 < μ := by
      rcases mul_pos_iff.mp hquad with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · linarith
    have hmass : massive G m *ᵥ y = μ⁻¹ • y := by
      refine (mulVec_smul_inv_iff hdet (inv_ne_zero (ne_of_gt hμpos)) y).mpr ?_
      rw [inv_inv]
      simpa [GraphLaplacian.green] using hy
    have hge : m ^ 2 ≤ μ⁻¹ := hub ⟨y, hy0, hmass⟩
    have hmul : μ * m ^ 2 ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hge (le_of_lt hμpos)
      rwa [mul_inv_cancel₀ (ne_of_gt hμpos)] at h
    rw [inv_eq_one_div, le_div_iff₀ hm2]
    linarith

/-! ## 3. The end `GreenNormExact` fenced: the smallest -/

/-- **THE LEAST EIGENVALUE OF THE PROPAGATOR IS `‖massive G m‖⁻¹`**, at every finite nonempty
graph. This is the end `GreenNormExact`'s header names and does not settle; the reciprocal is
`OpNormTopEigenvalue.isGreatest_eigenvalue_massive`, and on a `Δ`-regular graph with a
two-colourable component `LaplacianNormSharp` evaluates it as `(2Δ + m²)⁻¹`. -/
theorem isLeast_eigenvalue_green [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℝ} (hm : m ≠ 0) :
    IsLeast {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ green G m *ᵥ x = μ • x} (‖massive G m‖⁻¹) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hdet : IsUnit (massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit G hm)
  obtain ⟨⟨x, hx0, hx⟩, hub⟩ :=
    OpNormTopEigenvalue.isGreatest_eigenvalue_massive G hm
  have hnpos : 0 < ‖massive G m‖ := by
    have hge := MassiveSpectrumRange.isLeast_eigenvalue_massive (G := G) (m := m) |>.2
      ⟨x, hx0, hx⟩
    linarith
  refine ⟨⟨x, hx0, ?_⟩, ?_⟩
  · simpa [GraphLaplacian.green] using (mulVec_smul_inv_iff hdet (ne_of_gt hnpos) x).mp hx
  · rintro μ ⟨y, hy0, hy⟩
    have hquad : 0 < y ⬝ᵥ green G m *ᵥ y :=
      (Matrix.posDef_iff_dotProduct_mulVec.mp (green_posDef G hm)).2 hy0
    rw [hy, dotProduct_smul, smul_eq_mul] at hquad
    have hμpos : 0 < μ := by
      rcases mul_pos_iff.mp hquad with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · have hyy : 0 < y ⬝ᵥ y := by
          refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hy0 (dotProduct_self_eq_zero.1 h0))
          rw [dotProduct]
          exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
        linarith
    have hmass : massive G m *ᵥ y = μ⁻¹ • y := by
      refine (mulVec_smul_inv_iff hdet (inv_ne_zero (ne_of_gt hμpos)) y).mpr ?_
      rw [inv_inv]
      simpa [GraphLaplacian.green] using hy
    have hle : μ⁻¹ ≤ ‖massive G m‖ := hub ⟨y, hy0, hmass⟩
    have hmul : 1 ≤ μ * ‖massive G m‖ := by
      have h := mul_le_mul_of_nonneg_left hle (le_of_lt hμpos)
      rwa [mul_inv_cancel₀ (ne_of_gt hμpos)] at h
    rw [inv_eq_one_div, div_le_iff₀ hnpos]
    linarith

/-- **SO THE PROPAGATOR'S SPECTRUM SITS IN `[‖massive G m‖⁻¹, (m²)⁻¹]`, BOTH ENDS ATTAINED.** -/
theorem green_eigenvalue_mem_Icc [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℝ} (hm : m ≠ 0) {μ : ℝ}
    (hμ : μ ∈ {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ green G m *ᵥ x = μ • x}) :
    μ ∈ Set.Icc (‖massive G m‖⁻¹) ((m ^ 2)⁻¹) :=
  ⟨(isLeast_eigenvalue_green G hm).2 hμ, (isGreatest_eigenvalue_green G hm).2 hμ⟩

end GreenSpectrumRange
