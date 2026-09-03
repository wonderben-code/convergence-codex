import RayleighVariational
import ReflectionFailureCriterion
import CrossFormMatrix

/-!
# W1's necessary condition as one number

`ReflectionFailureCriterion.crossForm_le_of_reflectionPositive` is the wall's quantitative
statement: reflection positivity on the half forces

```
crossForm G m θ H (c · invDeg)  ≤  Δ²/(m²)³ · (c ⬝ᵥ c)      for every c vanishing off H.
```

That is a quantifier over vectors. **`RayleighVariational.isGreatest_rayleigh` says a quantifier
of exactly that shape is one number**, so the condition is a bound on a top eigenvalue — and this
file makes the matrix explicit and draws the conclusion.

```
0 ≤ reflectedForm on every c vanishing off H   ⟹   topEigen (twistedCross) ≤ Δ²/(m²)³
```

**`twistedCross` is not new mathematics and reuses the estate's own matrix** (`ERRATUM 337`):
`CrossFormMatrix.crossMatrix` already writes the cross form as a matrix and proves it symmetric
off `IsRefl`; the twist is a diagonal conjugation, `-(Dinv * crossMatrix * Dinv)`, which is what
the criterion's `c · invDeg` amounts to. The minus sign is the wall's sign convention, carried by
`CrossFormMatrix.dotProduct_crossMatrix`.

## What this is and is not

**It is the necessary direction only.** `W1` wants *reflection positive ⟹ `hcross`*, and nothing
here supplies a converse: an eigenvalue bound following from reflection positivity does not make
reflection positivity follow from an eigenvalue bound. `WALLS.md` §W1.5 states the missing
ingredient and this file does not supply it. **No wall moves.**

**What it changes is the shape of the test.** Refuting reflection positivity for a given graph was
a search over vectors; it is now a comparison of two numbers, one of them the largest eigenvalue of
an explicit matrix supported on `H × H`. `LaplacianDeltaPlusOne` is the day's evidence that a
witness beats an estimate, and `RayleighVariational.lt_topEigen_iff_exists_quadForm_gt` is the
statement that the two are the same question.

**It is not `CrossFormMatrix.crossForm_nonpos_iff_posSemidef`.** That identifies the *qualitative*
hypothesis `∀ w, crossForm w ≤ 0` with `crossMatrix` being positive semidefinite. This is the
*quantitative* statement, at the tail constant and after the `invDeg` twist, and neither implies
the other: positive semidefiniteness is a bound at `0` with no twist.

**No support hypothesis is needed in the conclusion**, and the reason is worth stating:
`twistedCross` vanishes off `H × H`, so any eigenvector at a **nonzero** eigenvalue lies in its
range and therefore
vanishes off `H` automatically. That is `eigenvector_eq_zero_of_not_mem` below, and it is why no
indicator-restriction argument appears.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CrossBlockTopEigenvalue

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection CrossFormMatrix
open ReflectionRemainderGeneral
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The twisted cross block -/

/-- **THE CROSS MATRIX, CONJUGATED BY THE DIAGONAL THE CRITERION TWISTS BY.** The sign is the
wall's convention, so that the quadratic form is `crossForm` and not its negative. -/
noncomputable def twistedCross (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) : Matrix V V ℝ :=
  -(Matrix.diagonal (invDeg G m) * crossMatrix G θ H * Matrix.diagonal (invDeg G m))

theorem twistedCross_apply (p q : V) :
    twistedCross G m θ H p q = -(invDeg G m p * crossMatrix G θ H p q * invDeg G m q) := by
  simp [twistedCross, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq, mul_comm, mul_left_comm, mul_assoc]

theorem twistedCross_isHermitian (h : IsRefl G θ) : (twistedCross G m θ H).IsHermitian := by
  ext p q
  have hc := congrFun (congrFun (crossMatrix_isHermitian (G := G) (θ := θ) (H := H) h) q) p
  simp only [Matrix.conjTranspose_apply, star_trivial] at hc ⊢
  rw [twistedCross_apply, twistedCross_apply, hc]
  ring

/-! ## 2. Its quadratic form is the criterion's cross form -/

theorem quadForm_twistedCross (hM : IsMirrorHalf θ H Mir) (c : V → ℝ) :
    c ⬝ᵥ twistedCross G m θ H *ᵥ c = crossForm G m θ H (fun v => c v * invDeg G m v) := by
  classical
  set w : V → ℝ := fun v => c v * invDeg G m v with hw
  have hmv : twistedCross G m θ H *ᵥ c = -(fun p => invDeg G m p * (crossMatrix G θ H *ᵥ w) p) := by
    ext p
    rw [Matrix.mulVec, dotProduct]
    simp only [twistedCross_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun q _ => by rw [hw]; ring)
  rw [hmv]
  have hsum : c ⬝ᵥ (-(fun p => invDeg G m p * (crossMatrix G θ H *ᵥ w) p))
      = -(w ⬝ᵥ (crossMatrix G θ H *ᵥ w)) := by
    rw [dotProduct, dotProduct, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp [hw]; ring
  rw [hsum, dotProduct_crossMatrix hM m w, neg_neg]

/-! ## 3. Eigenvectors at a nonzero eigenvalue live on the half -/

theorem twistedCross_apply_of_not_mem {p : V} (hp : p ∉ H) (q : V) :
    twistedCross G m θ H p q = 0 := by
  rw [twistedCross_apply, crossMatrix, if_neg fun hc => hp hc.1]
  ring

theorem eigenvector_eq_zero_of_not_mem {μ : ℝ} (hμ : μ ≠ 0) {x : V → ℝ}
    (hx : twistedCross G m θ H *ᵥ x = μ • x) {p : V} (hp : p ∉ H) : x p = 0 := by
  have h := congrFun hx p
  rw [Matrix.mulVec, dotProduct] at h
  have hzero : ∑ q : V, twistedCross G m θ H p q * x q = 0 :=
    Finset.sum_eq_zero fun q _ => by rw [twistedCross_apply_of_not_mem hp q, zero_mul]
  rw [hzero] at h
  have : μ * x p = 0 := by simpa [eq_comm] using h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hμ
  · exact h'

/-! ## 4. The necessary condition, as one number -/

/-- **REFLECTION POSITIVITY ON THE HALF BOUNDS THE TWISTED CROSS BLOCK'S TOP EIGENVALUE.** The
quantifier over vectors in `crossForm_le_of_reflectionPositive` is exactly the quantifier
`RayleighVariational.isGreatest_rayleigh` collapses. **The converse is not proved and is what W1
wants.** -/
theorem topEigen_twistedCross_le [Nonempty V] (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0)
    (hrp : ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) → 0 ≤ reflectedForm G m θ c) :
    RayleighVariational.topEigen (twistedCross_isHermitian (G := G) (m := m) (H := H) h)
      ≤ Δ ^ 2 / (m ^ 2) ^ 3 := by
  set hHerm := twistedCross_isHermitian (G := G) (m := m) (H := H) h with hHermDef
  set T := RayleighVariational.topEigen hHerm with hT
  by_contra hcon
  have hKnn : 0 ≤ Δ ^ 2 / (m ^ 2) ^ 3 := by positivity
  have hTpos : 0 < T := lt_of_le_of_lt hKnn (not_le.mp hcon)
  obtain ⟨x, hx0, hx⟩ := OpNormTopEigenvalue.exists_eigenvector_sup' hHerm
  have hxT : twistedCross G m θ H *ᵥ x = T • x := hx
  have hsupp : ∀ p, p ∉ H → x p = 0 := fun p hp =>
    eigenvector_eq_zero_of_not_mem (ne_of_gt hTpos) hxT hp
  have hxx : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx0 (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hquad : x ⬝ᵥ twistedCross G m θ H *ᵥ x = T * (x ⬝ᵥ x) := by
    rw [hxT, dotProduct_smul, smul_eq_mul]
  have hgt : Δ ^ 2 / (m ^ 2) ^ 3 * (x ⬝ᵥ x) < crossForm G m θ H (fun v => x v * invDeg G m v) := by
    rw [← quadForm_twistedCross hM x, hquad]
    exact mul_lt_mul_of_pos_right (not_le.mp hcon) hxx
  exact absurd (ReflectionFailureCriterion.crossForm_le_of_reflectionPositive
      hM h hΔ hm hsupp (hrp x hsupp))
    (not_le.mpr hgt)

end CrossBlockTopEigenvalue
