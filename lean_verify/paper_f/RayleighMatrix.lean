import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The variational inequality for a real symmetric matrix

`WALLS` §W4.0 §6 item 2's second route stops, after `PerronBound` and `PerronEquality`, at two
named halves. The first is **that equality holds at all** in `|μ|·|v| ≤ A *ᵥ |v|`, which needs the
variational picture of the largest eigenvalue — and the register recorded that **this estate has
no Rayleigh-quotient statement for matrices**, Mathlib's `ContinuousLinearMap.rayleighQuotient`
being about Hilbert-space operators and applied to `Matrix` nowhere here.

**That absence is about names, and this file is the test of what it costs.** Probed today: the
`Matrix.IsHermitian` API **identifies** eigenvalues — `spectral_theorem`, `eigenvectorBasis`,
`mulVec_eigenvectorBasis`, `roots_charpoly_eq_eigenvalues`, `posDef_iff_eigenvalues_pos` — and
contains **no** statement ordering the quadratic form against them: `eigenvalues_le_max`,
`le_eigenvalues`, `courant`, `Courant`, `iSup_eigenvalues` are **0** each. So the theorem is
missing and its ingredients are not.

> **`quadForm_le_of_eigenvalues_le`** — if every eigenvalue of a real symmetric `A` is at most
> `M`, then `⟪v, Av⟫ ≤ M·⟪v, v⟫` for **every** `v`.
>
> **`coeff_eq_zero_of_quadForm_eq`** — and at equality, `v` has no component along any
> eigenvector whose eigenvalue is strictly below `M`.

## What this does and does not give the wall

It gives the **inequality** half of the variational picture, which is the half that was missing by
name. It does **not** yet give *«a maximiser of the form is an eigenvector»* — that needs the
expansion of `v` back out of its coefficients, and is deliberately left to its own unit rather
than bundled here on the strength of the coefficients vanishing. **`coeff_eq_zero_of_quadForm_eq`
is the input to that step and is not that step.**

And even completed, this reaches only half (a) of `WALLS` §W4.0 §6 item 2. Half (b), simplicity of
the top eigenvalue, is untouched by everything here.
-/

namespace RayleighMatrix

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ## 1. The matrix as an operator on `EuclideanSpace`, and its two basic properties -/

/-- `A` acting on `EuclideanSpace ℝ n`, which is where the eigenbasis lives. -/
noncomputable def mv (A : Matrix n n ℝ) (v : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 (A *ᵥ (WithLp.ofLp v))

omit [DecidableEq n] in
theorem inner_expand (x y : EuclideanSpace ℝ n) :
    inner ℝ x y = ∑ i, (WithLp.ofLp x) i * (WithLp.ofLp y) i := by
  refine (EuclideanSpace.inner_eq_star_dotProduct x y).trans ?_
  simp [dotProduct, mul_comm]

omit [DecidableEq n] in
theorem mv_row (w : EuclideanSpace ℝ n) (i : n) :
    (WithLp.ofLp (mv A w)) i = ∑ j, A i j * (WithLp.ofLp w) j := by
  simp [mv, Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
/-- **SELF-ADJOINTNESS**, in the inner-product form the eigenbasis argument needs. -/
theorem mv_adjoint (hA : A.IsHermitian) (x y : EuclideanSpace ℝ n) :
    inner ℝ x (mv A y) = inner ℝ (mv A x) y := by
  rw [inner_expand, inner_expand]
  simp only [mv_row]
  have l : ∑ i, (WithLp.ofLp x) i * (∑ j, A i j * (WithLp.ofLp y) j)
      = ∑ i, ∑ j, A i j * ((WithLp.ofLp x) i * (WithLp.ofLp y) j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have r : ∑ i, (∑ j, A i j * (WithLp.ofLp x) j) * (WithLp.ofLp y) i
      = ∑ j, ∑ i, A j i * ((WithLp.ofLp x) i * (WithLp.ofLp y) j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [l, r, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hsym : A i j = A j i := by
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  rw [hsym]

theorem mv_eigenvectorBasis (hA : A.IsHermitian) (j : n) :
    mv A (hA.eigenvectorBasis j) = hA.eigenvalues j • (hA.eigenvectorBasis j) := by
  unfold mv
  rw [hA.mulVec_eigenvectorBasis]
  rfl

/-! ## 2. The quadratic form and the norm, in eigencoordinates -/

/-- The coefficient of `v` along the `j`-th eigenvector. -/
noncomputable def coeff (hA : A.IsHermitian) (v : EuclideanSpace ℝ n) (j : n) : ℝ :=
  inner ℝ (hA.eigenvectorBasis j) v

theorem inner_basis_mv (hA : A.IsHermitian) (v : EuclideanSpace ℝ n) (j : n) :
    inner ℝ (hA.eigenvectorBasis j) (mv A v) = hA.eigenvalues j * coeff hA v j := by
  rw [mv_adjoint hA, mv_eigenvectorBasis hA, real_inner_smul_left, coeff]

/-- **THE QUADRATIC FORM IS THE EIGENVALUE-WEIGHTED SUM OF SQUARED COEFFICIENTS.** -/
theorem quadForm_eq_sum (hA : A.IsHermitian) (v : EuclideanSpace ℝ n) :
    inner ℝ v (mv A v) = ∑ j, hA.eigenvalues j * (coeff hA v j) ^ 2 := by
  have hpar := (hA.eigenvectorBasis).sum_inner_mul_inner v (mv A v)
  refine hpar.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  have h1 : inner ℝ (hA.eigenvectorBasis j) (mv A v) = hA.eigenvalues j * coeff hA v j :=
    inner_basis_mv hA v j
  have h2 : inner ℝ v (hA.eigenvectorBasis j) = coeff hA v j := real_inner_comm _ _
  change inner ℝ v (hA.eigenvectorBasis j) * inner ℝ (hA.eigenvectorBasis j) (mv A v)
      = hA.eigenvalues j * coeff hA v j ^ 2
  rw [h1, h2]; ring

/-- **AND THE NORM IS THE PLAIN SUM.** -/
theorem normSq_eq_sum (hA : A.IsHermitian) (v : EuclideanSpace ℝ n) :
    inner ℝ v v = ∑ j, (coeff hA v j) ^ 2 := by
  have hpar := (hA.eigenvectorBasis).sum_inner_mul_inner v v
  refine hpar.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  have h2 : inner ℝ v (hA.eigenvectorBasis j) = coeff hA v j := real_inner_comm _ _
  have h3 : inner ℝ (hA.eigenvectorBasis j) v = coeff hA v j := rfl
  change inner ℝ v (hA.eigenvectorBasis j) * inner ℝ (hA.eigenvectorBasis j) v = coeff hA v j ^ 2
  rw [h2, h3]; ring

/-! ## 3. The variational inequality, and its equality case -/

/-- **THE VARIATIONAL INEQUALITY.** If every eigenvalue is at most `M`, the quadratic form is
bounded by `M` times the squared norm — for every vector, with no normalisation.

Absent from Mathlib by name: `eigenvalues_le_max`, `le_eigenvalues`, `courant`, `iSup_eigenvalues`
are `0` each, and the `Matrix.IsHermitian` API identifies eigenvalues without ever ordering the
form against them. -/
theorem quadForm_le_of_eigenvalues_le (hA : A.IsHermitian) {M : ℝ}
    (hmax : ∀ j, hA.eigenvalues j ≤ M) (v : EuclideanSpace ℝ n) :
    inner ℝ v (mv A v) ≤ M * inner ℝ v v := by
  rw [quadForm_eq_sum hA, normSq_eq_sum hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hmax j) (sq_nonneg _)

/-- **THE EQUALITY CASE.** At equality, `v` has no component along an eigenvector whose eigenvalue
is strictly below `M`.

**This is the input to «a maximiser is an eigenvector», and it is not that statement**: putting `v`
back together from its coefficients is a separate step and is not attempted here. -/
theorem coeff_eq_zero_of_quadForm_eq (hA : A.IsHermitian) {M : ℝ}
    (hmax : ∀ j, hA.eigenvalues j ≤ M) {v : EuclideanSpace ℝ n}
    (heq : inner ℝ v (mv A v) = M * inner ℝ v v) {j : n} (hj : hA.eigenvalues j < M) :
    coeff hA v j = 0 := by
  rw [quadForm_eq_sum hA, normSq_eq_sum hA, Finset.mul_sum] at heq
  have hle : ∀ k ∈ (univ : Finset n),
      hA.eigenvalues k * (coeff hA v k) ^ 2 ≤ M * (coeff hA v k) ^ 2 :=
    fun k _ => mul_le_mul_of_nonneg_right (hmax k) (sq_nonneg _)
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq j (mem_univ j)
  have hsq : (coeff hA v j) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < (coeff hA v j) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have := (mul_lt_mul_of_pos_right hj hpos)
    linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end RayleighMatrix
