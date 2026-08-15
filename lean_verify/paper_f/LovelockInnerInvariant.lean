import LovelockInnerPositive
import LovelockActComposition

/-!
# The form is `O(n)`-invariant, so the three squared lengths are invariants of the tensor

`LovelockOrthogonality` built `ip R S = ∑_{abcd} R_{abcd} S_{abcd}` and called what it enables
*"the quadratic curvature invariants"*. `LovelockInnerPositive` then made `ip R R` a genuine
squared length. **Neither proved that the number does not depend on the frame.**

## This is not an erratum, and the check that says so is worth the paragraph

`ERRATUM 171` was a word used before the theorem under it existed, so the same question was asked
here first, of the sentence *"the quadratic curvature invariants could not be **written**"*. **It
is about expressibility, not about invariance having been proved**, and *"quadratic curvature
invariant"* is the literature's own name for the object. So the phrase was not a claim, and
nothing here withdraws anything. What it was, was a **word not yet earned** — and this file earns
it.

## What is proved

* `ip_eq_trace` — `ip R S = tr (mat4 R · (mat4 S)ᵀ)`, so the form is an ordinary matrix trace once
  `LovelockActComposition.mat4` reads four-index arrays as matrices on pairs;
* `trace_conj` — `tr (K A Kᵀ · K B Kᵀ) = tr (A B)` for `Kᵀ K = 1`. Two rewrites and
  `Matrix.trace_mul_comm`;
* **`ip_act`** — for every orthogonal `Q`, `⟨act Q R, act Q S⟩ = ⟨R, S⟩`. The conjugating matrix
  is `Q ⊗ₖ Q`, orthogonal by `LovelockActComposition.isOrth_kronecker`;
* **`ip_weylPart_act`, `ip_ricciPart_act`, `ip_scalPart_act`** — and since the three projections
  commute with a frame change (`LovelockEquivariance`), **each summand's squared length is
  unchanged by it.** `|Weyl|²`, `|Ric₀|²` and `|scal|²` are functions of the tensor, not of the
  coordinates it is written in.

## What this is and is not, for `KillsWeyl`

**It is infrastructure that every classical route to `KillsWeyl` uses**, and its absence would have
been a blocker for any of them: the arguments that identify the Weyl summand as a subrepresentation
with no copy of the symmetric-2-tensor representation are run against an invariant form.

**It is not a step toward the statement.** Nothing here says anything about what an equivariant `T`
does to the Weyl summand, and no route to `KillsWeyl` is closer than it was this morning — there is
still no candidate elementary argument, as `WALLS` §W5.0 §5c records. **The watchlist item does not
move.** A missing ingredient supplied is not progress, and this file is written so nobody reads it
as any.

**And the other disclaimers stand.** No `InnerProductSpace` instance, no completeness, no norm; and
`LovelockOrthogonality`'s corrected `a₂` paragraph is unaffected — `a₂`'s integrand is a multiple
of the scalar curvature, the quadratic invariants belong to the next coefficient, and nothing in
this file is an `a₂` computation.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockInnerInvariant

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality
  LovelockActComposition Matrix Finset Kronecker

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The form is a trace -/

/-- **THE FULL CONTRACTION IS A MATRIX TRACE**, once a four-index array is read as a matrix on
pairs. -/
theorem ip_eq_trace (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip R S = Matrix.trace (mat4 R * (mat4 S)ᵀ) := by
  simp only [ip, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    mat4, Matrix.of_apply, Fintype.sum_prod_type]

/-- Conjugating both arguments by the same orthogonal matrix leaves the trace alone. -/
theorem trace_conj (K A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (hK : Kᵀ * K = 1) :
    Matrix.trace (K * A * Kᵀ * (K * B * Kᵀ)) = Matrix.trace (A * B) := by
  have h1 : K * A * Kᵀ * (K * B * Kᵀ) = K * (A * B) * Kᵀ := by
    rw [show K * A * Kᵀ * (K * B * Kᵀ) = K * A * (Kᵀ * K) * B * Kᵀ by simp only [mul_assoc], hK,
      mul_one]
    simp only [mul_assoc]
  rw [h1, Matrix.trace_mul_comm, ← mul_assoc, hK, one_mul]

/-! ## 2. And therefore invariant -/

/-- **THE FORM IS `O(n)`-INVARIANT.** -/
theorem ip_act (hQ : IsOrth Q) (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (act Q R) (act Q S) = ip R S := by
  have hK : (Matrix.of Q ⊗ₖ Matrix.of Q)ᵀ * (Matrix.of Q ⊗ₖ Matrix.of Q) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n × Fin n) ℝ).mp (isOrth_kronecker hQ)
  rw [ip_eq_trace, ip_eq_trace, mat4_act, mat4_act, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose,
    ← mul_assoc (Matrix.of Q ⊗ₖ Matrix.of Q) ((mat4 S)ᵀ), trace_conj _ _ _ hK]

/-- The squared length of a curvature tensor does not depend on the frame. -/
theorem ip_self_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (act Q R) (act Q R) = ip R R :=
  ip_act hQ R R

/-! ## 3. The three summand lengths are invariants of the tensor

The projections commute with a frame change, so the frame change moves each summand to the
corresponding summand of the moved tensor, and §2 says the length is unchanged.
-/

/-- **`|Weyl|²` IS A FUNCTION OF THE TENSOR, NOT OF THE COORDINATES.** -/
theorem ip_weylPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (weylPart (act Q R)) (weylPart (act Q R)) = ip (weylPart R) (weylPart R) := by
  have hfun : weylPart (act Q R) = act Q (weylPart R) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      (act_weylPart hQ R a b c d).symm
  rw [hfun, ip_act hQ]

/-- **AND SO IS `|Ric₀|²`.** -/
theorem ip_ricciPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (ricciPart (act Q R)) (ricciPart (act Q R)) = ip (ricciPart R) (ricciPart R) := by
  have hfun : ricciPart (act Q R) = act Q (ricciPart R) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      (act_ricciPart hQ R a b c d).symm
  rw [hfun, ip_act hQ]

/-- **AND `|scal|²`.** -/
theorem ip_scalPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (scalPart (act Q R)) (scalPart (act Q R)) = ip (scalPart R) (scalPart R) := by
  have hfun : scalPart (act Q R) = act Q (scalPart R) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      (act_scalPart hQ R a b c d).symm
  rw [hfun, ip_act hQ]

end LovelockInnerInvariant
