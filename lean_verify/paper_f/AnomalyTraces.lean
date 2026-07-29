/-
  AnomalyTraces: Gauge Anomaly Coefficients as Genuine Representation Traces
  ==========================================================================

  Upgrades: F3_9e_AnomalyCancellation, whose anomaly coefficients A(4) = +1,
  A(4̄) = −1 are integer literals. Here the same cancellations are derived
  from the trace form itself.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `cubicTrace` — the symmetrised cubic trace form
       d(T₁,T₂,T₃) = Tr(T₁·(T₂T₃ + T₃T₂)),
     the algebraic object whose values on representation generators are the
     cubic anomaly coefficients. Total symmetry proven (swap + cyclic).
  2. `cubicTrace_neg_transpose` — the conjugate (antifundamental) assignment
     T ↦ −Tᵀ flips the sign: d(−T₁ᵀ,−T₂ᵀ,−T₃ᵀ) = −d(T₁,T₂,T₃).
     A(R̄) = −A(R) as trace algebra, not as an integer stipulation.
  3. `fund_antifund_cubic_cancel`, `pati_salam_su4_cubic_cancel` — the SU(4)³
     cubic anomaly of the Pati-Salam fermion content (4,2,1) ⊕ (4̄,1,2)
     cancels for EVERY generator triple, any number of generations.
  4. `su2_cubic_vanishes` — pseudo-reality: with ε the antisymmetric 2×2 unit,
     ε·T = −Tᵀ·ε for every traceless T (proven entrywise), so conjugation by ε
     identifies the fundamental with its conjugate and the su(2) cubic form
     vanishes identically. The vanishing is DERIVED from the intertwiner,
     replacing F3_9e's arbitrary-integer identity a + (−a) = 0.
  5. `mixed_cubic_kronecker_vanishes` (+ `_left` variant) — mixed anomalies:
     on a product representation the generators are T ⊗ₖ 1 and 1 ⊗ₖ S, the
     cubic trace factorises through Matrix.trace_kronecker, and tracelessness
     of the single factor kills it.
  6. `linear_trace_kronecker_vanishes` — the gauge-gravitational (linear)
     anomaly: Tr(T ⊗ₖ 1) = Tr(T)·dim = 0 for traceless T.
  7. `su4_cubic_form_ne_zero` — non-triviality witness: d(T₀,T₀,T₀) = −48 ≠ 0
     for T₀ = diag(1,1,1,−3) ∈ sl₄, so the Pati-Salam cancellation is a
     genuine cancellation of a non-vanishing form, not 0 = 0.
  8. `pati_salam_anomaly_free` — master theorem bundling 3–6 for the
     Pati-Salam content, quantified over all generator triples.

  NOT proven here (cited, out of scope): the QFT input that the triangle
  anomaly is proportional to this d-symbol (Adler–Bell–Jackiw 1969); the
  Witten global SU(2) anomaly (π₄(SU(2)) = ℤ/2 — homotopy theory not in
  Mathlib; F3_9e's even-doublet COUNT remains arithmetic bookkeeping).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 axioms.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

open Matrix
open scoped Kronecker

noncomputable section

namespace AnomalyTraces

variable {k : Type*} [Fintype k]

/-! ## 1. The cubic trace form (the d-symbol) -/

/-- The symmetrised cubic trace form `d(T₁,T₂,T₃) = Tr(T₁·(T₂T₃ + T₃T₂))`.
    On the generators of a representation, its values are (up to the standard
    normalisation) the cubic anomaly coefficients `d^{abc}`. -/
def cubicTrace (T₁ T₂ T₃ : Matrix k k ℂ) : ℂ :=
  trace (T₁ * (T₂ * T₃ + T₃ * T₂))

/-- The form is symmetric in its last two arguments. -/
theorem cubicTrace_swap₂₃ (T₁ T₂ T₃ : Matrix k k ℂ) :
    cubicTrace T₁ T₂ T₃ = cubicTrace T₁ T₃ T₂ := by
  unfold cubicTrace
  rw [add_comm]

/-- The form is invariant under cyclic rotation of its arguments. -/
theorem cubicTrace_cyclic (T₁ T₂ T₃ : Matrix k k ℂ) :
    cubicTrace T₁ T₂ T₃ = cubicTrace T₂ T₃ T₁ := by
  unfold cubicTrace
  rw [mul_add, mul_add, trace_add, trace_add, ← mul_assoc, ← mul_assoc,
    ← mul_assoc, ← mul_assoc, trace_mul_cycle T₂ T₃ T₁, trace_mul_cycle T₂ T₁ T₃,
    trace_mul_cycle T₃ T₂ T₁]

/-- Full symmetry: the swap of the first two arguments. With `cubicTrace_swap₂₃`
    and `cubicTrace_cyclic` this generates all six permutations. -/
theorem cubicTrace_swap₁₂ (T₁ T₂ T₃ : Matrix k k ℂ) :
    cubicTrace T₁ T₂ T₃ = cubicTrace T₂ T₁ T₃ := by
  rw [cubicTrace_cyclic, cubicTrace_swap₂₃]

/-! ## 2. Antifundamental = −(fundamental): the sign flip is trace algebra -/

/-- The conjugate-representation assignment `T ↦ −Tᵀ` flips the sign of the
    cubic form: `d(−T₁ᵀ, −T₂ᵀ, −T₃ᵀ) = −d(T₁,T₂,T₃)`. This is the genuine
    content behind "A(4̄) = −A(4)". -/
theorem cubicTrace_neg_transpose (T₁ T₂ T₃ : Matrix k k ℂ) :
    cubicTrace (-T₁ᵀ) (-T₂ᵀ) (-T₃ᵀ) = -cubicTrace T₁ T₂ T₃ := by
  unfold cubicTrace
  have inner : (-T₂ᵀ) * (-T₃ᵀ) + (-T₃ᵀ) * (-T₂ᵀ) = (T₃ * T₂ + T₂ * T₃)ᵀ := by
    rw [neg_mul_neg, neg_mul_neg, ← transpose_mul, ← transpose_mul, ← transpose_add]
  rw [inner, neg_mul, trace_neg, ← transpose_mul, trace_transpose,
    trace_mul_comm, add_comm]

/-- SU(4)³ anomaly cancellation, fundamental + antifundamental, as an identity
    of trace forms valid for every generator triple. -/
theorem fund_antifund_cubic_cancel (T₁ T₂ T₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    cubicTrace T₁ T₂ T₃ + cubicTrace (-T₁ᵀ) (-T₂ᵀ) (-T₃ᵀ) = 0 := by
  rw [cubicTrace_neg_transpose]
  ring

/-- The Pati-Salam fermion content per generation is (4,2,1) ⊕ (4̄,1,2): the
    fundamental enters with multiplicity dim(2)·dim(1) = 2 and the
    antifundamental with multiplicity dim(1)·dim(2) = 2. The weighted cubic
    trace sum cancels for every generator triple and every generation count. -/
theorem pati_salam_su4_cubic_cancel (generations : ℕ)
    (T₁ T₂ T₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    (generations : ℂ) *
      (2 * cubicTrace T₁ T₂ T₃ + 2 * cubicTrace (-T₁ᵀ) (-T₂ᵀ) (-T₃ᵀ)) = 0 := by
  rw [cubicTrace_neg_transpose]
  ring

/-! ## 3. SU(2) pseudo-reality: the ε-intertwiner kills the cubic form -/

/-- The antisymmetric unit `ε = iσ₂` (up to phase): the intertwiner between the
    su(2) fundamental and its conjugate. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem eps_mul_neg_eps : eps * (-eps) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps, Matrix.mul_apply, Fin.sum_univ_succ]

theorem neg_eps_mul_eps : (-eps) * eps = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The intertwining identity: for every TRACELESS 2×2 matrix,
    `ε·T = −Tᵀ·ε`. Proven entrywise; the trace condition enters as
    `T₁₁ = −T₀₀`. This is the precise sense in which the su(2) fundamental is
    pseudo-real (self-conjugate). -/
theorem eps_intertwines (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : trace T = 0) :
    eps * T = -Tᵀ * eps := by
  have h11 : T 1 1 = -(T 0 0) := by
    have h := hT
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      Matrix.neg_apply, h11]

/-- For traceless T, the conjugate generator `−Tᵀ` IS the ε-conjugate of `T`. -/
theorem neg_transpose_eq_conj (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : trace T = 0) :
    -Tᵀ = eps * T * (-eps) := by
  calc -Tᵀ = -Tᵀ * 1 := (mul_one _).symm
    _ = -Tᵀ * (eps * (-eps)) := by rw [eps_mul_neg_eps]
    _ = (-Tᵀ * eps) * (-eps) := by rw [mul_assoc]
    _ = (eps * T) * (-eps) := by rw [← eps_intertwines T hT]

/-- The cubic form is invariant under conjugation by any one-sided-invertible
    pair (`Sinv * S = 1` suffices). -/
theorem cubicTrace_conj [DecidableEq k] (S Sinv : Matrix k k ℂ) (hS : Sinv * S = 1)
    (T₁ T₂ T₃ : Matrix k k ℂ) :
    cubicTrace (S * T₁ * Sinv) (S * T₂ * Sinv) (S * T₃ * Sinv)
      = cubicTrace T₁ T₂ T₃ := by
  unfold cubicTrace
  have collapse : ∀ A B : Matrix k k ℂ,
      (S * A * Sinv) * (S * B * Sinv) = S * (A * B) * Sinv := by
    intro A B
    calc (S * A * Sinv) * (S * B * Sinv)
        = S * A * (Sinv * S) * (B * Sinv) := by noncomm_ring
      _ = S * (A * B) * Sinv := by rw [hS]; noncomm_ring
  have tr_conj : ∀ W : Matrix k k ℂ, trace (S * W * Sinv) = trace W := by
    intro W
    rw [trace_mul_comm, ← mul_assoc, hS, one_mul]
  have sum_pull : S * (T₂ * T₃) * Sinv + S * (T₃ * T₂) * Sinv
      = S * (T₂ * T₃ + T₃ * T₂) * Sinv := by
    rw [mul_add S, add_mul]
  rw [collapse, collapse, sum_pull, collapse, tr_conj]

/-- **Pseudo-reality kills the su(2) cubic anomaly**: for traceless 2×2
    generators the cubic trace form vanishes identically. Derivation:
    conjugation by ε turns each generator into its conjugate `−Tᵀ`
    (`neg_transpose_eq_conj`), conjugation preserves the form
    (`cubicTrace_conj`), and the conjugate assignment flips the sign
    (`cubicTrace_neg_transpose`); hence d = −d, so d = 0. -/
theorem su2_cubic_vanishes (T₁ T₂ T₃ : Matrix (Fin 2) (Fin 2) ℂ)
    (h₁ : trace T₁ = 0) (h₂ : trace T₂ = 0) (h₃ : trace T₃ = 0) :
    cubicTrace T₁ T₂ T₃ = 0 := by
  have hconj : cubicTrace (-T₁ᵀ) (-T₂ᵀ) (-T₃ᵀ) = cubicTrace T₁ T₂ T₃ := by
    rw [neg_transpose_eq_conj T₁ h₁, neg_transpose_eq_conj T₂ h₂,
      neg_transpose_eq_conj T₃ h₃]
    exact cubicTrace_conj eps (-eps) neg_eps_mul_eps T₁ T₂ T₃
  have hneg := cubicTrace_neg_transpose T₁ T₂ T₃
  have hdd : cubicTrace T₁ T₂ T₃ = -cubicTrace T₁ T₂ T₃ := hconj.symm.trans hneg
  have h2 : (2 : ℂ) * cubicTrace T₁ T₂ T₃ = 0 := by linear_combination hdd
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-! ## 4. Mixed and gauge-gravitational anomalies via trace factorisation -/

/-- Mixed cubic anomaly `G₁²–G₂` on a product representation: generators
    `T ⊗ₖ 1`, `T' ⊗ₖ 1` (first factor) and `1 ⊗ₖ S` (second factor). The
    cubic trace factorises as `2·Tr(TT')·Tr(S)` and dies with `Tr S = 0`. -/
theorem mixed_cubic_kronecker_vanishes [DecidableEq k] {m : Type*} [Fintype m]
    [DecidableEq m] (T T' : Matrix k k ℂ) (S : Matrix m m ℂ) (hS : trace S = 0) :
    cubicTrace (T ⊗ₖ (1 : Matrix m m ℂ)) (T' ⊗ₖ (1 : Matrix m m ℂ))
      ((1 : Matrix k k ℂ) ⊗ₖ S) = 0 := by
  unfold cubicTrace
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, mul_one T', one_mul S, one_mul T',
    mul_one S, ← kronecker_add, ← mul_kronecker_mul, one_mul (S + S),
    trace_kronecker, trace_add, hS, add_zero, mul_zero]

/-- Mixed cubic anomaly `G₂²–G₁` (the other pairing): two second-factor
    generators and one traceless first-factor generator. -/
theorem mixed_cubic_kronecker_vanishes_left [DecidableEq k] {m : Type*} [Fintype m]
    [DecidableEq m] (T : Matrix k k ℂ) (S S' : Matrix m m ℂ) (hT : trace T = 0) :
    cubicTrace (T ⊗ₖ (1 : Matrix m m ℂ)) ((1 : Matrix k k ℂ) ⊗ₖ S)
      ((1 : Matrix k k ℂ) ⊗ₖ S') = 0 := by
  unfold cubicTrace
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, one_mul (1 : Matrix k k ℂ),
    ← kronecker_add, ← mul_kronecker_mul, mul_one T, one_mul (S * S' + S' * S),
    trace_kronecker, hT, zero_mul]

/-- Gauge-gravitational (linear) anomaly: the trace of a product-representation
    generator `T ⊗ₖ 1` is `Tr(T) · dim`, zero for traceless `T`. This replaces
    "Tr(T^a) = 0" bookkeeping with the actual trace computation. -/
theorem linear_trace_kronecker_vanishes {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix k k ℂ) (hT : trace T = 0) :
    trace (T ⊗ₖ (1 : Matrix m m ℂ)) = 0 := by
  rw [trace_kronecker, hT, zero_mul]

/-! ## 5. Non-triviality: the su(4) cubic form is NOT identically zero -/

/-- The traceless diagonal generator `T₀ = diag(1,1,1,−3) ∈ sl₄(ℂ)`
    (the B−L direction up to normalisation). -/
def T₀ : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, 1, 1, -3]

theorem T₀_traceless : trace T₀ = 0 := by
  simp only [T₀, Matrix.trace_diagonal, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- `d(T₀,T₀,T₀) = 2·Tr(T₀³) = 2(1+1+1−27) = −48 ≠ 0`: the su(4) cubic form is
    genuinely non-vanishing, so `fund_antifund_cubic_cancel` is a real
    cancellation of a non-zero quantity — not an instance of 0 = 0. -/
theorem su4_cubic_form_ne_zero : cubicTrace T₀ T₀ T₀ ≠ 0 := by
  have hval : cubicTrace T₀ T₀ T₀ = -48 := by
    unfold cubicTrace T₀
    rw [Matrix.diagonal_mul_diagonal, mul_add, Matrix.diagonal_mul_diagonal,
      trace_add, Matrix.trace_diagonal]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
  rw [hval]
  norm_num

/-! ## 6. Master theorem -/

/-- **Pati-Salam anomaly freedom as genuine representation theory.** For the
    fermion content (4,2,1) ⊕ (4̄,1,2) (any number of generations):
    (i)   the SU(4)³ cubic sum cancels for every generator triple;
    (ii)  the SU(2)_L³ and SU(2)_R³ cubic forms vanish identically on
          traceless generators (pseudo-reality via the ε-intertwiner);
    (iii) mixed SU(4)²–SU(2) traces vanish by trace factorisation;
    (iv)  mixed SU(2)²–SU(4) traces vanish by tracelessness of the su(4) factor;
    (v)   the gauge-gravitational linear trace vanishes;
    (vi)  the cancellation in (i) is non-trivial: the su(4) cubic form itself
          is non-zero (witness `T₀`).
    Every conjunct is quantified over ALL generators with only tracelessness
    assumed — no hardcoded coefficients anywhere. -/
theorem pati_salam_anomaly_free (generations : ℕ) :
    (∀ T₁ T₂ T₃ : Matrix (Fin 4) (Fin 4) ℂ,
      (generations : ℂ) *
        (2 * cubicTrace T₁ T₂ T₃ + 2 * cubicTrace (-T₁ᵀ) (-T₂ᵀ) (-T₃ᵀ)) = 0) ∧
    (∀ S₁ S₂ S₃ : Matrix (Fin 2) (Fin 2) ℂ, trace S₁ = 0 → trace S₂ = 0 →
      trace S₃ = 0 → cubicTrace S₁ S₂ S₃ = 0) ∧
    (∀ (T T' : Matrix (Fin 4) (Fin 4) ℂ) (S : Matrix (Fin 2) (Fin 2) ℂ),
      trace S = 0 →
      cubicTrace (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) (T' ⊗ₖ 1)
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ S) = 0) ∧
    (∀ (T : Matrix (Fin 4) (Fin 4) ℂ) (S S' : Matrix (Fin 2) (Fin 2) ℂ),
      trace T = 0 →
      cubicTrace (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ S)
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ S') = 0) ∧
    (∀ T : Matrix (Fin 4) (Fin 4) ℂ, trace T = 0 →
      trace (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0) ∧
    cubicTrace T₀ T₀ T₀ ≠ 0 := by
  refine ⟨fun T₁ T₂ T₃ => pati_salam_su4_cubic_cancel generations T₁ T₂ T₃,
    fun S₁ S₂ S₃ h₁ h₂ h₃ => su2_cubic_vanishes S₁ S₂ S₃ h₁ h₂ h₃,
    fun T T' S hS => mixed_cubic_kronecker_vanishes T T' S hS,
    fun T S S' hT => mixed_cubic_kronecker_vanishes_left T S S' hT,
    fun T hT => linear_trace_kronecker_vanishes T hT,
    su4_cubic_form_ne_zero⟩

end AnomalyTraces
