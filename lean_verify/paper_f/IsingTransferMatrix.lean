import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.Complex.Basic

/-!
# The one-dimensional Ising transfer matrix, and a gap that is derived rather than supplied

`WALLS.md` W4 (the mass gap) records its failing step as: *"an interacting transfer operator or
Hamiltonian for which a gap could even be STATED. None exists in the estate."* A note of
2026-08-10 sharpened it: the estate does have an interacting Hamiltonian,
`IsingFiniteVolume.isingH`, but that is a **function on configurations**, not an operator with a
spectrum, and *"the object
that would carry a gap is the Ising transfer matrix, and the estate does not build it."*

This file builds it, for the one-dimensional chain at zero field, and derives its whole spectrum.

> **`transfer β = !![e^β, e^(-β); e^(-β), e^β]`** — the nearest-neighbour Boltzmann weights
> `exp (β s s')` on spins `s, s' ∈ {±1}`.
>
> **`eigenvalue_eq`** — every eigenvalue is `2 cosh β` or `2 sinh β`. Not "these two are
> eigenvalues": these two and **no others**, proved by elimination rather than asserted.
>
> **`abs_lamMinus_lt_lamPlus`** — `|2 sinh β| < 2 cosh β` at every real `β`, so the top of the
> spectrum is simple and separated: a Perron-type statement, proved directly.
>
> **`gap_pos`** — hence the gap `2 cosh β − |2 sinh β|` is strictly positive, and
> **`gap_eq`** computes it exactly: it is `2 e^(−|β|)`.

Nothing here is supplied by the caller. Compare the estate's certificate shells, where `gap` is
a real-number **field** of a structure and no operator appears — `F3_9e_AnomalyCancellation`
still reads `C.to_transfer_matrix.gap` — and compare `TransferGap.lean`, which derives a genuine
gap from a genuine operator but a **model** one, `diag(e^{−Δk})`, chosen rather than obtained
from a Hamiltonian. This operator is not chosen: it is what the one-dimensional Ising
Hamiltonian's Boltzmann weights are.

## What this does NOT do, and the distance is not small

**It is one dimension.** The one-dimensional Ising chain has no phase transition, and the gap
here is positive at **every** `β` and never closes. So this says nothing whatever about the
`d ≥ 2` mass gap that W4 is about, and it is not evidence for it.

**It is not the estate's `isingH`.** That Hamiltonian is two-dimensional; its transfer matrix
acts on `2^n` spin columns, is not `2 × 2`, and is not built here. What is discharged is W4's
clause (i) — *a transfer operator for which a gap can be stated* — in the smallest case where
the operator is genuinely the model's rather than a stand-in.

**No Perron–Frobenius theorem is used or proved.** `abs_lamMinus_lt_lamPlus` is the `2 × 2`
instance done by hand, `|x − y| < x + y` for positive `x, y`. Mathlib has no Perron–Frobenius:
probed 2026-08-11, `PerronFrobenius` and `perronFrobenius` return **zero files**, and the 48
files matching `IsPrimitive` are Pythagorean triples, Dirichlet and additive characters,
polynomials and roots of unity — not matrix primitivity. For `2^n × 2^n` that theorem, or a
substitute, is what clause (ii) would need.
-/

namespace IsingTransferMatrix

open Real Matrix

variable {β : ℝ}

/-! ## 1. The operator -/

/-- **The one-dimensional Ising transfer matrix at zero field**: the entry at `(s, s')` is the
Boltzmann weight `exp (β s s')` of one bond, with `Fin 2` indexing the spin values `+1, -1`. -/
noncomputable def transfer (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![exp β, exp (-β); exp (-β), exp β]

/-- The larger eigenvalue, `2 cosh β`. -/
noncomputable def lamPlus (β : ℝ) : ℝ := exp β + exp (-β)

/-- The smaller eigenvalue, `2 sinh β`. -/
noncomputable def lamMinus (β : ℝ) : ℝ := exp β - exp (-β)

/-! ## 2. Both eigenvalues, with their eigenvectors exhibited -/

/-- The symmetric vector is an eigenvector, with eigenvalue `2 cosh β`. -/
theorem transfer_mulVec_plus (β : ℝ) :
    (transfer β).mulVec ![1, 1] = lamPlus β • ![1, 1] := by
  funext i
  fin_cases i
  · simp [transfer, lamPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [transfer, lamPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith [Real.exp_pos β, Real.exp_pos (-β)]

/-- The antisymmetric vector is an eigenvector, with eigenvalue `2 sinh β`. -/
theorem transfer_mulVec_minus (β : ℝ) :
    (transfer β).mulVec ![1, -1] = lamMinus β • ![1, -1] := by
  funext i
  fin_cases i
  · simp [transfer, lamMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith [Real.exp_pos β, Real.exp_pos (-β)]
  · simp [transfer, lamMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith [Real.exp_pos β, Real.exp_pos (-β)]

/-! ## 3. And no others

The elimination is the whole of it: adding the two coordinate equations isolates `a + b` against
`lamPlus`, subtracting them isolates `a − b` against `lamMinus`, and a vector killed by both is
zero. No characteristic polynomial and no `spectrum` API — `Matrix.charpoly_fin_two` would serve
but the direct argument is shorter and needs no `Nontrivial` plumbing. -/

/-- **THE SPECTRUM IS EXHAUSTED.** Any eigenvalue of the transfer matrix is `2 cosh β` or
`2 sinh β`. This is what makes the gap below a statement about the operator rather than about
two eigenvalues someone happened to exhibit. -/
theorem eigenvalue_eq {μ : ℝ} {v : Fin 2 → ℝ} (hv : v ≠ 0)
    (h : (transfer β).mulVec v = μ • v) : μ = lamPlus β ∨ μ = lamMinus β := by
  have h0 : exp β * v 0 + exp (-β) * v 1 = μ * v 0 := by
    have := congrFun h 0
    simpa [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h1 : exp (-β) * v 0 + exp β * v 1 = μ * v 1 := by
    have := congrFun h 1
    simpa [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_contra hc
  have hp : μ ≠ lamPlus β := fun hx => hc (Or.inl hx)
  have hm : μ ≠ lamMinus β := fun hx => hc (Or.inr hx)
  -- adding: `(lamPlus β - μ) * (v 0 + v 1) = 0`
  have hsum : (lamPlus β - μ) * (v 0 + v 1) = 0 := by
    have : exp β * v 0 + exp (-β) * v 1 + (exp (-β) * v 0 + exp β * v 1)
        = μ * v 0 + μ * v 1 := by rw [h0, h1]
    simp only [lamPlus]; nlinarith [this]
  -- subtracting: `(lamMinus β - μ) * (v 0 - v 1) = 0`
  have hdif : (lamMinus β - μ) * (v 0 - v 1) = 0 := by
    have : exp β * v 0 + exp (-β) * v 1 - (exp (-β) * v 0 + exp β * v 1)
        = μ * v 0 - μ * v 1 := by rw [h0, h1]
    simp only [lamMinus]; nlinarith [this]
  have e1 : v 0 + v 1 = 0 := by
    rcases mul_eq_zero.mp hsum with h' | h'
    · exact absurd (by linarith : μ = lamPlus β) hp
    · exact h'
  have e2 : v 0 - v 1 = 0 := by
    rcases mul_eq_zero.mp hdif with h' | h'
    · exact absurd (by linarith : μ = lamMinus β) hm
    · exact h'
  refine hv (funext fun i => ?_)
  fin_cases i
  · simpa using by linarith
  · simpa using by linarith

/-! ## 4. The gap -/

/-- **THE TOP OF THE SPECTRUM IS SEPARATED**, at every real `β`. The `2 × 2` instance of the
Perron–Frobenius conclusion, done by hand: `|x − y| < x + y` whenever `x` and `y` are positive,
and `exp` is positive. -/
theorem abs_lamMinus_lt_lamPlus (β : ℝ) : |lamMinus β| < lamPlus β := by
  have h1 : (0 : ℝ) < exp β := exp_pos β
  have h2 : (0 : ℝ) < exp (-β) := exp_pos (-β)
  rw [abs_lt]
  constructor <;> simp only [lamPlus, lamMinus] <;> linarith

/-- **HENCE A STRICTLY POSITIVE GAP**, derived from the operator and not supplied with it. -/
theorem gap_pos (β : ℝ) : 0 < lamPlus β - |lamMinus β| :=
  sub_pos.mpr (abs_lamMinus_lt_lamPlus β)

/-- **AND ITS EXACT SIZE: `2 e^(−|β|)`.** The gap closes only in the zero-temperature limit
`|β| → ∞`, which is the one-dimensional statement — no transition at finite `β`. -/
theorem gap_eq (β : ℝ) : lamPlus β - |lamMinus β| = 2 * exp (-|β|) := by
  rcases abs_cases β with ⟨hb, hβ⟩ | ⟨hb, hβ⟩
  · have : |lamMinus β| = lamMinus β := by
      refine abs_of_nonneg ?_
      simp only [lamMinus, sub_nonneg]
      exact exp_le_exp.mpr (by linarith)
    rw [this, hb]; simp only [lamPlus, lamMinus]; ring
  · have : |lamMinus β| = -lamMinus β := by
      refine abs_of_nonpos ?_
      simp only [lamMinus, sub_nonpos]
      exact exp_le_exp.mpr (by linarith)
    rw [this, hb]; simp only [lamPlus, lamMinus]; ring

end IsingTransferMatrix
