/-
  OrderOneCutoffFactorises: the shape L19's arrow assumes is, on the regular bimodule,
  forced by order-one — and the exponential cutoff's trace factorises for that reason

  Campaign 3 hardening unit 172 (20 September 2026). Written from RE-SWEEP #75's reading of
  UNLOCK_WATCHLIST `L40433` (the cascade's `D` as a tensor sum) against units 168–170.

  WHY. Spine link L19 ("spectral action → exponential forced") has had its ARROW as a
  theorem since 14 September: `SpectralCutoffFactorises.trace_exp_kroneckerSum` — the trace
  of an exponential cutoff factorises across a Kronecker sum `D₁ ⊗ₖ 1 + 1 ⊗ₖ D₂`, and the
  factorisation forces the semigroup law. What that file could not supply, and `L40433`
  records as the one identification the arrow still rests on, is the PREMISE: that a Dirac
  operator HAS the Kronecker-sum shape. For the cascade's own `D` nothing supplies it,
  because the estate has no `cascadeDirac` (unit 153's census) — the shape is an INPUT
  there. Unit 168 proved, on the regular bimodule of `Mₙ(ℂ)`, that CCM's order-one
  condition is EQUIVALENT to that shape (`OrderOneRegularBimodule.orderOne_iff_kron`). So
  in the one place this estate has a NON-ZERO Dirac operator subject to CCM's axioms —
  `realWitness`; the other `Triple`, `scalarWitness`, has `D = 0` — the premise is a theorem,
  and the two chains compose. This file writes the composition down.

  WHAT IS PROVED.
  (1) `trace_exp_of_orderOne` — for every `n ≥ 1` and every `M` on `ℂⁿ ⊗ ℂⁿ` satisfying
      order-one against the left action `a ⊗ₖ 1` and the right action `1 ⊗ₖ b` of `Mₙ(ℂ)`:
      `M = kroneckerSum C B` for some `C, B`, and
      `trace (exp (t • M)) = trace (exp (t • C)) · trace (exp (t • B))` for every complex
      `t`. Order-one is the hypothesis; the Kronecker-sum shape is a conclusion.
  (2) `trace_exp_of_orderOne_Hw` — the same on the witness space `Hw` with the estate's
      `piW`/`piOpW`: an order-one endomorphism is `matAlg Slots (kroneckerSum C B)` and its
      matrix's cutoff trace factorises. (`B` here is the transpose of `orderOne_Hw_iff`'s
      right factor, because `piOpW (op b)` acts by `1 ⊗ₖ bᵀ`.)
  (3) At the witness: `Dsym = kroneckerSum pauli3 pauli3` (definitionally), the exponential
      of `t • pauli3` read off (`exp_smul_pauli3`, `trace_exp_smul_pauli3`), and
      `trace (exp (t • Dsym)) = (eᵗ + e⁻ᵗ)²` by the factorisation (`trace_exp_smul_Dsym`).
      Independently, `Dsym` is DIAGONAL with entries `2, 0, 0, −2` (`Dsym_eq_diagonal`), so
      the same trace is `e^{2t} + 2 + e^{−2t}` by direct computation
      (`trace_exp_smul_Dsym_direct`); the two routes agree (`factorised_eq_direct`, which is
      how `(eᵗ + e⁻ᵗ)² = e^{2t} + 2 + e^{−2t}` is proved here — by two traces). And
      `Dsym² = diag(4, 0, 0, 4)` (`Dsym_sq`), so `trace (exp (s • Dsym²)) = 2 + 2 e^{4s}`
      (`trace_exp_smul_Dsym_sq`): the `Tr f(D²/Λ²)` shape, at `f = exp`, `s = −1/Λ²`.
  (4) `ccm_spectral_action` — for any `D` on `Hw` satisfying CCM's three conditions
      (order-one, `Jprod`-invariance, `Dγ = −γD`): `D = matAlg Slots (t • Dsym)` for a real
      `t`, `trace (exp (s • (t • Dsym))) = (e^{st} + e^{−st})²` and
      `trace (exp (s • (t • Dsym)²)) = 2 + 2 e^{4t²s}` for every complex `s`. The spectral
      action of the witness class is a function of one real number, given `π`, `J`, `γ`.

  NOT PROVED, said exactly.
  • Nothing about the cascade's `D`. There is no `cascadeDirac` in the estate (unit 153's
    census, `L40433`), `Hw` is the regular bimodule of `M₂(ℂ)` and not the cascade's space,
    and `L40433`'s trigger — a NUMBER quoted out of the spectral action, `G`, `g²`, `ρ_vac`
    — is not met by anything here. The numbers here are the witness's.
  • The exponential cutoff only. A general cutoff `f` and the heat-kernel expansion
    (`WALLS` §W5, spine L22) are untouched; `SpectralCutoffFactorises` §4–5 says what a
    general `f` must be for the factorisation to hold, and this file does not use it.
  • The scale. `t` is free (unit 170's `ccm_fixes_dirac` leaves it so) and `s` is free; the
    sign of `s` that makes `exp (s • D²)` a cutoff (`s < 0`) is not imposed, and no `Λ` is
    named.
  • The constant term `2` in `trace (exp (s • Dsym²))` is the dimension of `ker Dsym`, read
    off the diagonal; no theorem here names it as a kernel dimension.
  • `n = 2` for everything on `Hw`; (1) is at every `n ≥ 1`, and its `NeZero n` is inherited
    from `orderOne_iff_kron`, which needs one index to name `M (0,0) (0,0)`.
    ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): unit 228's
    `OrderOneBlockDiagonal.orderOne_iff_kron_of_const` derives the classification at every finite
    index type, the empty one included, so the reason is gone; (1) is not restated and keeps
    `[NeZero n]`. Unit 228's search for the sentences it answered missed this one.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). (1) takes `[NeZero n]` and the order-one
  hypothesis; (2) the order-one hypothesis on `Hw`; the nine declarations of (3) take no
  hypothesis; (4) the conjunction of CCM's three conditions on `D`. No theorem here takes a
  positivity, monotonicity or self-adjointness hypothesis.
-/

import GammaFixesDirac
import SpectralCutoffFactorises

open Matrix NormedSpace RealSpectralWitness OrderOneNontrivial SpectralTripleBimodule
open OppositeFromRealStructure OrderOneRegularBimodule SpectralCutoffFactorises GammaFixesDirac
open scoped Kronecker
open scoped Matrix.Norms.Operator

namespace OrderOneCutoffFactorises

/-- **ORDER-ONE FORCES THE SHAPE, AND THE SHAPE FACTORISES THE CUTOFF.** At every `n ≥ 1`. -/
theorem trace_exp_of_orderOne {n : ℕ} [NeZero n] (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (h : ∀ a b : Matrix (Fin n) (Fin n) ℂ,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)⁆, (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ b⁆ = 0) :
    ∃ C B : Matrix (Fin n) (Fin n) ℂ, M = kroneckerSum C B ∧
      ∀ t : ℂ, (exp (t • M)).trace = (exp (t • C)).trace * (exp (t • B)).trace := by
  obtain ⟨C, B, hM⟩ := (orderOne_iff_kron M).1 h
  refine ⟨C, B, hM, fun t => ?_⟩
  rw [hM]
  exact trace_exp_smul_kroneckerSum t C B

/-- `σ₃` is the diagonal matrix `diag(1, −1)`. -/
theorem pauli3_eq_diagonal : pauli3 = diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli3]

/-- `exp (t σ₃) = diag(eᵗ, e⁻ᵗ)`, by `Matrix.exp_diagonal`. -/
theorem exp_smul_pauli3 (t : ℂ) :
    exp (t • pauli3) = diagonal ![Complex.exp t, Complex.exp (-t)] := by
  rw [pauli3_eq_diagonal, ← diagonal_smul, exp_diagonal, Pi.exp_def]
  congr 1
  ext i
  fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]

/-- `trace (exp (t σ₃)) = eᵗ + e⁻ᵗ`. -/
theorem trace_exp_smul_pauli3 (t : ℂ) :
    (exp (t • pauli3)).trace = Complex.exp t + Complex.exp (-t) := by
  rw [exp_smul_pauli3, trace_diagonal, Fin.sum_univ_two]
  simp

/-- The witness's `Dsym` IS `SpectralCutoffFactorises.kroneckerSum pauli3 pauli3`, by definition. -/
theorem Dsym_eq_kroneckerSum : Dsym = kroneckerSum pauli3 pauli3 := rfl

/-- **The factorised route**: `trace (exp (t • Dsym)) = (eᵗ + e⁻ᵗ)²`. -/
theorem trace_exp_smul_Dsym (t : ℂ) :
    (exp (t • Dsym)).trace = (Complex.exp t + Complex.exp (-t)) ^ 2 := by
  rw [Dsym_eq_kroneckerSum, trace_exp_smul_kroneckerSum, trace_exp_smul_pauli3, sq]

/-- The diagonal of `Dsym`: `(i, j) ↦ (±1) + (±1)`, i.e. `2, 0, 0, −2`. -/
def dsymDiag : Slots → ℂ := fun p => ![(1 : ℂ), -1] p.1 + ![(1 : ℂ), -1] p.2

/-- `Dsym` is diagonal — its spectrum is `2, 0, 0, −2`, read off. -/
theorem Dsym_eq_diagonal : Dsym = diagonal dsymDiag := by
  ext ⟨i, p⟩ ⟨k, q⟩
  fin_cases i <;> fin_cases p <;> fin_cases k <;> fin_cases q <;>
    simp [Dsym, pauli3, dsymDiag, kroneckerMap_apply, diagonal]

/-- **The direct route**: `trace (exp (t • Dsym)) = e^{2t} + 2 + e^{−2t}`, by the diagonal. -/
theorem trace_exp_smul_Dsym_direct (t : ℂ) :
    (exp (t • Dsym)).trace = Complex.exp (2 * t) + 2 + Complex.exp (-(2 * t)) := by
  rw [Dsym_eq_diagonal, ← diagonal_smul, exp_diagonal, Pi.exp_def, trace_diagonal,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [dsymDiag, ← Complex.exp_eq_exp_ℂ]
  ring_nf

/-- `Dsym² = diag(4, 0, 0, 4)`. -/
theorem Dsym_sq : Dsym * Dsym = diagonal (fun p => dsymDiag p ^ 2) := by
  rw [Dsym_eq_diagonal, diagonal_mul_diagonal]
  congr 1
  ext p
  ring

/-- **The `Tr f(D²)` shape at `f = exp`**: `trace (exp (s • Dsym²)) = 2 + 2 e^{4s}`. -/
theorem trace_exp_smul_Dsym_sq (s : ℂ) :
    (exp (s • (Dsym * Dsym))).trace = 2 + 2 * Complex.exp (4 * s) := by
  rw [Dsym_sq, ← diagonal_smul, exp_diagonal, Pi.exp_def, trace_diagonal,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [dsymDiag, ← Complex.exp_eq_exp_ℂ]
  ring_nf

/-- **The same on the witness space**, with the estate's `piW`/`piOpW`: an order-one endomorphism of
`Hw` is `matAlg Slots (kroneckerSum C B)`, and its cutoff trace factorises. -/
theorem trace_exp_of_orderOne_Hw (D : Module.End ℂ Hw)
    (h : ∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
      ⁅⁅D, piW a⁆, piOpW b⁆ = 0) :
    ∃ C B : Matrix (Fin 2) (Fin 2) ℂ, D = matAlg Slots (kroneckerSum C B) ∧
      ∀ t : ℂ, (exp (t • kroneckerSum C B)).trace = (exp (t • C)).trace * (exp (t • B)).trace := by
  obtain ⟨C, B, hD⟩ := (orderOne_Hw_iff D).1 h
  refine ⟨C, Bᵀ, ?_, fun t => trace_exp_smul_kroneckerSum t C Bᵀ⟩
  rw [hD]
  change matAlg Slots (C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      + matAlg Slots ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Bᵀ) = _
  rw [← map_add]
  rfl

/-- The two routes agree — an identity of exponentials proved by two traces of one matrix. -/
theorem factorised_eq_direct (t : ℂ) :
    (Complex.exp t + Complex.exp (-t)) ^ 2 = Complex.exp (2 * t) + 2 + Complex.exp (-(2 * t)) := by
  rw [← trace_exp_smul_Dsym, trace_exp_smul_Dsym_direct]

/-- **CCM'S THREE CONDITIONS GIVE THE SPECTRAL ACTION UP TO ONE REAL NUMBER.** For `D` on `Hw`
satisfying order-one, `Jprod`-invariance and `Dγ = −γD`: `D = matAlg Slots (t • Dsym)`, and both
`trace (exp (s • D))` and `trace (exp (s • D²))` are closed forms in `s` and `t`. -/
theorem ccm_spectral_action (D : Module.End ℂ Hw)
    (hD : (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        ⁅⁅D, piW a⁆, piOpW b⁆ = 0) ∧ (∀ v : Hw, Jprod (D (Jprod v)) = D v)
      ∧ D * gammaCcm = -(gammaCcm * D)) :
    ∃ t : ℝ, D = matAlg Slots ((t : ℂ) • Dsym) ∧
      (∀ s : ℂ, (exp (s • ((t : ℂ) • Dsym))).trace
        = (Complex.exp (s * t) + Complex.exp (-(s * t))) ^ 2) ∧
      (∀ s : ℂ, (exp (s • (((t : ℂ) • Dsym) * ((t : ℂ) • Dsym)))).trace
        = 2 + 2 * Complex.exp (4 * (t : ℂ) ^ 2 * s)) := by
  obtain ⟨t, ht⟩ := (ccm_fixes_dirac D).1 hD
  refine ⟨t, ?_, fun s => ?_, fun s => ?_⟩
  · rw [ht, Dccm, map_smul]
  · rw [smul_smul, trace_exp_smul_Dsym]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, trace_exp_smul_Dsym_sq]
    ring_nf

end OrderOneCutoffFactorises
