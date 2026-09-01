import TransferPowerSum
import PowerSumMultiset

/-!
# Equal trace moments give the same eigenvalues, for a Hermitian matrix

`TraceMomentsSpectrum.charpoly_roots_eq_of_trace_pow_eq` (1 September) proves the watchlist item's
sentence over an **algebraically closed** field of characteristic zero. **`ℝ` is not one**, so that
theorem says nothing about a real symmetric matrix — and a real symmetric matrix is what this
estate's transfer-matrix work actually holds: `IsingTransferSym.transferSym` is real, `PerronGap`
and `IsingTopRatio` reason about its eigenvalues, and `TransferPowerSum`'s whole §5 is about the
free energy of that spectrum.

**This file is the Hermitian case, and it needs no algebraic closure because the spectral theorem
supplies what triangularisation would have to.** It is the same shape as
`HermitianSpectralMapping`'s: where the general route needs `IsAlgClosed`, a Hermitian matrix has
`Matrix.IsHermitian.eigenvalues` already, indexed by the vertex type and **real**.

## The two halves, and one is sharper than the equivalence needs

* **`trace_pow_eq_of_multiset_eq`** — equal eigenvalue multisets give equal trace moments, at
  **every** `k`, with no hypothesis. A power sum is a function of the multiset.
* **`multiset_eq_of_trace_pow_eq`** — the converse, from the moments `1 ≤ k ≤ Fintype.card n`
  **only**. `Fintype.card n` of the countably many moments already force the multiset.
* **`multiset_eq_iff_trace_pow_eq`** — the equivalence, stated over all `k` because that is the
  form a consumer meets it in; the finite hypothesis is the theorem above.

The route: `TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` turns each trace moment into
`∑ᵢ (λᵢ : 𝕜)ᵏ` with `λᵢ` real, `RCLike.ofReal_injective` brings the equation back to `ℝ`, and
`PowerSumMultiset.multiset_eq_of_sum_pow_eq` finishes. **Every step already existed**; what did not
exist is the statement.

## What this is NOT

* **It is not similarity.** Equal eigenvalue multisets are not equal matrices — for Hermitian
  matrices they are unitary conjugates, but that is the spectral theorem and is not proved here.
* **It is not the general complex case.** For a non-Hermitian matrix the eigenvalues need not be
  real and `Matrix.IsHermitian.eigenvalues` does not apply;
  `TraceMomentsSpectrum.charpoly_roots_eq_of_trace_pow_eq` is that case and it pays for it with
  `IsAlgClosed`. **Neither theorem subsumes the other**: this one covers `ℝ`, that one covers
  matrices that are not Hermitian.
* **Nothing quantitative.** Two matrices whose trace moments are merely *close* are not shown to
  have close spectra, and `UNLOCK_WATCHLIST`'s `UniformSubTopRatio` item needs exactly that. No cost
  is offered (`ERRATUM 194`, `ERRATUM 246`).
* **It does not re-derive `SpectralActionDetermines`.** That file proves the same equivalence for
  `M · Mᴴ` over `ℂ` with index `Fin n`, by its own route through the spectral action; this is the
  general statement beside it and **nothing there is changed or deleted** (`ERRATUM 373` is about
  duplicates, and the two differ in hypotheses, index type and field).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermitianTraceMoments

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The `k`-th trace moment of a Hermitian matrix, as a sum over its eigenvalue multiset. -/
theorem trace_pow_eq_multiset_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace
      = (Multiset.map (fun x : ℝ => ((x : 𝕜)) ^ k)
          (Multiset.map hA.eigenvalues Finset.univ.val)).sum := by
  rw [TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow hA k, Multiset.map_map]
  rfl

/-- **EQUAL EIGENVALUE MULTISETS GIVE EQUAL TRACE MOMENTS**, at every `k`, no hypotheses. A power
sum is a function of the multiset and of nothing else. -/
theorem trace_pow_eq_of_multiset_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : Multiset.map hA.eigenvalues Finset.univ.val
        = Multiset.map hB.eigenvalues Finset.univ.val) (k : ℕ) :
    (A ^ k).trace = (B ^ k).trace := by
  rw [trace_pow_eq_multiset_sum hA k, trace_pow_eq_multiset_sum hB k, h]

/-- **EQUAL TRACE MOMENTS GIVE EQUAL EIGENVALUE MULTISETS**, from `Fintype.card n` of them.

No algebraic closure: the eigenvalues are real by the spectral theorem, `RCLike.ofReal_injective`
brings the hypothesis down to `ℝ`, and `PowerSumMultiset.multiset_eq_of_sum_pow_eq` is Newton plus
Vieta over any characteristic-zero domain. -/
theorem multiset_eq_of_trace_pow_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ k, 1 ≤ k → k ≤ Fintype.card n → (A ^ k).trace = (B ^ k).trace) :
    Multiset.map hA.eigenvalues Finset.univ.val
      = Multiset.map hB.eigenvalues Finset.univ.val := by
  refine PowerSumMultiset.multiset_eq_of_sum_pow_eq (fun k hk hkn => ?_)
  have hEq := h k hk hkn
  rw [TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow hA k,
    TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow hB k] at hEq
  have hcast : ∀ (f : n → ℝ), ∑ i, ((f i : 𝕜)) ^ k = ((∑ i, f i ^ k : ℝ) : 𝕜) := by
    intro f
    rw [RCLike.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (RCLike.ofReal_pow (f i) k).symm
  rw [hcast hA.eigenvalues, hcast hB.eigenvalues] at hEq
  exact RCLike.ofReal_injective hEq

/-- **THE EQUIVALENCE.** Two Hermitian matrices have the same eigenvalues with the same
multiplicities exactly when all their trace moments agree — and the `←` direction consumes only
the first `Fintype.card n` of them. -/
theorem multiset_eq_iff_trace_pow_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Multiset.map hA.eigenvalues Finset.univ.val
        = Multiset.map hB.eigenvalues Finset.univ.val
      ↔ ∀ k : ℕ, (A ^ k).trace = (B ^ k).trace :=
  ⟨fun h k => trace_pow_eq_of_multiset_eq hA hB h k,
   fun h => multiset_eq_of_trace_pow_eq hA hB fun k _ _ => h k⟩

end HermitianTraceMoments
