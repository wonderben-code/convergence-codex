import TracePowerSpectrum
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The eigenvalue multiset of `Aᵏ` is the multiset of `k`-th powers, for Hermitian `A`

`UNLOCK_WATCHLIST`'s trace-moment item wants *"equal trace moments imply the same eigenvalue
multiset"* and splits it into three legs. Leg (i) — `Tr(Aᵏ) = ∑ λᵢᵏ` — landed on 16 August as
`TracePowerSpectrum.trace_pow_eq_sum_roots_charpoly`. Legs (ii) and (iii) — *power sums determine
the elementary symmetric functions, and equal characteristic polynomials give the same root
multiset* — are the block's own **project leg**, costed by probe on 16 August: Mathlib's Newton
identities live over `MvPolynomial σ R` with `[Fintype σ]`, **there is no multiset `psum` and no
multiset Newton**, and the work is ordering a root multiset as a `Fin n`-family and inducting.

**THE CONSUMER DOES NOT NEED THAT ROUTE.** The block records what legs (ii) and (iii) were wanted
FOR, on 22 August: with them, `TransferPowerSum.sum_eigenvalues_pow_pow` *"becomes a multiset
equality, which is the EIGENVALUE-FAMILY SPECTRAL MAPPING THEOREM"* — and `ERRATUM 222` established
by probe that neither this estate nor Mathlib has that in any form. **For a HERMITIAN matrix the
spectral mapping needs no power sums at all**, and this file is that: the spectral theorem writes
`A` as a unitary conjugate of a diagonal, conjugation is an algebra map so it commutes with the
power, and the characteristic polynomial does not see the conjugation.

**The pattern is a cousin of `ERRATUM 274`'s and `ERRATUM 278`'s and not the same thing**, and the
difference is worth stating. There, a HYPOTHESIS in a statement belonged to its proof. Here nothing
is over-hypothesised: legs (ii) and (iii) are a genuine route to the multiset, and the item costed
them honestly. What the item did not say is that they are *one* route. Power sums are how one
reaches a multiset when nothing better is available; for a Hermitian matrix the characteristic
polynomial is available, and it gives the multiset directly.

## What is proved

* **`charpoly_pow_eq`** — for Hermitian `A`, `(Aᵏ).charpoly = ∏ᵢ (X − C (λᵢᵏ))`. Mathlib's
  `Matrix.IsHermitian.charpoly_eq` is `k = 1`; the proof here is that one with `map_pow` and
  `Matrix.diagonal_pow` inserted, because `Unitary.conjStarAlgAut` is a `StarAlgEquiv`.
* **`eigenvalues_pow_multiset`** — hence the multiset of eigenvalues of `Aᵏ` is the multiset of
  `k`-th powers of the eigenvalues of `A`. **Stated as a multiset equality and not pointwise**,
  which is the honest form: `Matrix.IsHermitian.eigenvalues` is indexed by Mathlib's own choice of
  eigenvector basis, and nothing makes the `i`-th eigenvalue of `Aᵏ` the `k`-th power of the `i`-th
  eigenvalue of `A`.
* **`sum_eigenvalues_pow`** — the corollary a consumer uses: any sum over the eigenvalues of `Aᵏ`
  equals the same sum over the `k`-th powers.

## What is NOT proved, stated per `ERRATUM 60`

* **Legs (ii) and (iii) are untouched and the watchlist item does not close.** This file proves the
  spectral mapping for Hermitian matrices by a different route; it says nothing about whether equal
  power sums force equal multisets, which is what the item asks and what a NON-Hermitian consumer
  would still need.
* nothing about singular values as such. The singular values of `M` are the square roots of the
  eigenvalues of `M · Mᴴ`; that bridge is not built here.
* no claim that any downstream file is rewired, and **no claim that this closes the consumer gap
  the watchlist block names**. That gap is *"the gap is proved about the eigenvalues of `T` and
  `IsingTransferSym.partition2_eq_sum_eigenvalues` is stated about the eigenvalues of `T^(M+1)`,
  and nothing identifies the two families"* — and **for SUMS it is already closed**:
  `TransferPowerSum.partition2_eq_sum_eigenvalues_pow` proves
  `partition2 β n M = ∑ᵢ λᵢ^(M+1)` through the trace identity, without any multiset. Checked by
  reading `TransferPowerSum.lean`, not by reading the block.
  **What is new here is the FAMILY, not the sum.** `ERRATUM 222` probed for the eigenvalue-family
  spectral mapping theorem and found it absent from both this estate and Mathlib; the sum
  statements do not give it, because a sum is one functional of a multiset and the multiset
  determines all of them. `sum_map_eigenvalues_pow` is that difference made concrete.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermitianSpectralMapping

open Matrix Polynomial

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- **THE CHARACTERISTIC POLYNOMIAL OF A POWER.** `Matrix.IsHermitian.charpoly_eq` is `k = 1`.
The conjugation in the spectral theorem is a `StarAlgEquiv`, so it commutes with `(· ^ k)`, and
the characteristic polynomial does not see it. -/
theorem charpoly_pow_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).charpoly = ∏ i, (X - Polynomial.C (((hA.eigenvalues i : ℝ) : 𝕜) ^ k)) := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Matrix.diagonal_pow,
      Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

/-- **THE EIGENVALUE-FAMILY SPECTRAL MAPPING THEOREM, HERMITIAN CASE.** The eigenvalues of `Aᵏ`,
with multiplicity, are the `k`-th powers of the eigenvalues of `A`.

**A multiset equality, deliberately.** `Matrix.IsHermitian.eigenvalues` is indexed by a choice of
eigenvector basis, and no pointwise statement is true: the `i`-th eigenvalue of `Aᵏ` need not be the
`k`-th power of the `i`-th eigenvalue of `A`. -/
theorem eigenvalues_pow_multiset {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    Multiset.map (hA.pow k).eigenvalues Finset.univ.val
      = Multiset.map (fun i => hA.eigenvalues i ^ k) Finset.univ.val := by
  have hroots : (A ^ k).charpoly.roots
      = Multiset.map (fun i => (((hA.eigenvalues i : ℝ) : 𝕜)) ^ k) Finset.univ.val := by
    rw [charpoly_pow_eq hA k, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · simp only [Finset.prod_ne_zero_iff]
      intro a _
      exact Polynomial.X_sub_C_ne_zero _
  have h1 := (hA.pow k).roots_charpoly_eq_eigenvalues
  rw [hroots] at h1
  have h2 : Multiset.map (RCLike.ofReal (K := 𝕜))
        (Multiset.map (fun i => hA.eigenvalues i ^ k) Finset.univ.val)
      = Multiset.map (RCLike.ofReal (K := 𝕜))
        (Multiset.map (hA.pow k).eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    simpa only [Function.comp_def, RCLike.ofReal_pow] using h1
  exact (Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜)) h2).symm

/-- **THE FORM A CONSUMER USES**, for an arbitrary `g`.

**`TransferPowerSum.sum_eigenvalues_pow` is the `g = id` case and already exists** (found by
`grep`-ing the name before writing it, `ERRATUM 270`). It is proved the other way round — from
`sum_eigenvalues_pow_pow`, i.e. from the trace identity, both sides being `tr (A^(k·m))` — so it
needs no multiset statement and this one is not a replacement for it. What the multiset gives is
every `g` at once, which the trace route cannot reach: `tr` is one particular `g`. -/
theorem sum_map_eigenvalues_pow {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) {M : Type*}
    [AddCommMonoid M] (g : ℝ → M) :
    ∑ i, g ((hA.pow k).eigenvalues i) = ∑ i, g (hA.eigenvalues i ^ k) := by
  have h := congrArg (Multiset.map g) (eigenvalues_pow_multiset hA k)
  simpa only [Multiset.map_map, Finset.sum, Function.comp_def] using
    congrArg Multiset.sum h

/-- **EVERY EIGENVALUE OF `Aᵏ` IS A `k`-TH POWER OF AN EIGENVALUE OF `A`.** The membership form of
the multiset equality, and the form that makes the two `RayleighPow` bounds one-liners.

**They are NOT restated here** (`ERRATUM 271`): `RayleighPow.eigenvalues_pow_le_max` and
`RayleighPow.le_max_eigenvalues_pow` exist and restating them under new names would be a duplicate,
which is the defect this estate has caught four times this week. What is worth recording is that
each is now one line from this lemma — the first by rewriting the eigenvalue as some `λⱼᵏ` and
applying the hypothesis at `j`, the second by taking `i` with `(hA.pow k).eigenvalues i` the image
of `p` — and that their own proofs go a different way, through the variational characterisation.
**Two routes to one statement is not a duplicate; it is the thing the estate keeps both of.** -/
theorem exists_eigenvalue_pow_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) (i : n) :
    ∃ j, (hA.pow k).eigenvalues i = hA.eigenvalues j ^ k := by
  have hmem : (hA.pow k).eigenvalues i
      ∈ Multiset.map (hA.pow k).eigenvalues Finset.univ.val :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ i))
  rw [eigenvalues_pow_multiset hA k, Multiset.mem_map] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

end HermitianSpectralMapping
