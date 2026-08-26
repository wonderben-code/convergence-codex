import PowerSumMultiset
import SpectralActionSpectrum

/-!
# The spectral action DETERMINES the singular values, not merely sees them

`SpectralActionSpectrum` closed with the numbers the remaining gap is about: the action at the
even monomial `X^{2k}` and `Λ = 1` is `4 · ∑ᵢ λᵢᵏ`, where the `λᵢ` are the eigenvalues of
`M · Mᴴ` — the **squared singular values** — and those are non-negative reals. Its own header says
what was still missing:

> **they are wanted over non-negative reals, not over an algebraically closed field.**

`PowerSumMultiset` supplies exactly that, and this file is the composition. What
`SpectralAction §9` established was that the action *sees the Yukawa matrix only through* its
singular values. What is proved here is the converse-shaped statement that makes the seeing
faithful:

> **`eigenvalues_multiset_eq_of_spectralAction_eq`** — if two matrices give the **same spectral
> action at every even monomial `X^{2k}` for `1 ≤ k ≤ n`**, then `M · Mᴴ` and `N · Nᴴ` have the
> **same multiset of eigenvalues**, and hence `M` and `N` the same multiset of singular values.

`n` monomials, at one value of `Λ`. Not a family of `Λ`s, not a limit, not an asymptotic
expansion: the finitely many even moments the action already exposes.

## Which leg does the work, and it is NOT the one the record expected

The watchlist asks for legs (ii) and (iii) *"over non-negative reals"*, as though positivity were
needed to run the argument. It is not, and this file is where that shows:

* **Leg (ii) alone proves the main theorem.** The power sums here are over the eigenvalues of
  `M · Mᴴ` at **every** exponent `1 … n`, because the action's `X^{2k}` already delivers the `k`-th
  power of the SQUARED singular value. Nothing needs a square root and nothing needs a sign.
* **Leg (iii) is what upgrades the conclusion** from the squared singular values to the singular
  values themselves (`singularValues_multiset_eq`), and there
  `SpectralActionSpectrum.eigenvalues_nonneg` is exactly the hypothesis it wants. That is a
  one-line consequence of the main theorem, not a second argument.

## Not covered, per `ERRATUM 60`

* **This is not a statement that `M = N`, and it cannot be — §4 PROVES that**, rather than
  asserting it. `exists_ne_with_same_spectralAction`: for every `M ≠ 0` there is an `N ≠ M` with
  the same action at every even monomial, namely `-M`. The spectral action is blind to the
  unitaries — `M` and `U · M · V` have the same singular values — and the sign is the cheapest
  witness of that blindness. What is proved is that the action determines the singular value
  multiset and **nothing finer**, which is the honest reading of "sees the matrix through its
  singular values", now with a counterexample attached to the "nothing finer".
* It says nothing about odd monomials, about `Λ ≠ 1`, or about non-monomial `f`. `SpectralAction`'s
  `spectralAction_of_no_even_part` already records that the odd part is invisible.
* It gives no bound: equal actions force equal multisets, and nothing here says that *close*
  actions force *close* multisets.
-/

namespace SpectralActionDetermines

open Matrix

variable {n : ℕ}

/-! ## 1. The hypothesis, moved from `ℂ` to `ℝ` -/

/-- The action's values are complex and the eigenvalues are real, so the hypothesis has to cross
once. `4 ≠ 0` and `Complex.ofReal` is injective; nothing else happens here. -/
private lemma sum_pow_eq_of_spectralAction_eq {M N : Matrix (Fin n) (Fin n) ℂ} {k : ℕ}
    (h : SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M
       = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 N) :
    ∑ i, (isHermitian_mul_conjTranspose_self M).eigenvalues i ^ k
      = ∑ i, (isHermitian_mul_conjTranspose_self N).eigenvalues i ^ k := by
  rw [SpectralActionSpectrum.spectralAction_monomial_eq_power_sum,
    SpectralActionSpectrum.spectralAction_monomial_eq_power_sum] at h
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hsum := mul_left_cancel₀ h4 h
  have hcast : ((∑ i, (isHermitian_mul_conjTranspose_self M).eigenvalues i ^ k : ℝ) : ℂ)
      = ((∑ i, (isHermitian_mul_conjTranspose_self N).eigenvalues i ^ k : ℝ) : ℂ) := by
    push_cast
    exact hsum
  exact_mod_cast hcast

/-! ## 2. The theorem -/

/-- **THE SPECTRAL ACTION AT `n` EVEN MONOMIALS DETERMINES THE SQUARED SINGULAR VALUES.**

If `M` and `N` give the same action at `X^{2k}` and `Λ = 1` for every `1 ≤ k ≤ n`, then `M · Mᴴ`
and `N · Nᴴ` have the same multiset of eigenvalues.

**Leg (ii) does all the work.** The action's even monomials hand over the power sums of the
squared singular values at every exponent, so `PowerSumMultiset.multiset_eq_of_sum_pow_eq` applies
directly — with no positivity, and with the Hermitian structure entering only through
`SpectralActionSpectrum`'s composition, which is where it belongs. -/
theorem eigenvalues_multiset_eq_of_spectralAction_eq {M N : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ k, 1 ≤ k → k ≤ n →
      SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M
        = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 N) :
    Multiset.map (isHermitian_mul_conjTranspose_self M).eigenvalues Finset.univ.val
      = Multiset.map (isHermitian_mul_conjTranspose_self N).eigenvalues Finset.univ.val := by
  refine PowerSumMultiset.multiset_eq_of_sum_pow_eq (fun k hk hkn => ?_)
  exact sum_pow_eq_of_spectralAction_eq (h k hk (by simpa using hkn))

/-! ## 3. And the singular values themselves, which is where leg (iii)'s positivity is used -/

/-- **THE SINGULAR VALUES, NOT THEIR SQUARES.** The eigenvalues of `M · Mᴴ` are non-negative
(`SpectralActionSpectrum.eigenvalues_nonneg`), so taking square roots is unambiguous, and equal
multisets of squares give equal multisets of singular values.

This is leg (iii)'s content — a square root made unique by positivity — arriving as a corollary
rather than as a second argument, because the main theorem already delivered the squares. -/
theorem singularValues_multiset_eq {M N : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ k, 1 ≤ k → k ≤ n →
      SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M
        = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 N) :
    Multiset.map (fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self M).eigenvalues i))
        Finset.univ.val
      = Multiset.map (fun i => Real.sqrt ((isHermitian_mul_conjTranspose_self N).eigenvalues i))
        Finset.univ.val := by
  have hbase := eigenvalues_multiset_eq_of_spectralAction_eq h
  have hM : Multiset.map (fun i => Real.sqrt
        ((isHermitian_mul_conjTranspose_self M).eigenvalues i)) Finset.univ.val
      = Multiset.map Real.sqrt
        (Multiset.map (isHermitian_mul_conjTranspose_self M).eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  have hN : Multiset.map (fun i => Real.sqrt
        ((isHermitian_mul_conjTranspose_self N).eigenvalues i)) Finset.univ.val
      = Multiset.map Real.sqrt
        (Multiset.map (isHermitian_mul_conjTranspose_self N).eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [hM, hN, hbase]

/-! ## 4. The cutoff, removed — `Λ = 1` was a convenience of the ingredient, not a hypothesis -/

/-- **AT AN EVEN MONOMIAL THE CUTOFF IS A NONZERO SCALAR AND NOTHING ELSE.**
`spectralAction f Λ M` is `Tr (f (Λ⁻¹ • Dlin M))`, so at `f = X^m` it is `Λ⁻ᵐ` times the value at
`Λ = 1`. Stated for every `m`, even or odd, because the parity plays no part in it. -/
theorem spectralAction_pow_lambda (Λ : ℂ) (m : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    SpectralAction.spectralAction (Polynomial.X ^ m) Λ M
      = Λ⁻¹ ^ m * SpectralAction.spectralAction (Polynomial.X ^ m) 1 M := by
  unfold SpectralAction.spectralAction
  rw [Polynomial.aeval_X_pow, Polynomial.aeval_X_pow, smul_pow, map_smul, smul_eq_mul,
    inv_one, one_smul]

/-- **THE MAIN THEOREM AT EVERY NONZERO CUTOFF.** `§2` is stated at `Λ = 1` because its ingredient
`SpectralAction.trace_pow_eq_spectralAction` is. That is a convenience of the ingredient and not a
hypothesis of the mathematics: at a FIXED `Λ ≠ 0` the two actions differ from their `Λ = 1` values
by the same nonzero scalar `Λ⁻¹ ^ (2k)`, which cancels.

**This is the standing queue item — remove one restrictive hypothesis at a time — and the
hypothesis removed is a `Λ`.** Note what is NOT claimed: the action itself genuinely depends on the
cutoff (`SpectralAction.spectralAction_lambda_dependent` exhibits two different values), so this is
not a statement that `Λ` does not matter. It is that **`Λ` does not matter to what the action
DETERMINES**, which is a different sentence. -/
theorem eigenvalues_multiset_eq_of_spectralAction_eq_lambda {M N : Matrix (Fin n) (Fin n) ℂ}
    {Λ : ℂ} (hΛ : Λ ≠ 0)
    (h : ∀ k, 1 ≤ k → k ≤ n →
      SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) Λ M
        = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) Λ N) :
    Multiset.map (isHermitian_mul_conjTranspose_self M).eigenvalues Finset.univ.val
      = Multiset.map (isHermitian_mul_conjTranspose_self N).eigenvalues Finset.univ.val := by
  refine eigenvalues_multiset_eq_of_spectralAction_eq (fun k hk hkn => ?_)
  have hpow : (Λ⁻¹ : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (inv_ne_zero hΛ)
  have hk' := h k hk hkn
  -- Explicit arguments: a bare `rw` rewrites the LHS twice, because the `1` created by the
  -- first rewrite matches the `Λ` of the second.
  rw [spectralAction_pow_lambda Λ (2 * k) M, spectralAction_pow_lambda Λ (2 * k) N] at hk'
  exact mul_left_cancel₀ hpow hk'

/-! ## 5. The conclusion cannot be strengthened, and that is a theorem rather than a caveat -/

/-- **THE SAME ACTION AT EVERY EVEN MONOMIAL DOES NOT FORCE THE SAME MATRIX.** `-M` and `M` give
the same `M · Mᴴ`, hence the same action at every `X^{2k}` and every `Λ`.

Written because §2's docstring says the conclusion *"is not a statement that `M = N`, and it cannot
be"*, and a caveat asserted is worth less than a witness exhibited (`PROOF_STRATEGY` §7: fold back
by proving more). The sign is the cheapest witness; it is not the only one — any `U · M · V` with
`U`, `V` unitary does the same — but one witness settles the question the caveat raises. -/
theorem spectralAction_eq_neg (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 (-M)
      = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M := by
  rw [← SpectralAction.trace_pow_eq_spectralAction, ← SpectralAction.trace_pow_eq_spectralAction,
    conjTranspose_neg, neg_mul_neg]

/-- **AND THE TWO MATRICES ARE GENUINELY DIFFERENT WHENEVER `M ≠ 0`.** So the hypothesis of §2 is
satisfiable by a pair that is not a pair of equal matrices, and §2's conclusion is exactly as
strong as it can be. -/
theorem exists_ne_with_same_spectralAction {M : Matrix (Fin n) (Fin n) ℂ} (hM : M ≠ 0) :
    ∃ N : Matrix (Fin n) (Fin n) ℂ, N ≠ M ∧
      ∀ k, SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 N
         = SpectralAction.spectralAction (Polynomial.X ^ (2 * k)) 1 M :=
  ⟨-M, fun h => hM (by
      -- `IsAddTorsionFree` is not found for a matrix type, so the cancellation is done
      -- entrywise, where it is `ℂ`'s.
      ext i j
      have hij := congrFun (congrFun h i) j
      simp only [Matrix.neg_apply] at hij
      simpa using neg_eq_self.mp hij),
    fun k => spectralAction_eq_neg M k⟩

end SpectralActionDetermines
