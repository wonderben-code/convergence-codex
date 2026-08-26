import TransferPowerSum

/-!
# The TOP eigenvalue maps, without Newton's identities

`TransferPowerSum` §6 proved that **all power sums** of `(hA.pow k).eigenvalues` and of
`hA.eigenvalues ^ k` agree, and said what it is not: over `ℝ` those two families are then equal as
multisets, but only via Newton's identities, which `UNLOCK_WATCHLIST`'s trace-moments item calls
legs (ii) and (iii) and which nobody has built.

`PROOF_STRATEGY` §6 question 3 asks, of the thing most recently refused, *what is B* — the weaker
statement that is reachable now. **This file is that B.** The full multiset identification needs
Newton. The **largest** eigenvalue needs only the variational characterisation, which this estate
already has, and that is what the Perron chain actually consumes.

**^ "THE FULL MULTISET IDENTIFICATION NEEDS NEWTON" IS FALSE, 26 AUGUST 2026, AND SO IS THE SAME
CLAIM FOUR LINES ABOVE.** Both kept verbatim (`ERRATUM 94`); **neither is an erratum** — they were
exact when written on 22 August, and the theorem that refutes them landed four days later.

`HermitianSpectralMapping.eigenvalues_pow_multiset` proves the full multiset identification for a
Hermitian matrix **with no Newton identities and no power sums at all**. The route is the
characteristic polynomial: Mathlib's `Matrix.IsHermitian.charpoly_eq` writes `A.charpoly` as
`∏ᵢ (X − C λᵢ)`, the conjugation in the spectral theorem is a `StarAlgEquiv` so it commutes with
the power, and the roots of a characteristic polynomial ARE the eigenvalue multiset.

**WHAT THIS FILE'S B WAS RIGHT ABOUT, AND IT IS THE USEFUL HALF.** Newton IS the only route from
*equal power sums* to *equal multisets*, and that statement — the watchlist item's legs (ii) and
(iii) — remains unbuilt and is still the only route for a NON-Hermitian matrix. What was wrong was
identifying that route's difficulty with the problem's: **power sums are how one reaches a multiset
when nothing better is available, and for a Hermitian matrix something better is available.** That
is `ERRATUM 278`'s shape — one route's obstacle read as the statement's — and this is its second
instance in two days, which is why it is written out rather than quietly amended.

**THIS FILE IS NOT WITHDRAWN AND ITS THEOREMS ARE NOT DUPLICATES.** `eigenvalues_pow_le_max` and
`le_max_eigenvalues_pow` are now each one line from `exists_eigenvalue_pow_eq`, and they are kept
because their proofs go the other way — through the variational characterisation and
`eigenvalues_le_of_quadForm_le`, the converse that was *"absent until now"*. **Two routes to one
statement is not a duplicate**; it is the thing this estate keeps both of, and the second route is
what makes the first one's cost visible.

> **`eigenvalues_le_of_quadForm_le`** — the converse of
> `RayleighMatrix.quadForm_le_of_eigenvalues_le`: a uniform bound on the quadratic form bounds
> every eigenvalue. Two lines, and absent until now.
>
> **`quadForm_pow_eq_sum`** — the quadratic form of `A ^ k` in **`A`'s** eigencoordinates:
> `⟪v, A^k v⟫ = ∑ λⱼ^k · cⱼ²`. `RayleighMatrix.quadForm_eq_sum` is the case `k = 1`.
>
> **`eigenvalues_pow_le_max`** and **`le_max_eigenvalues_pow`** — hence every eigenvalue of `A ^ k`
> is at most `maxⱼ λⱼ^k`, and that value is attained.
>
> **`max_eigenvalues_pow`** — **the top eigenvalue of `A ^ k` IS the largest `k`-th power of an
> eigenvalue of `A`.** The top-eigenvalue spectral mapping, for a real symmetric matrix.

**WHAT THIS IS NOT.** It is not the spectral mapping theorem. It identifies **one** value in each
family — the maximum — and says nothing about the rest, about multiplicities, or about the order
of the two lists. `TransferPowerSum` §6's note stands unchanged: the full statement needs Newton
and is not proved anywhere here.

**AND IT IS NOT A MASS GAP.** Everything below is about one finite symmetric matrix.
-/

namespace RayleighPow

open Matrix Finset RayleighMatrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ## 1. The converse of the variational inequality

`RayleighMatrix.quadForm_le_of_eigenvalues_le` bounds the form from a bound on the eigenvalues.
This is the other direction, and it is the one that lets a bound proved in **one** eigenbasis be
read off in **another** — which is the whole difficulty with `A` and `A ^ k`.
-/

/-- **A UNIFORM BOUND ON THE QUADRATIC FORM BOUNDS EVERY EIGENVALUE.** Evaluate at the `j`-th
eigenvector, whose norm is `1`. -/
theorem eigenvalues_le_of_quadForm_le {B : Matrix n n ℝ} (hB : B.IsHermitian) {C : ℝ}
    (h : ∀ v : EuclideanSpace ℝ n, inner ℝ v (mv B v) ≤ C * inner ℝ v v) (j : n) :
    hB.eigenvalues j ≤ C := by
  set b := (hB.eigenvectorBasis j : EuclideanSpace ℝ n) with hb
  have hnorm : inner ℝ b b = (1 : ℝ) := by
    have h1 : ‖b‖ = 1 := (hB.eigenvectorBasis).orthonormal.1 j
    have := real_inner_self_eq_norm_sq b
    rw [this, h1]; norm_num
  have hq : inner ℝ b (mv B b) = hB.eigenvalues j := by
    rw [mv_eigenvectorBasis hB, real_inner_smul_right, hnorm, mul_one]
  have := h b
  rw [hq, hnorm, mul_one] at this
  exact this

/-! ## 2. The quadratic form of a power, in the base matrix's eigencoordinates -/

/-- A power of `A` acts on `A`'s eigenvectors by the power of the eigenvalue. -/
theorem mv_pow_eigenvectorBasis (hA : A.IsHermitian) (k : ℕ) (j : n) :
    mv (A ^ k) (hA.eigenvectorBasis j) = hA.eigenvalues j ^ k • (hA.eigenvectorBasis j) := by
  induction k with
  | zero => simp [mv, Matrix.one_mulVec]
  | succ m ih =>
      have hstep : mv (A ^ (m + 1)) (hA.eigenvectorBasis j)
          = mv A (mv (A ^ m) (hA.eigenvectorBasis j)) := by
        unfold mv
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      rw [hstep, ih, mv_smul, mv_eigenvectorBasis hA, smul_smul, pow_succ, mul_comm]

/-- **THE QUADRATIC FORM OF `A ^ k`, IN `A`'S OWN EIGENCOORDINATES.**
`RayleighMatrix.quadForm_eq_sum` is the case `k = 1`. -/
theorem quadForm_pow_eq_sum (hA : A.IsHermitian) (k : ℕ) (v : EuclideanSpace ℝ n) :
    inner ℝ v (mv (A ^ k) v) = ∑ j, hA.eigenvalues j ^ k * (coeff hA v j) ^ 2 := by
  have hpar := (hA.eigenvectorBasis).sum_inner_mul_inner v (mv (A ^ k) v)
  refine hpar.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  have h1 : inner ℝ (hA.eigenvectorBasis j) (mv (A ^ k) v)
      = hA.eigenvalues j ^ k * coeff hA v j := by
    rw [mv_adjoint (hA.pow k), mv_pow_eigenvectorBasis hA, real_inner_smul_left, coeff]
  have h2 : inner ℝ v (hA.eigenvectorBasis j) = coeff hA v j := real_inner_comm _ _
  change inner ℝ v (hA.eigenvectorBasis j) * inner ℝ (hA.eigenvectorBasis j) (mv (A ^ k) v)
      = hA.eigenvalues j ^ k * coeff hA v j ^ 2
  rw [h1, h2]; ring

/-! ## 3. The top eigenvalue maps -/

/-- Every eigenvalue of `A ^ k` is at most the largest `k`-th power of an eigenvalue of `A`. -/
theorem eigenvalues_pow_le_max (hA : A.IsHermitian) (k : ℕ) {p : n}
    (hp : ∀ j, hA.eigenvalues j ^ k ≤ hA.eigenvalues p ^ k) (j : n) :
    (hA.pow k).eigenvalues j ≤ hA.eigenvalues p ^ k := by
  refine eigenvalues_le_of_quadForm_le (hA.pow k) (fun v => ?_) j
  rw [quadForm_pow_eq_sum hA, normSq_eq_sum hA, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp i) (sq_nonneg _)

/-- And that value is **attained**: it is at most some eigenvalue of `A ^ k`. The witness is
`A`'s own `p`-th eigenvector, which `A ^ k` scales by `λₚ^k`. -/
theorem le_max_eigenvalues_pow [Nonempty n] (hA : A.IsHermitian) (k : ℕ) (p : n) :
    ∃ j, hA.eigenvalues p ^ k ≤ (hA.pow k).eigenvalues j := by
  by_contra hcon
  push Not at hcon
  set b := (hA.eigenvectorBasis p : EuclideanSpace ℝ n) with hb
  have hnorm : inner ℝ b b = (1 : ℝ) := by
    have h1 : ‖b‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 p
    have := real_inner_self_eq_norm_sq b
    rw [this, h1]; norm_num
  have hlt : ∀ j, (hA.pow k).eigenvalues j < hA.eigenvalues p ^ k := fun j => hcon j
  have hq : inner ℝ b (mv (A ^ k) b) = hA.eigenvalues p ^ k := by
    rw [mv_pow_eigenvectorBasis hA, real_inner_smul_right, hnorm, mul_one]
  obtain ⟨q, -, hq'⟩ :=
    Finset.exists_max_image (univ : Finset n) (hA.pow k).eigenvalues Finset.univ_nonempty
  have hbound : inner ℝ b (mv (A ^ k) b) ≤ (hA.pow k).eigenvalues q * inner ℝ b b :=
    quadForm_le_of_eigenvalues_le (hA.pow k) (fun j => hq' j (mem_univ j)) b
  rw [hq, hnorm, mul_one] at hbound
  exact absurd hbound (not_le.mpr (hlt q))

/-- **THE TOP EIGENVALUE OF `A ^ k` IS THE LARGEST `k`-TH POWER OF AN EIGENVALUE OF `A`.**
The top-eigenvalue half of the spectral mapping theorem, for a real symmetric matrix, proved from
the variational characterisation alone — **no Newton's identities, no multiset argument, and no
claim about any eigenvalue but the largest.** -/
theorem max_eigenvalues_pow [Nonempty n] (hA : A.IsHermitian) (k : ℕ) {p : n}
    (hp : ∀ j, hA.eigenvalues j ^ k ≤ hA.eigenvalues p ^ k) {q : n}
    (hq : ∀ j, (hA.pow k).eigenvalues j ≤ (hA.pow k).eigenvalues q) :
    (hA.pow k).eigenvalues q = hA.eigenvalues p ^ k := by
  refine le_antisymm (eigenvalues_pow_le_max hA k hp q) ?_
  obtain ⟨j, hj⟩ := le_max_eigenvalues_pow hA k p
  exact hj.trans (hq j)

end RayleighPow
