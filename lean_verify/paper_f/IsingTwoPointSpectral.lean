import IsingTwoPoint
import IsingTransferSym
import TransferPowerSum
import HermitianTwoPointTrace

/-!
# The strip's two-point function, in the eigenvalues

`TransferPowerSum` §2 put the **partition function** of the two-dimensional Ising strip in the
eigenvalues of its own symmetrised transfer matrix: `partition2 = ∑ₚ λₚᴹ⁺¹`. That is the
denominator of every correlation function and it is **not** proved again here.

This file supplies the numerator, and the numerator is where a correlation function differs from a
partition function: two exponents landing on **two different** eigenvalues, with a matrix element
of the observable between them. Getting there needs one thing `TransferPowerSum` did not:
`IsingTwoPoint.corr2Sep_eq_trace_div` states the two-point function over `transfer2`, and
`transfer2` is **not** Hermitian — `IsingTransferSym` exists precisely because the column's own
weight sits on one side of it. A trace of a *power* survives that (`trace_transferSym_pow`);
a trace with an observable inserted twice does not, and has to be earned.

## What is proved

* **`conj_mul_conj`** and **`pow_conj`** — for an explicit inverse pair `P · Q = 1`, two conjugates
  multiply as the conjugate of the product, and hence `(Q · B · P)ᵏ = Q · Bᵏ · P`. Stated over
  `CommRing` from **one** hypothesis: `mul_eq_one_comm` supplies the other side;
* **`diagonal_comm`** — diagonal matrices commute. Absent from Mathlib (probed) and from this
  estate (probed), and stated over `NonUnitalNonAssocCommSemiring`, which is what its two
  ingredients ask for and no more;
* **`halfIntraInv`** and its two inverse laws — the diagonal factor `IsingTransferSym` splits in
  half is invertible, explicitly, with no `Nonsing` machinery — together with
  **`isUnit_halfIntraInv`** and **`inv_halfIntraInv`**, which hand that explicit inverse to
  Mathlib's `⁻¹` so that `Matrix.trace_conj` applies verbatim rather than being re-proved;
* **`transferSym_pow_eq_conj`** — `transferSymᵏ = H⁻¹ · transfer2ᵏ · H`;
* **`trace_two_point_sym`** — **for any DIAGONAL insertion**, the two-point trace is the same for
  both matrices. The diagonal hypothesis is what the proof needs and it is exactly what the spin
  observable satisfies: `H⁻¹` and `D` commute, so the conjugation cancels between the two factors.
  This is the step that has no analogue in `TransferPowerSum`, where nothing is inserted;
* **`spinEigen`** and **`spinEigen_symm`** — the spin observable read in the eigenbasis of the
  symmetrised transfer matrix, and its symmetry;
* **`corr2Sep_eq_spectral`** — hence the two-point function of the strip is
  `(∑ₚ ∑_q ‖Bₚq‖² · λ_qᵏ · λₚᴹ⁺¹⁻ᵏ) / (∑ₚ λₚᴹ⁺¹)`, with `λ` the eigenvalues of the symmetrised
  transfer matrix and `B = spinEigen`;
* **`spectral_numerator_symm`** — and the formula passes the check `corr2Sep_neg` imposes on it:
  it is invariant under swapping the two exponents, for a reason sharing no step with the
  combinatorial proof of that symmetry. §7 says what the check catches and what it cannot.

## What this is NOT

**It is not decay and not a mass gap.** It is the formula a decay estimate is read off, with every
coefficient real and non-negative (`trace_mul_pow_mul_pow_self`) so that no term cancels another.
What is missing is unchanged and is one sentence: **the top eigenvalue simple and dominant,
uniformly in the width.** At *fixed* width `PerronSimple` and `PerronGap` supply it — the strip's
transfer matrix is strictly positive (`transferSym_pos`) — and every limit available here is in the
length, which `WALLS` §W4 §6 item 2 says is not a two-dimensional mass gap.

**And even at fixed width, this is not yet exponential decay in the separation.**
`IsingTwoPoint.corr2Sep_neg` proves the two-point function is symmetric about the midpoint of the
strip, so decay in `k` is *false* at finite length; the two exponents `k` and `M + 1 - k` below are
that symmetry, visible. Any decay statement has to be about `min k (M + 1 - k)`, or has to take
`M → ∞` first, and neither is done here.

**And no eigenvalue is ordered.** `λₚ` is Mathlib's `eigenvalues`, an unordered family indexed by
the columns; nothing below says which index carries the largest one, and `corr2Sep_eq_spectral`
is a sum over all pairs, not a leading term plus a remainder.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace IsingTwoPointSpectral

open IsingTransfer2D IsingTransferSym IsingTwoPoint HermitianTwoPointTrace Real

open scoped Matrix

/-! ## 1. Conjugation by an explicit inverse pair

Both statements below take **one** hypothesis, `P · Q = 1`. The other side is not assumed:
`mul_eq_one_comm` supplies it, square matrices over a commutative ring being Dedekind
finite. -/

section Conj

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

/-- **TWO CONJUGATES MULTIPLY AS THE CONJUGATE OF THE PRODUCT.** The inner `P · Q` cancels; this is
the whole content of a conjugation, and everything below is this lemma applied. -/
theorem conj_mul_conj (P Q A B : Matrix α α R) (hPQ : P * Q = 1) :
    Q * A * P * (Q * B * P) = Q * (A * B) * P := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul]

/-- **A CONJUGATE'S POWERS ARE THE CONJUGATE OF THE POWERS.** -/
theorem pow_conj (P Q B : Matrix α α R) (hPQ : P * Q = 1) :
    ∀ k : ℕ, (Q * B * P) ^ k = Q * B ^ k * P
  | 0 => by
    rw [pow_zero, pow_zero, Matrix.mul_one]
    exact (mul_eq_one_comm.mp hPQ).symm
  | k + 1 => by
    rw [pow_succ, pow_conj P Q B hPQ k, conj_mul_conj P Q (B ^ k) B hPQ, ← pow_succ]

/-- **DIAGONAL MATRICES COMMUTE**, over any commutative coefficient. Absent from Mathlib by name
and by shape (probed 2026-08-22: no `diagonal_comm`, no `Commute` lemma mentioning `diagonal`) and
absent from this estate. Stated over `NonUnitalNonAssocCommSemiring`, which is exactly what the two
lemmas it consumes ask for — `Matrix.diagonal_mul_diagonal` needs no unit and no associativity, and
the entrywise step needs only `mul_comm`. -/
theorem diagonal_comm {S : Type*} [NonUnitalNonAssocCommSemiring S] (d e : α → S) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact Matrix.diagonal_eq_diagonal_iff.mpr fun σ => mul_comm _ _

end Conj

/-! ## 2. The diagonal factor is invertible, explicitly -/

variable {n : ℕ}

/-- The inverse of `halfIntra`, written down rather than obtained. -/
noncomputable def halfIntraInv (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  Matrix.diagonal fun σ => exp (-(β * intra σ / 2))

theorem halfIntra_mul_inv (β : ℝ) (n : ℕ) : halfIntra β n * halfIntraInv β n = 1 := by
  rw [halfIntra, halfIntraInv, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun σ => ?_).trans Matrix.diagonal_one
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem halfIntraInv_mul (β : ℝ) (n : ℕ) : halfIntraInv β n * halfIntra β n = 1 := by
  rw [halfIntra, halfIntraInv, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun σ => ?_).trans Matrix.diagonal_one
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- The explicit inverse handed to Mathlib: `halfIntraInv` is a unit, witnessed by the two laws
above rather than by a one-sided criterion. -/
theorem isUnit_halfIntraInv (β : ℝ) (n : ℕ) : IsUnit (halfIntraInv β n) :=
  ⟨⟨halfIntraInv β n, halfIntra β n, halfIntraInv_mul β n, halfIntra_mul_inv β n⟩, rfl⟩

/-- …and `halfIntra` is Mathlib's `⁻¹` of it, so `Matrix.trace_conj` applies verbatim and is not
re-proved here. -/
theorem inv_halfIntraInv (β : ℝ) (n : ℕ) : (halfIntraInv β n)⁻¹ = halfIntra β n :=
  Matrix.inv_eq_right_inv (halfIntraInv_mul β n)

/-- **CONJUGATION BY THE DIAGONAL FACTOR DOES NOT MOVE A TRACE.** This is Mathlib's
`Matrix.trace_conj`, reached through the two bridge lemmas above rather than restated. -/
theorem trace_conj_halfIntra (β : ℝ) (n : ℕ) (X : Matrix (Col n) (Col n) ℝ) :
    (halfIntraInv β n * X * halfIntra β n).trace = X.trace := by
  rw [← inv_halfIntraInv β n]
  exact Matrix.trace_conj (isUnit_halfIntraInv β n) X

/-! ## 3. The symmetrised matrix is a diagonal conjugate

`IsingTransferSym`'s header already says the two matrices are "conjugate by a diagonal matrix"; what
it proves is the consequence it needed there, `trace_transferSym_pow`, by a cyclicity argument that
never names the conjugating matrix. Naming it is what §4 consumes. -/

theorem transferSym_eq_conj (β : ℝ) (n : ℕ) :
    transferSym β n = halfIntraInv β n * transfer2 β n * halfIntra β n := by
  rw [transfer2_eq, transferSym]
  simp only [← Matrix.mul_assoc]
  rw [halfIntraInv_mul, Matrix.one_mul]

theorem transferSym_pow_eq_conj (β : ℝ) (n : ℕ) (k : ℕ) :
    transferSym β n ^ k = halfIntraInv β n * transfer2 β n ^ k * halfIntra β n := by
  rw [transferSym_eq_conj]
  exact pow_conj (halfIntra β n) (halfIntraInv β n) (transfer2 β n) (halfIntra_mul_inv β n) k

/-! ## 4. A diagonal insertion does not see the conjugation -/

/-- The insertion slides through the left-hand factor: this is the only place the diagonality of
the observable is used, and it is used once. -/
theorem diag_mul_transferSym_pow (β : ℝ) (n : ℕ) (d : Col n → ℝ) (k : ℕ) :
    Matrix.diagonal d * transferSym β n ^ k
      = halfIntraInv β n * (Matrix.diagonal d * transfer2 β n ^ k) * halfIntra β n := by
  rw [transferSym_pow_eq_conj]
  simp only [← Matrix.mul_assoc]
  rw [halfIntraInv, diagonal_comm]

/-- **THE TWO-POINT TRACE IS THE SAME FOR BOTH MATRICES**, for any DIAGONAL insertion — which is
what the spin observable is.

This is the statement `IsingTransferSym.trace_transferSym_pow` does **not** give: there the trace
has one factor and cyclicity moves the diagonal weight around it, here it has two and the weight
would have to pass through the observable. It does, because the observable is diagonal too, and
that hypothesis is not decoration — for a general insertion the two traces differ. -/
theorem trace_two_point_sym (β : ℝ) (n : ℕ) (d : Col n → ℝ) (k m : ℕ) :
    (Matrix.diagonal d * transferSym β n ^ k * Matrix.diagonal d * transferSym β n ^ m).trace
      = (Matrix.diagonal d * transfer2 β n ^ k * Matrix.diagonal d * transfer2 β n ^ m).trace := by
  rw [Matrix.mul_assoc (Matrix.diagonal d * transferSym β n ^ k),
    diag_mul_transferSym_pow, diag_mul_transferSym_pow,
    conj_mul_conj (halfIntra β n) (halfIntraInv β n) _ _ (halfIntra_mul_inv β n),
    trace_conj_halfIntra, Matrix.mul_assoc (Matrix.diagonal d * transfer2 β n ^ k)]

/-! ## 5. The observable in the eigenbasis -/

/-- The spin observable is a real diagonal matrix, hence Hermitian. -/
theorem isHermitian_spinDiag (n : ℕ) (i : Fin (n + 1)) :
    (Matrix.diagonal fun σ : Col n => spin (σ i)).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- **THE SPIN OBSERVABLE READ IN THE EIGENBASIS** of the symmetrised transfer matrix. The squares
of its entries are the coefficients of the two-point function. -/
noncomputable def spinEigen (β : ℝ) (n : ℕ) (i : Fin (n + 1)) : Matrix (Col n) (Col n) ℝ :=
  ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ
    * (Matrix.diagonal fun σ : Col n => spin (σ i))
    * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)

theorem spinEigen_isHermitian (β : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    (spinEigen β n i).IsHermitian :=
  isHermitian_conj (isHermitian_spinDiag n i) _

/-- Over `ℝ` Hermitian is symmetric, so the coefficient matrix is symmetric. -/
theorem spinEigen_symm (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (p q : Col n) :
    spinEigen β n i p q = spinEigen β n i q p := by
  simpa using ((spinEigen_isHermitian β n i).apply p q).symm

/-! ## 6. The strip, read in its spectrum -/

/-- **THE TWO-POINT FUNCTION OF THE STRIP, IN THE EIGENVALUES.** Every coefficient
`‖spinEigen p q‖²` is real and non-negative, so no term of the numerator cancels another; the two
exponents land on different eigenvalues, which is why this is a two-point function and not a
partition function.

The denominator is `TransferPowerSum.partition2_eq_sum_eigenvalues_pow` and is not proved here.

**It is still not decay.** Reading a decay rate off this requires knowing which `λₚ` is largest,
that it is simple, and that the gap to the next survives the width — and, before any of that, a
separation variable in which decay is not forbidden by `corr2Sep_neg`. See the header. -/
theorem corr2Sep_eq_spectral (β : ℝ) (n M : ℕ) (k : Fin (M + 1)) (i : Fin (n + 1)) :
    corr2Sep β n M k i
      = (∑ p, ∑ q, ‖spinEigen β n i p q‖ ^ 2
            * ((transferSym_isHermitian β n).eigenvalues q ^ (k : ℕ)
              * (transferSym_isHermitian β n).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (transferSym_isHermitian β n).eigenvalues p ^ (M + 1) := by
  rw [spinEigen, corr2Sep_eq_trace_div, ← trace_two_point_sym, ← partition2_eq_trace,
    TransferPowerSum.partition2_eq_sum_eigenvalues_pow,
    trace_mul_pow_mul_pow_self (transferSym_isHermitian β n) (isHermitian_spinDiag n i)]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-! ## 7. That the formula is the right one

`IsingTwoPoint.corr2Sep_neg` proves, by reindexing the configuration sum, that the strip's
two-point function at separation `k` and at separation `M + 1 - k` are **the same number**. Any
correct spectral formula must therefore be invariant under swapping its two exponents, and §6's is
— for a reason with no step in common with the combinatorial proof: `Finset.sum_comm` and the
symmetry of `spinEigen`. -/

/-- **THE NUMERATOR IS SYMMETRIC UNDER SWAPPING THE TWO EXPONENTS.**

**What this checks and what it does not.** It is a necessary condition on the *shape* of the
numerator: a formula that put both exponents on the same summation index, or that dropped the
transpose in `spinEigen`, would fail it. It does **not** discriminate an exponent swap inside
`corr2Sep_eq_spectral`, because an exponent swap *is* this symmetry — which is the same reason
`corr2Sep_neg` forbids decay in `k` at finite length. -/
theorem spectral_numerator_symm (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (a b : ℕ) :
    (∑ p, ∑ q, ‖spinEigen β n i p q‖ ^ 2
        * ((transferSym_isHermitian β n).eigenvalues q ^ a
          * (transferSym_isHermitian β n).eigenvalues p ^ b))
      = ∑ p, ∑ q, ‖spinEigen β n i p q‖ ^ 2
        * ((transferSym_isHermitian β n).eigenvalues q ^ b
          * (transferSym_isHermitian β n).eigenvalues p ^ a) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [spinEigen_symm β n i q p]
  ring

end IsingTwoPointSpectral
