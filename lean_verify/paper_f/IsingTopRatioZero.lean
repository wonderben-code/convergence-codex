/-
  IsingTopRatioZero.lean — the target is satisfiable, and the witness is
  infinite temperature.

  WHY. `IsingTopRatio` states `WALLS` §W4 §6 item 3 as a `Prop`,
  `UniformSubTopRatio β`, and closes by saying it is not known to be inhabited
  — *"not even at infinite temperature"*. **That sentence is superseded here**
  (`ERRATUM 94`: it is kept where it stands, with a pointer). A `Prop` naming
  a gap with no inhabitant at all is a worse target than one with a trivial
  inhabitant, because nothing distinguishes "hard" from "false".

  WHAT THIS FILE PROVES:
  1. **`eigenvalues_sq_eq_of_mul_self`** — for a Hermitian `A` over `ℝ` with
     `A * A = c • A`, **every** eigenvalue satisfies `λ² = c·λ`. This is the
     general fact and it is the only real content: `A *ᵥ bⱼ = λⱼ • bⱼ` for the
     eigenvector basis, applied twice against the hypothesis applied once, and
     `bⱼ ≠ 0` because an orthonormal family has no zero vector.
  2. **`transferSym_zero_mul_self`** — at `β = 0` every entry of the
     symmetrised transfer matrix is `exp 0 = 1`, so it squares to `2ⁿ⁺¹` times
     itself.
  3. **`eigenvalues_zero_eq_or`** — hence every eigenvalue is `0` or `2ⁿ⁺¹`;
     **`eigenvalues_zero_top`** — the top one is the latter, because it is
     strictly positive; **`eigenvalues_zero_eq_zero_of_ne`** — and every other
     one is `0`, because the top value occurs exactly once in the list
     (`TransferPowerSum.index_eq_of_eigenvalues_eq_top`).
  4. **`subTopRatio_zero`** — so the sub-top ratio is `0` at every width, and
     **`uniformSubTopRatio_zero : UniformSubTopRatio 0`** with `δ = 1`.
  5. **`corr2SepInf_zero_eq_zero`** — and the payoff is not a statement about
     an empty set: at `β = 0` the infinite strip's two-point function is
     **exactly zero at every positive separation**. At infinite temperature
     the spins are independent, so that is the right answer, and it is a
     DISCRIMINATING check on the whole chain above — a transposed index or a
     wrong row in `corr2Sep_eq_spectral` would not survive it.

  WHAT THIS IS NOT.
  **It is not progress on item 3 and the wall does not move.** `β = 0` is the
  degenerate case: the matrix has RANK ONE, there is nothing for a width limit
  to do to it, and the physics is that non-interacting spins do not correlate.
  What it establishes is that `UniformSubTopRatio` is a satisfiable predicate
  and therefore a target rather than a possible impossibility — and, read the
  other way, that any proof strategy which would also work at `β = 0` is not
  yet doing the work, because this file does it in forty lines.

  **NOTHING HERE SAYS ANYTHING ABOUT `β ≠ 0`.** The moment `β` is nonzero the
  entries stop being equal, the rank stops being one, `A * A = c • A` fails,
  and every step below fails with it. There is no route from this file to any
  other temperature and none is suggested.

  ON THE GENERAL LEMMA IN §1, AND WHY IT IS HERE. It is about an arbitrary
  Hermitian matrix and mentions nothing about Ising, so this is not its
  natural home; it is here because this is its first consumer. Note also that
  `AdjSqForcesRegular.allOnes_mul_allOnes` is §2's content for the estate's own
  `allOnes` (`GreenExpansion`), and is NOT imported: that file's transitive
  `paper_f` closure is 57 files against this chain's 17, so importing it to
  reuse three lines would add **58 files** to the Ising chain's import graph.
  `allOnes` and its idempotence belong in a shared file below both; until one
  exists, §2 proves the instance it needs and cites the general one.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingTopRatio

namespace IsingTopRatioZero

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointSpectral IsingTwoPointLimit
open IsingTopRatio

/-! ## 1. Hermitian matrices that square to a multiple of themselves

The one general statement in the file. Absent from Mathlib by shape: probed 2026-08-22 against the
pinned dump for an eigenvalue statement about idempotents or about `A * A = c • A` — the nearest
hits are `Module.End.HasEigenvalue.pow` and `Matrix.IsParabolic.sub_eigenvalue_sq_eq_zero`, neither
of which is this — and absent from `paper_f`, where `Perron*` and `Rayleigh*` carry every other
eigenvalue fact this estate owns. -/

/-- **AN EIGENVALUE OF A HERMITIAN `A` WITH `A * A = c • A` SATISFIES `λ² = c·λ`.**

The proof is the definition of an eigenvector used twice against the hypothesis used once. The only
step that is not bookkeeping is `bⱼ ≠ 0`, which is `Orthonormal.ne_zero`: a family of unit vectors
contains no zero vector, and `Matrix.IsHermitian.eigenvectorBasis` is orthonormal by
construction. -/
theorem eigenvalues_sq_eq_of_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {c : ℝ} (h : A * A = c • A) (j : ι) :
    hA.eigenvalues j ^ 2 = c * hA.eigenvalues j := by
  have hne : (hA.eigenvectorBasis j).ofLp ≠ 0 := by
    rw [Ne, WithLp.ofLp_eq_zero]
    exact hA.eigenvectorBasis.orthonormal.ne_zero j
  have h1 : A *ᵥ (hA.eigenvectorBasis j).ofLp
      = hA.eigenvalues j • (hA.eigenvectorBasis j).ofLp := hA.mulVec_eigenvectorBasis j
  have h2 : (A * A) *ᵥ (hA.eigenvectorBasis j).ofLp
      = (hA.eigenvalues j ^ 2) • (hA.eigenvectorBasis j).ofLp := by
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h1, smul_smul, sq]
  rw [h, Matrix.smul_mulVec, h1, smul_smul] at h2
  have hz : (hA.eigenvalues j ^ 2 - c * hA.eigenvalues j) • (hA.eigenvectorBasis j).ofLp = 0 := by
    rw [sub_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp hz with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hne

/-! ## 2. At `β = 0` the transfer matrix is all-ones -/

/-- Every entry is `exp 0 = 1`. -/
theorem transferSym_zero_apply (n : ℕ) (σ τ : Col n) : transferSym 0 n σ τ = 1 := by
  rw [transferSym_apply]
  simp

/-- **SO IT SQUARES TO `2ⁿ⁺¹` TIMES ITSELF.** `AdjSqForcesRegular.allOnes_mul_allOnes` is this
statement for `allOnes`; see the header for why it is not imported. -/
theorem transferSym_zero_mul_self (n : ℕ) :
    transferSym 0 n * transferSym 0 n = ((2 ^ (n + 1) : ℕ) : ℝ) • transferSym 0 n := by
  ext σ τ
  simp [Matrix.mul_apply, transferSym_zero_apply]

/-! ## 3. Hence the eigenvalue list is `2ⁿ⁺¹` once and `0` everywhere else -/

theorem eigenvalues_zero_eq_or (n : ℕ) (j : Col n) :
    (transferSym_isHermitian 0 n).eigenvalues j = 0
      ∨ (transferSym_isHermitian 0 n).eigenvalues j = ((2 ^ (n + 1) : ℕ) : ℝ) := by
  have h := eigenvalues_sq_eq_of_mul_self (transferSym_isHermitian 0 n)
    (transferSym_zero_mul_self n) j
  have hf : (transferSym_isHermitian 0 n).eigenvalues j
      * ((transferSym_isHermitian 0 n).eigenvalues j - ((2 ^ (n + 1) : ℕ) : ℝ)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hf with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h0)

/-- **THE TOP ONE IS `2ⁿ⁺¹`**, because it is strictly positive and the only other option is `0`. -/
theorem eigenvalues_zero_top (n : ℕ) :
    (transferSym_isHermitian 0 n).eigenvalues (topIndex 0 n) = ((2 ^ (n + 1) : ℕ) : ℝ) := by
  rcases eigenvalues_zero_eq_or n (topIndex 0 n) with h | h
  · exact absurd h (topIndex_pos 0 n).ne'
  · exact h

/-- **AND EVERY OTHER ONE IS `0`**, because the top value occurs exactly once in the list. -/
theorem eigenvalues_zero_eq_zero_of_ne (n : ℕ) {q : Col n} (hq : q ≠ topIndex 0 n) :
    (transferSym_isHermitian 0 n).eigenvalues q = 0 := by
  rcases eigenvalues_zero_eq_or n q with h | h
  · exact h
  · exact absurd (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ (transferSym_entries_pos 0 n)
      (topIndex_max 0 n) (h.trans (eigenvalues_zero_top n).symm)) hq

/-! ## 4. So the ratio vanishes, and the item is satisfiable -/

theorem subTopRatio_zero (n : ℕ) : subTopRatio 0 n = 0 := by
  refine le_antisymm ?_ (subTopRatio_nonneg 0 n)
  have hrfl : subTopRatio 0 n
      = (univ.erase (topIndex 0 n)).sup' (erase_topIndex_nonempty 0 n) fun q =>
        |(transferSym_isHermitian 0 n).eigenvalues q
          / (transferSym_isHermitian 0 n).eigenvalues (topIndex 0 n)| := rfl
  rw [hrfl]
  refine Finset.sup'_le _ _ fun q hq => ?_
  rw [eigenvalues_zero_eq_zero_of_ne n (Finset.mem_erase.mp hq).1, zero_div, abs_zero]

/-- **`UniformSubTopRatio` IS INHABITED.** At `β = 0`, with `δ = 1`. This supersedes
`IsingTopRatio`'s closing sentence that the target is not known to be satisfiable *"not even at
infinite temperature"*; that sentence is kept where it stands (`ERRATUM 94`) with a pointer here. -/
theorem uniformSubTopRatio_zero : UniformSubTopRatio 0 :=
  ⟨1, one_pos, fun n => by rw [subTopRatio_zero n]; norm_num⟩

/-- **AND THE TARGET IS NOT VACUOUS EITHER.** At `β = 0` the infinite strip's two-point function is
exactly `0` at every positive separation — non-interacting spins do not correlate — which is a
DISCRIMINATING check on the chain above, not a restatement of it: a transposed index or a wrong row
in `corr2Sep_eq_spectral` would not produce it. -/
theorem corr2SepInf_zero_eq_zero (n : ℕ) (i : Fin (n + 1)) {κ : ℕ} (hκ : κ ≠ 0) :
    corr2SepInf 0 n i (topIndex 0 n) κ = 0 := by
  have h := corr2SepInf_abs_le_subTopRatio 0 n i κ
  rw [subTopRatio_zero n, zero_pow hκ] at h
  exact abs_nonpos_iff.mp h

end IsingTopRatioZero
