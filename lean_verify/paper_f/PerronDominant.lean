import PerronRowLower

/-!
# The Perron eigenvalue dominates the whole spectrum — with `IsHermitian` removed

`PerronGap.abs_le_top_of_eigenvector` says every eigenvalue of a **symmetric** nonnegative matrix is
bounded in modulus by the top one, and it is symmetric through and through: its hypothesis is the
whole eigenvalue family `hA.eigenvalues`, which exists only for a Hermitian matrix. **This file
removes the symmetry.**

**THE TRADE IS EXACT AND IS NOT A WEAKENING IN DISGUISE.** That theorem PRODUCES the top eigenvalue
from the spectral theorem; this one ASSUMES a strictly positive eigenvector and dominates every
other eigenvalue by its eigenvalue. Neither implies the other, and for a matrix that is not
symmetric — `IsingTransfer2D.transfer2` is the estate's own example, which is why `IsingTransferSym`
exists at all — the older theorem does not apply and this one can.

> **§1. The comparison.** `exists_max_index` — at the index `k` maximising `|w| / v`, one has
> `A *ᵥ |w| ≤ μ · |w k|` and `|w k| > 0`. **Everything below is that lemma plus one inequality**,
> and it is where the positive eigenvector is spent: `|w| ≤ t·v` everywhere, **equal at `k`**,
> so applying `A` and using `A *ᵥ v = μ • v` turns a bound on `|w|` into `μ · |w k|`.
>
> **§2. Domination.** `abs_le_of_pos_eigenvector` — `|λ| ≤ μ` for every real eigenvalue, with `A`
> only nonnegative and **no symmetry anywhere**. It is `PerronBound.abs_smul_abs_le_mulVec_abs`
> composed with §1.
>
> **§3. Strict, two ways, and they are different hypotheses.** `abs_lt_of_not_proportional` —
> strict when `|w|` is no scalar multiple of `v`, which makes §1's second inequality strict.
> `abs_lt_of_not_signConstant` — strict when `w` changes sign, which makes the FIRST one strict, by
> `PerronEquality.sign_constant_of_mulVec_abs_eq`. **Neither subsumes the other and the estate's own
> matrix shows why**: for `transfer β` the vector `![1,-1]` has `|w| = v` exactly, so it is
> proportional and the first test says nothing, while the second settles it.
>
> **§4. A spectral gap with no symmetry.** `abs_lt_of_rowSum_eq_of_not_signConstant` — a **strictly
> positive** matrix with **constant row sums** `C` has every sign-changing eigenvector's eigenvalue
> strictly inside `|λ| < C`. The positive eigenvector is the all-ones one, from
> `PerronBound.mulVec_one_of_rowSum_eq`, so the hypothesis of §2 is discharged rather than assumed.
> `transfer_abs_lt_lamPlus` is the instance at the estate's one-dimensional transfer matrix.

**AN ADVERSARIAL CHECK, AND IT IS THE POINT OF §4.** `IsingTransferMatrix.abs_lamMinus_lt_lamPlus`
proves `|lamMinus β| < lamPlus β` **by hand, for a `2 × 2` matrix, from closed forms of both
eigenvalues**. §4 gets the same separation from a general theorem that never computes an eigenvalue,
never mentions `lamMinus` and never uses symmetry. That theorem is **not restated** here
(`ERRATUM 176`): `transfer_abs_lt_lamPlus` is about EVERY sign-changing eigenvector, which is a
different and wider statement, and the hand theorem remains the one that names the value.

**WHAT THIS IS NOT, as of 2026-09-02.** It does not produce a positive eigenvector for a
non-symmetric matrix — that is the Perron half of Perron–Frobenius without symmetry, it needs a
fixed-point or compactness argument, and it is **not attempted and not costed** (`ERRATUM 194`,
`ERRATUM 246`). So nothing here applies to `transfer2` yet, and that is **grepped rather than
recalled** (`ERRATUM 396`): `PerronVector.exists_pos_top_eigenvector` is the only theorem under
`paper_f/` that produces a strictly positive eigenvector, and it takes `Matrix.IsHermitian`.

**^ FORWARD POINTER, ADDED 2026-09-02 THE SAME DAY: *"nothing here applies to `transfer2` yet"* IS
NO LONGER TRUE, AND THE SENTENCE IS KEPT** (`ERRATUM 94`). It is right that this file proves no
Perron–Frobenius without symmetry and right about the grep. It is wrong to conclude `transfer2` is
out of reach: `paper_f/Transfer2Perron.lean` gets a strictly positive eigenvector for `transfer2`
**without any fixed-point argument**, by transporting one across the positive diagonal similarity
`transfer2 · D = D · transferSym` that `IsingTransferSym.transfer2_eq` already supplied, and then
applies §2 and §3 of this file at it. **The missing step was never Perron–Frobenius; it was one
associativity identity nobody had written.** Added because a reader landing here otherwise takes
*"not available"* for *"not obtainable"* — `ERRATUM 230`'s defect, whose repair is a pointer at the
true claim and not a rewrite of the old one, and `ERRATUM 416`'s, which is what happens when a
correction is recorded in one place and not the others.

**AND NO GAP FOR `W4` FOLLOWS, for a reason stated as what is KNOWN and not as what is true.** §4
needs CONSTANT row sums. **No theorem in this estate gives `transferSym` constant row sums** — no
declaration under `paper_f/` states any row-sum identity for it at all — and `PerronBound`'s own
header records the same situation one matrix over, that *"`transfer2`'s row sums have no closed form
in this estate"*, which is why `abs_le_rowSum_transfer2` leaves its constant a hypothesis. **Whether
they are in fact constant is not decided here and is not asserted either way** (`ERRATUM 125`); what
is asserted is that §4's hypothesis is not available, so §4 is not applied **here**. A gap uniform
in the strip width is untouched by this file, and `UniformSubTopRatio` is not attempted in it —
neither claim is about what the rest of the estate does. Nothing earlier is restated, deleted or
deprecated, and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PerronDominant

open Finset Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ lam : ℝ} {v w : n → ℝ}

/-! ### §1. The comparison at the maximum of `|w| / v` -/

/-- **THE ONE COMPARISON THIS FILE RESTS ON.** At the index maximising `|w| / v`, the image of `|w|`
is at most `μ · |w k|`, and `|w k|` is strictly positive. The positive eigenvector is spent here:
`|w| ≤ t·v` everywhere **with equality at `k`**. -/
theorem exists_max_index [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hw0 : w ≠ 0) :
    ∃ k, 0 < |w k| ∧ (A *ᵥ fun j => |w j|) k ≤ μ * |w k| := by
  obtain ⟨k, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) (fun i => |w i| / v i) Finset.univ_nonempty
  set t : ℝ := |w k| / v k with ht
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hw0
  have htpos : 0 < t := lt_of_lt_of_le (div_pos (abs_pos.mpr hj₀) (hvpos j₀))
    (hmax j₀ (Finset.mem_univ j₀))
  have hkeq : t * v k = |w k| := div_mul_cancel₀ _ (hvpos k).ne'
  have hwk : 0 < |w k| := hkeq ▸ mul_pos htpos (hvpos k)
  refine ⟨k, hwk, ?_⟩
  have hle : ∀ j, |w j| ≤ t * v j := by
    intro j
    calc |w j| = (|w j| / v j) * v j := (div_mul_cancel₀ _ (hvpos j).ne').symm
      _ ≤ t * v j := mul_le_mul_of_nonneg_right (hmax j (Finset.mem_univ j)) (hvpos j).le
  have h2 : (A *ᵥ fun j => |w j|) k ≤ ∑ j, A k j * (t * v j) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA k j)
  have h3 : ∑ j, A k j * (t * v j) = μ * |w k| := by
    have e1 : ∑ j, A k j * (t * v j) = t * ∑ j, A k j * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, A k j * v j = μ * v k := by
      have h := congrFun hv k
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [e1, e2, ← hkeq]; ring
  exact h3 ▸ h2

/-! ### §2. Domination, with no symmetry -/

/-- **EVERY REAL EIGENVALUE IS DOMINATED BY THE ONE WITH A STRICTLY POSITIVE EIGENVECTOR.** `A` is
only asked to be nonnegative; **no symmetry, no irreducibility, no spectral theorem**. -/
theorem abs_le_of_pos_eigenvector [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hw : A *ᵥ w = lam • w) (hw0 : w ≠ 0) : |lam| ≤ μ := by
  obtain ⟨k, hwk, hk⟩ := exists_max_index hA hv hvpos hw0
  have h1 : |lam| * |w k| ≤ (A *ᵥ fun j => |w j|) k :=
    PerronBound.abs_smul_abs_le_mulVec_abs hA hw k
  exact le_of_mul_le_mul_right (h1.trans hk) hwk

/-! ### §3. Strict domination, by two different hypotheses -/

/-- **STRICT WHEN `|w|` IS NO MULTIPLE OF `v`**, which makes §1's second inequality strict. -/
theorem abs_lt_of_not_proportional [Nonempty n] (hA : ∀ i j, 0 < A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hw : A *ᵥ w = lam • w) (hw0 : w ≠ 0)
    (hnp : ∀ t : ℝ, (fun j => |w j|) ≠ t • v) : |lam| < μ := by
  obtain ⟨k, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) (fun i => |w i| / v i) Finset.univ_nonempty
  set t : ℝ := |w k| / v k with ht
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hw0
  have htpos : 0 < t := lt_of_lt_of_le (div_pos (abs_pos.mpr hj₀) (hvpos j₀))
    (hmax j₀ (Finset.mem_univ j₀))
  have hkeq : t * v k = |w k| := div_mul_cancel₀ _ (hvpos k).ne'
  have hwk : 0 < |w k| := hkeq ▸ mul_pos htpos (hvpos k)
  have hle : ∀ j, |w j| ≤ t * v j := by
    intro j
    calc |w j| = (|w j| / v j) * v j := (div_mul_cancel₀ _ (hvpos j).ne').symm
      _ ≤ t * v j := mul_le_mul_of_nonneg_right (hmax j (Finset.mem_univ j)) (hvpos j).le
  obtain ⟨j₁, hj₁⟩ : ∃ j, |w j| ≠ t * v j := by
    by_contra hcon
    push Not at hcon
    exact hnp t (by funext j; simpa [smul_eq_mul] using hcon j)
  have hlt : (A *ᵥ fun j => |w j|) k < ∑ j, A k j * (t * v j) := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA k j).le)
      ⟨j₁, Finset.mem_univ j₁, ?_⟩
    exact mul_lt_mul_of_pos_left (lt_of_le_of_ne (hle j₁) hj₁) (hA k j₁)
  have h3 : ∑ j, A k j * (t * v j) = μ * |w k| := by
    have e1 : ∑ j, A k j * (t * v j) = t * ∑ j, A k j * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, A k j * v j = μ * v k := by
      have h := congrFun hv k
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      exact h
    rw [e1, e2, ← hkeq]; ring
  have h1 : |lam| * |w k| ≤ (A *ᵥ fun j => |w j|) k :=
    PerronBound.abs_smul_abs_le_mulVec_abs (fun i j => (hA i j).le) hw k
  exact lt_of_mul_lt_mul_right (by rw [← h3]; exact lt_of_le_of_lt h1 hlt) hwk.le

/-- **STRICT WHEN `w` CHANGES SIGN**, which makes the FIRST inequality strict, by
`PerronEquality.sign_constant_of_mulVec_abs_eq`. **This is the case the proportionality test
misses** — `|w| = v` exactly is a multiple of `v` in modulus and still sign-changing. -/
theorem abs_lt_of_not_signConstant [Nonempty n] (hA : ∀ i j, 0 < A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hw : A *ᵥ w = lam • w) (hw0 : w ≠ 0)
    (hsign : ¬((∀ j, 0 ≤ w j) ∨ (∀ j, w j ≤ 0))) : |lam| < μ := by
  obtain ⟨k, hwk, hk⟩ := exists_max_index (fun i j => (hA i j).le) hv hvpos hw0
  have h1 : |lam| * |w k| ≤ (A *ᵥ fun j => |w j|) k :=
    PerronBound.abs_smul_abs_le_mulVec_abs (fun i j => (hA i j).le) hw k
  have h1' : |lam| * |w k| < (A *ᵥ fun j => |w j|) k :=
    lt_of_le_of_ne h1 fun heq => hsign (PerronEquality.sign_constant_of_mulVec_abs_eq hA hw heq)
  exact lt_of_mul_lt_mul_right (h1'.trans_le hk) hwk.le

/-! ### §4. A spectral gap with no symmetry -/

/-- **A STRICTLY POSITIVE MATRIX WITH CONSTANT ROW SUMS SEPARATES ITS TOP EIGENVALUE**, with no
symmetry: every sign-changing eigenvector's eigenvalue is strictly inside `|λ| < C`. The positive
eigenvector §3 needs is the all-ones one, so that hypothesis is **discharged, not assumed**. -/
theorem abs_lt_of_rowSum_eq_of_not_signConstant [Nonempty n] (hA : ∀ i j, 0 < A i j) {C : ℝ}
    (hrow : ∀ i, ∑ j, A i j = C) (hw : A *ᵥ w = lam • w) (hw0 : w ≠ 0)
    (hsign : ¬((∀ j, 0 ≤ w j) ∨ (∀ j, w j ≤ 0))) : |lam| < C :=
  abs_lt_of_not_signConstant hA (PerronBound.mulVec_one_of_rowSum_eq hrow)
    (fun _ => zero_lt_one) hw hw0 hsign

/-- **AT THE ESTATE'S ONE-DIMENSIONAL TRANSFER MATRIX**, whose rows all sum to `lamPlus β`
(`PerronRowLower.transfer_rowSum`) and whose entries are exponentials. **Symmetry is available
here and is not used.** -/
theorem transfer_abs_lt_lamPlus (β : ℝ) {lam : ℝ} {w : Fin 2 → ℝ}
    (hw : IsingTransferMatrix.transfer β *ᵥ w = lam • w) (hw0 : w ≠ 0)
    (hsign : ¬((∀ j, 0 ≤ w j) ∨ (∀ j, w j ≤ 0))) : |lam| < IsingTransferMatrix.lamPlus β := by
  have hA : ∀ i j, 0 < IsingTransferMatrix.transfer β i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [IsingTransferMatrix.transfer, Real.exp_pos]
  exact abs_lt_of_rowSum_eq_of_not_signConstant hA (PerronRowLower.transfer_rowSum β) hw hw0 hsign

end PerronDominant
