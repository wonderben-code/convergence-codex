import PerronRowLower

/-!
# Collatz–Wielandt: the row-sum bounds with the all-ones test vector removed

`PerronRowLower` bounds an eigenvalue with a strictly positive eigenvector between the smallest and
the largest ROW SUM. A row sum is `(A *ᵥ 1) i`, so that theorem is a statement about ONE test
vector, the all-ones one, and it happens to be the worst available whenever the row sums are spread
out. **This file removes that restriction**: any strictly positive `w` at all may be used, and the
bounds become `min_i (A *ᵥ w) i / w i ≤ μ ≤ max_i (A *ᵥ w) i / w i` in the form the proof consumes.

> **§1. The two bounds.** `le_of_subinvariant` — if `A ≥ 0`, `A *ᵥ v = μ • v` with `v > 0`, and some
> `w > 0` has `c · w ≤ A *ᵥ w` entrywise, then `c ≤ μ`. `le_of_superinvariant` is the mirror.
> **The proof is one comparison, and it is the reason the eigenvector must be positive**: put
> `t = min_i (v i / w i)`, attained at `k`. Then `t·w ≤ v` everywhere **with equality at `k`**, so
> `μ v k = ∑_j A k j v j ≥ t ∑_j A k j w j = t (A *ᵥ w) k ≥ t·c·w k = c·v k`. Dividing by `v k > 0`
> is the last step and is where positivity is spent for the second time.
>
> **§2. `PerronRowLower` IS THE `w = 1` CASE, AND THAT IS A THEOREM HERE, NOT A REMARK.**
> `subinvariant_one_iff` and `superinvariant_one_iff` — at `w = 1` the hypothesis of §1 says exactly
> that `c` is under every row sum. **Neither of `PerronRowLower`'s statements is restated**
> (`ERRATUM 176`); they keep their own short proofs and this file records the link.
>
> **§3. A test vector that pins what the all-ones vector only brackets.** `ex = !![1,4;1,1]` has row
> sums `5` and `2`, so `PerronRowLower` gives `2 ≤ μ ≤ 5` and no more (`ex_rowSum_bracket`). The
> vector `![2,1]` gives `A *ᵥ w = ![6,3]`, whose ratios to `w` are both `3`, so §1's two halves
> meet: **`ex_eigenvalue_eq_three`** — any eigenvalue with a strictly positive eigenvector is `3`.
> `ex_bracket_strict` records that `2 < 3 < 5`, so the improvement is **measured and not asserted**
> (`ERRATUM 194`).
>
> **§4. Sharp, and the difficulty moves rather than disappears.** `eigenvector_is_optimal` — at
> `w = v` both hypotheses of §1 hold with EQUALITY, so `μ` is the best constant either half can
> certify and the bounds give nothing away. **What §1 does not do is produce `w`**: `![2,1]` above
> was chosen knowing the answer, and the ideal choice is the eigenvector itself. Collatz–Wielandt
> turns an eigenvalue problem into a search, and the search is not attempted here.

**WHAT THIS IS NOT — AND FOR `W4` IT IS WEAKER THAN WHAT IT REPLACES, WHICH IS WORTH SAYING.**
`PerronRowLower`'s note in `WALLS` §W4.1 §2 observed that row sums bound `λ₁` from below and bound
`|λ₂|` only by the largest row sum, so the quotient they certify is never below `1`. **§1 does not
improve that and cannot even state it**: both halves require the eigenvalue to HAVE a strictly
positive eigenvector, which is the top one, so Collatz–Wielandt is silent about `λ₂` altogether.
`PerronBound.abs_le_of_rowSum_le`, which asks nothing of the eigenvector, remains the only handle on
the sub-top eigenvalue in this direction. `UniformSubTopRatio` is untouched, not attempted, not
costed (`ERRATUM 194`, `ERRATUM 246`). **This is a sharper tool for the Perron root and not a step
toward a gap**, and nothing earlier is restated, deleted or deprecated.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PerronCollatzWielandt

open Finset Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} {μ c : ℝ} {v w : n → ℝ}

/-! ### §1. The two bounds -/

/-- `(A *ᵥ x) i` written out, used in both proofs. -/
theorem mulVec_apply (A : Matrix n n ℝ) (x : n → ℝ) (i : n) : (A *ᵥ x) i = ∑ j, A i j * x j := by
  simp [Matrix.mulVec, dotProduct]

/-- **THE COLLATZ–WIELANDT LOWER BOUND.** A strictly positive `w` with `c · w ≤ A *ᵥ w` entrywise
certifies `c ≤ μ`, for every eigenvalue `μ` with a strictly positive eigenvector. -/
theorem le_of_subinvariant [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hwpos : ∀ i, 0 < w i) (hw : ∀ i, c * w i ≤ (A *ᵥ w) i) : c ≤ μ := by
  obtain ⟨k, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset n) (fun i => v i / w i) Finset.univ_nonempty
  set t : ℝ := v k / w k with ht
  have htpos : 0 < t := div_pos (hvpos k) (hwpos k)
  have hle : ∀ j, t * w j ≤ v j := by
    intro j
    have h := hmin j (Finset.mem_univ j)
    calc t * w j ≤ (v j / w j) * w j := mul_le_mul_of_nonneg_right h (hwpos j).le
      _ = v j := div_mul_cancel₀ _ (hwpos j).ne'
  have hkeq : t * w k = v k := div_mul_cancel₀ _ (hwpos k).ne'
  have hrow : μ * v k = ∑ j, A k j * v j := by
    have h := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hstep : c * v k ≤ μ * v k := by
    have h1 : t * (c * w k) ≤ t * (A *ᵥ w) k := by
      exact mul_le_mul_of_nonneg_left (hw k) htpos.le
    have h2 : t * (A *ᵥ w) k = ∑ j, A k j * (t * w j) := by
      rw [mulVec_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : ∑ j, A k j * (t * w j) ≤ ∑ j, A k j * v j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA k j)
    have h4 : t * (c * w k) = c * v k := by rw [← hkeq]; ring
    rw [hrow]
    calc c * v k = t * (c * w k) := h4.symm
      _ ≤ t * (A *ᵥ w) k := h1
      _ = ∑ j, A k j * (t * w j) := h2
      _ ≤ ∑ j, A k j * v j := h3
  exact le_of_mul_le_mul_right hstep (hvpos k)

/-- **THE COLLATZ–WIELANDT UPPER BOUND**, the same comparison at the maximum of `v / w`. -/
theorem le_of_superinvariant [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) (hv : A *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) (hwpos : ∀ i, 0 < w i) (hw : ∀ i, (A *ᵥ w) i ≤ c * w i) : μ ≤ c := by
  obtain ⟨k, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) (fun i => v i / w i) Finset.univ_nonempty
  set t : ℝ := v k / w k with ht
  have htpos : 0 < t := div_pos (hvpos k) (hwpos k)
  have hle : ∀ j, v j ≤ t * w j := by
    intro j
    have h := hmax j (Finset.mem_univ j)
    calc v j = (v j / w j) * w j := (div_mul_cancel₀ _ (hwpos j).ne').symm
      _ ≤ t * w j := mul_le_mul_of_nonneg_right h (hwpos j).le
  have hkeq : t * w k = v k := div_mul_cancel₀ _ (hwpos k).ne'
  have hrow : μ * v k = ∑ j, A k j * v j := by
    have h := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hstep : μ * v k ≤ c * v k := by
    have h1 : ∑ j, A k j * v j ≤ ∑ j, A k j * (t * w j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle j) (hA k j)
    have h2 : ∑ j, A k j * (t * w j) = t * (A *ᵥ w) k := by
      rw [mulVec_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : t * (A *ᵥ w) k ≤ t * (c * w k) := mul_le_mul_of_nonneg_left (hw k) htpos.le
    have h4 : t * (c * w k) = c * v k := by rw [← hkeq]; ring
    rw [hrow]
    calc ∑ j, A k j * v j ≤ ∑ j, A k j * (t * w j) := h1
      _ = t * (A *ᵥ w) k := h2
      _ ≤ t * (c * w k) := h3
      _ = c * v k := h4
  exact le_of_mul_le_mul_right hstep (hvpos k)

/-! ### §2. `PerronRowLower` is the `w = 1` case -/

/-- At the all-ones test vector §1's hypothesis says exactly that `c` is under every row sum, which
is `PerronRowLower.le_of_rowSum_ge`'s hypothesis. That theorem is **not restated** here. -/
theorem subinvariant_one_iff (A : Matrix n n ℝ) (c : ℝ) :
    (∀ i, c * (1 : ℝ) ≤ (A *ᵥ (fun _ => (1 : ℝ))) i) ↔ ∀ i, c ≤ ∑ j, A i j := by
  constructor <;> intro h i <;> have := h i <;> simpa [mulVec_apply] using this

/-- And the mirror, against `PerronBound.abs_le_of_rowSum_le`'s hypothesis. -/
theorem superinvariant_one_iff (A : Matrix n n ℝ) (c : ℝ) :
    (∀ i, (A *ᵥ (fun _ => (1 : ℝ))) i ≤ c * (1 : ℝ)) ↔ ∀ i, ∑ j, A i j ≤ c := by
  constructor <;> intro h i <;> have := h i <;> simpa [mulVec_apply] using this

/-! ### §3. A test vector that pins what the all-ones vector only brackets -/

/-- A matrix whose row sums are far apart: `5` and `2`. -/
def ex : Matrix (Fin 2) (Fin 2) ℝ := !![1, 4; 1, 1]

/-- The all-ones vector brackets and no more: every eigenvalue of `ex` with a strictly positive
eigenvector lies in `[2, 5]`, which is `PerronRowLower` at this matrix. -/
theorem ex_rowSum_bracket {μ : ℝ} {v : Fin 2 → ℝ} (hv : ex *ᵥ v = μ • v) (hvpos : ∀ i, 0 < v i) :
    2 ≤ μ ∧ μ ≤ 5 := by
  have hA : ∀ i j, 0 ≤ ex i j := by
    intro i j; fin_cases i <;> fin_cases j <;> norm_num [ex]
  refine PerronRowLower.rowSum_sandwich hA hv hvpos (fun i => ?_) (fun i => ?_) <;>
    fin_cases i <;> norm_num [ex, Fin.sum_univ_two]

/-- **AND `![2,1]` PINS IT.** `ex *ᵥ ![2,1] = ![6,3]`, whose ratios to `![2,1]` are both `3`, so
§1's two halves meet at `c = 3`. -/
theorem ex_eigenvalue_eq_three {μ : ℝ} {v : Fin 2 → ℝ} (hv : ex *ᵥ v = μ • v)
    (hvpos : ∀ i, 0 < v i) : μ = 3 := by
  have hA : ∀ i j, 0 ≤ ex i j := by
    intro i j; fin_cases i <;> fin_cases j <;> norm_num [ex]
  have hwpos : ∀ i, 0 < (![2, 1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have hsub : ∀ i, (3 : ℝ) * (![2, 1] : Fin 2 → ℝ) i ≤ (ex *ᵥ ![2, 1]) i := by
    intro i; fin_cases i <;> norm_num [ex, mulVec_apply, Fin.sum_univ_two]
  have hsup : ∀ i, (ex *ᵥ ![2, 1]) i ≤ (3 : ℝ) * (![2, 1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num [ex, mulVec_apply, Fin.sum_univ_two]
  exact le_antisymm (le_of_superinvariant hA hv hvpos hwpos hsup)
    (le_of_subinvariant hA hv hvpos hwpos hsub)

/-- **THE IMPROVEMENT IS MEASURED, NOT ASSERTED** (`ERRATUM 194`): the value `3` sits strictly
inside the bracket `[2, 5]` the all-ones vector gives. -/
theorem ex_bracket_strict : (2 : ℝ) < 3 ∧ (3 : ℝ) < 5 := by norm_num

/-! ### §4. The bounds are sharp, and that is where the difficulty moves to -/

/-- **THE EIGENVECTOR IS ITSELF A TEST VECTOR, AND AT IT BOTH HYPOTHESES HOLD WITH EQUALITY.** So
`μ` is exactly the best `c` either half of §1 can certify: the bounds are SHARP, and §1 gives away
nothing. **What it does not do is produce `w`** — `![2,1]` in §3 was chosen knowing the answer, and
this theorem says the ideal choice is the eigenvector, which is the thing one is trying to find.
Collatz–Wielandt converts an eigenvalue problem into a search, and the search is not attempted here
and its cost is not claimed (`ERRATUM 194`, `ERRATUM 246`). -/
theorem eigenvector_is_optimal (hv : A *ᵥ v = μ • v) (i : n) :
    μ * v i ≤ (A *ᵥ v) i ∧ (A *ᵥ v) i ≤ μ * v i := by
  have h : (A *ᵥ v) i = μ * v i := by
    have := congrFun hv i
    simpa using this
  exact ⟨h.ge, h.le⟩

end PerronCollatzWielandt
