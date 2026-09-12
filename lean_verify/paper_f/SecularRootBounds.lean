import SecularRootSeparation

/-!
# Where the secular roots are: between the extreme poles, but one

**THE TWO PREVIOUS UNITS DID THE TOP END AND THE GAPS; THIS IS THE BOTTOM END, AND IT IS THE
CHEAPEST OF THE THREE.** Below the *smallest* of the values `N − 2nᵢ` every denominator is
**positive**, so every term is positive and the sum is positive — and a positive number is not `−1`.
That single observation closes the left-hand side: **no solution of the secular equation lies below
the smallest pole**, and with the earlier uniqueness above the largest pole, **every root but one
lies in the closed interval between the two extremes**.

## What is proved

**`poleMin`, `poleMin_le`, `denom_pos`** — the smallest of the `N − 2nᵢ`, and the sign of the
denominators below it. **`secularSum_pos`** — the sum is strictly positive there, which needs both
`Nonempty ι` (a sum over nothing is zero, not positive) and non-empty parts (a part of size zero
contributes a zero term).

**`poleMin_le_of_secular_root`** — hence every root satisfies `poleMin ≤ μ`.
**`mem_Icc_of_secular_root_ne`** — hence, with entry 164's uniqueness above `poleMax`, every root
other than that one lies in `[poleMin, poleMax]`.
**`poleMin_le_of_isEigenvalue`** — and in graph terms: **every eigenvalue of `Q` that is not a part
value is at least `N − 2·maxᵢ nᵢ`**, through entry 157's criterion.

## What is NOT here

* **THE BOUND IS `poleMin ≤ μ` AND NOT `poleMin < μ`, DELIBERATELY.** At a pole the corresponding
  denominator is zero and Lean's division makes that term zero rather than undefined, so
  `secularSum` takes a value there which means nothing; the statement is worded so that it never
  depends on that value. The strict inequality is true and is **not** proved, because proving it
  means saying what happens at a pole.
* **STILL NO COUNT.** Entries 164 and 165 name it and this does not supply it: bounding the roots
  into an interval says nothing about how many there are, and the finiteness of the root set is
  still unproved. Not attempted (`ERRATUM 246`).
* **NO UPPER BOUND ON THE ONE ROOT ABOVE `poleMax`.** It exists and is unique; nothing here or
  anywhere in this chain bounds it above, and the bracket entry 164 used (`2N + 1`) is a device for
  the intermediate value theorem, not a claim about the root.
* **NOTHING FOR THE PART VALUES.** `N − nᵢ` is an eigenvalue by a different route entirely and
  these bounds say nothing about where those lie relative to the poles.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` instances;
`Nonempty ι` wherever `poleMin` appears; `∀ i, Nonempty (V i)` on the positivity and everything
downstream of it; the graph statement additionally takes entry 157's two, that `μ` is no part's
`N − nᵢ` and that no denominator vanishes. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootBounds

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootLocation SecularRootSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The smallest of the values `N − 2nᵢ`, below which every secular denominator is positive. -/
noncomputable def poleMin (hι : Nonempty ι) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr hι)
    fun i => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem poleMin_le (hι : Nonempty ι) (i : ι) :
    poleMin (V := V) hι ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) := by
  rw [poleMin]
  exact Finset.inf'_le
    (fun j : ι => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j))
    (Finset.mem_univ i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem denom_pos (hι : Nonempty ι) {μ : ℝ} (hμ : μ < poleMin (V := V) hι) (i : ι) :
    0 < (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ :=
  sub_pos.mpr (lt_of_lt_of_le hμ (poleMin_le hι i))

/-! ## 1. Below the smallest pole the sum is positive, so there is no root there -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_pos (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ : ℝ}
    (hμ : μ < poleMin (V := V) hι) : 0 < secularSum (V := V) μ := by
  rw [secularSum]
  refine Finset.sum_pos (fun i _ => ?_) (Finset.univ_nonempty_iff.mpr hι)
  refine div_pos ?_ (denom_pos hι hμ i)
  exact_mod_cast Fintype.card_pos_iff.mpr (hne i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **NO SOLUTION OF THE SECULAR EQUATION LIES BELOW THE SMALLEST POLE.** -/
theorem poleMin_le_of_secular_root (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ : ℝ}
    (hs : secularSum (V := V) μ = -1) : poleMin (V := V) hι ≤ μ := by
  by_contra hcon
  have hpos := secularSum_pos (V := V) hne hι (lt_of_not_ge hcon)
  rw [hs] at hpos
  linarith

/-! ## 2. So every root but one lies in the closed interval between the extreme poles -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE LOCALISATION.** Every root of the secular equation other than the single one above
`poleMax` lies in `[poleMin, poleMax]`. -/
theorem mem_Icc_of_secular_root_ne (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ ν : ℝ}
    (hs : secularSum (V := V) μ = -1) (hν : poleMax (V := V) hι < ν)
    (hsν : secularSum (V := V) ν = -1) (hne' : μ ≠ ν) :
    μ ∈ Set.Icc (poleMin (V := V) hι) (poleMax (V := V) hι) := by
  refine ⟨poleMin_le_of_secular_root hne hι hs, ?_⟩
  by_contra hcon
  exact hne' (secular_root_unique hne hι (lt_of_not_ge hcon) hν hs hsν)

/-- **AND SO EVERY EIGENVALUE OF `Q` OFF THE PART VALUES IS BOUNDED BELOW BY `N − 2·maxᵢ nᵢ`.** -/
theorem poleMin_le_of_isEigenvalue (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ : ℝ}
    (hval : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hx : ∃ x : (Σ i, V i) → ℝ, x ≠ 0
      ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x) :
    poleMin (V := V) hι ≤ μ :=
  poleMin_le_of_secular_root hne hι
    ((isEigenvalue_signless_iff_secular hne (Classical.choice hι) hval hd).mp hx)

end SecularRootBounds
