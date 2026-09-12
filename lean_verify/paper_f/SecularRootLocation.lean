import MultipartiteSignlessSingleton

/-!
# Locating a secular root without solving for it

**FIVE UNITS HAVE PRICED THE SECULAR EQUATION AND NONE HAS TOUCHED IT.** Since entry 154 the chain
has said the same thing in five headers: `∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1` is *a polynomial of degree up
to `r`, and nothing here solves it*. That pricing is right and this file does not solve it either.
**It does something the pricing did not consider: it locates a root.** The function is a sum of
simple fractions, and above all of its poles every term is negative and every term is increasing,
so the sum climbs strictly from below `−1` to nearly `0` — and crosses `−1` exactly once. Two
explicit values and the intermediate value theorem do the rest; no root is computed anywhere.

## What is proved

**`poleMax`** — the largest of the values `N − 2nᵢ`, above which every denominator is negative
(`denom_neg`). **`term_nonpos`, `secularSum_strictMono`** — above it every term of the sum is
non-positive, and the sum is **strictly increasing**.

**`secularSum_le_neg_two`** — at `poleMax + nᵢ₀/2`, where `i₀` is a part achieving the maximum, the
sum is at most `−2`: the `i₀` term is exactly `−2` and every other term is non-positive. **No limit
is taken** — the value is explicit. **`secularSum_gt_neg_one`** — at `2N + 1` the sum exceeds `−1`,
because each term is at least `−nᵢ/(N + 1)` and the sizes add to `N`.

**`continuousOn_secularSum`, `exists_secular_root`** — so by the intermediate value theorem the
equation **has a root above `poleMax`**, on every complete multipartite graph with non-empty parts,
with no size condition and no colourability condition. **`secular_root_unique`** — and strict
monotonicity makes it **the only** root there.

**`exists_signless_eigenvector_above_poleMax`** — and that root **is an eigenvalue of `Q`**, through
entry 157's explicit secular eigenvector. This is the chain's first `Q`-eigenvalue statement that
takes no hypothesis but non-emptiness: entry 154's needs a part with two or more vertices, so at a
graph whose parts are all singletons it says nothing, and this says something.

## What is NOT here

* **THE ROOT IS NOT COMPUTED, AND THAT IS THE POINT.** Nothing here evaluates it, bounds it above,
  or identifies it with a named quantity. The two explicit values are a bracket for the
  intermediate value theorem and are not claimed to be tight.
* **IT IS NOT SHOWN TO BE THE ONLY EIGENVALUE ABOVE `poleMax`, AND IT IS NOT.** Uniqueness here is
  uniqueness of the **secular root**. A part value `N − nᵢ` can also exceed `poleMax` and be an
  eigenvalue — at `r` equal parts of size `t` the part value `(r−1)t` exceeds `poleMax = (r−2)t`
  and is an eigenvalue of multiplicity `r(t−1)`. Confusing the two would be a real error and the
  statements are worded to prevent it.
* **NO CLAIM THAT IT IS THE LARGEST EIGENVALUE.** It is, in every case this chain has computed —
  `3 + √5` at `K₄` minus an edge, `2(r−1)t` on the equipartite family, `3` on the three-vertex path
  — but that is three data points read off, **not a theorem**, and no Perron-type argument is given.
* **NO COUNT OF THE OTHER ROOTS.** The same monotonicity argument between consecutive poles would
  give one root in each gap, and hence the exact number of secular eigenvalues; that needs the
  distinct pole values ordered and is **not attempted** (`ERRATUM 246`). Naming it is not a claim
  that it is short (`ERRATUM 194`).
* **NOTHING FOR THE ORDINARY LAPLACIAN**, which has no secular equation on this family — its whole
  spectrum was computed exactly, units ago, without one.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `Nonempty ι` wherever `poleMax` appears, since a maximum over an empty index has no
meaning; `∀ i, Nonempty (V i)` on everything analytic, because a part of size zero contributes a
term that is identically zero and breaks the strict monotonicity. **No mass, no propagator, and no
metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootLocation

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open UnbalancedMultipartiteSignless UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The largest of the values `N − 2nᵢ`, above which every secular denominator is negative. -/
noncomputable def poleMax (hι : Nonempty ι) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr hι)
    fun i => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem le_poleMax (hι : Nonempty ι) (i : ι) :
    (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) ≤ poleMax (V := V) hι := by
  rw [poleMax]
  exact Finset.le_sup'
    (fun j : ι => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j))
    (Finset.mem_univ i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem exists_eq_poleMax (hι : Nonempty ι) :
    ∃ i : ι, poleMax (V := V) hι
      = (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) := by
  rw [poleMax]
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.mpr hι)
    (fun i => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
  exact ⟨i, hi⟩

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem denom_neg (hι : Nonempty ι) {μ : ℝ} (hμ : poleMax (V := V) hι < μ) (i : ι) :
    (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ < 0 :=
  sub_neg.mpr (lt_of_le_of_lt (le_poleMax hι i) hμ)

/-! ## 2. Above the largest pole the secular sum is negative and strictly increasing -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem term_nonpos (hι : Nonempty ι) {μ : ℝ}
    (hμ : poleMax (V := V) hι < μ) (i : ι) :
    (Fintype.card (V i) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≤ 0 := by
  have hn : (0 : ℝ) ≤ Fintype.card (V i) := Nat.cast_nonneg _
  exact div_nonpos_of_nonneg_of_nonpos hn (le_of_lt (denom_neg hι hμ i))

theorem div_lt_div_of_neg_denom {n d₁ d₂ : ℝ} (hn : 0 < n) (h₁ : d₁ < 0) (h₂ : d₂ < 0)
    (h : d₂ < d₁) : n / d₁ < n / d₂ := by
  have hd₁ : d₁ ≠ 0 := ne_of_lt h₁
  have hd₂ : d₂ ≠ 0 := ne_of_lt h₂
  have hsub : n / d₂ - n / d₁ = n * (d₁ - d₂) / (d₁ * d₂) := by
    field_simp
  have hpos : 0 < n * (d₁ - d₂) / (d₁ * d₂) :=
    div_pos (mul_pos hn (by linarith)) (mul_pos_of_neg_of_neg h₁ h₂)
  linarith [hsub ▸ hpos]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_strictMono (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ₁ μ₂ : ℝ}
    (h₁ : poleMax (V := V) hι < μ₁) (h₁₂ : μ₁ < μ₂) :
    secularSum (V := V) μ₁ < secularSum (V := V) μ₂ := by
  rw [secularSum, secularSum]
  refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr hι) fun i _ => ?_
  refine div_lt_div_of_neg_denom ?_ (denom_neg hι h₁ i)
    (denom_neg hι (lt_trans h₁ h₁₂) i) (by linarith)
  exact_mod_cast Fintype.card_pos_iff.mpr (hne i)

/-! ## 3. Two explicit values, one on each side of `−1` -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_le_neg_two (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {i₀ : ι}
    (hi₀ : poleMax (V := V) hι
      = (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀)) :
    secularSum (V := V) (poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2) ≤ -2 := by
  classical
  have hn0 : (0 : ℝ) < Fintype.card (V i₀) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (hne i₀)
  have hlt : poleMax (V := V) hι < poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2 := by
    linarith
  have hterm : (Fintype.card (V i₀) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀)
        - (poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2)) = -2 := by
    rw [← hi₀]
    have : poleMax (V := V) hι
        - (poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2)
        = -((Fintype.card (V i₀) : ℝ) / 2) := by ring
    rw [this]
    field_simp
  have hrest : ∑ i ∈ Finset.univ.erase i₀, (Fintype.card (V i) : ℝ)
      / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
        - (poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => term_nonpos hι hlt i
  rw [secularSum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hterm]
  linarith

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_gt_neg_one :
    -1 < secularSum (V := V) (2 * (Fintype.card (Σ i, V i) : ℝ) + 1) := by
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  have hkey : ∀ i : ι, -((Fintype.card (V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1))
      ≤ (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
          - (2 * (Fintype.card (Σ i, V i) : ℝ) + 1)) := by
    intro i
    have hn : (0 : ℝ) ≤ Fintype.card (V i) := Nat.cast_nonneg _
    have hd : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
        - (2 * (Fintype.card (Σ i, V i) : ℝ) + 1)
        = -((Fintype.card (Σ i, V i) : ℝ) + 1 + 2 * Fintype.card (V i)) := by ring
    rw [hd, div_neg, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hn (by linarith) (by linarith)
  have hsum : ∑ i : ι, -((Fintype.card (V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1))
      ≤ secularSum (V := V) (2 * (Fintype.card (Σ i, V i) : ℝ) + 1) := by
    rw [secularSum]
    exact Finset.sum_le_sum fun i _ => hkey i
  have hval : ∑ i : ι, -((Fintype.card (V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1))
      = -((Fintype.card (Σ i, V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1)) := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, sum_card_part]
  rw [hval] at hsum
  have hlt : -((Fintype.card (Σ i, V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1)) > -1 := by
    have : (Fintype.card (Σ i, V i) : ℝ) / ((Fintype.card (Σ i, V i) : ℝ) + 1) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  linarith

/-! ## 4. Continuity, and the root -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem continuousOn_secularSum (hι : Nonempty ι) {a b : ℝ} (ha : poleMax (V := V) hι < a) :
    ContinuousOn (secularSum (V := V)) (Set.Icc a b) := by
  unfold secularSum
  refine continuousOn_finset_sum _ fun i _ => ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
  exact ne_of_lt (denom_neg hι (lt_of_lt_of_le ha hx.1) i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SECULAR EQUATION HAS A ROOT ABOVE EVERY POLE.** -/
theorem exists_secular_root (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ μ : ℝ, poleMax (V := V) hι < μ ∧ secularSum (V := V) μ = -1 := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_poleMax (V := V) hι
  have hn0 : (0 : ℝ) < Fintype.card (V i₀) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (hne i₀)
  have hN : (0 : ℝ) ≤ Fintype.card (Σ i, V i) := Nat.cast_nonneg _
  set a := poleMax (V := V) hι + (Fintype.card (V i₀) : ℝ) / 2 with hadef
  set b := 2 * (Fintype.card (Σ i, V i) : ℝ) + 1 with hbdef
  have hpa : poleMax (V := V) hι < a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef, hi₀]; linarith
  have hmem : (-1 : ℝ) ∈ Set.Icc (secularSum (V := V) a) (secularSum (V := V) b) :=
    ⟨by linarith [secularSum_le_neg_two (V := V) hne hι hi₀],
      le_of_lt (secularSum_gt_neg_one (V := V))⟩
  obtain ⟨μ, hμmem, hμ⟩ :=
    intermediate_value_Icc hab (continuousOn_secularSum (V := V) hι (b := b) hpa) hmem
  exact ⟨μ, lt_of_lt_of_le hpa hμmem.1, hμ⟩

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **AND IT IS THE ONLY ONE THERE**, by strict monotonicity. -/
theorem secular_root_unique (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ₁ μ₂ : ℝ}
    (h₁ : poleMax (V := V) hι < μ₁) (h₂ : poleMax (V := V) hι < μ₂)
    (hs₁ : secularSum (V := V) μ₁ = -1) (hs₂ : secularSum (V := V) μ₂ = -1) :
    μ₁ = μ₂ := by
  rcases lt_trichotomy μ₁ μ₂ with h | h | h
  · exact absurd (secularSum_strictMono hne hι h₁ h) (by rw [hs₁, hs₂]; exact lt_irrefl _)
  · exact h
  · exact absurd (secularSum_strictMono hne hι h₂ h) (by rw [hs₁, hs₂]; exact lt_irrefl _)

/-! ## 5. So `Q` has an eigenvalue above every pole, and exactly one -/

/-- **AN EIGENVALUE OF `Q` ABOVE `max (N − 2nᵢ)`, ON EVERY COMPLETE MULTIPARTITE GRAPH WITH
NON-EMPTY PARTS** — no size condition, no two-colourability, no computation of the value. -/
theorem exists_signless_eigenvector_above_poleMax (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ μ : ℝ, poleMax (V := V) hι < μ ∧ ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x := by
  obtain ⟨μ, hμp, hμ⟩ := exists_secular_root (V := V) hne hι
  have hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0 :=
    fun i => ne_of_lt (denom_neg hι hμp i)
  obtain ⟨x, hx, hxp⟩ :=
    exists_eigenvector_of_mem_ker_secular hne (mem_ker_secularVec (V := V) hd hμ)
  refine ⟨μ, hμp, x, fun h0 => ?_, hx⟩
  exact secularVec_ne_zero hne (Classical.choice hι) hd (by rw [← hxp, h0, map_zero])

end SecularRootLocation
