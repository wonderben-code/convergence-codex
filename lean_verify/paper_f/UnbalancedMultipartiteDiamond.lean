import UnbalancedMultipartiteSecularEquation

/-!
# `K₄` minus an edge: the whole signless spectrum, irrational eigenvalues and all

**THE PREVIOUS UNIT'S `§6` REFUSED EXACTLY THIS AND NAMED THE OBSTACLE.** It computed a complete
signless spectrum, at the three-vertex path — and said plainly that the path is two-colourable, so
the answer was never in doubt, and that a complete spectrum at a graph that is **not**
two-colourable would need the quadratic `μ² − 6μ + 4`, whose roots are irrational. **That is this
file.** Parts of sizes `1`, `1`, `2`: four vertices, five edges, the graph this chain has carried
as its witness since `UnbalancedMultipartiteSignless`, and
`UnbalancedMultipartiteSignless.not_colorable_two_diamond` proves it is not two-colourable.

**THE ANSWER.** `Q = D + A` has eigenvalues **`2`, `3 + √5` and `3 − √5`**, and nothing else; the
first has multiplicity `2`, the other two are simple, and the three multiplicities sum to `4`.

## What is actually new, stated narrowly

The estate already holds complete signless spectra at the cycle, the box, the torus, the complete
graph (`CompleteSignlessSpectrum`, non-two-colourable from three vertices) and the balanced complete
multipartite family (`MultipartiteSpectrum.eigenvalue_signlessLap_multi`, non-two-colourable from
three parts), and the previous unit added the three-vertex path. **Every one of those graphs is
regular or two-colourable** — read off, not formalised — and every one of those spectra is reached
by the same two vectors, the constant one and the zero-sum ones. **This graph is neither**: its
degrees are `3, 3, 2, 2`, it is not two-colourable, and its eigenvalues are irrational, so no
constant-plus-zero-sum decomposition can produce them. That is the novelty, and it is narrow: the
point is not that four vertices are hard, but that **nothing about this graph was used except its
part sizes** — the route is the general secular criterion, instantiated.

## What is proved

**`two_lt_sqrt_five`, `sqrt_five_lt_three`** — the two bounds every non-degeneracy below needs.
**`secularSum_diamond`** — the secular sum here is `2/(2 − μ) + 2/(0 − μ)`, written as the three
part terms. **`secularSum_diamond_eq_neg_one`** — off `μ = 2` and `μ = 0` it equals `−1` exactly at
`3 ± √5`; the quadratic is cleared and factored by hand, `√5 ² = 5` being the only fact about the
root that is used.

**`finrank_signless_diamond_zero`, `finrank_signless_diamond_three`** — the two excluded values that
are *not* eigenvalues: `0` by the previous chain's one-half-part equality (`n = 4`, no part of size
four), and `3` by the secular criterion at the part value `N − 1` (no part of size one-half, and the
sum there is `−8/3`). **The third excluded value, `2`, is an eigenvalue** and its multiplicity was
computed two units ago: exactly `2`.

**`part_value_ne_diamond`, `denom_ne_zero_diamond`** — the criterion's two hypotheses, discharged at
this graph by three-way case analysis. **`finrank_signless_diamond_add_sqrt`,
`finrank_signless_diamond_sub_sqrt`** — so each irrational eigenvalue is **simple**.

**`isEigenvalue_signless_diamond`** — **THE SPECTRUM, AS AN `iff`**, by cases on the three excluded
values and the criterion everywhere else. **`finrank_signless_diamond_add`** — and the
multiplicities `2 + 1 + 1` add to the vertex count, which is what makes the list complete rather
than merely correct.

## What is NOT here

* **NO CHARACTERISTIC POLYNOMIAL**, here or anywhere for `Q` on this family. The spectrum is a set
  with multiplicities, not a factorisation of `Matrix.charpoly (signlessLap …)`, and the agreement
  of these multiplicities with `Polynomial.rootMultiplicity` is not proved — the same gap
  `MultipartiteCharpoly` closed on the *ordinary* Laplacian's side and nobody has closed here.

⚠ **BOTH HALVES CLOSED AT THIS GRAPH THE NEXT UNIT (2026-09-12, entry 159), AND THE PARAGRAPH IS
KEPT AS WRITTEN** (`ERRATUM 94`). `HermitianRootMultiplicity.charpoly_signless_diamond` gives
`(X − 2)²·(X − (3 + √5))·(X − (3 − √5))`, and `rootMultiplicity_charpoly_signlessLap` gives the
agreement for `Q` on any graph. **The clause's first three words still stand for the family**: the
general polynomial needs the secular roots, and only this graph's are known.
* **NO SECOND GRAPH.** The quadratic is solved because it is a quadratic. At `r` parts the secular
  equation has degree up to `r` and nothing here helps; this is one instance, not a method for the
  family (`ERRATUM 194`).
* **NO IDENTIFICATION WITH `K₄` MINUS AN EDGE.** That is the classical name for the graph and no
  isomorphism to any other description is formalised, as everywhere in this chain. What is
  machine-checked is the spectrum of the complete multipartite graph on parts of sizes `1`, `1`
  and `2`.
* **NOTHING AT AN EMPTY PART, NOTHING OVER `ℂ`, AND NO ORDINARY-LAPLACIAN CLAIM** — `L`'s spectrum
  here is the earlier units' and is different (`0`, `2`, `4`); nothing in this file compares them.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none but the concrete type
`fun i : Fin 3 => Fin (i.1 / 2 + 1)` — every statement here is about one graph, and the general
hypotheses of the theorems it invokes are discharged inside. **No mass, no propagator, and no
metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteDiamond

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open UnbalancedMultipartiteSignless UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularBound UnbalancedMultipartiteSecularEquation

/-- The parts of the diamond: sizes `1`, `1`, `2`. -/
abbrev DiamondPart : Fin 3 → Type := fun i => Fin (i.1 / 2 + 1)

/-! ## 1. Two bounds on `√5` -/

theorem two_lt_sqrt_five : (2 : ℝ) < Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

/-! ## 2. The secular sum at the diamond -/

theorem secularSum_diamond (μ : ℝ) :
    secularSum (V := DiamondPart) μ = 1 / (2 - μ) + 1 / (2 - μ) + 2 / (0 - μ) := by
  rw [secularSum, card_diamond, Fin.sum_univ_three]
  norm_num

/-- **THE SECULAR EQUATION HERE IS A QUADRATIC, AND ITS ROOTS ARE IRRATIONAL.** -/
theorem secularSum_diamond_eq_neg_one {μ : ℝ} (h2 : μ ≠ 2) (h0 : μ ≠ 0) :
    secularSum (V := DiamondPart) μ = -1 ↔ μ = 3 + Real.sqrt 5 ∨ μ = 3 - Real.sqrt 5 := by
  have ha : (2 : ℝ) - μ ≠ 0 := fun h => h2 (by linarith)
  have hb : (0 : ℝ) - μ ≠ 0 := fun h => h0 (by linarith)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [secularSum_diamond]
  constructor
  · intro h
    field_simp at h
    have hq : (μ - (3 + Real.sqrt 5)) * (μ - (3 - Real.sqrt 5)) = 0 := by
      linear_combination h - h5
    rcases mul_eq_zero.mp hq with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> · field_simp; nlinarith [h5]

/-! ## 3. The two excluded values that are not eigenvalues -/

theorem finrank_signless_diamond_zero :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (0 : ℝ) • LinearMap.id)) = 0 := by
  have hval : ((Fintype.card (Σ i : Fin 3, DiamondPart i) : ℝ) - ((4 : ℕ) : ℝ)) = 0 := by
    rw [card_diamond]; norm_num
  have hk : Fintype.card {i : Fin 3 // 2 * Fintype.card (DiamondPart i) = 4} = 1 := by decide
  have hle := finrank_ker_secularMap_le_half (V := DiamondPart) (n := 4) (fun _ => ⟨0⟩) 2
    (by decide)
  rw [hval, hk] at hle
  have heq := finrank_signless_eigenspace_of_ne (V := DiamondPart) (μ := 0) (fun _ => ⟨0⟩)
    (fun i => by
      rw [card_diamond, Fintype.card_fin]
      fin_cases i <;> norm_num)
  omega

theorem finrank_signless_diamond_three :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (3 : ℝ) • LinearMap.id)) = 0 := by
  have hval : ((Fintype.card (Σ i : Fin 3, DiamondPart i) : ℝ) - ((1 : ℕ) : ℝ)) = 3 := by
    rw [card_diamond]; norm_num
  have hs : secularSum (V := DiamondPart)
      ((Fintype.card (Σ i : Fin 3, DiamondPart i) : ℝ) - ((1 : ℕ) : ℝ)) ≠ -1 := by
    rw [hval, secularSum_diamond]
    norm_num
  have h := finrank_signless_size_secular_zero (V := DiamondPart) (n := 1) (by norm_num)
    (by rw [card_diamond]; norm_num) (fun _ => ⟨0⟩) (by decide) hs
  rw [hval] at h
  rw [h]
  decide

/-! ## 4. The criterion's two hypotheses, at this graph -/

theorem part_value_ne_diamond {μ : ℝ} (h2 : μ ≠ 2) (h3 : μ ≠ 3) (i : Fin 3) :
    ((Fintype.card (Σ i : Fin 3, DiamondPart i) : ℝ) - Fintype.card (DiamondPart i)) ≠ μ := by
  rw [card_diamond, Fintype.card_fin]
  fin_cases i
  · intro h; exact h3 (by norm_num at h; linarith)
  · intro h; exact h3 (by norm_num at h; linarith)
  · intro h; exact h2 (by norm_num at h; linarith)

theorem denom_ne_zero_diamond {μ : ℝ} (h2 : μ ≠ 2) (h0 : μ ≠ 0) (i : Fin 3) :
    ((Fintype.card (Σ i : Fin 3, DiamondPart i) : ℝ)
      - 2 * Fintype.card (DiamondPart i) - μ) ≠ 0 := by
  rw [card_diamond, Fintype.card_fin]
  fin_cases i
  · intro h; exact h2 (by norm_num at h; linarith)
  · intro h; exact h2 (by norm_num at h; linarith)
  · intro h; exact h0 (by norm_num at h; linarith)

/-! ## 5. The two irrational eigenvalues, each simple -/

theorem finrank_signless_diamond_secular {μ : ℝ} (h2 : μ ≠ 2) (h0 : μ ≠ 0) (h3 : μ ≠ 3)
    (hs : secularSum (V := DiamondPart) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart)) - μ • LinearMap.id)) = 1 :=
  finrank_signless_eigenspace_secular_one (fun _ => ⟨0⟩) 0 (part_value_ne_diamond h2 h3)
    (denom_ne_zero_diamond h2 h0) hs

theorem finrank_signless_diamond_add_sqrt :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (3 + Real.sqrt 5) • LinearMap.id)) = 1 := by
  have hb2 := two_lt_sqrt_five
  have h2 : (3 : ℝ) + Real.sqrt 5 ≠ 2 := by intro h; linarith
  have h0 : (3 : ℝ) + Real.sqrt 5 ≠ 0 := by intro h; linarith
  have h3 : (3 : ℝ) + Real.sqrt 5 ≠ 3 := by intro h; linarith
  exact finrank_signless_diamond_secular h2 h0 h3
    ((secularSum_diamond_eq_neg_one h2 h0).mpr (Or.inl rfl))

theorem finrank_signless_diamond_sub_sqrt :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (3 - Real.sqrt 5) • LinearMap.id)) = 1 := by
  have hb2 := two_lt_sqrt_five
  have hb3 := sqrt_five_lt_three
  have h2 : (3 : ℝ) - Real.sqrt 5 ≠ 2 := by intro h; linarith
  have h0 : (3 : ℝ) - Real.sqrt 5 ≠ 0 := by intro h; linarith
  have h3 : (3 : ℝ) - Real.sqrt 5 ≠ 3 := by intro h; linarith
  exact finrank_signless_diamond_secular h2 h0 h3
    ((secularSum_diamond_eq_neg_one h2 h0).mpr (Or.inr rfl))

/-! ## 6. The whole signless spectrum of a graph that is not two-colourable -/

/-- **THE SPECTRUM.** `Q`'s eigenvalues at parts of sizes `1`, `1`, `2` are exactly `2`,
`3 + √5` and `3 − √5`. -/
theorem isEigenvalue_signless_diamond (μ : ℝ) :
    (∃ x : (Σ i : Fin 3, DiamondPart i) → ℝ, x ≠ 0 ∧
        signlessLap (completeMultipartiteGraph DiamondPart) *ᵥ x = μ • x)
      ↔ μ = 2 ∨ μ = 3 + Real.sqrt 5 ∨ μ = 3 - Real.sqrt 5 := by
  have hb2 := two_lt_sqrt_five
  have hb3 := sqrt_five_lt_three
  by_cases h2 : μ = 2
  · subst h2
    refine iff_of_true ?_ (Or.inl rfl)
    rw [isEigenvector_iff_finrank_pos, finrank_signless_eigenspace_diamond]
    norm_num
  by_cases h0 : μ = 0
  · subst h0
    refine iff_of_false (fun hex => ?_) (by rintro (h | h | h) <;> linarith)
    rw [isEigenvector_iff_finrank_pos, finrank_signless_diamond_zero] at hex
    exact lt_irrefl 0 hex
  by_cases h3 : μ = 3
  · subst h3
    refine iff_of_false (fun hex => ?_) (by rintro (h | h | h) <;> linarith)
    rw [isEigenvector_iff_finrank_pos, finrank_signless_diamond_three] at hex
    exact lt_irrefl 0 hex
  rw [isEigenvalue_signless_iff_secular (V := DiamondPart) (fun _ => ⟨0⟩) 0
      (part_value_ne_diamond h2 h3) (denom_ne_zero_diamond h2 h0),
    secularSum_diamond_eq_neg_one h2 h0]
  constructor
  · rintro (h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact absurd h h2
    · exact Or.inl h
    · exact Or.inr h

/-- **THE THREE MULTIPLICITIES EXHAUST THE VERTEX COUNT**, so the list is the whole spectrum. -/
theorem finrank_signless_diamond_add :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart)) - (2 : ℝ) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (3 + Real.sqrt 5) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph DiamondPart))
      - (3 - Real.sqrt 5) • LinearMap.id))
      = Fintype.card (Σ i : Fin 3, DiamondPart i) := by
  rw [finrank_signless_eigenspace_diamond, finrank_signless_diamond_add_sqrt,
    finrank_signless_diamond_sub_sqrt, card_diamond]

end UnbalancedMultipartiteDiamond
