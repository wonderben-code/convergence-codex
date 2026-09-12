import CompleteSpectrumTwoPoints

/-!
# The complete equipartite graph: both spectra, complete, on a non-bipartite family

**THE GAP THIS CLOSES IS THE ONE THE LAST TWO UNITS LEFT NAMED.** `ERRATUM 506` corrected a fence of
mine into its true form — *no eigenvalue of `Q` is known at any graph that is neither a cycle, nor a
torus, nor two-colourable with a known Laplacian spectrum* — and `CompleteSignlessSpectrum` narrowed
it by the complete graph. The watchlist line then asked for *a non-bipartite graph that is neither a
cycle nor complete*. This file gives a **two-parameter family** of them: Mathlib's
`completeEquipartiteGraph r t`, `r` parts of `t` vertices with every cross-pair adjacent — complete
multipartite, balanced. It is non-complete for `t ≥ 2`, not a cycle beyond the smallest cases, and
**not two-colourable for `r ≥ 3`**, which is proved here.

**THE ARGUMENT IS THE PREVIOUS UNIT'S, ONE LEVEL DEEPER.** On `K_n` the off-diagonal part is the
all-ones matrix, so an eigenvector either has zero sum or is constant — two cases. Here the
neighbour sum of a vertex is *the total sum minus the sum over the vertex's own part*, so the
relevant data is the **part sums**, and there are three cases: the total sum is non-zero, or it
vanishes with some part sum non-zero, or every part sum vanishes. Summing the eigenvector equation
over all vertices settles the first, summing over **one part** settles the second, and the row
equation settles the third. **No orthogonality, no diagonalisation, no `IsHermitian`.**

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED** (`ERRATUM 500`'s rule): all of it, the family
being new here. Mathlib supplies the graph, `completeEquipartiteGraph_adj`,
`neighborFinset_completeEquipartiteGraph` and `degree_completeEquipartiteGraph` — the degree is
`(r − 1)t` exactly, not bounded, which is what makes the row identity clean. The part sum has no
name in this estate and is written out here as `partSum`.

## What is proved

**`partSum`, `sum_partSum`, `sum_partSum_comp`** — the sum over one part, that the part sums add to
the total, and that `∑_v partSum x v.1 = t · ∑ x` — the second identity being the one the
part-splitting argument turns on.

**`adjMatrix_multi_mulVec`, `degMatrix_multi_mulVec`** — the neighbour sum is `∑x − partSum x v.1`
and the degree acts by `(r − 1)t`; **`signlessLap_multi_mulVec`, `lapMatrix_multi_mulVec`** — hence
`(Qx)(v) = (r−1)t·x(v) + ∑x − partSum x v.1` and `(Lx)(v) = (r−1)t·x(v) − ∑x + partSum x v.1`.

**`signlessLap_multi_mulVec_const`** — `Q` has eigenvalue **`2(r−1)t`** on the constants;
**`signlessLap_multi_mulVec_of_part_const`** — **`(r−2)t`** on the vectors that are constant on
each part and sum to zero; **`signlessLap_multi_mulVec_of_partSum_eq_zero`** — **`(r−1)t`** on the
vectors whose every part sum vanishes.

**`eigenvalue_signlessLap_multi`** — **AND THOSE THREE ARE ALL OF THEM**: every eigenvalue of `Q` on
`completeEquipartiteGraph r t` is `2(r−1)t`, `(r−2)t` or `(r−1)t`, with **no hypothesis on `r` or
`t`**.

**`lapMatrix_multi_mulVec_of_partSum_eq_zero`, `lapMatrix_multi_mulVec_of_part_const`,
`eigenvalue_lapMatrix_multi`** — the same for the ordinary Laplacian: `0` on the constants, `rt` on
the part-constant zero-sum vectors, `(r−1)t` on the vectors with vanishing part sums, and **those
three are all of them**. That is the classical complete-multipartite Laplacian spectrum, which this
estate did not have.

**`not_colorable_two_multi`** — **AND THE GRAPH IS NOT TWO-COLOURABLE FOR `r ≥ 3`**, from one vertex
in each of three parts: they are pairwise adjacent, so their colours are pairwise distinct, and
three distinct colours do not fit in `Fin 2`. That is what makes this family a witness for the gap
rather than another instance of `SignlessBipartite`.

**A CONSISTENCY CHECK THE READER CAN DO IN THEIR HEAD, AND IT IS ARITHMETIC AND NOT A THEOREM.** At
`r = 2` the graph is bipartite, and `SignlessBipartite` says the two spectra must then coincide:
`Q`'s three values are `2t, 0, t` and `L`'s are `0, 2t, t`. They do. At `t = 1` the graph is `K_r`
and the values are `2r − 2, r − 2, r − 1` against `CompleteSignlessSpectrum`'s `2n − 2` and `n − 2`
— the third is spurious there, because at `t = 1` the *vectors with vanishing part sums* are all
zero, so `(r−1)t` is attained by nothing. **Neither observation is proved below**, and the second is
a reminder that an exhaustion theorem lists candidates, not attained values.

## What is NOT here

* **NO MULTIPLICITIES AND NO EIGENSPACES.** `CompleteSpectrumTwoPoints` identified both of `K_n`'s
  eigenspaces as submodules and counted their dimensions. Nothing of the kind is done here: the
  three families are exhibited and the exhaustion is proved, and the dimensions `1`, `r − 1`,
  `r(t − 1)` are **not** computed. Not attempted, no cost claimed (`ERRATUM 246`); the watchlist
  carries it.
* **NO CHARACTERISTIC POLYNOMIAL.** As in the previous unit, that step needs diagonalisability,
  which this argument avoids.
⚠ **THE REASON IN THE PARAGRAPH ABOVE IS FALSE AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`, `ERRATUM 508`, 2026-09-12). It does not matter what this file's argument avoids:
`Matrix.IsHermitian.charpoly_eq` supplies the diagonalisation for **every** Hermitian matrix, and
this estate had been citing it since 2026-08-26 (`HermitianSpectralMapping`, `RayleighPow`). What
was genuinely missing was the **grouping** — the product over the index type is free, and the
explicit factorisation with multiplicities as exponents needed the dimension-to-fibre bridge, now
`HermitianCharpoly.charpoly_eq_prod_pow_finrank`. **The absence itself was correctly declared**:
this file writes no characteristic polynomial.
* **NO NON-VACUITY FOR THE THIRD FAMILY.** That a vector with every part sum zero and not
  identically zero exists needs `t ≥ 2`, and **it is not proved below** — at `t = 1` the family is
  trivial, which is exactly the `K_n` case the check above describes. * **NO CONNECTEDNESS.** The
  graph is connected for `r ≥ 2` and nothing here says so. * **NOTHING FOR AN UNBALANCED COMPLETE
  MULTIPARTITE GRAPH.** Mathlib's `completeEquipartiteGraph` has parts of equal size; the general
  `K_{n₁,…,n_k}` spectrum needs the degree to vary with the part, and the row identity above would
  change shape. * **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and
  `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `r` and `t` natural numbers and nothing
else on the fourteen spectral statements — no positivity, no bound, and in particular **the two
exhaustion theorems take no hypothesis on `r` or `t` at all**. Only `not_colorable_two_multi`
takes `3 ≤ r` and `1 ≤ t`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteSpectrum

open Matrix Finset SimpleGraph LaplacianSignless

variable {r t : ℕ}

/-- The sum of a vector over one part of the complete equipartite graph. -/
def partSum (x : Fin r × Fin t → ℝ) (i : Fin r) : ℝ := ∑ j : Fin t, x (i, j)

theorem sum_partSum (x : Fin r × Fin t → ℝ) : ∑ i, partSum x i = ∑ u, x u := by
  simp only [partSum]
  exact (Fintype.sum_prod_type (f := x)).symm

/-! ## 1. The two matrices acting on a vector -/

theorem adjMatrix_multi_mulVec (x : Fin r × Fin t → ℝ) (v : Fin r × Fin t) :
    ((completeEquipartiteGraph r t).adjMatrix ℝ *ᵥ x) v = (∑ u, x u) - partSum x v.1 := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_completeEquipartiteGraph,
    Finset.sum_product]
  have hpart : ∀ i : Fin r, ∑ j : Fin t, x (i, j) = partSum x i := fun _ => rfl
  rw [Finset.sum_congr rfl fun i _ => hpart i, eq_sub_iff_add_eq,
    ← Finset.sum_singleton (f := partSum x) (a := v.1), Finset.sum_compl_add_sum, sum_partSum]

theorem degMatrix_multi_mulVec (x : Fin r × Fin t → ℝ) (v : Fin r × Fin t) :
    ((completeEquipartiteGraph r t).degMatrix ℝ *ᵥ x) v = (((r : ℝ) - 1) * t) * x v := by
  classical
  have hd : (completeEquipartiteGraph r t).degree v = (r - 1) * t :=
    degree_completeEquipartiteGraph v
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact absurd v.1.isLt (by simp [h])
    · exact h
  rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal, hd]
  push_cast [Nat.cast_sub hr]
  ring

theorem signlessLap_multi_mulVec (x : Fin r × Fin t → ℝ) (v : Fin r × Fin t) :
    (signlessLap (completeEquipartiteGraph r t) *ᵥ x) v
      = (((r : ℝ) - 1) * t) * x v + (∑ u, x u) - partSum x v.1 := by
  rw [signlessLap, Matrix.add_mulVec, Pi.add_apply, degMatrix_multi_mulVec,
    adjMatrix_multi_mulVec]
  ring

theorem lapMatrix_multi_mulVec (x : Fin r × Fin t → ℝ) (v : Fin r × Fin t) :
    ((completeEquipartiteGraph r t).lapMatrix ℝ *ᵥ x) v
      = (((r : ℝ) - 1) * t) * x v - (∑ u, x u) + partSum x v.1 := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply, degMatrix_multi_mulVec,
    adjMatrix_multi_mulVec]
  ring

/-! ## 2. The three eigenvector families -/

theorem sum_partSum_comp (x : Fin r × Fin t → ℝ) :
    ∑ v : Fin r × Fin t, partSum x v.1 = (t : ℝ) * ∑ u, x u := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_partSum, mul_comm]

theorem signlessLap_multi_mulVec_const (c : ℝ) :
    signlessLap (completeEquipartiteGraph r t) *ᵥ (fun _ ↦ c)
      = (2 * ((r : ℝ) - 1) * t) • (fun _ ↦ c) := by
  funext v
  rw [signlessLap_multi_mulVec]
  simp only [partSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fintype.card_prod, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem signlessLap_multi_mulVec_of_partSum_eq_zero {x : Fin r × Fin t → ℝ}
    (h : ∀ i, partSum x i = 0) :
    signlessLap (completeEquipartiteGraph r t) *ᵥ x = (((r : ℝ) - 1) * t) • x := by
  funext v
  have hS : ∑ u, x u = 0 := by rw [← sum_partSum]; simp [h]
  rw [signlessLap_multi_mulVec, hS, h v.1]
  simp

theorem signlessLap_multi_mulVec_of_part_const {x : Fin r × Fin t → ℝ}
    (hpc : ∀ v : Fin r × Fin t, partSum x v.1 = (t : ℝ) * x v) (hS : ∑ u, x u = 0) :
    signlessLap (completeEquipartiteGraph r t) *ᵥ x = (((r : ℝ) - 2) * t) • x := by
  funext v
  rw [signlessLap_multi_mulVec, hS, hpc v]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 3. And every eigenvalue is one of the three -/

theorem eigenvalue_signlessLap_multi {μ : ℝ} {x : Fin r × Fin t → ℝ} (hx0 : x ≠ 0)
    (hx : signlessLap (completeEquipartiteGraph r t) *ᵥ x = μ • x) :
    μ = 2 * ((r : ℝ) - 1) * t ∨ μ = ((r : ℝ) - 2) * t ∨ μ = ((r : ℝ) - 1) * t := by
  classical
  have hrow : ∀ v : Fin r × Fin t,
      (((r : ℝ) - 1) * t) * x v + (∑ u, x u) - partSum x v.1 = μ * x v := by
    intro v
    have hv := congrFun hx v
    rw [signlessLap_multi_mulVec] at hv
    simpa using hv
  by_cases hS : ∑ u, x u = 0
  · by_cases hP : ∀ i, partSum x i = 0
    · right; right
      obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
        by_contra hall
        exact hx0 (funext fun v => by simpa using not_not.mp (not_exists.mp hall v))
      have hvx := hrow v
      rw [hS, hP v.1, add_zero, sub_zero] at hvx
      exact (mul_right_cancel₀ hv hvx).symm
    · right; left
      obtain ⟨i, hi⟩ := not_forall.mp hP
      have hpart : (((r : ℝ) - 2) * t) * partSum x i = μ * partSum x i := by
        have h1 : ∑ j : Fin t, ((((r : ℝ) - 1) * t) * x (i, j) + (∑ u, x u) - partSum x i)
            = ∑ j : Fin t, μ * x (i, j) :=
          Finset.sum_congr rfl fun j _ => hrow (i, j)
        simp only [hS, add_zero, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        simp only [partSum] at h1 ⊢
        ring_nf at h1 ⊢
        linarith [h1]
      exact (mul_right_cancel₀ hi hpart).symm
  · left
    have hsum : (2 * ((r : ℝ) - 1) * t) * (∑ u, x u) = μ * ∑ u, x u := by
      have h1 : ∑ v : Fin r × Fin t, ((((r : ℝ) - 1) * t) * x v + (∑ u, x u) - partSum x v.1)
          = ∑ v : Fin r × Fin t, μ * x v :=
        Finset.sum_congr rfl fun v _ => hrow v
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, sum_partSum_comp] at h1
      push_cast at h1
      ring_nf at h1 ⊢
      linarith [h1]
    exact (mul_right_cancel₀ hS hsum).symm

/-! ## 4. The same for the ordinary Laplacian -/

theorem lapMatrix_multi_mulVec_of_partSum_eq_zero {x : Fin r × Fin t → ℝ}
    (h : ∀ i, partSum x i = 0) :
    (completeEquipartiteGraph r t).lapMatrix ℝ *ᵥ x = (((r : ℝ) - 1) * t) • x := by
  funext v
  have hS : ∑ u, x u = 0 := by rw [← sum_partSum]; simp [h]
  rw [lapMatrix_multi_mulVec, hS, h v.1]
  simp

theorem lapMatrix_multi_mulVec_of_part_const {x : Fin r × Fin t → ℝ}
    (hpc : ∀ v : Fin r × Fin t, partSum x v.1 = (t : ℝ) * x v) (hS : ∑ u, x u = 0) :
    (completeEquipartiteGraph r t).lapMatrix ℝ *ᵥ x = ((r : ℝ) * t) • x := by
  funext v
  rw [lapMatrix_multi_mulVec, hS, hpc v]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem eigenvalue_lapMatrix_multi {μ : ℝ} {x : Fin r × Fin t → ℝ} (hx0 : x ≠ 0)
    (hx : (completeEquipartiteGraph r t).lapMatrix ℝ *ᵥ x = μ • x) :
    μ = 0 ∨ μ = (r : ℝ) * t ∨ μ = ((r : ℝ) - 1) * t := by
  classical
  have hrow : ∀ v : Fin r × Fin t,
      (((r : ℝ) - 1) * t) * x v - (∑ u, x u) + partSum x v.1 = μ * x v := by
    intro v
    have hv := congrFun hx v
    rw [lapMatrix_multi_mulVec] at hv
    simpa using hv
  by_cases hS : ∑ u, x u = 0
  · by_cases hP : ∀ i, partSum x i = 0
    · right; right
      obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
        by_contra hall
        exact hx0 (funext fun v => by simpa using not_not.mp (not_exists.mp hall v))
      have hvx := hrow v
      rw [hS, hP v.1, sub_zero, add_zero] at hvx
      exact (mul_right_cancel₀ hv hvx).symm
    · right; left
      obtain ⟨i, hi⟩ := not_forall.mp hP
      have hpart : ((r : ℝ) * t) * partSum x i = μ * partSum x i := by
        have h1 : ∑ j : Fin t, ((((r : ℝ) - 1) * t) * x (i, j) - (∑ u, x u) + partSum x i)
            = ∑ j : Fin t, μ * x (i, j) :=
          Finset.sum_congr rfl fun j _ => hrow (i, j)
        simp only [hS, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        simp only [partSum] at h1 ⊢
        ring_nf at h1 ⊢
        linarith [h1]
      exact (mul_right_cancel₀ hi hpart).symm
  · left
    have hsum : (0 : ℝ) * (∑ u, x u) = μ * ∑ u, x u := by
      have h1 : ∑ v : Fin r × Fin t, ((((r : ℝ) - 1) * t) * x v - (∑ u, x u) + partSum x v.1)
          = ∑ v : Fin r × Fin t, μ * x v :=
        Finset.sum_congr rfl fun v _ => hrow v
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, sum_partSum_comp] at h1
      push_cast at h1
      ring_nf at h1 ⊢
      linarith [h1]
    exact (mul_right_cancel₀ hS hsum).symm

/-! ## 5. And the graph is not two-colourable above two parts -/

theorem not_colorable_two_multi (hr : 3 ≤ r) (ht : 1 ≤ t) :
    ¬ (completeEquipartiteGraph r t).Colorable 2 := by
  intro hcol
  obtain ⟨C⟩ := hcol
  set j : Fin t := ⟨0, by omega⟩ with hj
  set a : Fin r × Fin t := (⟨0, by omega⟩, j) with ha
  set b : Fin r × Fin t := (⟨1, by omega⟩, j) with hb
  set c : Fin r × Fin t := (⟨2, by omega⟩, j) with hc
  have hab : (completeEquipartiteGraph r t).Adj a b := by
    rw [completeEquipartiteGraph_adj]
    simp [ha, hb, Fin.ext_iff]
  have hac : (completeEquipartiteGraph r t).Adj a c := by
    rw [completeEquipartiteGraph_adj]
    simp [ha, hc, Fin.ext_iff]
  have hbc : (completeEquipartiteGraph r t).Adj b c := by
    rw [completeEquipartiteGraph_adj]
    simp [hb, hc, Fin.ext_iff]
  have h1 : C a ≠ C b := C.valid hab
  have h2 : C a ≠ C c := C.valid hac
  have h3 : C b ≠ C c := C.valid hbc
  have : (3 : ℕ) ≤ Fintype.card (Fin 2) := by
    refine Fintype.card_le_of_injective
      (fun i : Fin 3 => if i = 0 then C a else if i = 1 then C b else C c) ?_
    intro i i' hii
    fin_cases i <;> fin_cases i' <;> simp_all
  simp at this

end MultipartiteSpectrum
