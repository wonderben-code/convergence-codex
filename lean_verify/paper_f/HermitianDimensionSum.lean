import SignlessP1123Exact

/-!
# The eigenspace dimensions add to the size, so the last multiplicity is a subtraction

`HermitianFibreCount` proved that a real Hermitian matrix's eigenspace at `μ` has dimension equal
to the **size of the fibre** of Mathlib's eigenvalue enumeration over `μ`, and drew from it the
**inequality** `∑_{μ ∈ s} dim ≤ card V` for any finite `s`. It then stated
`mem_of_isEigenvalue_of_sum_eq` with *the sum equals `card V`* as a **hypothesis**, and every
consumer since has discharged that hypothesis by computing every dimension separately and adding
them up.

**The equality is a theorem, and it was one line from what that file already had**: the fibres of
`hA.eigenvalues` partition `V`, so over the **full image** the sum is `card V` exactly. With it,
the last multiplicity in a table is a subtraction rather than a computation — which matters
because the chain's dimension theorems have a hypothesis (*no part is half-sized*) that fails at
exactly one value on the graphs it can now compute.

## What is proved

**`finrank_eigenspace_eq_zero_of_notMem`** — off the image the eigenspace is trivial, because the
fibre is empty.

**`sum_finrank_image`** — **over the full image the dimensions sum to `card V`.**

**`sum_finrank_eq_of_subset`** — and so over any finset containing the image, the extra terms being
zero. This is the form a consumer wants: it takes a spectrum known as a **set** and returns the
total.

**`image_eigenvalues_P1123`, `finrank_four_P1123`, `finrank_lo_P1123`, `finrank_hi_P1123`,
`finrank_five_P1123`** — **the multiplicity table at `K_{1,1,2,3}`, and the one that could not be
computed is the one that falls out.** At the part value `4` the chain's dimension count applies —
no size is half of `3` — and gives `1·(3−1) + 1 = 3`. At the two irrational roots it gives `1`
each. **At `5` it does not apply at all**: `5 = N − 2` and the singleton parts make `2·1 = 2`
exactly half-sized, which is the hypothesis `finrank_signless_size_eq` needs and the case entry 156
left with only a bound. The sum theorem gives it as `7 − 3 − 1 − 1 = 2`.

**`charpoly_signlessLap_P1123`** — so the characteristic polynomial is `(X − 5)²(X − 4)³(X − (6 −
√17))(X − (6 + √17))`, of degree `2 + 3 + 1 + 1 = 7`. **The chain's first at a complete
multipartite graph with three distinct part sizes** — `MultipartiteSignlessCharpoly` and
`MultipartiteSignlessSingleton` are equipartite, `SignlessPart133Complete` has two sizes — and
**the first anywhere whose exponents are not all computed**: the `2` is a subtraction.

⚠ A first draft called it *the chain's first characteristic polynomial at a graph with an
irrational spectrum*. **That is false and a `grep` before the commit found why**:
`PawSignlessSpectrum.charpoly_signlessLap_paw` has had one since entry 177, the paw's eigenvalues
being `1`, `2`, `(5 ± √17)/2`. Corrected rather than kept, the draft being uncommitted
(`ERRATUM 518`'s precedent).

## What is NOT here

* **THE HALF-SIZED CASE IS STILL NOT COMPUTED, as of 2026-09-13 (entry 66).** The multiplicity at
  `5` is obtained by subtraction, not by an argument about that eigenspace, so nothing here helps
  at a graph with **two** half-sized values — the subtraction determines one unknown, not two. That
  is the honest limit and it is the same gap entry 156 named.
* **NO OTHER GRAPH GAINS A POLYNOMIAL, as of 2026-09-13 (entry 66).** `K_{1,1,2,2}` has the same
  shape of obstruction and is not done here; `K_{1,3,3}` already had its polynomial at entry 180.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the general theorems take a `Fintype` and
`DecidableEq` index and `A.IsHermitian`, **and nothing else** — no positivity, no graph, no
spectrum. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianDimensionSum

open Matrix Polynomial Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessSpectrumComplete SignlessRootOverlap SignlessP1123Exact
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

/-! ## 1. Off the image the eigenspace is trivial -/

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finrank_eigenspace_eq_zero_of_notMem {A : Matrix V V ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (hμ : μ ∉ Finset.univ.image hA.eigenvalues) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) = 0 := by
  classical
  rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA μ,
    Fintype.card_eq_zero_iff]
  exact ⟨fun i => hμ (Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, i.2⟩)⟩

/-! ## 2. So the dimensions add to the size -/

/-- **THE EIGENSPACE DIMENSIONS SUM TO THE SIZE**, the equality `HermitianFibreCount` stated only
as an inequality and then took as a hypothesis. -/
theorem sum_finrank_image {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    ∑ μ ∈ Finset.univ.image hA.eigenvalues,
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Fintype.card V := by
  classical
  have hterm : ∀ μ ∈ Finset.univ.image hA.eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
        = (Finset.univ.filter fun i => hA.eigenvalues i = μ).card := by
    intro μ _
    rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA μ, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm]
  have hfib := Finset.card_eq_sum_card_fiberwise
      (f := hA.eigenvalues) (s := (Finset.univ : Finset V))
      (t := Finset.univ.image hA.eigenvalues)
      (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [Finset.card_univ] at hfib
  rw [← hfib]

/-- And over any finset containing the image, which is the form a consumer wants. -/
theorem sum_finrank_eq_of_subset {A : Matrix V V ℝ} (hA : A.IsHermitian) {s : Finset ℝ}
    (hs : Finset.univ.image hA.eigenvalues ⊆ s) :
    ∑ μ ∈ s, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Fintype.card V := by
  classical
  rw [← Finset.sum_subset hs (fun μ _ hμ => finrank_eigenspace_eq_zero_of_notMem hA hμ)]
  exact sum_finrank_image hA

/-! ## 3. The multiplicity table at `K_{1,1,2,3}` -/

/-- The Hermitian structure on this graph's signless Laplacian. -/
theorem herm_P1123 : (signlessLap (completeMultipartiteGraph P1123)).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian _

theorem distinct_P1123 : (5 : ℝ) ≠ 4 ∧ (5 : ℝ) ≠ lo_P1123 ∧ (5 : ℝ) ≠ hi_P1123
    ∧ (4 : ℝ) ≠ lo_P1123 ∧ (4 : ℝ) ≠ hi_P1123 ∧ lo_P1123 ≠ hi_P1123 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds_P1123
  obtain ⟨hi1, hi2⟩ := hi_bounds_P1123
  refine ⟨by norm_num, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← h] at lo2; norm_num at lo2
  · rw [← h] at hi1; norm_num at hi1
  · rw [← h] at lo2; norm_num at lo2
  · rw [← h] at hi1; norm_num at hi1
  · rw [h] at lo2; linarith

theorem image_eigenvalues_P1123 :
    Finset.univ.image herm_P1123.eigenvalues = ({5, 4, lo_P1123, hi_P1123} : Finset ℝ) := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact spectrum_P1123 μ

theorem finrank_four_P1123 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1123)) - (4 : ℝ) • LinearMap.id)) = 3 := by
  have h := finrank_signless_size_secular_one (V := P1123) (n := 3) (by norm_num)
    (by rw [total_P1123]; norm_num) nonempty_P1123 0
    (by intro i; rcases size_cases_P1123 i with h | h | h <;> rw [h] <;> norm_num)
    (by rw [show ((Fintype.card (Σ i, P1123 i) : ℝ) - ((3 : ℕ) : ℝ)) = 4 from by
          rw [total_P1123]; norm_num]
        rw [show (4 : ℝ) = (Fintype.card (Σ i, P1123 i) : ℝ) - Fintype.card (P1123 3) from by
          rw [total_P1123, card_P1123]; norm_num]
        exact root_P1123)
  rw [show ((Fintype.card (Σ i, P1123 i) : ℝ) - ((3 : ℕ) : ℝ)) = 4 from by
    rw [total_P1123]; norm_num] at h
  rw [h, show Fintype.card {i : Fin 4 // Fintype.card (P1123 i) = 3} = 1 from by decide]

theorem finrank_root_P1123 {μ : ℝ} (h6 : μ ≠ 6) (h5 : μ ≠ 5) (h4 : μ ≠ 4) (h3 : μ ≠ 3)
    (h1 : μ ≠ 1) (hroot : secularSum (V := P1123) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1123)) - μ • LinearMap.id)) = 1 := by
  refine finrank_signless_eigenspace_secular_one (V := P1123) nonempty_P1123 0 ?_ ?_ hroot
  · intro i
    rw [total_P1123]
    rcases size_cases_P1123 i with h | h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h6 (by linarith)
    · exact h5 (by linarith)
    · exact h4 (by linarith)
  · intro i
    rw [total_P1123]
    rcases size_cases_P1123 i with h | h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h5 (by linarith)
    · exact h3 (by linarith)
    · exact h1 (by linarith)

theorem finrank_lo_P1123 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1123)) - lo_P1123 • LinearMap.id)) = 1 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds_P1123
  exact finrank_root_P1123 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    ((root_iff_P1123 lo_P1123 (by linarith) (by linarith) (by linarith)).mpr (Or.inr (Or.inl rfl)))

theorem finrank_hi_P1123 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1123)) - hi_P1123 • LinearMap.id)) = 1 := by
  obtain ⟨hi1, hi2⟩ := hi_bounds_P1123
  exact finrank_root_P1123 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    ((root_iff_P1123 hi_P1123 (by linarith) (by linarith) (by linarith)).mpr (Or.inr (Or.inr rfl)))

/-- **THE ONE THE CHAIN'S DIMENSION COUNT CANNOT REACH, BY SUBTRACTION.** `5 = N − 2` and the
singleton parts make `2 · 1 = 2` exactly half-sized, which is the hypothesis that fails. -/
theorem finrank_five_P1123 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1123)) - (5 : ℝ) • LinearMap.id)) = 2 := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_P1123
  have hsum := sum_finrank_eq_of_subset herm_P1123
    (le_of_eq image_eigenvalues_P1123 : Finset.univ.image herm_P1123.eigenvalues ⊆ _)
  have n5 : (5 : ℝ) ∉ ({4, lo_P1123, hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact d1 h
    · exact d2 h
    · exact d3 h
  have n4 : (4 : ℝ) ∉ ({lo_P1123, hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact d4 h
    · exact d5 h
  have nlo : lo_P1123 ∉ ({hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_singleton]; exact d6
  rw [Finset.sum_insert n5, Finset.sum_insert n4, Finset.sum_insert nlo,
    Finset.sum_singleton, finrank_four_P1123, finrank_lo_P1123, finrank_hi_P1123,
    show Fintype.card (Σ i, P1123 i) = 7 from total_P1123] at hsum
  omega

/-! ## 4. And the characteristic polynomial -/

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL ON `K_{1,1,2,3}`.** -/
theorem charpoly_signlessLap_P1123 :
    (signlessLap (completeMultipartiteGraph P1123)).charpoly
      = (X - C (5 : ℝ)) ^ 2 * (X - C (4 : ℝ)) ^ 3
        * (X - C lo_P1123) * (X - C hi_P1123) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := distinct_P1123
  have n5 : (5 : ℝ) ∉ ({4, lo_P1123, hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact d1 h
    · exact d2 h
    · exact d3 h
  have n4 : (4 : ℝ) ∉ ({lo_P1123, hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact d4 h
    · exact d5 h
  have nlo : lo_P1123 ∉ ({hi_P1123} : Finset ℝ) := by
    simp only [Finset.mem_singleton]; exact d6
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank herm_P1123, image_eigenvalues_P1123,
    Finset.prod_insert n5, Finset.prod_insert n4, Finset.prod_insert nlo,
    Finset.prod_singleton, finrank_five_P1123, finrank_four_P1123, finrank_lo_P1123,
    finrank_hi_P1123]
  ring

end HermitianDimensionSum
