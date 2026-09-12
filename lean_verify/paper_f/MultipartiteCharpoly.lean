import HermitianCharpoly
import UnbalancedMultipartiteTable

/-!
# The complete multipartite graph's characteristic polynomial, written out

**THE PREVIOUS UNIT NAMED THIS AS THE NEXT UNIT'S WORK AND THIS IS IT.**
`HermitianCharpoly` factorised every Hermitian real matrix's characteristic polynomial by
multiplicity, over the image of Mathlib's eigenvalue enumeration, and fenced the rest: *writing
`X(X − N)^{r−1}∏(X − (N − n))^{k(n−1)}` for the complete multipartite family means identifying that
`Finset` with an explicit one … a unit's work of reindexing.* **Here it is:**

`charpoly = X · (X − N)^{r−1} · ∏ₙ (X − (N − n))^{kₙ(n−1)}`

with the product over the **distinct part sizes `n ≥ 2`** and `kₙ` the number of parts of that size,
for an arbitrary complete multipartite graph with non-empty parts and at least two of them.

**WHAT THE UNIT ACTUALLY DOES, SINCE THE MATHEMATICS WAS ALREADY PROVED.** Four earlier units
supply the content: the eigenvalue set (`UnbalancedMultipartite`), the multiplicity at each
`N − n` (`UnbalancedMultipartiteFibre`), the multiplicities at `0` and `N`
(`UnbalancedMultipartiteTable`), and the factorisation itself (`HermitianCharpoly`). What was left
was **bookkeeping, and it is the bookkeeping that was fenced**: the spectrum has to become a
`Finset`, the three families have to be split off it, and the product over the eigenvalues
`N − nᵢ` has to be reindexed as a product over the part **sizes**, which is where equal-sized parts
collapse into one factor with a bigger exponent.

## What is proved

**`specSet`, `mem_specSet_iff`** — the spectrum as a `Finset ℝ`: `0`, the vertex count, and
`N − nᵢ` for each part with at least two vertices.

**`image_eigenvalues_eq_specSet`** — **that `Finset` IS the image of Mathlib's enumeration**, by
`HermitianCharpoly.mem_image_eigenvalues_lapMatrix_iff` against
`UnbalancedMultipartite.isEigenvalue_lapMatrix_unbal_iff`. The two side conditions in that `iff` —
a vertex exists, and two parts are non-empty — are discharged from the hypotheses here, which is
exactly what they are for.

**`charpoly_eq_prod_specSet`** — so the polynomial is the product over `specSet`, with eigenspace
dimensions as exponents.

**`sizeSet_ne_zero`, `sizeSet_ne_card`, `charpoly_lapMatrix_multi`** — **THE POLYNOMIAL, WRITTEN
OUT.** The three factors are split off with `Finset.prod_insert` (`0` and `N` are outside the rest
because no part size is `0` or `N`), the exponents come from the three multiplicity theorems, and
`Finset.image_image` with `Finset.prod_image` reindexes the last product over sizes — the injection
being `n ↦ N − n` on `ℝ`.

**`charpoly_path_example`** — a numerical check: parts of sizes `1` and `2` give
`X(X − 3)(X − 1)`, the characteristic polynomial of the path on three vertices. The two `Finset`
computations behind it are `decide`.

## What is NOT here

* **NO SIGNLESS LAPLACIAN.** `UnbalancedMultipartite.not_isEigenvector_one_signlessLap` is still
  the reason: the constant vector is a `Q`-eigenvector for no scalar once two parts differ in size,
  so `Q`'s spectrum on this family is not in hand and its polynomial cannot be written.
* **NOTHING AT AN EMPTY PART OR AT ONE PART.** Both hypotheses come from the multiplicity table and
  are not decoration there: an empty part is counted by `r` and contributes no vertex, and one part
  is an edgeless graph whose `0` is not simple.
* **NO ROOT-MULTIPLICITY STATEMENT.** The exponents here are eigenspace dimensions. That they agree
  with `Polynomial.rootMultiplicity` is true and **not proved** — the previous unit fences it too.
* **NO CLAIM THAT THIS FAMILY'S POLYNOMIAL IS NEW TO THE LITERATURE.** It is classical; what is
  new is that it is **proved here from the estate's own spectrum**, with no spectral theorem used
  beyond Mathlib's diagonalisation of a Hermitian matrix.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)` and `2 ≤ Fintype.card ι` — the same two the table takes, and for
the same reasons. `specSet` is `noncomputable` because `Finset ℝ` needs `Real.decidableEq`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteCharpoly

open Matrix Finset SimpleGraph Polynomial
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open HermitianCharpoly

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The eigenvalue set, as a `Finset` -/

/-- The eigenvalues of the complete multipartite graph's Laplacian: `0`, the vertex count, and
`N - nᵢ` for each part of at least two vertices. -/
noncomputable def specSet (V : ι → Type*) [∀ i, Fintype (V i)] [DecidableEq ι] : Finset ℝ :=
  insert 0 (insert (Fintype.card (Σ i, V i) : ℝ)
    ((Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
      fun i => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)))

omit [∀ i, DecidableEq (V i)] in
theorem mem_specSet_iff (μ : ℝ) :
    μ ∈ specSet V
      ↔ μ = 0 ∨ μ = (Fintype.card (Σ i, V i) : ℝ)
          ∨ ∃ i : ι, 1 < Fintype.card (V i)
              ∧ μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i) := by
  simp only [specSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | h | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
  · rintro (h | h | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

theorem image_eigenvalues_eq_specSet (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    Finset.univ.image
        (FieldSimpleConverse.lapMatrix_isHermitian (completeMultipartiteGraph V)).eigenvalues
      = specSet V := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  have hV : Nonempty (Σ i, V i) := ⟨⟨i₀, (hne i₀).some⟩⟩
  obtain ⟨j₀, hj₀⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i₀
  refine Finset.ext fun μ => ?_
  rw [mem_image_eigenvalues_lapMatrix_iff, isEigenvalue_lapMatrix_unbal_iff, mem_specSet_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl ⟨h, hV⟩
    · exact Or.inr (Or.inl ⟨h, j₀, i₀, hj₀, hne j₀, hne i₀⟩)
    · exact Or.inr (Or.inr h)

/-! ## 2. The characteristic polynomial over that set -/

theorem charpoly_eq_prod_specSet (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    ((completeMultipartiteGraph V).lapMatrix ℝ).charpoly
      = ∏ μ ∈ specSet V, (X - C μ) ^ Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ) - μ • LinearMap.id)) := by
  rw [charpoly_lapMatrix_eq_prod_pow_finrank, image_eigenvalues_eq_specSet hne hι]

/-! ## 3. Splitting it into the three families -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sizeSet_ne_zero {n : ℕ}
    (hn : n ∈ (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
      fun i => Fintype.card (V i)) : n ≠ 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  have := (Finset.mem_filter.mp hi).2
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sizeSet_ne_card (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) {n : ℕ}
    (hn : n ∈ (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
      fun i => Fintype.card (V i)) : n ≠ Fintype.card (Σ i, V i) := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
  exact card_part_ne_card hne hι i

theorem charpoly_lapMatrix_multi (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    ((completeMultipartiteGraph V).lapMatrix ℝ).charpoly
      = X * (X - C (Fintype.card (Σ i, V i) : ℝ)) ^ (Fintype.card ι - 1)
          * ∏ n ∈ (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
                (fun i => Fintype.card (V i)),
              (X - C ((Fintype.card (Σ i, V i) : ℝ) - n))
                ^ (Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1)) := by
  classical
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  have hV : Nonempty (Σ i, V i) := ⟨⟨i₀, (hne i₀).some⟩⟩
  have hNpos : 0 < Fintype.card (Σ i, V i) := Fintype.card_pos_iff.mpr hV
  have hmemS : ∀ μ ∈ (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
      (fun i => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)),
      ∃ i : ι, 1 < Fintype.card (V i)
        ∧ μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i) := by
    intro μ hμ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hμ
    exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩
  have hNnotS : (Fintype.card (Σ i, V i) : ℝ) ∉
      (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
        (fun i => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) := by
    intro h
    obtain ⟨i, -, hi⟩ := hmemS _ h
    have hz : (Fintype.card (V i) : ℝ) = 0 := by linarith
    exact card_part_ne_zero hne i (by exact_mod_cast hz)
  have h0notS : (0 : ℝ) ∉
      (Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
        (fun i => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) := by
    intro h
    obtain ⟨i, -, hi⟩ := hmemS _ h
    have hz : (Fintype.card (V i) : ℝ) = (Fintype.card (Σ i, V i) : ℝ) := by linarith
    exact card_part_ne_card hne hι i (by exact_mod_cast hz)
  have h0neN : (0 : ℝ) ≠ (Fintype.card (Σ i, V i) : ℝ) := by
    intro h
    have : Fintype.card (Σ i, V i) = 0 := by exact_mod_cast h.symm
    omega
  rw [charpoly_eq_prod_specSet hne hι, specSet,
    Finset.prod_insert (by
      intro h
      rcases Finset.mem_insert.mp h with h1 | h1
      · exact h0neN h1
      · exact h0notS h1),
    Finset.prod_insert hNnotS, finrank_eigenspace_zero hne hι,
    finrank_eigenspace_top hne ⟨i₀⟩]
  simp only [map_zero, sub_zero, pow_one]
  rw [mul_assoc]
  congr 1
  congr 1
  rw [show ((Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
        (fun i => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)))
      = ((Finset.univ.filter fun i : ι => 1 < Fintype.card (V i)).image
        (fun i => Fintype.card (V i))).image
        (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - n) from by
      simp only [Finset.image_image, Function.comp_def]]
  rw [Finset.prod_image]
  · refine Finset.prod_congr rfl fun n hn => ?_
    rw [finrank_eigenspace_size (sizeSet_ne_zero hn) (sizeSet_ne_card hne hι hn)]
  · intro a _ b _ hab
    have : (a : ℝ) = (b : ℝ) := by linarith [hab]
    exact_mod_cast this

/-! ## 4. A numerical check: the path on three vertices -/

/-- Parts of sizes `1` and `2`, three vertices: the polynomial comes out `X(X − 3)(X − 1)`, the
characteristic polynomial of the path on three vertices. -/
theorem charpoly_path_example :
    ((completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))).lapMatrix ℝ).charpoly
      = X * (X - C (3 : ℝ)) * (X - C (1 : ℝ)) := by
  classical
  have himg : (Finset.univ.filter fun i : Fin 2 => 1 < Fintype.card (Fin (i.1 + 1))).image
      (fun i => Fintype.card (Fin (i.1 + 1))) = {2} := by decide
  have hk : Fintype.card {i : Fin 2 // Fintype.card (Fin (i.1 + 1)) = 2} = 1 := by decide
  have h := charpoly_lapMatrix_multi (V := fun i : Fin 2 => Fin (i.1 + 1))
    (fun i => ⟨0⟩) (by simp)
  rw [card_path_example, himg] at h
  rw [h, Finset.prod_singleton, hk]
  norm_num

end MultipartiteCharpoly
