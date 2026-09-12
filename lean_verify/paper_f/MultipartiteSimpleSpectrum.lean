import MultipartiteCharpoly

/-!
# Which complete multipartite graphs have a simple Laplacian spectrum: exactly two, and both were
already known

**THE SWEEP ASKED FOR THIS AND THIS IS THE ANSWER, INCLUDING THE PART THAT IS A NEGATIVE.**
`UNLOCK_WATCHLIST`'s standing question — *which finite graphs have a SIMPLE Laplacian spectrum* —
says in its own words that what this estate can add is **data points**, and asks for *a family on
the satisfying side*. The complete multipartite family is now completely known, so it can be
**searched**. It is, and the answer is: **exactly `K₂` and `K₁,₂`**, which are the path on two
vertices and the path on three. **Both were already on that item's satisfying list**, so the family
contributes no new example — and a family searched to exhaustion with a negative answer is worth
more than a guess that one might be hiding there.

**HOW THE SEARCH IS POSSIBLE AT ALL.** Because the multiplicities are known exactly: `1` at `0`,
`r − 1` at `N`, and `kₙ(n − 1)` at `N − n`. A simple spectrum is *every multiplicity at most one*
(`FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective`), so it is three arithmetic
conditions: `r − 1 ≤ 1` forces **two parts**; `kₙ(n − 1) ≤ 1` at a part of size `n ≥ 3` is false
because `kₙ ≥ 1`, so **no part has three vertices**; and at two parts of size two `k₂ = 2` gives
multiplicity two, so **the two parts cannot both have two vertices**. That leaves the sizes
`(1,1)` and `(1,2)`.

**THE ONE PIECE THE EARLIER UNITS DID NOT SUPPLY** is that **off** the spectrum the eigenspace is
trivial — otherwise *every multiplicity at most one* would be a condition about infinitely many
reals rather than about three. `finrank_eq_zero_of_not_mem_specSet` gets it from
`HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` and
`MultipartiteCharpoly.image_eigenvalues_eq_specSet`: a non-trivial eigenspace has a non-empty
fibre, and every fibre value is in the spectrum.

## What is proved

**`finrank_eq_zero_of_not_mem_specSet`** — outside the spectrum the eigenspace is `0`-dimensional.

**`injective_eigenvalues_iff`** — **THE CLASSIFICATION**: with non-empty parts and at least two of
them, the Laplacian's eigenvalues are pairwise distinct **iff** there are exactly two parts, both of
size at most two, and at least one of size one.

**`sizes_of_injective_eigenvalues`** — the same conclusion as an explicit list of size profiles:
`(1,1)`, `(1,2)` or `(2,1)`.

## What is NOT here

* **THE IDENTIFICATION WITH THE PATHS IS NOT FORMALISED.** That the two-part graphs with sizes
  `(1,1)` and `(1,2)` are `P₂` and `P₃` is classical and is **not** proved here: this chain has
  never built a graph isomorphism, and `UnbalancedMultipartite` declined the same identification for
  the same reason. What is machine-checked is the classification by **size profile**; that those
  profiles name the paths is the sentence a reader supplies.

⚠ **BOTH ISOMORPHISMS ARE BUILT 2026-09-12 (entry 183), AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`). `GraphIsoSignlessSpectrum.pathIso` and `.edgeIso` identify the `(1,2)` and `(1,1)`
profiles with `pathGraph 3` and `pathGraph 2`, both by `decide`; the sentence a reader supplied is
now a definition. **The estimate above was right that this chain had never built a graph
isomorphism and right that the identification is classical** — it was wrong only in leaving it to
the reader, which cost about twenty lines. **Nothing about this file's classification changes**,
and it still adds no new graph to the satisfying list.
* **NO NEW NECESSARY CONDITION.** The watchlist item asks for a family on the satisfying side **or**
  a third necessary condition excluding a graph the two known ones admit. This unit answers the
  first with a negative and contributes **nothing** to the second: every failure here is already
  explained by the twin conditions the item lists, since a part of two or more vertices is a twin
  class.
* **NOTHING AT AN EMPTY PART OR AT ONE PART**, inherited from the multiplicity table.
* **NO SIGNLESS LAPLACIAN**, for the reason `UnbalancedMultipartite` makes a theorem.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)` and `2 ≤ Fintype.card ι` — the multiplicity table's two, and no
others; the classification takes no mass and mentions no propagator.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteSimpleSpectrum

open Matrix Finset SimpleGraph
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open HermitianFibreCount MultipartiteCharpoly

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. Off the spectrum the eigenspace is trivial -/

theorem finrank_eq_zero_of_not_mem_specSet (hne : ∀ i, Nonempty (V i))
    (hι : 2 ≤ Fintype.card ι) {μ : ℝ} (hμ : μ ∉ specSet V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ) - μ • LinearMap.id)) = 0 := by
  classical
  by_contra h
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ) - μ • LinearMap.id)) := by
    omega
  rw [finrank_eigenspace_hermitian_eq_card_fibre
    (FieldSimpleConverse.lapMatrix_isHermitian (completeMultipartiteGraph V))] at hpos
  obtain ⟨i, hi⟩ := Fintype.card_pos_iff.mp hpos
  exact hμ (by
    rw [← image_eigenvalues_eq_specSet hne hι]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)

/-! ## 2. So the family's simple-spectrum members are classified -/

theorem injective_eigenvalues_iff (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    Function.Injective
        (FieldSimpleConverse.lapMatrix_isHermitian (completeMultipartiteGraph V)).eigenvalues
      ↔ Fintype.card ι = 2 ∧ (∀ i : ι, Fintype.card (V i) ≤ 2)
          ∧ ∃ i : ι, Fintype.card (V i) = 1 := by
  classical
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  rw [← FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective]
  constructor
  · intro h
    have hr : Fintype.card ι = 2 := by
      have h1 := h ((Fintype.card (Σ i, V i) : ℝ))
      rw [finrank_eigenspace_top hne ⟨i₀⟩] at h1
      omega
    have hle : ∀ i : ι, Fintype.card (V i) ≤ 2 := by
      intro i
      by_contra hc
      have h1 := h ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
      rw [finrank_eigenspace_size (card_part_ne_zero hne i) (card_part_ne_card hne hι i)] at h1
      have hk : 1 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
        Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
      have h2 : 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)}
          * (Fintype.card (V i) - 1) := by
        calc 2 = 1 * 2 := by norm_num
          _ ≤ _ := Nat.mul_le_mul hk (by omega)
      omega
    refine ⟨hr, hle, ?_⟩
    by_contra hall
    simp only [not_exists] at hall
    have h2 : ∀ i : ι, Fintype.card (V i) = 2 := by
      intro i
      have hp := Fintype.card_pos_iff.mpr (hne i)
      have := hle i
      have := hall i
      omega
    have hk2 : Fintype.card {j : ι // Fintype.card (V j) = 2} = 2 := by
      have hcong : Fintype.card {j : ι // Fintype.card (V j) = 2} = Fintype.card ι :=
        Fintype.card_congr (Equiv.subtypeUnivEquiv fun j => h2 j)
      omega
    have h1 := h ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i₀))
    rw [finrank_eigenspace_size (card_part_ne_zero hne i₀) (card_part_ne_card hne hι i₀),
      h2 i₀, hk2] at h1
    omega
  · rintro ⟨hr, hle, i₁, h1⟩
    intro ν
    by_cases hν : ν ∈ specSet V
    · rw [mem_specSet_iff] at hν
      rcases hν with rfl | rfl | ⟨i, hi, rfl⟩
      · rw [finrank_eigenspace_zero hne hι]
      · rw [finrank_eigenspace_top hne ⟨i₀⟩]
        omega
      · rw [finrank_eigenspace_size (card_part_ne_zero hne i) (card_part_ne_card hne hι i)]
        have hn2 : Fintype.card (V i) = 2 := le_antisymm (hle i) hi
        rw [hn2]
        have hlt : Fintype.card {j : ι // Fintype.card (V j) = 2} < Fintype.card ι :=
          Fintype.card_subtype_lt (x := i₁) (by rw [h1]; omega)
        omega
    · rw [finrank_eq_zero_of_not_mem_specSet hne hι hν]
      omega

/-! ## 3. And the two survivors, written as size profiles -/

theorem sizes_of_injective_eigenvalues (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι)
    (h : Function.Injective
      (FieldSimpleConverse.lapMatrix_isHermitian (completeMultipartiteGraph V)).eigenvalues)
    {i j : ι} (hij : i ≠ j) :
    (Fintype.card (V i) = 1 ∧ Fintype.card (V j) = 1)
      ∨ (Fintype.card (V i) = 1 ∧ Fintype.card (V j) = 2)
      ∨ (Fintype.card (V i) = 2 ∧ Fintype.card (V j) = 1) := by
  classical
  obtain ⟨hr, hle, i₁, h1⟩ := (injective_eigenvalues_iff hne hι).mp h
  have hpair : ({i, j} : Finset ι) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_pair hij, hr]
  have hmem : i₁ = i ∨ i₁ = j := by
    have : i₁ ∈ ({i, j} : Finset ι) := by rw [hpair]; exact Finset.mem_univ i₁
    simpa using this
  have hpi := Fintype.card_pos_iff.mpr (hne i)
  have hpj := Fintype.card_pos_iff.mpr (hne j)
  have hli := hle i
  have hlj := hle j
  rcases hmem with rfl | rfl
  · rcases Nat.lt_or_ge (Fintype.card (V j)) 2 with hj | hj
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
  · rcases Nat.lt_or_ge (Fintype.card (V i)) 2 with hi | hi
    · exact Or.inl ⟨by omega, h1⟩
    · exact Or.inr (Or.inr ⟨by omega, h1⟩)

end MultipartiteSimpleSpectrum
