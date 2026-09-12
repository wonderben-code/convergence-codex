import HermitianFibreCount

/-!
# The characteristic polynomial, factorised by multiplicity

**SIX FILES IN THIS CHAIN FENCED THIS, AND FIVE OF THEM GAVE THE WRONG REASON.**
`CompleteSpectrumTwoPoints`, `MultipartiteSpectrum`, `MultipartiteMultiplicity`,
`UnbalancedMultipartite` and `UnbalancedMultipartiteFibre` all say the characteristic polynomial is
not written because *that step needs diagonalisability, which this argument avoids* — and it does
not matter what those arguments avoid, because **Mathlib supplies the diagonalisation**:
`Matrix.IsHermitian.charpoly_eq` writes `Matrix.charpoly A` as a product over the index type for
every Hermitian matrix, and this estate has been citing it since 2026-08-26. `ERRATUM 508` records
the count and the five sentences are annotated where they stand. **The sixth**,
`UnbalancedMultipartiteTable`, names the real obstacle — *the transfer from these eigenspace
dimensions to the multiset `Matrix.IsHermitian.eigenvalues` enumerates* — and the previous unit
closed it.

**SO THE MISSING STEP WAS THE GROUPING, AND IT IS ONE LEMMA.** Mathlib's product runs over the
index type, one factor per index; the polynomial a reader wants runs over **distinct** eigenvalues
with the multiplicities as exponents. `Finset.prod_comp` — the multiplicative twin of the
`Finset.sum_comp` the multiplicity table used — collects the factors into fibres, and the previous
unit's `finrank_eigenspace_hermitian_eq_card_fibre` turns each fibre's size into the dimension of
an eigenspace.

## What is proved

**`mem_image_eigenvalues_iff`** — **THE IMAGE OF MATHLIB'S ENUMERATION IS THE SET OF EIGENVALUES**,
both directions: `μ` occurs in the enumeration **iff** some non-zero vector satisfies `Ax = μx`.
Forward by the eigenvector basis, whose vectors are non-zero because they are unit vectors;
backward because a non-trivial eigenspace has positive dimension, hence a non-empty fibre. Without
this the factorisation below would be a product over an enumeration artefact rather than over the
spectrum.

**`charpoly_eq_prod_pow_finrank`** — **THE CHARACTERISTIC POLYNOMIAL OF EVERY HERMITIAN REAL
MATRIX, FACTORISED**: `Matrix.charpoly A = ∏_{μ} (X − C μ) ^ dim (ker (toLin' A − μ·id))`, over
the eigenvalues.

**`sum_finrank_image_eigenvalues`** — and over the **whole** spectrum the dimensions sum to
**exactly** `Fintype.card V`. This is not the previous unit's `sum_finrank_le`, which bounds the sum
over an **arbitrary** finite set of reals and is the statement that closes an exhaustion argument;
this one is an equality and needs the set to be the spectrum. Together they say: a finite set's
dimensions sum to `card V` exactly when the set contains every eigenvalue.

**`mem_image_eigenvalues_lapMatrix_iff`, `charpoly_lapMatrix_eq_prod_pow_finrank`** — the graph
Laplacian's case, one line each.

## What is NOT here

* **NO EXPLICIT POLYNOMIAL FOR ANY NAMED GRAPH.** The factorisation is over the spectrum as a
  `Finset`, and writing `(X)(X − N)^{r−1}∏(X − (N − n))^{k(n−1)}` for the complete multipartite
  family means identifying that `Finset` with an explicit one — which
  `UnbalancedMultipartite.isEigenvalue_lapMatrix_unbal_iff` and the table between them supply, and
  which is a unit's work of reindexing. **Named, not attempted** (`ERRATUM 246`), and it is the
  obvious next unit.
* **NOTHING OVER `ℂ`.** Mathlib's ingredients are `RCLike`, so the same proof runs; every statement
  here is real because the estate's matrices are.
* **NO DEGREE, MONICITY OR ROOT-MULTIPLICITY STATEMENT.** `Matrix.charpoly_monic` and
  `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` are Mathlib's and are not restated; the
  exponents here are eigenspace dimensions, and their agreement with `Polynomial.rootMultiplicity`
  is not proved.

⚠ **THE AGREEMENT IS PROVED AS OF 2026-09-12 (entry 159)** (`ERRATUM 94`):
`HermitianRootMultiplicity.rootMultiplicity_charpoly`, for every real Hermitian matrix. **The rest
of the clause still stands** — degree and monicity are still Mathlib's and still not restated, and
so is the root multiset this paragraph names. **`ERRATUM 510` is about that name**: the unit that
closed the clause re-proved `roots_charpoly_eq_eigenvalues` before grepping for it, and the
re-proof was deleted. A fence that names its own inputs is a parts list; this one was read as a
single absence.
* **NO CLAIM OF A FIRST.** `ERRATUM 507`'s lesson: `HermitianSpectralMapping.charpoly_pow_eq`
  already writes a Hermitian matrix's power's characteristic polynomial as a product over the index
  type, and `Matrix.IsHermitian.charpoly_eq` is the `k = 1` case of that. **What is new here is the
  grouping by distinct eigenvalue**, which is a different shape and is what the six fences wanted.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, and
`Matrix.IsHermitian` of the matrix. No mass, no graph, no positivity; the Laplacian statements name
a graph and take nothing else.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianCharpoly

open Matrix Polynomial HermitianFibreCount

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The image of Mathlib's enumeration is the set of eigenvalues -/

theorem mem_image_eigenvalues_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    μ ∈ Finset.univ.image hA.eigenvalues ↔ ∃ x : V → ℝ, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  classical
  constructor
  · intro hμ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
    refine ⟨fun v => hA.eigenvectorBasis i v, ?_, ?_⟩
    · intro h
      have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
      have : (hA.eigenvectorBasis i : EuclideanSpace ℝ V) = 0 := by
        ext v
        exact congrFun h v
      rw [this, norm_zero] at hnorm
      exact zero_ne_one hnorm
    · exact hA.mulVec_eigenvectorBasis i
  · rintro ⟨x, hx0, hx⟩
    have hmem : x ∈ LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id) :=
      (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr hx
    have hnt : Nontrivial (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) :=
      ⟨⟨⟨x, hmem⟩, 0, by simpa using hx0⟩⟩
    have hpos : 0 < Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) :=
      Module.finrank_pos_iff.mpr hnt
    rw [finrank_eigenspace_hermitian_eq_card_fibre hA μ] at hpos
    obtain ⟨i, hi⟩ := Fintype.card_pos_iff.mp hpos
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-! ## 2. So the characteristic polynomial factors with the multiplicities as exponents -/

theorem charpoly_eq_prod_pow_finrank {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    A.charpoly = ∏ μ ∈ Finset.univ.image hA.eigenvalues,
      (X - C μ) ^ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  classical
  have hcp : A.charpoly = ∏ i, (X - C (hA.eigenvalues i)) := by
    simpa using hA.charpoly_eq
  rw [hcp, Finset.prod_comp (fun μ : ℝ => X - C μ) hA.eigenvalues]
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [finrank_eigenspace_hermitian_eq_card_fibre hA μ, Fintype.card_subtype]

/-! ## 3. The graph Laplacian's characteristic polynomial -/

theorem mem_image_eigenvalues_lapMatrix_iff (G : SimpleGraph V) [DecidableRel G.Adj] (μ : ℝ) :
    μ ∈ Finset.univ.image (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues
      ↔ ∃ x : V → ℝ, x ≠ 0 ∧ G.lapMatrix ℝ *ᵥ x = μ • x :=
  mem_image_eigenvalues_iff _ μ

theorem charpoly_lapMatrix_eq_prod_pow_finrank (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).charpoly
      = ∏ μ ∈ Finset.univ.image (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues,
          (X - C μ) ^ Module.finrank ℝ
            (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) :=
  charpoly_eq_prod_pow_finrank _

/-- **AND THE DEGREE IS THE VERTEX COUNT**, so the exponents in the factorisation above are a
partition of `|V|` — the same arithmetic a multiplicity table asserts, read off the polynomial. -/
theorem sum_finrank_image_eigenvalues {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    ∑ μ ∈ Finset.univ.image hA.eigenvalues,
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Fintype.card V := by
  classical
  have hterm : ∀ μ ∈ Finset.univ.image hA.eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
        = (Finset.univ.filter fun i => hA.eigenvalues i = μ).card := by
    intro μ _
    rw [finrank_eigenspace_hermitian_eq_card_fibre hA μ, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm, ← Finset.card_eq_sum_card_fiberwise
    (f := hA.eigenvalues) (s := Finset.univ) (t := Finset.univ.image hA.eigenvalues)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  exact Finset.card_univ

end HermitianCharpoly
