import PawSimpleSpectrum
import SignlessSpectrumTrichotomy

/-!
# The paw's signless spectrum: a graph the conjugation route cannot reach

**THE SIGNLESS FRONTIER ITEM'S CLAUSE (b) HAS ONE RESIDUE AND THIS IS A GRAPH IN IT.** After
`ERRATUM 506` corrected it, the clause asks for a **non-bipartite graph that is neither a cycle nor
complete**; the multipartite chain of entries 155–174 added *nor complete multipartite*. The paw —
a triangle with a pendant vertex — is all three of those and none of the exceptions.

**AND IT WAS ALREADY BUILT.** `PawSimpleSpectrum` was written for a different item entirely — *a
graph other than the line whose propagator has a simple spectrum* — and it carries `pawGraph`, its
degrees, its **Laplacian** as an explicit `4 × 4` matrix, four eigenvectors, a basis and every
eigenspace measured. It contains **no occurrence of `signlessLap`**. This unit is that file's
construction pointed one matrix over, which is the same shape as entries 28, 31 and 33.

## What is proved

**`signlessLap_pawGraph`** — `Q = D + A` on the paw, entry by entry, mirroring that file's
`lapMatrix_pawGraph`.

**`pawQ_mulVec`, `pawQEig_injective`, `pawQVec_linearIndependent`, `pawQBasis`** — four
eigenvectors with eigenvalues `1`, `2`, `(5 ± √17)/2`, pairwise distinct, and a basis. The two
irrational modes are `(λ + 1, λ − 1, λ − 1, λ − 3)` at a root of `λ² − 5λ + 2`, which is what the
symmetry swapping the triangle's two far corners leaves after the antisymmetric mode is removed.
Independence is `Module.End.eigenvectors_linearIndependent'` **because the eigenvalues are
distinct**, not a determinant.

**`finrank_eigenspace_pawQ`, `isEigenvalue_signless_paw`** — so every eigenspace is the fibre of
`pawQEig`, and a real `μ` is an eigenvalue of `Q` **exactly when** it is one of those four numbers.
A complete spectral description, of the kind this estate has for the complete graph, `K₄` minus an
edge and the three-vertex path.

**`nodup_roots_charpoly_signlessLap_paw`** — **the signless spectrum is simple.** Counted rather
than asserted (`ERRATUM 507`): this is the **second** graph on the satisfying side of
`SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff` — the first is the single edge,
`MultipartiteSignlessSingleton.nodup_roots_charpoly_signlessLap_edge` — and **the first that is not
two-colourable**.

**`posDef_signlessLap_paw`, `charpoly_signlessLap_paw`** — `Q` is positive definite here, read off
the spectrum rather than off a colouring, and the characteristic polynomial is four distinct linear
factors.

**`charpoly_signlessLap_ne_lapMatrix_paw`, `not_colorable_two_paw`** — **and the two spectra
differ**, which is the clause's actual point: `0` is an eigenvalue of `L` and not of `Q`, so
`SignlessBipartite`'s conjugation `Q = S L S` **cannot** have produced this spectrum. Turned round,
that proves the paw is not two-colourable **from its spectra**, with no colouring argument.

## What is NOT here

* **THE CLAUSE IS NARROWED, NOT CLOSED, AND ONE GRAPH IS ONE GRAPH.** The wheel, and a general
  odd-cycle graph, are untouched, and **nothing here generalises off four vertices**: every proof
  is a `fin_cases` or a `decide`. What the clause asks for is a graph, and it now has one more; what
  a reader would want next is a family. Not attempted (`ERRATUM 246`).
* **THE COMPARISON WITH `L` IS AT ONE EIGENVALUE.**
  `charpoly_signlessLap_ne_lapMatrix_paw` separates
  the two polynomials at `0` and says nothing about the other three; the eigenvectors of the two
  matrices are not compared at all, and the paw's Laplacian spectrum is `PawSimpleSpectrum`'s and
  is not restated here.
* **NO MULTIPLICITY QUESTION SURVIVES**, which is worth saying because it usually does: all four
  eigenvalues are simple, so there is nothing left to count on this graph.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): **none.** Every statement is about one
explicit four-vertex graph, and every side condition — the degrees, the adjacency, the four
`mulVec` identities, the distinctness of the eigenvalues — is discharged here by `decide`,
`fin_cases`, `norm_num` and two bounds on `√17`, rather than assumed. **No mass, no propagator, and
no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace PawSignlessSpectrum

open Matrix SimpleGraph LaplacianSignless PawSimpleSpectrum Polynomial

/-! ## 1. The matrix -/

def pawQ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3, 1, 1, 1; 1, 2, 1, 0; 1, 1, 2, 0; 1, 0, 0, 1]

theorem signlessLap_pawGraph : signlessLap pawGraph = pawQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signlessLap, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, pawQ,
      pawGraph_adj, pawAdj, pawGraph_degree]

/-! ## 2. `√17` -/

theorem sq_sqrt17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem four_lt_sqrt17 : (4 : ℝ) < Real.sqrt 17 := by
  nlinarith [sq_sqrt17, Real.sqrt_nonneg 17]

theorem sqrt17_lt_five : Real.sqrt 17 < 5 := by
  nlinarith [sq_sqrt17, Real.sqrt_nonneg 17]

/-! ## 3. Four eigenvectors -/

noncomputable def pawQEig : Fin 4 → ℝ :=
  ![1, 2, (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2]

noncomputable def pawQVec : Fin 4 → (Fin 4 → ℝ) :=
  ![![0, 1, -1, 0], ![1, -1, -1, 1],
    ![(7 + Real.sqrt 17) / 2, (3 + Real.sqrt 17) / 2, (3 + Real.sqrt 17) / 2,
      (-1 + Real.sqrt 17) / 2],
    ![(7 - Real.sqrt 17) / 2, (3 - Real.sqrt 17) / 2, (3 - Real.sqrt 17) / 2,
      (-1 - Real.sqrt 17) / 2]]

theorem pawQ_mulVec (k : Fin 4) : pawQ *ᵥ pawQVec k = pawQEig k • pawQVec k := by
  have h := sq_sqrt17
  fin_cases k <;> ext v <;> fin_cases v <;>
    simp [pawQ, pawQVec, pawQEig, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> nlinarith [h]

theorem pawQEig_injective : Function.Injective pawQEig := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [pawQEig] at h ⊢ <;> linarith

theorem pawQVec_ne_zero (k : Fin 4) : pawQVec k ≠ 0 := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  fin_cases k
  · intro h; have := congrFun h 1; simp [pawQVec] at this
  · intro h; have := congrFun h 0; simp [pawQVec] at this
  · intro h; have := congrFun h 0; simp [pawQVec] at this; linarith
  · intro h; have := congrFun h 0; simp [pawQVec] at this; linarith

theorem hasEigenvector_pawQ (k : Fin 4) :
    Module.End.HasEigenvector (Matrix.mulVecLin pawQ) (pawQEig k) (pawQVec k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact pawQ_mulVec k
  · exact pawQVec_ne_zero k

theorem pawQVec_linearIndependent : LinearIndependent ℝ pawQVec :=
  Module.End.eigenvectors_linearIndependent' _ _ pawQEig_injective _ hasEigenvector_pawQ

noncomputable def pawQBasis : Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank pawQVec_linearIndependent (by simp)

theorem pawQBasis_apply (k : Fin 4) : pawQBasis k = pawQVec k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

theorem finrank_eigenspace_pawQ (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph) - μ • LinearMap.id))
      = Nat.card {k : Fin 4 // pawQEig k = μ} :=
  EigenBasisDimension.finrank_ker_sub_smul pawQBasis
    (fun k => by rw [pawQBasis_apply, signlessLap_pawGraph]; exact pawQ_mulVec k) μ

theorem finrank_signless_le_one_paw (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph) - ν • LinearMap.id))
      ≤ 1 := by
  rw [finrank_eigenspace_pawQ, Finite.card_le_one_iff_subsingleton]
  exact ⟨fun a b => Subtype.ext (pawQEig_injective (a.2.trans b.2.symm))⟩

/-! ## 4. So the spectrum is exactly those four numbers, and it is simple -/

theorem isEigenvalue_signless_paw (μ : ℝ) :
    (∃ x : Fin 4 → ℝ, x ≠ 0 ∧ signlessLap pawGraph *ᵥ x = μ • x)
      ↔ μ = 1 ∨ μ = 2 ∨ μ = (5 + Real.sqrt 17) / 2 ∨ μ = (5 - Real.sqrt 17) / 2 := by
  rw [UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos,
    finrank_eigenspace_pawQ, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, -⟩
    fin_cases k <;> simp only [pawQEig] at hk <;> simp [← hk]
  · intro h
    refine ⟨?_, Subtype.finite⟩
    rcases h with h | h | h | h
    · exact ⟨⟨0, by simp [pawQEig, h]⟩⟩
    · exact ⟨⟨1, by simp [pawQEig, h]⟩⟩
    · exact ⟨⟨2, by simp [pawQEig, h]⟩⟩
    · exact ⟨⟨3, by simp [pawQEig, h]⟩⟩

/-- **THE PAW'S SIGNLESS SPECTRUM IS SIMPLE.** -/
theorem nodup_roots_charpoly_signlessLap_paw :
    (signlessLap pawGraph).charpoly.roots.Nodup :=
  (SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff pawGraph).mpr
    finrank_signless_le_one_paw

/-- **AND `Q` IS POSITIVE DEFINITE HERE**, computed from the spectrum rather than from a colouring:
none of the four numbers is `0`. -/
theorem posDef_signlessLap_paw : (signlessLap pawGraph).PosDef := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  rw [← LaplacianSignlessKernel.finrank_ker_eq_zero_iff_posDef]
  have h : Matrix.toLin' (signlessLap pawGraph)
      = Matrix.toLin' (signlessLap pawGraph) - (0 : ℝ) • LinearMap.id := by simp
  rw [h, finrank_eigenspace_pawQ, Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨k, hk⟩ => ?_⟩
  fin_cases k <;> simp only [pawQEig] at hk <;> norm_num at hk <;> linarith

/-! ## 5. Each eigenvalue simple, and the characteristic polynomial -/

theorem finrank_eigenspace_pawQ_eq_one (k : Fin 4) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - pawQEig k • LinearMap.id)) = 1 := by
  rw [finrank_eigenspace_pawQ, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (pawQEig_injective (a.2.trans b.2.symm))⟩, ⟨⟨k, rfl⟩⟩⟩

theorem finrank_signless_paw_one :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - (1 : ℝ) • LinearMap.id)) = 1 := by
  simpa [pawQEig] using finrank_eigenspace_pawQ_eq_one 0

theorem finrank_signless_paw_two :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - (2 : ℝ) • LinearMap.id)) = 1 := by
  simpa [pawQEig] using finrank_eigenspace_pawQ_eq_one 1

theorem finrank_signless_paw_add :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - ((5 + Real.sqrt 17) / 2) • LinearMap.id)) = 1 := by
  simpa [pawQEig] using finrank_eigenspace_pawQ_eq_one 2

theorem finrank_signless_paw_sub :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - ((5 - Real.sqrt 17) / 2) • LinearMap.id)) = 1 := by
  simpa [pawQEig] using finrank_eigenspace_pawQ_eq_one 3

theorem image_eigenvalues_signless_paw :
    Finset.univ.image (LaplacianSignlessDefinite.signlessLap_isHermitian pawGraph).eigenvalues
      = {1, 2, (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2} := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff, isEigenvalue_signless_paw]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL ON THE PAW**, four distinct linear factors. -/
theorem charpoly_signlessLap_paw :
    (signlessLap pawGraph).charpoly
      = (X - C (1 : ℝ)) * (X - C (2 : ℝ)) * (X - C ((5 + Real.sqrt 17) / 2))
        * (X - C ((5 - Real.sqrt 17) / 2)) := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  have hA := LaplacianSignlessDefinite.signlessLap_isHermitian pawGraph
  have hne1 : (1 : ℝ) ∉ ({2, (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h) <;> linarith
  have hne2 : (2 : ℝ) ∉ ({(5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h) <;> linarith
  have hne3 : (5 + Real.sqrt 17) / 2 ∉ ({(5 - Real.sqrt 17) / 2} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    intro h; linarith
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank hA, image_eigenvalues_signless_paw,
    Finset.prod_insert hne1, Finset.prod_insert hne2, Finset.prod_insert hne3,
    Finset.prod_singleton, finrank_signless_paw_one, finrank_signless_paw_two,
    finrank_signless_paw_add, finrank_signless_paw_sub]
  ring

/-! ## 6. The two spectra differ, so the conjugation route could not have reached this graph -/

theorem finrank_signless_paw_zero :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap pawGraph)
      - (0 : ℝ) • LinearMap.id)) = 0 := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  rw [finrank_eigenspace_pawQ, Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨k, hk⟩ => ?_⟩
  fin_cases k <;> simp only [pawQEig] at hk <;> norm_num at hk <;> linarith

/-- **`Q` AND `L` HAVE DIFFERENT CHARACTERISTIC POLYNOMIALS ON THE PAW**: `0` is an eigenvalue of
`L` — the constant vector — and of `Q` it is not. -/
theorem charpoly_signlessLap_ne_lapMatrix_paw :
    (signlessLap pawGraph).charpoly ≠ (pawGraph.lapMatrix ℝ).charpoly := by
  intro h
  have h1 := HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap pawGraph 0
  have h2 := HermitianRootMultiplicity.rootMultiplicity_charpoly_lapMatrix pawGraph 0
  rw [h, h2, finrank_signless_paw_zero, PawSimpleSpectrum.finrank_eigenspace_paw] at h1
  have : Nat.card {k : Fin 4 // PawSimpleSpectrum.pawEig k = 0} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (PawSimpleSpectrum.pawEig_injective (a.2.trans b.2.symm))⟩,
      ⟨⟨0, rfl⟩⟩⟩
  omega

/-- **SO THE PAW IS NOT TWO-COLOURABLE, PROVED FROM ITS SPECTRA.**
`SignlessBipartite.charpoly_signlessLap_eq_of_colorable` says a two-colouring makes the two
polynomials equal; they are not. -/
theorem not_colorable_two_paw : ¬ pawGraph.Colorable 2 := fun hcol =>
  charpoly_signlessLap_ne_lapMatrix_paw
    (SignlessBipartite.charpoly_signlessLap_eq_of_colorable pawGraph hcol)

end PawSignlessSpectrum
