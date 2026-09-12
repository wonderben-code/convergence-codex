import FieldEigenMultiplicity
import FieldSimpleConverse

/-!
# Every Hermitian matrix's multiplicities are its eigenvalue fibres

**THE PREVIOUS UNIT SAID IT NEEDED THIS AND DID NOT HAVE IT.**
`UnbalancedMultipartiteTable` computed a complete multiplicity table for a family of graphs and
wrote, in its own *what is NOT here*: *reading `so there is no room for a fourth eigenvalue` off
this table needs the eigenspaces at distinct eigenvalues to be independent — available in this
estate **pairwise** … and **not assembled here** into a spanning argument*. **This file supplies
that step, for every Hermitian real matrix and not only for that family**, and it does it without
any orthogonality at all.

**THE ROUTE IS THIS ESTATE'S OWN, GENERALISED.** `FieldEigenMultiplicity` proved the same statement
for the **propagator** by matrix algebra on a diagonalisation: `green = P D Pᵀ`, so
`green − μ·1 = P (D − μ·1) Pᵀ`; multiplying by matrices of unit determinant does not change rank;
the rank of a diagonal matrix is its number of non-zero entries; and rank–nullity turns that into
the kernel's dimension. **The four steps never used the graph.** Replacing that file's graph-built
`P` with Mathlib's `Matrix.IsHermitian.eigenvectorUnitary` and `spectral_theorem` gives the same
proof for an arbitrary Hermitian `A`, and the rank–nullity step is reused **verbatim** from that
file (`finrank_ker_toLin'`, which is already stated for an arbitrary square matrix).

**AND THE PROPAGATOR'S CASE IS NOW A SPECIAL CASE — DECLARED, NOT RE-DERIVED.**
`FieldBlockDiagonal.eigMu G m hm` is *literally* `(green_isHermitian G m hm).eigenvalues`, so
`FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre` **is** the theorem below at
`A := green G m`. It is not restated here, and no duplicate is written: this file **imports** that
one for the rank–nullity lemma, so the dependency runs the wrong way for a replacement. **The
restructuring — moving the general statement upstream and re-deriving the propagator's case from it
— is named here and not done.** The general theorem carries a different name for the same reason
(`newnames_scan`).

## What is proved

**`conj_eq`, `mul_star_eigU`, `star_mul_eigU`, `isUnit_det_eigU`, `isUnit_det_star_eigU`** — a
Hermitian real matrix as `A = U D U*` with `U` unitary, and both determinants units.

**`sub_smul_eq_conj`, `rank_sub_smul`** — `A − μ·1 = U (D − μ·1) U*`, so its rank is the number of
eigenvalues **away** from `μ`.

**`finrank_eigenspace_hermitian_eq_card_fibre`** — **THE MULTIPLICITY OF AN EIGENVALUE IS THE SIZE
OF ITS FIBRE**, for every Hermitian real matrix and every real `μ`: the eigenspace
`ker (toLin' A − μ·id)` has dimension exactly the number of indices where
`Matrix.IsHermitian.eigenvalues` takes the value `μ`.

**`sum_finrank_le`** — so the dimensions over **any** finite set of values add to at most the
dimension of the space. The proof is a fibrewise count (`Finset.card_eq_sum_card_fiberwise`): the
fibres over distinct values are disjoint subsets of the index type. **No orthogonality and no
independence lemma appears**, which is the point — the geometry the previous unit was reaching for
is replaced by disjointness of index sets.

**`mem_of_isEigenvalue_of_sum_eq`** — **AND A TABLE THAT ADDS TO THE DIMENSION LEAVES NO ROOM FOR
ANOTHER EIGENVALUE.** If the dimensions over a finite set `s` sum to `Fintype.card V`, then every
`μ` with a non-zero eigenvector lies in `s`. This is the missing step, in the general form.

**`finrank_eigenspace_lapMatrix_eq_card_fibre`, `mem_of_isEigenvalue_lapMatrix`** — the graph
Laplacian's case, which is the one the estate wanted and had for no Laplacian anywhere:
`UnbalancedMultipartiteTable`'s own fence says the transfer *is done for the propagator … and for no
Laplacian anywhere*. Both are one line from the general theorem.

## What is NOT here

* **NO APPLICATION TO ANY FAMILY.** The multipartite table is the motivating case and is **not**
  instantiated here: turning `finrank_eigenspaces_add` into a second proof of that family's
  exhaustion means building the `Finset` of its eigenvalues and reindexing the sum, which is a
  unit's work and is not this unit's. Named, not attempted (`ERRATUM 246`).
* **NOTHING OVER `ℂ`.** Mathlib's spectral theorem is stated for `RCLike`, so the same proof runs
  over `ℂ` with `star` in place of transpose; every statement here is real because that is what the
  estate's matrices are. Not generalised, and nothing is lost that anything here wants.
* **NO ORTHOGONALITY, NO EIGENBASIS STATEMENT.** `SymmetricEigenOrthogonal`'s pairwise fact is
  **not used** and no independent family of subspaces is constructed. A reader wanting *the
  eigenspaces span* will not find it here; what is here is the counting consequence of that fact,
  proved another way.
* **NO CHARACTERISTIC POLYNOMIAL.** Knowing every multiplicity fixes the eigenvalue **multiset**,
  and `Matrix.charpoly`'s factorisation over `ℝ` is a further step — the one
  `UnbalancedMultipartiteTable` named — which this file does not take.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, and
`Matrix.IsHermitian A`. **No mass, no graph, no positivity and no non-degeneracy anywhere** — the
two Laplacian statements take a graph only because they name one, and the propagator's case takes
`m ≠ 0` only inside the estate's own `green_isHermitian`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianFibreCount

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Any Hermitian real matrix, diagonalised as a product -/

theorem conj_eq {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix V V ℝ) * diagonal hA.eigenvalues
          * star (hA.eigenvectorUnitary : Matrix V V ℝ) := by
  have h := hA.spectral_theorem
  simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using h

theorem mul_star_eigU {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix V V ℝ) * star (hA.eigenvectorUnitary : Matrix V V ℝ) = 1 := by
  simp

theorem star_mul_eigU {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix V V ℝ) * (hA.eigenvectorUnitary : Matrix V V ℝ) = 1 :=
  Unitary.coe_star_mul_self hA.eigenvectorUnitary

theorem isUnit_det_eigU {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    IsUnit ((hA.eigenvectorUnitary : Matrix V V ℝ)).det :=
  IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, mul_star_eigU hA, Matrix.det_one])

theorem isUnit_det_star_eigU {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    IsUnit ((star (hA.eigenvectorUnitary : Matrix V V ℝ))).det :=
  IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, star_mul_eigU hA, Matrix.det_one])

/-! ## 2. The shifted matrix, its rank, and the eigenspace's dimension -/

theorem sub_smul_eq_conj {A : Matrix V V ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    A - μ • (1 : Matrix V V ℝ)
      = (hA.eigenvectorUnitary : Matrix V V ℝ) * diagonal (fun i => hA.eigenvalues i - μ)
          * star (hA.eigenvectorUnitary : Matrix V V ℝ) := by
  have hd : (diagonal fun i => hA.eigenvalues i - μ)
      = diagonal hA.eigenvalues - μ • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne h, h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, ← conj_eq hA]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_star_eigU hA]

theorem rank_sub_smul {A : Matrix V V ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    (A - μ • (1 : Matrix V V ℝ)).rank = Fintype.card {i : V // hA.eigenvalues i ≠ μ} := by
  classical
  rw [sub_smul_eq_conj hA μ,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_star_eigU hA),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_eigU hA),
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp [sub_eq_zero])

/-- **THE MULTIPLICITY OF AN EIGENVALUE IS THE SIZE OF ITS FIBRE, FOR EVERY HERMITIAN REAL
MATRIX.** -/
theorem finrank_eigenspace_hermitian_eq_card_fibre {A : Matrix V V ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Fintype.card {i : V // hA.eigenvalues i = μ} := by
  classical
  have hlin : (Matrix.toLin' A - μ • LinearMap.id)
      = Matrix.toLin' (A - μ • (1 : Matrix V V ℝ)) := by
    rw [map_sub]
    congr 1
    ext x i
    simp
  rw [hlin, FieldEigenMultiplicity.finrank_ker_toLin', rank_sub_smul hA μ]
  have hcompl : Fintype.card {i : V // hA.eigenvalues i ≠ μ}
      = Fintype.card V - Fintype.card {i : V // hA.eigenvalues i = μ} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i : V // hA.eigenvalues i = μ} ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  omega

/-! ## 3. So the dimensions over any finite set of values fit inside the space -/

theorem sum_finrank_le {A : Matrix V V ℝ} (hA : A.IsHermitian) (s : Finset ℝ) :
    ∑ μ ∈ s, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      ≤ Fintype.card V := by
  classical
  have hterm : ∀ μ ∈ s, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = (Finset.univ.filter fun i => hA.eigenvalues i = μ).card := by
    intro μ _
    rw [finrank_eigenspace_hermitian_eq_card_fibre hA μ, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm]
  have hfib := Finset.card_eq_sum_card_fiberwise
      (f := hA.eigenvalues) (s := Finset.univ.filter fun i => hA.eigenvalues i ∈ s) (t := s)
      (fun i hi => (Finset.mem_filter.mp hi).2)
  have hinner : ∀ μ ∈ s,
      ((Finset.univ.filter fun i => hA.eigenvalues i ∈ s).filter
          fun i => hA.eigenvalues i = μ).card
        = (Finset.univ.filter fun i => hA.eigenvalues i = μ).card := by
    intro μ hμ
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hμ, h⟩⟩
  rw [Finset.sum_congr rfl hinner] at hfib
  rw [← hfib]
  exact le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)

/-- **AND SO A TABLE THAT ADDS TO THE DIMENSION LEAVES NO ROOM FOR ANOTHER EIGENVALUE.** -/
theorem mem_of_isEigenvalue_of_sum_eq {A : Matrix V V ℝ} (hA : A.IsHermitian) (s : Finset ℝ)
    (hsum : ∑ μ ∈ s, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Fintype.card V)
    {μ : ℝ} {x : V → ℝ} (hx0 : x ≠ 0) (hx : A *ᵥ x = μ • x) : μ ∈ s := by
  classical
  by_contra hμ
  have hmem : x ∈ LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id) :=
    (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr hx
  have hnt : Nontrivial (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) :=
    ⟨⟨⟨x, hmem⟩, 0, by simpa using hx0⟩⟩
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) :=
    Module.finrank_pos_iff.mpr hnt
  have hle := sum_finrank_le hA (insert μ s)
  rw [Finset.sum_insert hμ, hsum] at hle
  omega

/-! ## 4. The graph Laplacian's multiplicities, which is the case the estate wanted -/

theorem finrank_eigenspace_lapMatrix_eq_card_fibre (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
      = Fintype.card {i : V //
          (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues i = μ} :=
  finrank_eigenspace_hermitian_eq_card_fibre _ μ

theorem mem_of_isEigenvalue_lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset ℝ)
    (hsum : ∑ μ ∈ s, Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
      = Fintype.card V)
    {μ : ℝ} {x : V → ℝ} (hx0 : x ≠ 0) (hx : G.lapMatrix ℝ *ᵥ x = μ • x) : μ ∈ s :=
  mem_of_isEigenvalue_of_sum_eq (FieldSimpleConverse.lapMatrix_isHermitian G) s hsum hx0 hx

end HermitianFibreCount
