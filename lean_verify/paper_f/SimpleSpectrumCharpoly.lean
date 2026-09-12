import HermitianRootMultiplicity

/-!
# The simple-spectrum criterion, moved off the spectrum and onto a polynomial

**`RE-SWEEP #52`'s result (i), and the objection it answers is the item's own.** The standing
`UNLOCK_WATCHLIST` item *which finite graphs have a simple Laplacian spectrum* records, in its
`STATUS` of 10 September, that the criterion the estate holds — every eigenspace of the Laplacian
at most a line — *is stated ON the spectrum, so it decides nothing about a graph presented
combinatorially*. The previous unit's `HermitianRootMultiplicity.rootMultiplicity_charpoly` changes
the vocabulary, and this file spends the change: **the condition is that the characteristic
polynomial has no repeated root**, and a characteristic polynomial is determined by the adjacency
matrix.

## What is proved

**`nodup_roots_charpoly_iff`** — for every real Hermitian matrix, the root multiset of
`Matrix.charpoly A` is `Multiset.Nodup` **iff** every eigenspace is at most a line.
**`card_roots_charpoly_hermitian`, `card_distinct_roots_iff`** — equivalently, **as many distinct
roots as rows**, the root multiset having the size it must.

**`nodup_roots_charpoly_lapMatrix_iff`, `nodup_roots_charpoly_signlessLap_iff`** — both graph
matrices, on any finite simple graph, the Laplacian's stated through
`FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective` as the injectivity of the eigenvalue
enumeration.

**`finite_symmetryMatrices_iff_nodup`, `finite_symmetryMatrices_iff_card`** — **the Gaussian
field's symmetry group is finite if and only if the Laplacian's characteristic polynomial has no
repeated root**, at every finite graph and every non-zero mass; and equivalently iff that
polynomial has `|V|` distinct roots. That is the dividing line `FieldSymmetryFinite` established,
restated in a vocabulary that does not mention an eigenvalue.

**`nodup_roots_charpoly_multi_iff`** — and the complete multipartite family's classification
restated in it: no repeated root **iff** two parts, both of size at most two, one of size one.

## What is NOT here

* **THIS IS A REFORMULATION AND NOT WHAT THE ITEM ASKS FOR.** That item wants a **family** on the
  satisfying side or a **third necessary condition**, and gets neither: the gap between the
  necessary conditions (connected, every automorphism an involution) and the failure conditions (a
  non-involutive automorphism, twin classes) is exactly where it was, and `FieldTwinSpectrum`'s
  witness still sits in it. What changes is the vocabulary of the criterion, which is what the
  item's `STATUS` line objected to — a smaller thing than the item, and it is recorded as smaller.
* **NO DISCRIMINANT, AND SO NO SINGLE INEQUATION IN THE ENTRIES.** The natural next step is to say
  *the discriminant of the characteristic polynomial is non-zero*, which would be one polynomial
  condition on the adjacency matrix. **Nothing here does that, and the reason is that there is
  nothing to do it with**: `grep` finds no polynomial discriminant in Mathlib and the word occurs
  in five `paper_f` files only as a quadratic form's, in prose. Building one is not attempted
  (`ERRATUM 246`), and naming it is not a claim that it is short (`ERRATUM 194`).
* **NO `Squarefree` STATEMENT.** Mathlib's `Squarefree` predicate, applied to the polynomial, is
  the classical phrasing and is not derived here; the polynomial does split, so the bridge exists,
  but it is not written.
* **NO INSTANCE ON THE SIGNLESS SIDE.** `nodup_roots_charpoly_signlessLap_iff` is a criterion with
  no graph put through it: the field-symmetry consequence is the *ordinary* Laplacian's
  (`FieldSymmetryFinite` has no signless analogue), and this chain's two computed signless spectra
  are not run through it here.

⚠ **A FAMILY IS PUT THROUGH IT THE NEXT UNIT (2026-09-12, entry 162), AND THE PARAGRAPH IS KEPT AS
WRITTEN** (`ERRATUM 94`). `MultipartiteSignlessCharpoly.not_nodup_roots_charpoly_signlessLap_multi`
uses this criterion to show the equipartite family's signless spectrum is **not** simple, for
`r ≥ 2` and `t ≥ 2`. **The rest of the clause stands**: that is a negative instance, there is still
no graph on the satisfying side, and `FieldSymmetryFinite` still has no signless analogue, so the
signless criterion still carries no consequence about a symmetry group.
* **NOTHING OVER `ℂ`**, and no wall moves and no published tag moves. `W1`'s open part is still
  `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `Fintype` and `DecidableEq` on the vertex
type throughout; `Matrix.IsHermitian A` for the general statements and nothing else;
`DecidableRel G.Adj` for the graph ones; a non-zero mass on the two field-symmetry statements, which
is what `FieldSymmetryFinite` takes; `∀ i, Nonempty (W i)` and `2 ≤ card ι` on the multipartite one,
which is what the classification takes. **No propagator and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SimpleSpectrumCharpoly

open Matrix Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. No repeated root is the same as no eigenspace above a line -/

theorem nodup_roots_charpoly_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    A.charpoly.roots.Nodup
      ↔ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) ≤ 1 := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  exact forall_congr' fun μ => by
    rw [Polynomial.count_roots, HermitianRootMultiplicity.rootMultiplicity_charpoly hA]

theorem card_roots_charpoly_hermitian {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    Multiset.card A.charpoly.roots = Fintype.card V := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.card_map]
  rfl

/-- **AND SO: THE SPECTRUM IS SIMPLE IFF THE POLYNOMIAL HAS AS MANY DISTINCT ROOTS AS THERE ARE
ROWS.** -/
theorem card_distinct_roots_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    A.charpoly.roots.toFinset.card = Fintype.card V
      ↔ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) ≤ 1 := by
  classical
  rw [← card_roots_charpoly_hermitian hA, Multiset.toFinset_card_eq_card_iff_nodup,
    nodup_roots_charpoly_iff hA]

/-! ## 2. The graph Laplacian, and the criterion in adjacency vocabulary -/

theorem nodup_roots_charpoly_lapMatrix_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).charpoly.roots.Nodup
      ↔ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := by
  rw [nodup_roots_charpoly_iff (FieldSimpleConverse.lapMatrix_isHermitian G),
    FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective]

/-- **THE GAUSSIAN FIELD'S SYMMETRY GROUP IS FINITE IFF THE LAPLACIAN'S CHARACTERISTIC POLYNOMIAL
HAS NO REPEATED ROOT** — the criterion, moved off the spectrum and onto a polynomial the adjacency
matrix determines. -/
theorem finite_symmetryMatrices_iff_nodup {G : SimpleGraph V} [DecidableRel G.Adj] {μ : ℝ}
    (hμ : μ ≠ 0) :
    (FieldRotationCount.symmetryMatrices G μ).Finite
      ↔ (G.lapMatrix ℝ).charpoly.roots.Nodup := by
  rw [FieldSymmetryFinite.finite_iff_lapMatrix hμ,
    nodup_roots_charpoly_iff (FieldSimpleConverse.lapMatrix_isHermitian G)]

/-- The same with the count of distinct roots in front. -/
theorem finite_symmetryMatrices_iff_card {G : SimpleGraph V} [DecidableRel G.Adj] {μ : ℝ}
    (hμ : μ ≠ 0) :
    (FieldRotationCount.symmetryMatrices G μ).Finite
      ↔ (G.lapMatrix ℝ).charpoly.roots.toFinset.card = Fintype.card V := by
  rw [FieldSymmetryFinite.finite_iff_lapMatrix hμ,
    card_distinct_roots_iff (FieldSimpleConverse.lapMatrix_isHermitian G)]

/-- The signless Laplacian's version, free from the general theorem. -/
theorem nodup_roots_charpoly_signlessLap_iff (G : SimpleGraph V) [DecidableRel G.Adj] :
    (LaplacianSignless.signlessLap G).charpoly.roots.Nodup
      ↔ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (LaplacianSignless.signlessLap G) - μ • LinearMap.id)) ≤ 1 :=
  nodup_roots_charpoly_iff (LaplacianSignlessDefinite.signlessLap_isHermitian G)

/-! ## 3. The complete multipartite family, in the new vocabulary -/

theorem nodup_roots_charpoly_multi_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Type*} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    (hne : ∀ i, Nonempty (W i)) (hι : 2 ≤ Fintype.card ι) :
    ((SimpleGraph.completeMultipartiteGraph W).lapMatrix ℝ).charpoly.roots.Nodup
      ↔ Fintype.card ι = 2 ∧ (∀ i : ι, Fintype.card (W i) ≤ 2)
          ∧ ∃ i : ι, Fintype.card (W i) = 1 := by
  rw [nodup_roots_charpoly_lapMatrix_iff,
    MultipartiteSimpleSpectrum.injective_eigenvalues_iff hne hι]

end SimpleSpectrumCharpoly
