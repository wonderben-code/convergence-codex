import HermitianDimensionSum
import SignlessRootOverlap

/-!
# Few distinct eigenvalues forces a big eigenspace

**A PIGEONHOLE THE ESTATE HAD BOTH HALVES OF AND HAD NEVER PUT TOGETHER.** This morning's
`HermitianDimensionSum.sum_finrank_image` says a real symmetric matrix's eigenspace dimensions,
summed over its **distinct** eigenvalues, come to the number of vertices. This whole fortnight's
signless chain has been counting those distinct eigenvalues and bounding them — `s ≤ #spec ≤ 3s`
on a complete multipartite graph with `s` distinct part sizes. **A fixed total shared among a
bounded number of parts means one part is large**, and nothing anywhere in this estate says so.

**`exists_finrank_card_le`** — on a non-empty vertex set, some eigenvalue `μ` satisfies
`card V ≤ (number of distinct eigenvalues) * finrank (ker (A − μ))`. In words: **the largest
multiplicity is at least the number of vertices divided by the number of distinct eigenvalues.**
Every degeneracy statement this chain has proved so far has been about a *named* eigenvalue of a
*named* graph; this one is about every finite graph at once and names no eigenvalue.

**WHY IT IS NOT A COROLLARY OF ANYTHING HERE ALREADY.** The estate's degeneracy results run the
other way — from a symmetry, an orbit or a fibre to a lower bound on one multiplicity
(`TorusEigenspaceLowerBound`, `BoxLapMultiplicity`, `MultipartiteSignless*`). **This needs no
symmetry at all.** It is the counting dual: a bound on the number of distinct values is
automatically a bound on how flat the spectrum can be.

## What is proved

**`image_eigenvalues_nonempty`** — a non-empty vertex set has at least one eigenvalue.

**`exists_finrank_card_le`** — the pigeonhole, for any real symmetric matrix.

**`exists_finrank_card_le_of_card_image_le`** — the form a consumer wants: if the number of
distinct eigenvalues is at most `k`, some multiplicity is at least `card V / k`, stated as
`card V ≤ k * finrank`.

**`card_image_eigenvalues_P1123`**, **`exists_finrank_two_le_P1123`** — the check, at the
seven-vertex graph `K_{1,1,2,3}` whose
signless spectrum this chain computed in full: four distinct eigenvalues and seven vertices, so
some multiplicity is at least `⌈7/4⌉ = 2`. **It is `3`**, so the bound is true and not tight there,
and saying which it is costs nothing because the table is known.

## What is NOT here

* **NO SHARPNESS.** Nothing says the bound is attained, and at the one graph checked it is not. A
  graph attaining it would have all multiplicities equal, which is a real condition nobody here
  has looked at.
* **NO CONSUMER IN THE SIGNLESS CHAIN YET.** `SignlessSpectrumComplete`'s `#spec ≤ 3s` bound is
  stated for a `Finset` of eigenvalues built by that file, **not** for
  `Finset.univ.image hA.eigenvalues`, and identifying the two is a step nobody has taken. The
  header above says what the composition *would* give; **it is not made here**, and the general
  theorem is stated so that it can be made later without restating anything.
* **NOTHING ABOUT THE SMALLEST MULTIPLICITY**, which the same sum bounds from the other side and
  which is not stated because nothing has asked.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite non-empty index type with
decidable equality, and `A.IsHermitian`. **No graph, no positivity, no connectivity.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianMaxMultiplicity

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A non-empty matrix has an eigenvalue -/

theorem image_eigenvalues_nonempty [Nonempty V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    (Finset.univ.image hA.eigenvalues).Nonempty :=
  ⟨hA.eigenvalues (Classical.arbitrary V),
    Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/-! ## 2. The pigeonhole -/

/-- **THE LARGEST MULTIPLICITY IS AT LEAST THE VERTEX COUNT OVER THE NUMBER OF DISTINCT
EIGENVALUES.** -/
theorem exists_finrank_card_le [Nonempty V] {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    ∃ μ : ℝ, Fintype.card V
      ≤ (Finset.univ.image hA.eigenvalues).card
        * Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  classical
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image (Finset.univ.image hA.eigenvalues)
    (fun ν => Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)))
    (image_eigenvalues_nonempty hA)
  refine ⟨μ, ?_⟩
  calc Fintype.card V
      = ∑ ν ∈ Finset.univ.image hA.eigenvalues,
          Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)) :=
        (HermitianDimensionSum.sum_finrank_image hA).symm
    _ ≤ ∑ _ν ∈ Finset.univ.image hA.eigenvalues,
          Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) :=
        Finset.sum_le_sum fun ν hν => hmax ν hν
    _ = (Finset.univ.image hA.eigenvalues).card
          * Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- The form a consumer wants: a bound on the number of distinct eigenvalues is a bound on how
flat the spectrum can be. -/
theorem exists_finrank_card_le_of_card_image_le [Nonempty V] {A : Matrix V V ℝ}
    (hA : A.IsHermitian) {k : ℕ} (hk : (Finset.univ.image hA.eigenvalues).card ≤ k) :
    ∃ μ : ℝ, Fintype.card V
      ≤ k * Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  obtain ⟨μ, hμ⟩ := exists_finrank_card_le hA
  exact ⟨μ, hμ.trans (Nat.mul_le_mul_right _ hk)⟩

/-! ## 3. The check, at a graph whose table is known -/

/-- `K_{1,1,2,3}` has four distinct signless eigenvalues. -/
theorem card_image_eigenvalues_P1123 :
    (Finset.univ.image HermitianDimensionSum.herm_P1123.eigenvalues).card = 4 := by
  rw [HermitianDimensionSum.image_eigenvalues_P1123]
  obtain ⟨-, h5lo, h5hi, h4lo, h4hi, hlohi⟩ := HermitianDimensionSum.distinct_P1123
  rw [Finset.card_insert_of_notMem (by simp [h5lo, h5hi]),
    Finset.card_insert_of_notMem (by simp [h4lo, h4hi]),
    Finset.card_insert_of_notMem (by simp [hlohi]), Finset.card_singleton]

/-- **THE PIGEONHOLE AT `K_{1,1,2,3}`**: seven vertices and four distinct eigenvalues, so some
multiplicity is at least two. It is three (`HermitianDimensionSum.finrank_four_P1123`), so the
bound holds and is not tight here. -/
theorem exists_finrank_two_le_P1123 :
    ∃ μ : ℝ, 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
      (LaplacianSignless.signlessLap
        (SimpleGraph.completeMultipartiteGraph SignlessRootOverlap.P1123))
          - μ • LinearMap.id)) := by
  have hne : Nonempty (Σ i, SignlessRootOverlap.P1123 i) :=
    ⟨⟨0, (SignlessRootOverlap.nonempty_P1123 0).some⟩⟩
  obtain ⟨μ, hμ⟩ := exists_finrank_card_le_of_card_image_le
    HermitianDimensionSum.herm_P1123 card_image_eigenvalues_P1123.le
  rw [SignlessRootOverlap.total_P1123] at hμ
  exact ⟨μ, by omega⟩

end HermitianMaxMultiplicity
