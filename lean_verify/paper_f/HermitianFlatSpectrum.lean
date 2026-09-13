import HermitianMaxMultiplicity
import SignlessSimpleFamilies
import SignlessP1122Charpoly

/-!
# The pigeonhole is attained exactly when the spectrum is flat

**THE QUESTION `HermitianMaxMultiplicity`'s `§6` POSED AND ITS FENCE DECLINED.** That file proved
that some eigenvalue's multiplicity is at least the vertex count over the number of **distinct**
eigenvalues, and fenced itself: *nothing says the bound is attained, and at the one graph checked
it is not. A graph attaining it would have all multiplicities equal, which is a real condition
nobody here has looked at.* **The parenthetical is a theorem and this file proves it**, in both
directions and for every real symmetric matrix.

**`forall_finrank_eq_iff`** — the bound is attained at the largest multiplicity `M` **iff every**
eigenvalue has multiplicity `M`. The easy direction is that `k` equal terms sum to `k · M`; the
other is that `k` terms each at most `M` summing to `k · M` leaves no room, and is a contradiction
against `Finset.sum_lt_sum`.

**SO ATTAINMENT IS FLATNESS, AND THE SIMPLEST FLAT SPECTRUM IS A SIMPLE ONE.** A matrix all of
whose eigenspaces are lines has `M = 1` and `card V` distinct eigenvalues, so it attains the bound
trivially — and the estate has an **infinite family** of those on the signless side:
`SignlessSimpleFamilies.finrank_signless_le_one_line`, the path at every length. **The bound is
attained at every path**, which is the answer to the fence, and it is attained for the least
interesting reason.

**AND THE INTERESTING CASE IS EMPTY SO FAR.** A flat spectrum with `M ≥ 2` — every eigenvalue
equally degenerate, more than once — is attainment that is not simplicity, and **no graph in this
estate is known to have one.** That is written below as what is open rather than left for a reader
to assume the family is bigger than it is.

## What is proved

**`finrank_pos_of_mem_image`** — an eigenvalue's multiplicity is positive. One line from
`HermitianFibreCount`, and the estate did not have it as a statement.

**`forall_finrank_eq_iff`** — **THE FILE'S THEOREM**: `card V = k · M` iff every multiplicity is
`M`, where `k` is the number of distinct eigenvalues.

**`forall_finrank_eq_one_of_le_one`**, **`card_image_eq_card_of_le_one`** — a matrix whose
eigenspaces are all at most lines has all of them exactly lines, and then exactly `card V`
distinct eigenvalues.

**`attained_line`** — **the witness, at every length**: on the path `boxGraph 1 (k+1)` the signless
bound is attained.

**`not_attained_P1122`** — and the graph the previous file checked does **not** attain it: its
multiplicities are `3, 1, 1, 1`.

## What is NOT here

* **NO FLAT SPECTRUM WITH `M ≥ 2`, as of 2026-09-13 (entry 13).** Every witness here is simple,
  so every witness attains the bound with `M = 1`. **As of 2026-09-13 (entry 13) whether any graph
  has all its multiplicities equal to some `M ≥ 2` is open**, is not attempted, and is the only
  part of the fence that stays shut (`ERRATUM 246`).
* **NOTHING ABOUT WHICH GRAPHS ARE SIMPLE, as of 2026-09-13 (entry 13).** That is a separate open
  item on `UNLOCK_WATCHLIST` and this file cites the estate's answer for the path rather than
  adding to it.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite index type with decidable
equality, `IsHermitian`, and — for `forall_finrank_eq_iff` only — that `M` bounds every
multiplicity. **No non-emptiness**: an empty index type makes both sides of the biconditional
vacuously true.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianFlatSpectrum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. An eigenvalue has a positive multiplicity -/

theorem finrank_pos_of_mem_image {A : Matrix V V ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (hμ : μ ∈ Finset.univ.image hA.eigenvalues) :
    0 < Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hμ
  rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA μ]
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-! ## 2. Attainment is flatness -/

/-- **THE PIGEONHOLE IS ATTAINED EXACTLY WHEN EVERY MULTIPLICITY IS THE SAME.** -/
theorem forall_finrank_eq_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) {M : ℕ}
    (hle : ∀ μ ∈ Finset.univ.image hA.eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) ≤ M) :
    Fintype.card V = (Finset.univ.image hA.eigenvalues).card * M
      ↔ ∀ μ ∈ Finset.univ.image hA.eigenvalues,
          Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) = M := by
  classical
  have hsum := HermitianDimensionSum.sum_finrank_image hA
  constructor
  · intro hcard μ hμ
    by_contra hne
    have hlt : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) < M :=
      lt_of_le_of_ne (hle μ hμ) hne
    have := Finset.sum_lt_sum (f := fun ν => Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' A - ν • LinearMap.id))) (g := fun _ => M) hle ⟨μ, hμ, hlt⟩
    rw [hsum, Finset.sum_const, smul_eq_mul] at this
    omega
  · intro hall
    rw [← hsum, Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul]

/-! ## 3. A simple spectrum attains it, for the least interesting reason -/

/-- Eigenspaces at most lines are exactly lines. -/
theorem forall_finrank_eq_one_of_le_one {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (h1 : ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' A - μ • LinearMap.id)) ≤ 1) (μ : ℝ)
    (hμ : μ ∈ Finset.univ.image hA.eigenvalues) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) = 1 :=
  le_antisymm (h1 μ) (finrank_pos_of_mem_image hA hμ)

/-- **SO SUCH A MATRIX HAS EXACTLY `card V` DISTINCT EIGENVALUES**, and the bound is attained. -/
theorem card_image_eq_card_of_le_one {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (h1 : ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' A - μ • LinearMap.id)) ≤ 1) :
    Fintype.card V = (Finset.univ.image hA.eigenvalues).card * 1 :=
  (forall_finrank_eq_iff hA (fun μ _ => h1 μ)).2
    (fun μ hμ => forall_finrank_eq_one_of_le_one hA h1 μ hμ)

/-! ## 4. The witness, at every length, and a graph that misses -/

/-- The signless Laplacian of a path is symmetric. -/
theorem herm_line (k : ℕ) :
    (LaplacianSignless.signlessLap (BoxGraph.boxGraph 1 (k + 1))).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian _

/-- **THE BOUND IS ATTAINED AT EVERY PATH.** -/
theorem attained_line (k : ℕ) :
    Fintype.card (BoxGraph.Site 1 (k + 1))
      = (Finset.univ.image (herm_line k).eigenvalues).card * 1 :=
  card_image_eq_card_of_le_one (herm_line k)
    (SignlessSimpleFamilies.finrank_signless_le_one_line k)

/-- **AND `K_{1,1,2,2}` DOES NOT ATTAIN IT**: its multiplicity at `4` is `3` and its multiplicity
at `2` is `1`, so the spectrum is not flat. -/
theorem not_attained_P1122 :
    ¬ ∀ μ ∈ Finset.univ.image SignlessP1122Charpoly.herm_P1122.eigenvalues,
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (LaplacianSignless.signlessLap (SimpleGraph.completeMultipartiteGraph
            SignlessDoublingFails.P1122)) - μ • LinearMap.id)) = 3 := by
  intro h
  have hmem : (2 : ℝ) ∈ Finset.univ.image SignlessP1122Charpoly.herm_P1122.eigenvalues := by
    rw [SignlessP1122Charpoly.image_eigenvalues_P1122]; simp
  have := h 2 hmem
  rw [SignlessP1122Charpoly.finrank_two_P1122] at this
  omega

end HermitianFlatSpectrum
