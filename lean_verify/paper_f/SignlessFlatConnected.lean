import SignlessFlatWitness
import SignlessConjugateMultiplicity
import FieldSimpleConnected

/-!
# On a connected two-colourable graph, flat means simple

**THE SHARPER QUESTION `SignlessFlatWitness` LEFT OPEN, ANSWERED FOR HALF OF IT.** That file
exhibited a graph whose signless multiplicities are all `2` — two disjoint edges — and said its
**disconnectedness is doing real work**, leaving open *whether a connected graph can have a flat
signless spectrum with `M ≥ 2`.* **For a connected two-colourable graph it cannot**, and the proof
is one value.

**WHY `μ = 0` SETTLES IT.** On a two-colourable graph `Q` and `L` have the same multiplicity at
every real, which is the same day's `SignlessConjugateMultiplicity`. On a **connected** graph `L`'s
kernel is a **line** — `FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected`, the standard
fact that the kernel counts components. So `Q`'s multiplicity at `0` is `1`; a flat spectrum makes
every multiplicity equal to that one; hence `M = 1` and the spectrum is **simple**. The witness on
four vertices escapes exactly because it has two components, so its kernel is a plane.

## What is proved

**`mem_image_of_finrank_pos`** — a positive multiplicity means the value is an eigenvalue, which
is the converse of `HermitianFlatSpectrum.finrank_pos_of_mem_image` and was missing because that
file needed only one direction.

**`finrank_zero_signlessLap_connected`** — on a connected two-colourable graph `Q`'s kernel is a
line, which is the transfer composed with the component count and is stated here because nothing
had composed them.

**`flat_implies_simple_of_connected`** — **THE FILE'S THEOREM**: if such a graph's multiplicities
are all `M`, then `M = 1`.

**`forall_finrank_le_one_of_flat_connected`** — so every eigenspace is a line: the spectrum is
simple, in the estate's own vocabulary.

## What is NOT here

* **NOTHING FOR A CONNECTED GRAPH THAT IS NOT TWO-COLOURABLE, as of 2026-09-13 (entry 15), AND
  THE BLOCKER IS NOW LOCATED EXACTLY.** There `Q` is positive definite, `0` is not an eigenvalue,
  and this proof has nothing to work with. The classical answer is **Perron–Frobenius**: `Q` is
  entrywise non-negative and irreducible for a connected graph, so its largest eigenvalue is
  simple and flatness again forces `M = 1`. **That theorem is in neither library.** Mathlib has
  `Matrix.IsIrreducible` and `isIrreducible_iff_exists_pow_pos` and **no simplicity statement of
  any kind**; this estate's `PerronSimple.top_eigenspace_dim_one` proves simplicity but requires
  **every entry strictly positive**, which `Q` is not.
* **THE ROUTE IS NAMED AND NOT COSTED** (`ERRATUM 194`, `ERRATUM 246`). A connected graph on two
  or more vertices has every degree at least one, so `Q` has a strictly positive diagonal, and a
  non-negative irreducible matrix with positive diagonal is **primitive**: some power is entrywise
  positive, `PerronSimple` applies to that power, and the top eigenspace of `Q` sits inside the
  top eigenspace of the power. **Every step of that is a build and none of it is attempted here.**
* **NO CONVERSE.** Nothing says a connected simple spectrum exists at every size, and nothing here
  bears on which connected graphs are simple.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency, `G.Connected`, and `G.Colorable 2`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessFlatConnected

open Matrix SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. A positive multiplicity means the value is an eigenvalue -/

/-- The converse of `HermitianFlatSpectrum.finrank_pos_of_mem_image`, which that file proved one
way round because that was the direction it needed. -/
theorem mem_image_of_finrank_pos {A : Matrix V V ℝ} (hA : A.IsHermitian) {μ : ℝ}
    (hpos : 0 < Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))) :
    μ ∈ Finset.univ.image hA.eigenvalues := by
  classical
  rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA μ] at hpos
  obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

/-! ## 2. A connected two-colourable graph has a one-dimensional signless kernel -/

theorem finrank_zero_signlessLap_connected (hconn : G.Connected) (hcol : G.Colorable 2) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - (0 : ℝ) • LinearMap.id))
      = 1 := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable hcol 0]
  exact FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected hconn

/-! ## 3. So a flat spectrum there is a simple one -/

/-- **FLAT MEANS SIMPLE ON A CONNECTED TWO-COLOURABLE GRAPH.** -/
theorem flat_implies_simple_of_connected (hconn : G.Connected) (hcol : G.Colorable 2) {M : ℕ}
    (hflat : ∀ μ ∈ Finset.univ.image
        (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) = M) :
    M = 1 := by
  classical
  have hzero := finrank_zero_signlessLap_connected G hconn hcol
  have hmem : (0 : ℝ) ∈ Finset.univ.image
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues :=
    mem_image_of_finrank_pos _ (by rw [hzero]; norm_num)
  have := hflat 0 hmem
  omega

/-- **SO EVERY EIGENSPACE IS A LINE**, which is the estate's own way of saying simple. -/
theorem forall_finrank_le_one_of_flat_connected (hconn : G.Connected) (hcol : G.Colorable 2)
    {M : ℕ} (hflat : ∀ μ ∈ Finset.univ.image
        (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) = M)
    (μ : ℝ) (hμ : μ ∈ Finset.univ.image
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) = 1 := by
  rw [hflat μ hμ, flat_implies_simple_of_connected G hconn hcol hflat]

end SignlessFlatConnected
