import HermitianMaxMultiplicity
import SignlessSpectrumComplete
import SignlessSharpBracket

/-!
# Bounding the number of eigenvalues bounds how flat the spectrum can be

**THE COMPOSITION `HermitianMaxMultiplicity` NAMED AND DID NOT MAKE, AND NAMED CORRECTLY AS A REAL
STEP.** That file proved a pigeonhole — the largest multiplicity is at least the vertex count over
the number of **distinct** eigenvalues — and fenced itself: *its consumer is not built, because
this chain's `#spec ≤ 3s` is stated for a `Finset` `SignlessSpectrumComplete` builds by hand and
not for `Finset.univ.image hA.eigenvalues`, and identifying the two is a step nobody has taken.*

**THE STEP IS ONE LINE AND THE BRIDGE WAS ALREADY THERE.** `IsEigen V μ` is *by definition*
`∃ x ≠ 0, Q *ᵥ x = μ • x`, and `HermitianCharpoly.mem_image_eigenvalues_iff` says exactly that a
real is in a Hermitian matrix's eigenvalue image iff such an `x` exists. So the chain's hand-built
spectrum `Finset` and the matrix's eigenvalue image **have the same members**, hence the same
card, and every count this fortnight proved about the first is a count about the second.

**WHAT THAT BUYS.** Every degeneracy statement in this chain so far has been about a **named**
eigenvalue of a **named** graph — `finrank_four_P1122 = 3` and the like. This gives one about the
whole family and names nothing: **on a complete multipartite graph with `s` distinct part sizes,
some eigenvalue of `Q` has multiplicity at least `N / 3s`.** No part size is fixed, no graph is
exhibited, and the proof computes no eigenvalue.

## What is proved

**`mem_image_eigenvalues_iff_isEigen`** — the identification, for every complete multipartite
graph and every real. This is the step the previous file said was missing.

**`card_image_eigenvalues_le_refined`** — so the refined ceiling
`#bigSizes + #repSizes + #sizes` bounds the number of **distinct eigenvalues of the matrix**, not
merely the size of a `Finset` the chain constructed.

**`exists_finrank_refined`** — and therefore some multiplicity is at least the vertex count over
that ceiling.

**`exists_finrank_three_mul`** — the same with the chain's headline ceiling `3s`, under the
hypotheses `SignlessSharpBracket` takes: **some eigenvalue's multiplicity is at least `N / 3s`.**

## What is NOT here

* **NO SHARPNESS, AND THE INHERITED BOUND IS NOT SHARP EITHER.** `SignlessSharpBracket` shows
  `#spec = 3s` is attained; that makes the *ceiling* sharp and says nothing about whether a graph
  attains this *multiplicity* bound, which would need all multiplicities equal. Not examined.
* **NOTHING AT `s = 0`.** The statements take the hypotheses their sources take, including a
  non-empty index type; the pigeonhole itself needs a non-empty vertex set.
* **NO NAMED EIGENVALUE.** The conclusion is an existence statement inherited from a counting
  argument, and counting names nothing — the same limitation `SignlessSeparationNonzero` records.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): non-empty parts, a non-empty index type,
and — for the `3s` form only — the four conditions `card_spectrum_eq_three_mul` takes.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessMultipartiteDegeneracy

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessSpectrumComplete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- The signless Laplacian of a complete multipartite graph is symmetric. -/
theorem herm_multi : (signlessLap (completeMultipartiteGraph V)).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian _

/-! ## 1. The chain's spectrum is the matrix's eigenvalue image -/

/-- **THE IDENTIFICATION.** `IsEigen` is the `mulVec` statement by definition, and
`HermitianCharpoly.mem_image_eigenvalues_iff` is that statement for the eigenvalue image. -/
theorem mem_image_eigenvalues_iff_isEigen (μ : ℝ) :
    μ ∈ Finset.univ.image (herm_multi (V := V)).eigenvalues ↔ IsEigen V μ :=
  HermitianCharpoly.mem_image_eigenvalues_iff _ μ

/-- So the refined ceiling bounds the number of **distinct eigenvalues of the matrix**. -/
theorem card_image_eigenvalues_le_refined (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) :
    (Finset.univ.image (herm_multi (V := V)).eigenvalues).card
      ≤ (bigSizes V).card + (repSizes V).card
        + (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  obtain ⟨S, hS, hcard⟩ := card_spectrum_le_refined (V := V) hne htwo
  refine le_trans (le_of_eq ?_) hcard
  congr 1
  ext μ
  rw [mem_image_eigenvalues_iff_isEigen, hS]

/-! ## 2. So some multiplicity is large -/

/-- **THE REFINED FORM.** -/
theorem exists_finrank_refined [Nonempty (Σ i, V i)] (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) :
    ∃ μ : ℝ, Fintype.card (Σ i, V i)
      ≤ ((bigSizes V).card + (repSizes V).card
          + (Finset.univ.image (fun i : ι => Fintype.card (V i))).card)
        * Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
            (signlessLap (completeMultipartiteGraph V)) - μ • LinearMap.id)) :=
  HermitianMaxMultiplicity.exists_finrank_card_le_of_card_image_le herm_multi
    (card_image_eigenvalues_le_refined hne htwo)

/-- **THE HEADLINE FORM: SOME EIGENVALUE OF `Q` HAS MULTIPLICITY AT LEAST `N / 3s`**, under the
hypotheses the sharp bracket takes. -/
theorem exists_finrank_three_mul [Nonempty (Σ i, V i)] (hne : ∀ i, Nonempty (V i))
    (hι : Nonempty ι) (hsize : ∀ i, 2 ≤ Fintype.card (V i))
    (htwice : ∀ i, 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)})
    (hspread : ∀ i k : ι, Fintype.card (V k) < 2 * Fintype.card (V i)) :
    ∃ μ : ℝ, Fintype.card (Σ i, V i)
      ≤ 3 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card
        * Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
            (signlessLap (completeMultipartiteGraph V)) - μ • LinearMap.id)) := by
  classical
  obtain ⟨S, hS, hcard⟩ := SignlessSharpBracket.card_spectrum_eq_three_mul
    (V := V) hne hι hsize htwice hspread
  refine HermitianMaxMultiplicity.exists_finrank_card_le_of_card_image_le herm_multi ?_
  refine le_of_eq ?_
  rw [← hcard]
  congr 1
  ext μ
  rw [mem_image_eigenvalues_iff_isEigen, hS]

end SignlessMultipartiteDegeneracy
