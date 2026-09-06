import LaplacianTwinClass

/-!
# The twin bound is not the dimension, and the reason I gave for that was also wrong

`LaplacianTwins` fenced its lower bound with a sentence naming what a reader should expect instead:
*"the eigenspace of a twin class is spanned by such differences and has dimension one less than the
class size"*. `LaplacianTwinClass` proved the inequality half of it and explained the gap by saying
the eigenspace *"is not shown to be exactly that, and for a class that is not maximal it will not
be"*. **Both sentences are wrong, and one graph shows it.**

Two disjoint triangles. Every closed twin class has three members, so the class bound is `2`. The
eigenspace at `3` has dimension **four** — two differences from each triangle — and the classes are
**maximal**, so non-maximality is not the reason and cannot be.

## What is proved

**`twoTriangles`**, six vertices, and **`degrees`** — every vertex has degree two.

**`closed_class_card_le_three`, `open_class_card_le_one`** — **every** closed twin class has at most
three members and **every** open twin class at most one, by `decide` over all sixty-four subsets and
six base points. These are the statements that make the counterexample a counterexample rather than
an example: they quantify over all classes, not over one.

**`eig_of_closed`, `linearIndependent_fam`, `four_le_finrank`** — the four differences `0−1`, `1−2`,
`3−4`, `4−5` are eigenvectors at `3` (through
`LaplacianClosedTwins.lapMatrix_mulVec_twinDiff_closed`, degree two plus one) and independent, so
that eigenspace is at least four-dimensional.

**`class_bound_lt_finrank`** — **so for every twin class of this graph the bound is strictly less
than the dimension.** `LaplacianTwinClass`'s theorem is not sharp, not for a maximal class either,
and the sentence that predicted otherwise is corrected in place (`ERRATUM 468`).

## What is NOT here

**THE EIGENSPACE IS NOT COMPUTED.** `4 ≤ dim` is proved and **the dimension is not claimed to be
four**, though it is. Nothing here bounds it above, and this estate still has **no upper bound on
the multiplicity of any eigenvalue of any graph** as of 2026-09-06.

**NO REPAIRED STATEMENT IS OFFERED.** The true statement in this direction is presumably that the
twin differences of **all** classes together span a subspace whose dimension is `∑ (|Sᵢ| − 1)`, and
that the rest of the spectrum comes from the quotient graph. **None of that is proved, stated or
attempted here** (`ERRATUM 246`), and the arithmetic of this example — `(3−1) + (3−1) = 4` —
**is not evidence for it**, being one graph.

**NO CLAIM THAT THE CLASSES ARE MAXIMAL IN GENERAL.** `closed_class_card_le_three` is about
`twoTriangles` and is proved by exhaustion over its subsets. **Nothing here defines maximality**,
and the word is used in prose only.

**THIS IS NOT A COUNTEREXAMPLE TO ANY THEOREM.** `LaplacianTwinClass`'s inequality holds here, as it
must — `2 ≤ 4`. What fails is the **expectation** written beside it, which is why the correction is
an erratum about a fence rather than about a proof.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **nothing here takes a hypothesis beyond
the graph being this graph**, and the two class-size theorems take a twin hypothesis they quantify
over rather than assume.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace TwinClassNotExact

open SimpleGraph Matrix GraphLaplacian LaplacianTwinClass LaplacianClosedTwins

/-! ## 1. Two triangles -/

/-- Adjacency of `twoTriangles`: the triangles `0–1–2` and `3–4–5`, with nothing between them. -/
def twoAdj : Fin 6 → Fin 6 → Bool
  | 0, 1 | 1, 0 => true
  | 0, 2 | 2, 0 => true
  | 1, 2 | 2, 1 => true
  | 3, 4 | 4, 3 => true
  | 3, 5 | 5, 3 => true
  | 4, 5 | 5, 4 => true
  | _, _ => false

def twoTriangles : SimpleGraph (Fin 6) where
  Adj u v := twoAdj u v = true
  symm := by intro u v h; revert u v; decide
  loopless := ⟨by intro u h; revert u; decide⟩

instance : DecidableRel twoTriangles.Adj := fun u v =>
  inferInstanceAs (Decidable (twoAdj u v = true))

theorem degrees : ∀ v : Fin 6, twoTriangles.degree v = 2 := by decide

/-! ## 2. Every twin class has at most three members -/

theorem closed_class_card_le_three (S : Finset (Fin 6)) (u₀ : Fin 6)
    (hS : ∀ u ∈ S, insert u (twoTriangles.neighborFinset u)
      = insert u₀ (twoTriangles.neighborFinset u₀)) : S.card ≤ 3 := by
  revert hS
  revert S u₀
  decide

theorem open_class_card_le_one (S : Finset (Fin 6)) (u₀ : Fin 6)
    (hS : ∀ u ∈ S, twoTriangles.neighborFinset u = twoTriangles.neighborFinset u₀) :
    S.card ≤ 1 := by
  revert hS
  revert S u₀
  decide

/-! ## 3. But the eigenspace at three is four-dimensional -/

theorem eig_of_closed {u v : Fin 6} (huv : u ≠ v)
    (h : insert u (twoTriangles.neighborFinset u) = insert v (twoTriangles.neighborFinset v)) :
    twoTriangles.lapMatrix ℝ *ᵥ CutTwins.twinDiff u v = (3 : ℝ) • CutTwins.twinDiff u v := by
  have h1 := lapMatrix_mulVec_twinDiff_closed huv h
  have hd : ((twoTriangles.degree u : ℝ) + 1) = 3 := by rw [degrees u]; norm_num
  rwa [hd] at h1

/-- The four differences, two from each triangle. -/
noncomputable def fam : Fin 4 → (Fin 6 → ℝ) :=
  ![CutTwins.twinDiff 0 1, CutTwins.twinDiff 1 2, CutTwins.twinDiff 3 4, CutTwins.twinDiff 4 5]

theorem linearIndependent_fam : LinearIndependent ℝ fam := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  fin_cases i
  · simpa [fam, CutTwins.twinDiff, Fin.sum_univ_four] using congrFun hg 0
  · simpa [fam, CutTwins.twinDiff, Fin.sum_univ_four] using congrFun hg 2
  · simpa [fam, CutTwins.twinDiff, Fin.sum_univ_four] using congrFun hg 3
  · simpa [fam, CutTwins.twinDiff, Fin.sum_univ_four] using congrFun hg 5

theorem four_le_finrank :
    4 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (twoTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range fam) ≤ LinearMap.ker
      (Matrix.toLin' (twoTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i <;>
      exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr
        (eig_of_closed (by decide) (by decide))
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range fam)) = 4 := by
    rw [finrank_span_eq_card linearIndependent_fam]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-! ## 4. So the class bound is not the dimension -/

/-- **A TWIN CLASS DOES NOT DETERMINE THE EIGENSPACE, EVEN WHEN IT IS MAXIMAL.** Every twin class
of `twoTriangles` has at most three members, so `LaplacianTwinClass`'s bound gives at most `2`; the
eigenspace at `3` has dimension at least `4`. -/
theorem class_bound_lt_finrank (S : Finset (Fin 6)) (u₀ : Fin 6)
    (hS : ∀ u ∈ S, insert u (twoTriangles.neighborFinset u)
      = insert u₀ (twoTriangles.neighborFinset u₀)) :
    S.card - 1 < Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (twoTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id)) := by
  have h1 := closed_class_card_le_three S u₀ hS
  have h2 := four_le_finrank
  omega

end TwinClassNotExact
