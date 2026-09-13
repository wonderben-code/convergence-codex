import SignlessSeparationNonzero
import SignlessP1122Charpoly
import UnbalancedMultipartiteTable

/-!
# The excess runs both ways, and one six-vertex graph shows it

**THE QUESTION THE PREVIOUS UNIT DECLINED TO ASK, ASKED AND ANSWERED.**
`SignlessSeparationNonzero` proved that on a graph which is not two-colourable `Q` has **strictly
more** multiplicity than `L` at some non-zero value — the deficit at `0` has to be paid back — and
fenced itself: *whether `L` can also exceed `Q` at some value is not asked and not answered*. It
can, and the witness is a graph this chain already knows completely.

**`K_{1,1,2,2}`, ON SIX VERTICES.** `SignlessP1122Charpoly` has `Q`'s whole multiplicity table
there and `UnbalancedMultipartiteTable` has `L`'s top eigenvalue on any complete multipartite
graph. Put beside each other at the value `6`, which is the vertex count:

* `L`'s multiplicity is `3` — the number of parts minus one, which is what the top eigenvalue of a
  complete multipartite graph always carries;
* `Q`'s is `0` — `6` is not a root of its characteristic polynomial at all, that polynomial being
  `(X − 2)(X − 4)³(X − lo)(X − hi)` with `lo = 6 − 2√2` and `hi = 6 + 2√2`, neither of them `6`.

**So `L` exceeds `Q` by three at a non-zero value.** Combined with the previous unit, whose theorem
applies to this graph, **both excesses occur on the same graph**: `Q` is ahead somewhere and `L` is
ahead at `6`, and neither is at zero.

**AND THE GRAPH'S NON-TWO-COLOURABILITY IS NOT ASSUMED, IT IS COMPUTED.** `Q`'s spectrum is
`{2, 4, lo, hi}`, every one of them positive, so `Q`'s kernel is trivial; `L`'s is a line, the
graph being connected. By `SignlessColourableNecessary.finrank_ker_eq_iff_colorable` those two
numbers differing **is** the failure of two-colourability. No triangle is exhibited and no
colouring argument is made — the two tables already say it.

## What is proved

**`card_sigma_P1122`** — the graph has `6` vertices. **`six_notMem_spectrum_P1122`** — `6` is not
an eigenvalue of `Q` there. **`finrank_signlessLap_six_P1122`**, **`finrank_lapMatrix_six_P1122`**
— the two multiplicities at `6`, namely `0` and `3`.

**`lapMatrix_finrank_gt_signlessLap_P1122`** — **THE ANSWER**: `L` exceeds `Q` at a non-zero value.

**`zero_notMem_spectrum_P1122`**, **`finrank_signlessLap_zero_P1122`** — the same reading at `0`,
where `Q`'s kernel is trivial because all four of its eigenvalues are positive.

**`not_colorable_P1122`** — and the graph is not two-colourable, read off the two kernels.

**`excess_both_ways_P1122`** — both statements at once: there is a non-zero value where `Q` is
ahead and a non-zero value where `L` is ahead, on this one graph.

## What is NOT here

* **THE VALUE WHERE `Q` IS AHEAD IS NOT NAMED.** It comes from the previous unit's counting
  argument, which produces an existence statement and no witness. `Q`'s multiplicity at `4` is `3`
  and `L`'s at `4` is not computed anywhere in this estate, so **naming it would be a new
  computation** and this file does not make one.
* **NO GENERAL STATEMENT.** That `L` can exceed `Q` away from zero is proved **at one graph**.
  Nothing here says when it happens, and there is no analogue of the previous unit's counting
  argument in this direction — the deficit at zero forces `Q` ahead somewhere, and forces nothing
  the other way.
* **NOTHING NEW IS COMPUTED.** Every number in this file was proved elsewhere; the file is the
  comparison. It is recorded as a unit because the question was on the open list, not because
  anything was hard.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none. Every theorem is about one named
graph.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessExcessBothWays

open Matrix SimpleGraph LaplacianSignless SignlessDoublingFails SignlessP1122Exact
open SignlessP1122Charpoly SignlessColourableNecessary

/-! ## 1. The graph has six vertices -/

theorem card_sigma_P1122 : Fintype.card (Σ i, P1122 i) = 6 := by
  rw [Fintype.card_sigma]
  decide

/-! ## 2. Six is not a signless eigenvalue -/

theorem six_notMem_spectrum_P1122 :
    (6 : ℝ) ∉ Finset.univ.image herm_P1122.eigenvalues := by
  rw [image_eigenvalues_P1122]
  have hlo := lo_bounds
  have hhi := hi_bounds
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨by norm_num, by norm_num, fun h => by linarith [hlo.2, h ▸ hlo.2],
    fun h => by linarith [hhi.2, h ▸ hhi.2]⟩

/-- **`Q` HAS NOTHING AT `6`.** -/
theorem finrank_signlessLap_six_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - (6 : ℝ) • LinearMap.id)) = 0 :=
  HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem herm_P1122
    six_notMem_spectrum_P1122

/-! ## 3. And `L` has a three-dimensional eigenspace there -/

/-- **`L`'s TOP EIGENVALUE IS THE VERTEX COUNT, WITH MULTIPLICITY ONE LESS THAN THE NUMBER OF
PARTS.** -/
theorem finrank_lapMatrix_six_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        ((completeMultipartiteGraph P1122).lapMatrix ℝ) - (6 : ℝ) • LinearMap.id)) = 3 := by
  have h := UnbalancedMultipartiteTable.finrank_eigenspace_top (V := P1122)
    (fun i => by rw [← Fintype.card_pos_iff, card_P1122]; omega) ⟨0⟩
  rw [card_sigma_P1122] at h
  rw [show ((6 : ℕ) : ℝ) = (6 : ℝ) by norm_num] at h
  rw [h]
  decide

/-! ## 4. So the excess runs the other way too -/

/-- **`L` EXCEEDS `Q` AT A NON-ZERO VALUE.** -/
theorem lapMatrix_finrank_gt_signlessLap_P1122 :
    ∃ μ : ℝ, μ ≠ 0 ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeMultipartiteGraph P1122)) - μ • LinearMap.id))
        < Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          ((completeMultipartiteGraph P1122).lapMatrix ℝ) - μ • LinearMap.id)) := by
  refine ⟨6, by norm_num, ?_⟩
  rw [finrank_signlessLap_six_P1122, finrank_lapMatrix_six_P1122]
  norm_num

theorem zero_notMem_spectrum_P1122 :
    (0 : ℝ) ∉ Finset.univ.image herm_P1122.eigenvalues := by
  rw [image_eigenvalues_P1122]
  have hlo := lo_bounds
  have hhi := hi_bounds
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨by norm_num, by norm_num, fun h => by linarith [hlo.1, h ▸ hlo.1],
    fun h => by linarith [hhi.1, h ▸ hhi.1]⟩

/-- `Q`'s kernel on this graph is trivial: every one of its four eigenvalues is positive. -/
theorem finrank_signlessLap_zero_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - (0 : ℝ) • LinearMap.id)) = 0 :=
  HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem herm_P1122
    zero_notMem_spectrum_P1122

/-- **THE GRAPH IS NOT TWO-COLOURABLE, READ OFF THE TWO KERNELS** rather than from a triangle. -/
theorem not_colorable_P1122 : ¬ (completeMultipartiteGraph P1122).Colorable 2 := by
  intro hcol
  have h := (finrank_ker_eq_iff_colorable (completeMultipartiteGraph P1122)).2 hcol
  rw [← SignlessSeparationNonzero.ker_sub_zero_smul
      (signlessLap (completeMultipartiteGraph P1122)),
    ← SignlessSeparationNonzero.ker_sub_zero_smul
      ((completeMultipartiteGraph P1122).lapMatrix ℝ)] at h
  rw [finrank_signlessLap_zero_P1122,
    UnbalancedMultipartiteTable.finrank_eigenspace_zero (V := P1122)
      (fun i => by rw [← Fintype.card_pos_iff, card_P1122]; omega) (by decide)] at h
  exact absurd h (by norm_num)

/-- **BOTH EXCESSES, ON ONE GRAPH, NEITHER OF THEM AT ZERO.** -/
theorem excess_both_ways_P1122 :
    (∃ μ : ℝ, μ ≠ 0 ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          ((completeMultipartiteGraph P1122).lapMatrix ℝ) - μ • LinearMap.id))
        < Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeMultipartiteGraph P1122)) - μ • LinearMap.id)))
    ∧ (∃ μ : ℝ, μ ≠ 0 ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeMultipartiteGraph P1122)) - μ • LinearMap.id))
        < Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          ((completeMultipartiteGraph P1122).lapMatrix ℝ) - μ • LinearMap.id))) :=
  ⟨SignlessSeparationNonzero.exists_ne_zero_finrank_signlessLap_gt _ not_colorable_P1122,
    lapMatrix_finrank_gt_signlessLap_P1122⟩

end SignlessExcessBothWays
