import LaplacianTwins
import LaplacianClosedTwins
import SignlessSimpleNotNecessary

/-!
# Twins degenerate BOTH operators, so no twin-rich graph can separate the two simplicities

`SignlessSimpleNotNecessary` closed the hypothesis question and left the one both its fences were
really asking: **a graph where `Q` is simple and `L` is not, or the reverse.** Its item lists six
non-two-colourable families whose signless spectra are measured and says checking them is a reading.
**The reading has a theorem behind it, and this file is the theorem.**

## What is proved

**`adjMatrix_mulVec_twinDiff`** — for two vertices with the same neighbourhood, `A` kills their
difference. This is `LaplacianTwins.lapMatrix_mulVec_twinDiff`'s own key step —
*`u` is a neighbour of `w` exactly when `v` is* — extracted as a statement about `A` alone, which is
what makes the rest free.

**`signlessLap_eq_lapMatrix_add_two_smul_adj`** — `Q = L + 2A`, one `abel` from the definitions.

**`signlessLap_mulVec_twinDiff`** — hence **the difference of two open twins is an eigenvector of
`Q` at the same eigenvalue it has for `L`**, their common degree. Not a new computation: `A` sends
it to zero, so `Q` and `L` do the same thing to it.

**`adjMatrix_mulVec_twinDiff_closed`, `signlessLap_mulVec_twinDiff_closed`** — for **adjacent**
twins the difference is an eigenvector of `A` at `−1`, so `Q` and `L` disagree by exactly `2`:
`L` gives `deg + 1` and `Q` gives `deg − 1`. **Different eigenvalues, both eigenvectors** — the
degeneracy transfers even though the value does not.

**`two_le_finrank_signlessLap_of_twin_pairs`, `not_finrank_signless_le_one_of_twin_pairs`** — two
twin pairs at one degree make `Q`'s spectrum degenerate, exactly as `LaplacianTwins` makes `L`'s.

**`twin_pairs_separate_nothing`** — **THE FILE'S THEOREM, and it is a negative one.** A graph with
two twin pairs at one degree has **both** spectra degenerate, so it is not a witness for the open
item in either direction. **The search for a separating graph must be twin-free**, and that rules
out four of the six families the item names in one theorem instead of four readings.

**`top_separates_nothing`** — the complete graph, spelled out, through
`LaplacianClosedTwins.closed_top`: every pair of its vertices is an adjacent twin pair.

## What is NOT here

* **NO SEPARATING GRAPH.** The item stays open and this file makes it *harder*, not easier: it
  removes candidates. **A negative result, and it is filed as one** (`ERRATUM 246`).
* **THE FAMILIES ARE RULED OUT BY A THEOREM AND NAMED BY A READING.**
  `twin_pairs_separate_nothing` is proved; that the equipartite multipartite family, `K_{1,1,2,2}`
  and
  `K_{1,1,2,3}` satisfy its hypothesis is **read off their constructions and not formalised
  here** — only the complete graph is instantiated, because `LaplacianClosedTwins.closed_top` had
  already done that work. A reader wanting the other four in Lean should expect one lemma each.
  ⚠ **The odd cycle is the exception and is ruled out for a different reason**: `C_n` has no twins
  at all for `n ≥ 5`, its degeneracy coming from the reflection `k ↦ n − k` pairing the eigenvalues
  — a symmetry of the spectrum, not a twin pair — and **this file does not cover it.** The reading,
  **done and recorded as a reading**: `SignlessCycleSpectrum` gives `Q`'s eigenvalues as
  `2 + 2cos(2πk/N)` and `CycleLaplacianSpectrum` gives `L`'s as `2 − 2cos(2πk/N)`; in both, `k` and
  `N − k` collide, so **both are degenerate for `N ≥ 3` and the odd cycle separates nothing
  either**. That is arithmetic about two formulas the estate proves and is **not formalised as a
  multiplicity statement here**.
  **AND THE PAW IS NOT AN OVERSIGHT.** It has exactly one closed twin pair — the two triangle
  vertices away from the pendant — and the theorem below needs **two** pairs, which is why it does
  not apply and why the paw is simple on both sides. The hypothesis is doing real work.
* **NOTHING ABOUT WHETHER A TWIN-FREE SEPARATING GRAPH EXISTS.** Twin-freeness is necessary for a
  witness by the above and nothing here suggests it is sufficient.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable equality
and adjacency; the twin statements take the neighbourhood equalities and the same five distinctness
conditions `LaplacianTwins` uses — **five, not six**, so the two pairs may share a vertex.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessTwins

open SimpleGraph Matrix LaplacianSignless GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. `Q = L + 2A` -/

theorem signlessLap_eq_lapMatrix_add_two_smul_adj :
    signlessLap G = G.lapMatrix ℝ + (2 : ℝ) • G.adjMatrix ℝ := by
  rw [signlessLap, SimpleGraph.lapMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## 2. The adjacency matrix on a twin difference -/

/-- **`A` KILLS THE DIFFERENCE OF TWO OPEN TWINS.** `u` is a neighbour of `w` exactly when `v` is,
so the two indicators cancel at every vertex. -/
theorem adjMatrix_mulVec_twinDiff {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    G.adjMatrix ℝ *ᵥ CutTwins.twinDiff u v = 0 := by
  funext w
  rw [SimpleGraph.adjMatrix_mulVec_apply, LaplacianTwins.cutTwinDiff_eq huv]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  rw [if_congr (LaplacianTwins.mem_neighborFinset_iff_of_neighborFinset_eq hnb w) rfl rfl]
  simp

/-- **SO `Q` AND `L` DO THE SAME THING TO IT.** -/
theorem signlessLap_mulVec_twinDiff {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    signlessLap G *ᵥ CutTwins.twinDiff u v = (G.degree u : ℝ) • CutTwins.twinDiff u v := by
  rw [signlessLap_eq_lapMatrix_add_two_smul_adj, Matrix.add_mulVec,
    LaplacianTwins.lapMatrix_mulVec_twinDiff huv hnb]
  have hA : ((2 : ℝ) • G.adjMatrix ℝ) *ᵥ CutTwins.twinDiff u v = 0 := by
    rw [Matrix.smul_mulVec, adjMatrix_mulVec_twinDiff huv hnb, smul_zero]
  rw [hA, add_zero]

/-! ## 3. Two pairs, and `Q`'s spectrum is degenerate too -/

theorem mem_ker_twinDiff_signless {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    CutTwins.twinDiff u v ∈ LinearMap.ker
      (Matrix.toLin' (signlessLap G) - (G.degree u : ℝ) • LinearMap.id) :=
  (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (signlessLap_mulVec_twinDiff huv hnb)

/-- **TWO TWIN PAIRS AT ONE DEGREE DEGENERATE `Q`**, exactly as they degenerate `L`. -/
theorem two_le_finrank_signlessLap_of_twin_pairs {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - (G.degree u : ℝ) • LinearMap.id)) := by
  have hm2 : CutTwins.twinDiff x y ∈ LinearMap.ker
      (Matrix.toLin' (signlessLap G) - (G.degree u : ℝ) • LinearMap.id) := by
    have h := mem_ker_twinDiff_signless hxy hnb2
    rwa [hdeg] at h
  have hsub : Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])
      ≤ LinearMap.ker (Matrix.toLin' (signlessLap G) - (G.degree u : ℝ) • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact mem_ker_twinDiff_signless huv hnb1
    · exact hm2
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])) = 2 := by
    rw [finrank_span_eq_card (LaplacianTwins.linearIndependent_twinDiff hux huy hvx)]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

theorem not_finrank_signless_le_one_of_twin_pairs {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) ≤ 1 := by
  intro h
  have := two_le_finrank_signlessLap_of_twin_pairs hnb1 hnb2 hdeg huv hxy hux huy hvx
  have h1 := h (G.degree u : ℝ)
  omega

/-! ## 4. So a twin-rich graph separates nothing -/

/-- **THE FILE'S THEOREM, AND IT IS NEGATIVE.** Two twin pairs at one degree make **both** spectra
degenerate, so such a graph is a witness for neither direction of the separation question. -/
theorem twin_pairs_separate_nothing {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    (¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) ≤ 1)
      ∧ (¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1) :=
  ⟨not_finrank_signless_le_one_of_twin_pairs hnb1 hnb2 hdeg huv hxy hux huy hvx,
    LaplacianTwins.not_finrank_lapMatrix_le_one_of_twin_pairs hnb1 hnb2 hdeg huv hxy hux huy hvx⟩

/-! ## 5. Adjacent twins: both eigenvectors, and the two eigenvalues differ by exactly two -/

/-- **`A` SENDS THE DIFFERENCE OF TWO CLOSED TWINS TO MINUS ITSELF.** The edge between the pair is
the whole of it: at `u` the neighbour sum sees `v` and not `u`, and away from the pair the two
indicators cancel as in the open case. -/
theorem adjMatrix_mulVec_twinDiff_closed {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) :
    G.adjMatrix ℝ *ᵥ CutTwins.twinDiff u v = -CutTwins.twinDiff u v := by
  funext w
  rw [SimpleGraph.adjMatrix_mulVec_apply, LaplacianClosedTwins.sum_twinDiff_of_closed huv h,
    Pi.neg_apply, LaplacianTwins.cutTwinDiff_eq huv]
  by_cases hwu : w = u
  · subst hwu; simp [huv]
  · by_cases hwv : w = v
    · subst hwv; simp [hwu]
    · simp [hwu, hwv]

/-- **SO `Q` GIVES `deg − 1` WHERE `L` GIVES `deg + 1`.** Different eigenvalues, the same
eigenvector, and the degeneracy transfers even though the value does not. -/
theorem signlessLap_mulVec_twinDiff_closed {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) :
    signlessLap G *ᵥ CutTwins.twinDiff u v
      = ((G.degree u : ℝ) - 1) • CutTwins.twinDiff u v := by
  rw [signlessLap_eq_lapMatrix_add_two_smul_adj, Matrix.add_mulVec,
    LaplacianClosedTwins.lapMatrix_mulVec_twinDiff_closed huv h, Matrix.smul_mulVec,
    adjMatrix_mulVec_twinDiff_closed huv h]
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem mem_ker_twinDiff_closed_signless {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) :
    CutTwins.twinDiff u v ∈ LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ((G.degree u : ℝ) - 1) • LinearMap.id) :=
  (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr
    (signlessLap_mulVec_twinDiff_closed huv h)

/-- **TWO CLOSED TWIN PAIRS AT ONE DEGREE DEGENERATE `Q`.** -/
theorem two_le_finrank_signlessLap_of_closed_pairs {u v x y : V}
    (h1 : insert u (G.neighborFinset u) = insert v (G.neighborFinset v))
    (h2 : insert x (G.neighborFinset x) = insert y (G.neighborFinset y))
    (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ((G.degree u : ℝ) - 1) • LinearMap.id)) := by
  have hm2 : CutTwins.twinDiff x y ∈ LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ((G.degree u : ℝ) - 1) • LinearMap.id) := by
    have hk := mem_ker_twinDiff_closed_signless hxy h2
    rwa [hdeg] at hk
  have hsub : Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])
      ≤ LinearMap.ker
        (Matrix.toLin' (signlessLap G) - ((G.degree u : ℝ) - 1) • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact mem_ker_twinDiff_closed_signless huv h1
    · exact hm2
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])) = 2 := by
    rw [finrank_span_eq_card (LaplacianTwins.linearIndependent_twinDiff hux huy hvx)]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-- **THE COMPLETE GRAPH ON FOUR OR MORE VERTICES SEPARATES NOTHING**, every pair of its vertices
being an adjacent twin pair. `LaplacianClosedTwins.closed_top` is what makes this three lines. -/
theorem top_separates_nothing (n : ℕ) :
    ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (⊤ : SimpleGraph (Fin (n + 4)))) - μ • LinearMap.id)) ≤ 1 := by
  intro hsimple
  have h2 := two_le_finrank_signlessLap_of_closed_pairs
    (G := (⊤ : SimpleGraph (Fin (n + 4))))
    (u := ⟨0, by omega⟩) (v := ⟨1, by omega⟩) (x := ⟨2, by omega⟩) (y := ⟨3, by omega⟩)
    ((LaplacianClosedTwins.closed_top _).trans (LaplacianClosedTwins.closed_top _).symm)
    ((LaplacianClosedTwins.closed_top _).trans (LaplacianClosedTwins.closed_top _).symm)
    (LaplacianClosedTwins.degree_eq_of_closed
      ((LaplacianClosedTwins.closed_top _).trans (LaplacianClosedTwins.closed_top _).symm))
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have h1 := hsimple (((⊤ : SimpleGraph (Fin (n + 4))).degree ⟨0, by omega⟩ : ℝ) - 1)
  omega

end SignlessTwins
