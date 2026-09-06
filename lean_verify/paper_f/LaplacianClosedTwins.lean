import LaplacianTwins

/-!
# Closed twins: the case the last unit excluded rather than covered

`LaplacianTwins` proved that two vertices with the same **open** neighbourhood have a difference of
indicators that is an eigenvector of the Laplacian, at their common degree, and fenced the sibling
case in as many words: *vertices with the same **closed** neighbourhood — so adjacent to each other
— also give an eigenvector, at `deg u + 1`. That case is not treated.* **It is treated here**, and
the difference between the two eigenvalues is exactly the edge between the pair.

## What is proved

**`adj_of_closed`** — **two vertices with the same closed neighbourhood are adjacent**, the mirror
of `LaplacianTwins.not_adj_of_neighborFinset_eq` and again a consequence rather than a hypothesis.
**`degree_eq_of_closed`** — and they have the same degree, from one `Finset.card_insert_of_notMem`
on each side; **it takes no `u ≠ v`**, the linter having reported that binder unused.

**`sum_twinDiff_of_closed`** — the neighbour sum of the difference is `0` away from the pair and
`∓1` on it, which is the whole content: in the open case it vanished everywhere, and the `±1` here
is the edge.

**`lapMatrix_mulVec_twinDiff_closed`** — **so the difference of two closed twins is an eigenvector
at one more than their degree.**

**`two_le_finrank_of_pair`** — **the counting step, factored out of the kind of twin.**
`LaplacianTwins` did this inline for the open case; stated against two eigenvector equations at a
common `ν` it serves all three combinations and mentions neither notion of twin.

**`two_le_finrank_of_closed_pairs`, `not_injective_of_closed_pairs`** — two closed pairs at the same
degree give a repeated Laplacian eigenvalue. **`two_le_finrank_of_mixed_pairs`,
`not_injective_of_mixed_pairs`** — **and one pair of each kind does too**, when the closed pair sits
one degree lower, since the open pair's eigenvalue is its degree and the closed pair's is one more
than its own.

**`closed_top`, `not_injective_top_via_closed_twins`** — **the hypothesis is inhabited**: in a
complete graph every vertex's closed neighbourhood is everything, so every pair is a closed twin
pair, and the complete graph on four or more vertices has a repeated Laplacian eigenvalue.

## What is NOT here

**THE COMPLETE-GRAPH COROLLARY IS A DUPLICATE, ON PURPOSE, AND IS WEAKER BY ONE VERTEX.**
`FieldAutOrder.not_injective_lapMatrix_eigenvalues_top` has the same conclusion from three vertices
up, through the graph's **rotational symmetry**; this one runs through its **twins** and needs four.
It is here because a theorem with no instance is not known to have one, and it is labelled rather
than presented as new.

**NO GRAPH IS EXHIBITED FOR THE MIXED CASE.** `two_le_finrank_of_mixed_pairs` has no instance
anywhere in this estate as of 2026-09-06, and its hypothesis — an open pair whose degree is one more
than a closed pair's — is not shown to be satisfiable by any graph. Not attempted, no cost claimed
(`ERRATUM 246`); the item is on `UNLOCK_WATCHLIST`.

**NO MULTIPLICITY IS COMPUTED IN THIS FILE**, in either case: the bound is `2 ≤` throughout, and a
twin class of size `k` should give `k − 1`, which is not proved anywhere in this estate as of
2026-09-06.

**NO CHARACTERISATION.** Twins of either kind are **sufficient** for a repeated eigenvalue and
nowhere near necessary — the cycle has a repeated eigenvalue and no twins of either kind. The
standing `UNLOCK_WATCHLIST` question is untouched.

**NOTHING IS SAID ABOUT WHICH EIGENVALUE.** Both theorems name an eigenvalue and prove its
eigenspace is at least a plane; **neither says the eigenvalue is in any particular part of the
spectrum**, and no ordering is used.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement takes a mass, a propagator
or a measure**. `degree_eq_of_closed` takes no `u ≠ v`; `two_le_finrank_of_pair` takes **three**
distinctness conditions and neither notion of twin; the pair theorems take five, `v ≠ y` being
unused there exactly as in `LaplacianTwins`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianClosedTwins

open SimpleGraph Matrix GraphLaplacian LaplacianTwins

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Closed twins -/

/-- **TWO VERTICES WITH THE SAME CLOSED NEIGHBOURHOOD ARE ADJACENT** — the mirror of
`LaplacianTwins.not_adj_of_neighborFinset_eq`, and again a consequence rather than a hypothesis. -/
theorem adj_of_closed {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) : G.Adj u v := by
  have hv : v ∈ insert v (G.neighborFinset v) := Finset.mem_insert_self _ _
  rw [← h] at hv
  rcases Finset.mem_insert.mp hv with hvu | hvu
  · exact absurd hvu.symm huv
  · exact (by simpa using hvu : G.Adj u v)

theorem degree_eq_of_closed {u v : V}
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) :
    G.degree u = G.degree v := by
  have hu : u ∉ G.neighborFinset u := by simp
  have hv : v ∉ G.neighborFinset v := by simp
  have hcard := congrArg Finset.card h
  rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem hv,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

theorem mem_iff_of_closed {u v : V}
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) {w : V}
    (hwu : w ≠ u) (hwv : w ≠ v) : u ∈ G.neighborFinset w ↔ v ∈ G.neighborFinset w := by
  constructor
  · intro hmem
    have h1 : w ∈ insert u (G.neighborFinset u) := by
      refine Finset.mem_insert_of_mem ?_
      simpa using (by simpa using hmem : G.Adj w u).symm
    rw [h] at h1
    rcases Finset.mem_insert.mp h1 with hc | hc
    · exact absurd hc hwv
    · simpa using (by simpa using hc : G.Adj v w).symm
  · intro hmem
    have h1 : w ∈ insert v (G.neighborFinset v) := by
      refine Finset.mem_insert_of_mem ?_
      simpa using (by simpa using hmem : G.Adj w v).symm
    rw [← h] at h1
    rcases Finset.mem_insert.mp h1 with hc | hc
    · exact absurd hc hwu
    · simpa using (by simpa using hc : G.Adj u w).symm

/-! ## 2. The difference of two closed twins is an eigenvector, at one more than their degree -/

theorem sum_twinDiff_of_closed {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) (w : V) :
    ∑ y ∈ G.neighborFinset w, CutTwins.twinDiff u v y
      = (if w = v then (1 : ℝ) else 0) - (if w = u then 1 else 0) := by
  rw [cutTwinDiff_eq huv]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  by_cases hwu : w = u
  · subst hwu
    have h1 : w ∉ G.neighborFinset w := by simp
    have h2 : v ∈ G.neighborFinset w := by simpa using (adj_of_closed huv h)
    simp [h1, h2, huv]
  · by_cases hwv : w = v
    · subst hwv
      have h1 : w ∉ G.neighborFinset w := by simp
      have h2 : u ∈ G.neighborFinset w := by simpa using (adj_of_closed huv h).symm
      simp [h1, h2, hwu]
    · rw [if_congr (mem_iff_of_closed h hwu hwv) rfl rfl]
      simp [hwu, hwv]

/-- **THE DIFFERENCE OF TWO CLOSED TWINS IS AN EIGENVECTOR OF THE LAPLACIAN, AT ONE MORE THAN THEIR
DEGREE.** The open case (`LaplacianTwins.lapMatrix_mulVec_twinDiff`) sits at the degree itself; the
edge between the pair is the whole of the difference. -/
theorem lapMatrix_mulVec_twinDiff_closed {u v : V} (huv : u ≠ v)
    (h : insert u (G.neighborFinset u) = insert v (G.neighborFinset v)) :
    G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u v
      = ((G.degree u : ℝ) + 1) • CutTwins.twinDiff u v := by
  funext w
  rw [SimpleGraph.lapMatrix_mulVec_apply, sum_twinDiff_of_closed huv h, cutTwinDiff_eq huv]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hwu : w = u
  · subst hwu
    simp only [↓reduceIte]
    ring
  · by_cases hwv : w = v
    · subst hwv
      rw [degree_eq_of_closed h]
      simp [hwu]
      ring
    · simp [hwu, hwv]

/-! ## 3. Two eigenvectors at one eigenvalue, whichever kind of pair they come from -/

/-- **THE COUNTING STEP, FACTORED OUT OF THE KIND OF TWIN.** `LaplacianTwins` did this inline for
the open case; stated this way it serves all three combinations below and is kept separate from
either notion of twin. -/
theorem two_le_finrank_of_pair {u v x y : V} {ν : ℝ}
    (h1 : G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u v = ν • CutTwins.twinDiff u v)
    (h2 : G.lapMatrix ℝ *ᵥ CutTwins.twinDiff x y = ν • CutTwins.twinDiff x y)
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])
      ≤ LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr h1
    · exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr h2
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])) = 2 := by
    rw [finrank_span_eq_card (linearIndependent_twinDiff hux huy hvx)]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-! ## 4. So two closed pairs, or one of each, give a repeated eigenvalue -/

theorem two_le_finrank_of_closed_pairs {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (h1 : insert u (G.neighborFinset u) = insert v (G.neighborFinset v))
    (h2 : insert x (G.neighborFinset x) = insert y (G.neighborFinset y))
    (hdeg : G.degree x = G.degree u) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ((G.degree u : ℝ) + 1) • LinearMap.id)) := by
  refine two_le_finrank_of_pair (lapMatrix_mulVec_twinDiff_closed huv h1) ?_ hux huy hvx
  have h := lapMatrix_mulVec_twinDiff_closed hxy h2
  rwa [hdeg] at h

/-- **A GRAPH WITH TWO CLOSED TWIN PAIRS OF THE SAME DEGREE HAS A REPEATED LAPLACIAN
EIGENVALUE.** -/
theorem not_injective_of_closed_pairs {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (h1 : insert u (G.neighborFinset u) = insert v (G.neighborFinset v))
    (h2 : insert x (G.neighborFinset x) = insert y (G.neighborFinset y))
    (hdeg : G.degree x = G.degree u) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj
  have h1' := hdim ((G.degree u : ℝ) + 1)
  have h2' := two_le_finrank_of_closed_pairs huv hxy h1 h2 hdeg hux huy hvx
  omega

/-- **AND ONE PAIR OF EACH KIND DOES TOO**, when the closed pair sits one degree lower: the open
pair's eigenvalue is its degree and the closed pair's is one more than its own. -/
theorem two_le_finrank_of_mixed_pairs {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (h1 : G.neighborFinset u = G.neighborFinset v)
    (h2 : insert x (G.neighborFinset x) = insert y (G.neighborFinset y))
    (hdeg : G.degree x + 1 = G.degree u) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u : ℝ) • LinearMap.id)) := by
  refine two_le_finrank_of_pair (LaplacianTwins.lapMatrix_mulVec_twinDiff huv h1) ?_ hux huy hvx
  have h := lapMatrix_mulVec_twinDiff_closed hxy h2
  have hcast : ((G.degree x : ℝ) + 1) = (G.degree u : ℝ) := by
    rw [← hdeg]
    push_cast
    ring
  rwa [hcast] at h

theorem not_injective_of_mixed_pairs {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (h1 : G.neighborFinset u = G.neighborFinset v)
    (h2 : insert x (G.neighborFinset x) = insert y (G.neighborFinset y))
    (hdeg : G.degree x + 1 = G.degree u) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj
  have h1' := hdim (G.degree u : ℝ)
  have h2' := two_le_finrank_of_mixed_pairs huv hxy h1 h2 hdeg hux huy hvx
  omega

/-! ## 5. The hypothesis is inhabited: every pair in a complete graph is a closed twin pair -/

theorem closed_top (u : V) :
    insert u ((⊤ : SimpleGraph V).neighborFinset u) = (Finset.univ : Finset V) := by
  ext w
  by_cases hw : w = u
  · simp [hw]
  · simp [hw, Ne.symm hw]

/-- **THE COMPLETE GRAPH ON FOUR OR MORE VERTICES HAS A REPEATED LAPLACIAN EIGENVALUE, BY TWINS.**
This **duplicates `FieldAutOrder.not_injective_lapMatrix_eigenvalues_top` on purpose**, and is
weaker than it by one vertex: that route runs through the graph's rotational symmetry and this one
through its twins, and the point is not the conclusion but that the hypothesis above is inhabited
by a graph this estate already names. -/
theorem not_injective_top_via_closed_twins (n : ℕ) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian
      (⊤ : SimpleGraph (Fin (n + 4)))).eigenvalues :=
  not_injective_of_closed_pairs
    (u := ⟨0, by omega⟩) (v := ⟨1, by omega⟩) (x := ⟨2, by omega⟩) (y := ⟨3, by omega⟩)
    (by simp) (by simp)
    ((closed_top _).trans (closed_top _).symm)
    ((closed_top _).trans (closed_top _).symm)
    (degree_eq_of_closed ((closed_top _).trans (closed_top _).symm))
    (by simp) (by simp) (by simp)

end LaplacianClosedTwins
