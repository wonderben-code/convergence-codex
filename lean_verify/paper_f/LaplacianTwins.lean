import FieldTwinSpectrum
import CutTwins

/-!
# Twins: two vertices with the same neighbours, and the eigenvector their difference is

`FieldTwinSpectrum` settled a question with a hand-drawn eight-vertex tree and two eigenvectors
verified coordinate by coordinate. It fenced the obvious generalisation and said so: *two disjoint
pairs of non-adjacent twins of equal degree give a repeated Laplacian eigenvalue is a general
theorem, and this file proves it for one graph by direct computation instead. Not attempted.* **The
fence lasted one unit.** This is the general theorem, and it is shorter than the computation it
replaces.

## What is proved

**`cutTwinDiff_eq`** — **the vector was already in the estate.** `newnames_scan` flagged the name
against `CutTwins.twinDiff`, written for a completely different purpose — equal columns of a cut
matrix — and it is the same vector. **No second definition is introduced**; this file states
`CutTwins.twinDiff` in the difference-of-indicators form the sums below want, and records that the
two forms agree exactly when `u ≠ v`, which is why that hypothesis appears where it does. Third
time a name collision has revealed a shared object (`ERRATUM 465`).

**`not_adj_of_neighborFinset_eq`** — **two vertices with the same neighbours are never adjacent**,
since otherwise each would be its own neighbour. So the hypothesis `¬ G.Adj u v` that a reader
expects beside *same neighbourhood* is **not needed anywhere**, and is not taken.

**`degree_eq_of_neighborFinset_eq`, `mem_neighborFinset_iff_of_neighborFinset_eq`** — twins have the
same degree, and `u` is a neighbour of `w` exactly when `v` is. The second is the fact the whole
file turns on.

**`lapMatrix_mulVec_twinDiff`** — **the difference of two twins is an eigenvector of the Laplacian,
at their common degree.** The neighbour sum vanishes at **every** vertex, not just off the pair,
which is what makes the proof three lines rather than a case analysis.

**`two_le_finrank_of_twin_pairs`, `not_finrank_lapMatrix_le_one_of_twin_pairs`,
`not_injective_lapMatrix_eigenvalues_of_twin_pairs`** — **so two twin pairs at the same degree make
that degree a repeated eigenvalue**, and such a graph fails the symmetry chain's hypothesis and has
a repeated Laplacian eigenvalue. **Five distinctness conditions, not six**: `v ≠ y` is never used,
so the two pairs may share that vertex — in which case `u`, `v`, `x` are three mutual twins and the
multiplicity is larger still. The linear-independence step needs **three** of the five — `u ≠ x`,
`u ≠ y`, `v ≠ x` — and takes no `u ≠ v` at all, because at `u = v` the vector is an indicator and
still independent of the other. **Each hypothesis was dropped when the linter said it was unused,
not guessed at in advance** (`ERRATUM 455`).

**`twinGraph_not_injective`** — **and the previous unit's graph goes through it in one line**, its
`0, 1` and `3, 4` being two twin pairs of degree one. That unit's `lap_v01`, `lap_v34` and
`two_le_finrank_eigenspace` are the general argument at one graph, and are kept as written
(`ERRATUM 94`).

## What is NOT here

**NO CHARACTERISATION, AND THE CONVERSE IS FALSE.** Having two twin pairs is **sufficient** for a
repeated Laplacian eigenvalue and nowhere near necessary — the cycle has a repeated eigenvalue and
no twins at all. Nothing here narrows the standing `UNLOCK_WATCHLIST` question about which graphs
have a simple spectrum.

**NO MULTIPLICITY IS COMPUTED.** The bound is `2 ≤`, from two independent eigenvectors. **The
eigenspace of a twin class is spanned by such differences and has dimension one less than the class
size**; that is not proved here, and no upper bound of any kind appears.

⚠ **HALF SUPERSEDED THE SAME DAY, KEPT AS WRITTEN** (`ERRATUM 94`, found by `fences_scan`).
`LaplacianTwinClass.card_sub_one_le_finrank_of_open_class` proves **one inequality** of that
sentence: `|S| − 1 ≤ dim`, for a class of any size. **The other half does not move**: nothing shows
the eigenspace is *spanned* by twin differences or that the dimension is *exactly* `|S| − 1`, and
for a class that is not maximal it will not be. **No upper bound on the multiplicity of any
eigenvalue of any graph exists in this estate as of 2026-09-06.**

⚠⚠⚠ **AND THAT LAST SENTENCE IS FALSE TOO** (`ERRATUM 469`, the same day; kept as written per
`ERRATUM 94`). `FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component` — proved seven
units **before** this sentence was written, in the same run — gives the multiplicity of the
eigenvalue `0` **exactly**, as the number of connected components, on every finite graph; and
`finrank_ker_lapMatrix_zero_connected` makes it the explicit number **1** on every connected one.
**The bound above is still not sharp**, which is what the paragraph was reaching for.

⚠⚠ **AND THE OTHER HALF IS NOT MERELY UNPROVED — IT IS FALSE, AND SO IS THE REASON GIVEN FOR IT
IMMEDIATELY ABOVE** (`ERRATUM 468`, the same day; both paragraphs kept as written per
`ERRATUM 94`). `TwinClassNotExact`: **two disjoint triangles**. Every closed twin class has three
members (`closed_class_card_le_three`, by exhaustion over all sixty-four subsets), so the bound is
`2`; the eigenspace at `3` has dimension at least **four**. And the classes **are** maximal, so
*"for a class that is not maximal it will not be"* names the wrong reason. **The inequality above
stands and is not sharp.**

**NOTHING ABOUT ADJACENT TWINS.** Vertices with the same **closed** neighbourhood — `N[u] = N[v]`,
so `u` and `v` adjacent — also give an eigenvector, at `deg u + 1`. **That case is not treated**,
and `not_adj_of_neighborFinset_eq` shows the case treated here excludes it rather than covering it.

**NO AUTOMORPHISM IS BUILT.** A twin pair gives a transposition automorphism, and that is how
`FieldTwinSpectrum` reads; **this file constructs none** and its argument is purely spectral.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement in this file takes a mass,
a propagator or a measure** — it is graph theory throughout, and reaches
`Matrix.IsHermitian.eigenvalues` only through `FieldSimpleConverse.lapMatrix_isHermitian`, which
takes no hypothesis either. `twinDiff` and its two evaluation lemmas take neither `Fintype` nor a
graph; three of the graph lemmas `omit` `DecidableEq`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianTwins

open SimpleGraph Matrix GraphLaplacian

/-! ## 1. The vector, which the estate already had -/

section Vec

variable {V : Type*} [DecidableEq V]

/-- **`CutTwins.twinDiff` IS THE VECTOR THIS FILE NEEDS**, and this is it in the form the sums
below want: a **difference of indicators** rather than a nested `if`. The two agree only when
`u ≠ v` — at `u = v` the nested form is the indicator of `u` and this one is `0` — which is why
every statement below takes that hypothesis. Found by `newnames_scan` (`ERRATUM 465`), and no
second definition is introduced. -/
theorem cutTwinDiff_eq {u v : V} (h : u ≠ v) :
    CutTwins.twinDiff u v = fun i => (if i = u then 1 else 0) - (if i = v then 1 else 0) := by
  funext i
  by_cases hiu : i = u
  · subst hiu
    simp [CutTwins.twinDiff, h]
  · by_cases hiv : i = v <;> simp [CutTwins.twinDiff, hiu, hiv, Ne.symm h]

end Vec

/-! ## 2. Twins -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- **TWO VERTICES WITH THE SAME NEIGHBOURS ARE NOT ADJACENT** — otherwise each would be its own
neighbour. The hypothesis `¬ G.Adj u v` a reader expects beside *same neighbourhood* is therefore
never needed. -/
theorem not_adj_of_neighborFinset_eq {u v : V} (hnb : G.neighborFinset u = G.neighborFinset v) :
    ¬ G.Adj u v := by
  intro hadj
  have h1 : u ∈ G.neighborFinset v := by simp [hadj.symm]
  rw [← hnb] at h1
  simp at h1

omit [DecidableEq V] in
theorem degree_eq_of_neighborFinset_eq {u v : V} (hnb : G.neighborFinset u = G.neighborFinset v) :
    G.degree u = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree, hnb]

omit [DecidableEq V] in
theorem mem_neighborFinset_iff_of_neighborFinset_eq {u v : V}
    (hnb : G.neighborFinset u = G.neighborFinset v) (w : V) :
    u ∈ G.neighborFinset w ↔ v ∈ G.neighborFinset w := by
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    have h1 : w ∈ G.neighborFinset u := by simp [h.symm]
    rw [hnb] at h1
    exact ((by simpa using h1 : G.Adj v w)).symm
  · intro h
    have h1 : w ∈ G.neighborFinset v := by simp [h.symm]
    rw [← hnb] at h1
    exact ((by simpa using h1 : G.Adj u w)).symm

/-! ## 3. The difference of two twins is an eigenvector -/

/-- **THE DIFFERENCE OF TWO TWINS IS AN EIGENVECTOR OF THE LAPLACIAN, AT THEIR COMMON DEGREE.**
The neighbour sum vanishes at *every* vertex, not just off the pair: `u` is a neighbour of `w`
exactly when `v` is. -/
theorem lapMatrix_mulVec_twinDiff {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u v = (G.degree u : ℝ) • CutTwins.twinDiff u v := by
  funext w
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  rw [cutTwinDiff_eq huv]
  have hsum : ∑ y ∈ G.neighborFinset w,
      ((if y = u then (1:ℝ) else 0) - (if y = v then 1 else 0)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    rw [if_congr (mem_neighborFinset_iff_of_neighborFinset_eq hnb w) rfl rfl]
    ring
  rw [hsum, sub_zero, Pi.smul_apply, smul_eq_mul]
  by_cases hw : w = v
  · subst hw
    rw [degree_eq_of_neighborFinset_eq hnb]
  · by_cases hwu : w = u
    · subst hwu; rfl
    · simp [hwu, hw]

/-! ## 4. Two twin pairs at the same degree give a repeated eigenvalue -/

theorem mem_ker_twinDiff {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    CutTwins.twinDiff u v ∈ LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u : ℝ) • LinearMap.id) :=
  (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (lapMatrix_mulVec_twinDiff huv hnb)

omit [Fintype V] [DecidableRel G.Adj] in
theorem linearIndependent_twinDiff {u v x y : V}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    LinearIndependent ℝ ![CutTwins.twinDiff u v, CutTwins.twinDiff x y] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  constructor
  · have h := congrFun hab u
    simpa [CutTwins.twinDiff, hux, huy] using h
  · have h := congrFun hab x
    simpa [CutTwins.twinDiff, hux.symm, hvx.symm] using h

/-- **TWO PAIRS OF TWINS AT THE SAME DEGREE MAKE THAT DEGREE A REPEATED EIGENVALUE.** **Five
distinctness conditions, not six**: `v ≠ y` is never needed, so the pairs may share that vertex —
in which case `u`, `v`, `x` are three mutual twins and the multiplicity is larger still. -/
theorem two_le_finrank_of_twin_pairs {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u : ℝ) • LinearMap.id)) := by
  have hm2 : CutTwins.twinDiff x y ∈ LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u : ℝ) • LinearMap.id) := by
    have h := mem_ker_twinDiff hxy hnb2
    rwa [hdeg] at h
  have hsub : Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])
      ≤ LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u : ℝ) • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact mem_ker_twinDiff huv hnb1
    · exact hm2
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![CutTwins.twinDiff u v, CutTwins.twinDiff x y])) = 2 := by
    rw [finrank_span_eq_card (linearIndependent_twinDiff hux huy hvx)]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

theorem not_finrank_lapMatrix_le_one_of_twin_pairs {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  have h1 := hdim (G.degree u : ℝ)
  have h2 := two_le_finrank_of_twin_pairs hnb1 hnb2 hdeg huv hxy hux huy hvx
  omega

/-- **SO SUCH A GRAPH HAS A REPEATED LAPLACIAN EIGENVALUE** — no mass, no propagator, no measure. -/
theorem not_injective_lapMatrix_eigenvalues_of_twin_pairs {u v x y : V}
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (huv : u ≠ v) (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := fun hinj =>
  not_finrank_lapMatrix_le_one_of_twin_pairs hnb1 hnb2 hdeg huv hxy hux huy hvx
    (FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj)

/-! ## 5. The previous unit's graph, through the general theorem -/

/-- **`FieldTwinSpectrum`'s EIGENVECTOR COMPUTATION WAS THE GENERAL ARGUMENT AT ONE GRAPH.** Its
`0, 1` and `3, 4` are two twin pairs, both of degree one. -/
theorem twinGraph_not_injective : ¬ Function.Injective
    (FieldSimpleConverse.lapMatrix_isHermitian FieldTwinSpectrum.twinGraph).eigenvalues :=
  not_injective_lapMatrix_eigenvalues_of_twin_pairs (u := 0) (v := 1) (x := 3) (y := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

end LaplacianTwins
