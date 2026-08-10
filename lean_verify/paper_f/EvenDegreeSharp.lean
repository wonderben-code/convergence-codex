import CycleDecomposition

/-!
# Which hypotheses of the circuit decomposition can be dropped, and which cannot

`EvenDegreeCycle` and `CycleDecomposition` carry three hypotheses between them:
a `Fintype` on the vertices, a `DecidableRel` on the adjacency, and finiteness. This
file settles all three, in the two ways a hypothesis can be settled.

**Two come off.** The gate is restated with `Finite V` and no decidability at all, in
terms of `EvenDegrees` rather than `SimpleGraph.degree`. The mathematics is unchanged —
`Finite` plus choice manufactures the other two — and the point is which hypotheses the
*caller* must supply. That this matters is not a guess:
`CycleDecomposition.exists_cycle_decomposition_aux` had to write `classical` and
`Fintype.ofFinite` inside its own induction precisely because the gate demanded them.

**That scaffolding is deliberately left in place.** `EvenDegrees` is defined in
`CycleDecomposition`, so the weakened gate cannot be stated upstream of it, and using it
inside `CycleDecomposition` would mean reordering two pushed files to save two lines in a
proof. The deepening is for callers of the chain, and this paragraph exists so that the
next reader does not mistake the leftover `Fintype.ofFinite` for an oversight.

**One does not come off, and that is a theorem rather than a shrug.** Finiteness is
essential: `intPath`, the two-way infinite path on `ℤ`, has **every degree equal to two**
and **no cycle at all**. So "even degrees and an edge" does not force a cycle without
finiteness, and the decomposition fails with it — a graph with an edge cannot be the
union of an empty family, and it has no circuits to put in a nonempty one.

## The argument for the infinite path

Not by a general theory of infinite graphs: by the same Mathlib lemma the decomposition
itself runs on. A cycle has exactly two neighbours at each vertex it visits
(`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`), its support is a finite list, so
that support has a **largest** integer `m` — and both of `m`'s neighbours in the path are
`m - 1` and `m + 1`, of which the second is too big to be on the cycle. One neighbour,
not two.

## Main results

* `SimpleGraph.exists_isCycle_of_evenDegrees` — the gate with `Finite` and no
  decidability.
* `SimpleGraph.exists_ncard_neighborSet_eq_one_of_isAcyclic` — the leaf lemma likewise.
* `EvenDegreeSharp.intPath_evenDegrees` and `EvenDegreeSharp.intPath_isAcyclic` — the
  witness that finiteness is not removable.
* `EvenDegreeSharp.not_exists_cycle_decomposition_intPath` — and hence the decomposition
  itself fails.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## 1. The two hypotheses that come off

Nothing here is new mathematics; `Finite V` and choice rebuild what was assumed. What
changes is the interface. -/

/-- The leaf lemma without a `Fintype` or a `DecidableRel`: a finite acyclic graph with
an edge has a vertex with exactly one neighbour. -/
theorem exists_ncard_neighborSet_eq_one_of_isAcyclic [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) {a b : V} (hab : G.Adj a b) :
    ∃ v, (G.neighborSet v).ncard = 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  obtain ⟨v, hv⟩ := G.exists_degree_one_of_isAcyclic hG hab
  exact ⟨v, by rw [← degree_eq_ncard_neighborSet]; exact hv⟩

/-- **The gate, with `Finite` and nothing else**: a finite graph with all degrees even
and at least one edge contains a cycle. This is the form
`CycleDecomposition.exists_cycle_decomposition_aux` actually wanted; it had to
manufacture a `Fintype` and a `DecidableRel` at the call site to use the old one. -/
theorem exists_isCycle_of_evenDegrees [Finite V] (G : SimpleGraph V) (h : EvenDegrees G)
    (hne : G ≠ ⊥) : ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  exact G.exists_isCycle_of_forall_even_degree_of_ne_bot
    ((G.evenDegrees_iff_forall_even_degree).mp h) hne

end SimpleGraph

namespace EvenDegreeSharp

open SimpleGraph

/-! ## 2. Finiteness does not come off

The two-way infinite path. Every vertex has exactly two neighbours, and there is no
cycle anywhere in it. -/

/-- The two-way infinite path on `ℤ`. -/
def intPath : SimpleGraph ℤ where
  Adj a b := a = b + 1 ∨ b = a + 1
  symm := by rintro a b (h | h) <;> simp [h]
  loopless := ⟨by rintro a (h | h) <;> omega⟩

@[simp] theorem intPath_adj (a b : ℤ) : intPath.Adj a b ↔ a = b + 1 ∨ b = a + 1 := Iff.rfl

theorem intPath_neighborSet (a : ℤ) : intPath.neighborSet a = {a - 1, a + 1} := by
  ext w
  simp only [mem_neighborSet, intPath_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **Every vertex of the infinite path has exactly two neighbours**, so all its degrees
are even. -/
theorem intPath_evenDegrees : EvenDegrees intPath := by
  intro a
  rw [intPath_neighborSet, Set.ncard_pair (by omega : a - 1 ≠ a + 1)]
  exact even_two

theorem intPath_ne_bot : intPath ≠ ⊥ := by
  intro hEq
  have hadj : intPath.Adj 0 1 := by simp
  rw [hEq] at hadj
  exact hadj

/-- **And it has no cycle.** A cycle visits finitely many vertices, so its support has a
largest integer `m`; a cycle has exactly two neighbours at every vertex it visits; but
`m`'s neighbours in the path are `m - 1` and `m + 1`, and the second is larger than the
largest. One neighbour, not two. -/
theorem intPath_isAcyclic : intPath.IsAcyclic := by
  classical
  intro v c hc
  set S : Finset ℤ := c.support.toFinset with hS
  have hvS : v ∈ S := by simp [hS]
  obtain ⟨m, hmS, hmax⟩ := S.exists_max_image id ⟨v, hvS⟩
  have hm : m ∈ c.support := by simpa [hS] using hmS
  have h2 : (c.toSubgraph.neighborSet m).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two hm
  have hsub : c.toSubgraph.neighborSet m ⊆ {m - 1} := by
    intro w hw
    have hadj : intPath.Adj m w := hw.adj_sub
    have hwS : w ∈ c.support := by
      have : w ∈ c.toSubgraph.verts := hw.symm.fst_mem
      simpa [Walk.verts_toSubgraph] using this
    have hle : w ≤ m := hmax w (by simpa [hS] using hwS)
    simp only [intPath_adj] at hadj
    simp only [Set.mem_singleton_iff]
    omega
  have hle : (c.toSubgraph.neighborSet m).ncard ≤ ({m - 1} : Set ℤ).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [h2, Set.ncard_singleton] at hle
  omega

/-! ## 3. So the hypothesis is sharp

Both halves fail: the gate produces no cycle, and the decomposition cannot hold either,
because a graph with an edge is not the union of the empty family and there is no
circuit to put in a nonempty one. -/

/-- **The gate is false without finiteness.** -/
theorem not_exists_isCycle_intPath : ¬ ∃ (v : ℤ) (c : intPath.Walk v v), c.IsCycle := by
  rintro ⟨v, c, hc⟩
  exact intPath_isAcyclic c hc

/-- **And so is the decomposition.** Any list of circuits summing to `intPath` would have
to be nonempty, since `intPath ≠ ⊥`, and its first member would be a circuit of a graph
that has none. -/
theorem not_exists_cycle_decomposition_intPath :
    ¬ ∃ L : List (SimpleGraph ℤ), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = intPath := by
  rintro ⟨L, hcyc, -, hsup⟩
  match L, hcyc, hsup with
  | [], _, hsup => exact intPath_ne_bot (by simpa using hsup.symm)
  | K :: L, hcyc, hsup =>
    obtain ⟨w, p, hp, hK⟩ := hcyc K (List.mem_cons_self ..)
    have hKle : K ≤ intPath := hsup ▸ le_foldr_sup_of_mem (List.mem_cons_self ..)
    exact intPath_isAcyclic (p.mapLe hKle) (Walk.IsCycle.mapLe hKle hp)

end EvenDegreeSharp
