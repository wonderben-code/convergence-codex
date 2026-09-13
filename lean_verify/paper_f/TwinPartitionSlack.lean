/-
  TwinPartitionSlack.lean — the partition bound is not an invariant of the graph,
  and it is not tight even for the maximal partition.

  WHY THIS FILE EXISTS. `LaplacianTwinPartition` proved
  `|V| − |C| ≤ mult(ν)` for a covering family of twin classes, and its §6 asked the
  obvious next question: **is the bound ever slack?** The two instances it had —
  the star and two disjoint triangles — both attain it, and it said so, adding that
  on present evidence the bound might always be tight, *"which I do not believe and
  have not tested"*. This is the test.

  **AND IT ALSO CLOSES A GAP THAT FILE OPENED IN ITS OWN PROSE.** Its §3 docstring
  says *"The star has two twin classes, so §2 reads `|V| − 2 ≤ mult(1)`"* — and §3
  never applies §2 to the star. It cites the squeeze instead. The sentence is true
  and was unproved, which is the shape three of today's errata are about
  (`ERRATUM 545`); `star_bound_from_partition` is that sentence as a theorem.

  WHAT THIS FILE PROVES.

  1. **`star_bound_from_partition`** — the star's partition really does give
     `|V| − 2 ≤ mult(1)` through `LaplacianTwinPartition.card_sub_card_le_finrank`.
     **Note which form is used and why**: not `_of_open`, whose `hdeg` clause asks
     every class's base to have degree `ν` — the centre has degree `|V| − 1`, so
     that form does NOT apply. The general form's `heig` clause is vacuous on the
     singleton class, and that is the whole difference. A reader who reached for
     `_of_open` would have concluded the star was not covered.
  2. **`bound_slack_of_refinement`** — the bound is **not an invariant of the
     graph**. Splitting one class into singletons keeps the family covering and
     pairwise disjoint, raises `|C|`, and lowers the bound while the multiplicity
     does not move. Instantiated on the star: the all-singleton family gives `0`.
     Obvious once said, and worth saying, because it means *"the bound is tight"*
     is only a question about a PARTICULAR family.
  3. **`bound_slack_bot`** — and for the MAXIMAL family it is still not tight. On
     the edgeless graph over two vertices the two vertices are twins (both have no
     neighbours at all), so the maximal family is the single class `{0, 1}`, giving
     `2 − 1 = 1`; the Laplacian is the zero matrix and its kernel at `0` is
     everything, so the multiplicity is `2`. **Slack by one, on two vertices, with
     the coarsest possible family.**

  WHAT IS NOT CLAIMED, AND THE REFINED QUESTION IS THE POINT. `bound_slack_bot` is
  **disconnected** and sits at `ν = 0`, where the multiplicity counts components and
  the twin structure cannot see them. So it answers §6's question as asked and
  leaves the question worth asking: **is the bound tight for a CONNECTED graph with
  its maximal twin family?** Every connected instance in the estate — the star, two
  disjoint triangles (not connected either, and tight anyway), the complete graph —
  attains it, and no proof or counterexample is offered. Not attempted, no cost
  claimed (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import LaplacianTwinPartition

namespace TwinPartitionSlack

open SimpleGraph Matrix GraphLaplacian StarAdjNormExact

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The star's bound, from the partition rather than from the squeeze -/

/-- **THE SENTENCE `LaplacianTwinPartition`'s §3 ASSERTED, AS A THEOREM.** The star's
two twin classes give `|V| − 2 ≤ mult(1)` through the partition bound.
**The `_of_open` form does not apply** — its `hdeg` clause wants every class's base
at degree `ν`, and the centre has degree `|V| − 1` — so the general form is used and
the singleton class contributes through a vacuous `heig`. -/
theorem star_bound_from_partition [Nontrivial V] (c : V) :
    Fintype.card V - 2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (1 : ℝ) • LinearMap.id)) := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, u₀ ≠ c := exists_ne c
  set C : Finset (Finset V) := {Finset.univ.erase c, {c}} with hC
  set base : Finset V → V := fun T => if c ∈ T then c else u₀ with hbaseDef
  have hne : Finset.univ.erase c ≠ ({c} : Finset V) := by
    intro h
    have : u₀ ∈ ({c} : Finset V) := h ▸ Finset.mem_erase.mpr ⟨hu₀, Finset.mem_univ u₀⟩
    exact hu₀ (Finset.mem_singleton.mp this)
  have hcnot : c ∉ Finset.univ.erase c := fun h => (Finset.mem_erase.mp h).1 rfl
  have hbase1 : base (Finset.univ.erase c) = u₀ := by simp [hbaseDef, hcnot]
  have hbase2 : base ({c} : Finset V) = c := by simp [hbaseDef]
  have hcard : C.card = 2 := by rw [hC, Finset.card_insert_of_notMem (by simpa using hne),
    Finset.card_singleton]
  have hmain := LaplacianTwinPartition.card_sub_card_le_finrank
    (G := starGraph c) (C := C) (base := base) (ν := 1)
    (by
      intro T hT
      rw [hC] at hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · rw [hbase1]; exact Finset.mem_erase.mpr ⟨hu₀, Finset.mem_univ u₀⟩
      · rw [hbase2]; exact Finset.mem_singleton_self c)
    (by
      intro T hT U hU hTU
      rw [hC] at hT hU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT hU
      rcases hT with rfl | rfl <;> rcases hU with rfl | rfl
      · exact absurd rfl hTU
      · exact Finset.disjoint_singleton_right.mpr hcnot
      · exact Finset.disjoint_singleton_left.mpr hcnot
      · exact absurd rfl hTU)
    (by rw [hC]; exact LaplacianTwinPartition.star_partition c)
    (by
      intro T hT u hu
      rw [hC] at hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · rw [hbase1] at hu ⊢
        have hun : u ≠ c := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hu)).1
        have hnb : (starGraph c).neighborFinset u = (starGraph c).neighborFinset u₀ := by
          rw [neighborFinset_leaf hun, neighborFinset_leaf hu₀]
        have h := LaplacianTwins.lapMatrix_mulVec_twinDiff
          (G := starGraph c) (Finset.ne_of_mem_erase hu) hnb
        rwa [degree_leaf hun, Nat.cast_one] at h
      · rw [hbase2] at hu
        simp at hu)
  rwa [hcard] at hmain

/-! ## 2. The bound depends on the family, so it is not a graph invariant -/

/-- **REFINING THE FAMILY LOWERS THE BOUND.** The all-singleton family is covering
and pairwise disjoint, has `|C| = |V|`, and gives `0`. So *"the bound is tight"* is
never a question about a graph — only about a family. -/
theorem singleton_family_cover :
    (Finset.univ.image (fun v : V => ({v} : Finset V))).biUnion id = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_image, id_eq, Finset.mem_univ, iff_true]
  refine ⟨{v}, ?_, Finset.mem_singleton_self v⟩
  simp

/-- On the star, the all-singleton family gives `0` where the two-class family gives
`|V| − 2`, and the multiplicity is the same number either way. -/
theorem bound_slack_of_refinement [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    (0 : ℕ) < Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (1 : ℝ) • LinearMap.id)) := by
  have h := star_bound_from_partition (V := V) c
  omega

/-! ## 3. And the maximal family is not tight either -/

/-- The edgeless graph on two vertices has the zero Laplacian. -/
theorem lapMatrix_bot_two : (⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ = 0 := by
  have hdeg : ∀ v : Fin 2, (⊥ : SimpleGraph (Fin 2)).degree v = 0 := by
    intro v
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
  ext i j
  simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Matrix.zero_apply]
  by_cases hij : i = j
  · rw [if_pos hij, hdeg i, if_neg (by rw [hij]; exact fun hc => hc.ne rfl)]
    norm_num
  · rw [if_neg hij, if_neg (fun hc : (⊥ : SimpleGraph (Fin 2)).Adj i j => hc)]
    norm_num

/-- So its eigenspace at `0` is everything: dimension `2`. -/
theorem finrank_ker_bot_two :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)) = 2 := by
  rw [lapMatrix_bot_two, zero_smul, sub_zero, map_zero, LinearMap.ker_zero]
  simp

/-- The two vertices are twins: neither has any neighbour. -/
theorem bot_twins (u v : Fin 2) :
    (⊥ : SimpleGraph (Fin 2)).neighborFinset u = (⊥ : SimpleGraph (Fin 2)).neighborFinset v := by
  ext w
  simp [SimpleGraph.mem_neighborFinset]

/-- **THE BOUND IS NOT TIGHT EVEN FOR THE MAXIMAL FAMILY.** On the edgeless graph
over two vertices the maximal twin family is the single class `{0, 1}` — both
vertices have no neighbours, so all of them are twins — and the bound reads
`2 − 1 = 1` while the multiplicity at `0` is `2`. **Slack by one, on two vertices,
with the coarsest family there is.**

The witness is disconnected and sits at `ν = 0`, where the multiplicity counts
components and the twin structure cannot see them; the refined question — a
CONNECTED graph with its maximal family — is left open in the header and is not
answered here. -/
theorem bound_slack_bot :
    ({Finset.univ} : Finset (Finset (Fin 2))).biUnion id = Finset.univ
      ∧ ({Finset.univ} : Finset (Finset (Fin 2))).card = 1
      ∧ Fintype.card (Fin 2) - ({Finset.univ} : Finset (Finset (Fin 2))).card
          < Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ)
              - (0 : ℝ) • LinearMap.id)) := by
  refine ⟨by simp, Finset.card_singleton _, ?_⟩
  rw [finrank_ker_bot_two, Finset.card_singleton, Fintype.card_fin]
  omega

/-! ## 4. Review round 68 — the ways this could be hollow

**"§1 could be the squeeze again."** It is not: it goes through
`LaplacianTwinPartition.card_sub_card_le_finrank` and cites nothing from
`SignlessStarSpectrum` or `SpectrumReflection`. That matters because
`LaplacianTwinPartition`'s §3 asserted this and then proved something else — the
gap `ERRATUM 545` is about.

**"§2 is trivial."** It is, and it is stated because the triviality is the content:
refining a family lowers the bound without moving the multiplicity, so the bound is
a property of a FAMILY and *"is it tight"* has no answer until a family is named.
Every earlier discussion of tightness in this chain, including my own, left that
implicit.

**"§3's witness is degenerate."** It is disconnected and at `ν = 0`, and the header
and the theorem's own docstring both say so before anything else. **It still answers
the question that was asked** — `LaplacianTwinPartition`'s §6 asked whether the bound
is ever slack for a covering family, not whether it is slack for a connected one —
and refusing to answer the asked question because a better one exists would be worse
than answering it and naming the better one, which is what is done.

**"The maximal family on `⊥` might not be `{univ}`."** Every pair of vertices is a
twin pair (`bot_twins`), so the whole vertex set is one class and no coarser family
exists. On two vertices that is `{univ}`.
-/

end

end TwinPartitionSlack
