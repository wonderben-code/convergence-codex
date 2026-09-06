import LaplacianClassFamily

/-!
# An upper bound on the multiplicity of every non-zero Laplacian eigenvalue

Five files of this run said, in their *what is NOT here* sections, that this estate had **no upper
bound on the multiplicity of any eigenvalue of any graph**. `ERRATUM 469` records that the sentence
was false when written — the eigenvalue `0` has its multiplicity exactly — and that its true residue
was *no upper bound at a **non-zero** eigenvalue*. **That residue is closed here**, in three lines,
and the ingredients had all been in place since entry 9.

## What is proved

**`disjoint_ker_zero`** — the kernel of the Laplacian meets the eigenspace at any `ν ≠ 0` only at
`0`: a vector in both satisfies `0 · x = ν · x`.

**`finrank_add_card_component_le`** — **so for every finite graph and every non-zero `ν`, the
multiplicity of `ν` plus the number of connected components is at most `|V|`.** The kernel's
dimension **is** the component count
(`FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component`), and two disjoint subspaces of
`ℝ^V` cannot together exceed it.

**`finrank_le_of_connected`** — on a connected graph the bound is `|V| − 1`.

**`nbr_top`, `degree_top`, `finrank_top_eq`** — **and the complete graph's non-zero eigenvalue has
multiplicity exactly `|V| − 1`**, the lower bound coming from
`LaplacianTwinClass.card_sub_one_le_finrank_of_closed_class` (the whole vertex set is one closed
twin class) and the upper from the theorem above.

## What is NOT here

**NO "FIRST" IS CLAIMED FOR THE EXACT MULTIPLICITY, AND THE FIRST DRAFT OF THIS FILE CLAIMED ONE.**
Counted (`ERRATUM 450`; the count was run because `ERRATUM 469`, an hour old, is about exactly this
failure): `CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` already gives an exact
multiplicity — the number `2` — for a non-zero eigenvalue on the cycle, and
`TorusRealMultiplicity` and `BoxEigenspaceDimension` give exact multiplicities as **fibre
cardinalities** for the torus and the box. **What is new is the route**: a multiplicity pinned by
squeezing a lower bound against an upper one, rather than computed as the size of a fibre.

**THE BOUND IS NOT SHARP IN GENERAL, AND NOTHING HERE SAYS WHEN IT IS.** `|V| − 1` is attained by
the complete graph and by nothing else this file examines. On the path graph every eigenvalue is
simple, so the bound is off by `|V| − 2`. **No characterisation of the graphs attaining it is
offered**, and the obvious guess — that only the complete graph attains it — is **not proved**. Not
attempted, no cost claimed (`ERRATUM 246`).

**NOTHING ABOUT TWO NON-ZERO EIGENVALUES.** The argument uses the kernel and **one** other
eigenspace. Summing over all distinct eigenvalues would give the far stronger *the multiplicities
sum to `|V|`*, which is the spectral theorem and **is not proved here or anywhere in this estate for
a graph Laplacian**.

**NO PROPAGATOR, NO MASS, NO MEASURE.** This is graph theory throughout. The corresponding bound for
`massive` and `green` follows from `FieldLaplacianSimple.ker_massive_eq` and the inversion, and **is
not stated**, because nothing needs it yet.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `ν ≠ 0` is taken by the two bounds and is
load-bearing — at `ν = 0` the statement is `2 × (component count) ≤ |V|`, which is false for a
connected graph on one vertex. `finrank_le_of_connected` takes connectedness; the general bound
takes no connectivity, no mass and no propagator.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianMultiplicityBound

open SimpleGraph Matrix GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The kernel and any other eigenspace are disjoint -/

theorem disjoint_ker_zero {ν : ℝ} (hν : ν ≠ 0) :
    Disjoint (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have h0 := (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hx
  have h1 := (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hy
  have h2 : (0 : ℝ) • x = ν • x := h0.symm.trans h1
  rw [zero_smul] at h2
  rcases smul_eq_zero.mp h2.symm with h | h
  · exact absurd h hν
  · exact h

/-! ## 2. So every non-zero eigenvalue's multiplicity is bounded above -/

/-- **AN UPPER BOUND ON THE MULTIPLICITY OF EVERY NON-ZERO LAPLACIAN EIGENVALUE OF EVERY FINITE
GRAPH.** The eigenspace at `0` has dimension the number of connected components
(`FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component`) and meets any other
eigenspace only at `0`, so the two together fit inside `ℝ^V`. -/
theorem finrank_add_card_component_le {ν : ℝ} (hν : ν ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id))
      + Fintype.card G.ConnectedComponent ≤ Fintype.card V := by
  have h := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_ker_zero (G := G) hν)
  rw [FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component,
    Module.finrank_pi] at h
  omega

/-- **AND ON A CONNECTED GRAPH IT IS `|V| − 1`.** -/
theorem finrank_le_of_connected (hconn : G.Connected) {ν : ℝ} (hν : ν ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) + 1
      ≤ Fintype.card V := by
  have hcomp : Fintype.card G.ConnectedComponent = 1 := by
    rw [← FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component]
    exact FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected hconn
  have h := finrank_add_card_component_le (G := G) hν
  omega

/-! ## 3. The first exact multiplicity of a non-zero eigenvalue in this estate -/

theorem nbr_top (n : ℕ) (u : Fin (n + 3)) :
    (⊤ : SimpleGraph (Fin (n + 3))).neighborFinset u = Finset.univ.erase u := by
  ext w
  simp [SimpleGraph.mem_neighborFinset, ne_comm]

theorem degree_top (n : ℕ) (u : Fin (n + 3)) :
    (⊤ : SimpleGraph (Fin (n + 3))).degree u = n + 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, nbr_top,
    Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
  omega

/-- **THE COMPLETE GRAPH ON `n + 3` VERTICES HAS ITS NON-ZERO LAPLACIAN EIGENVALUE WITH
MULTIPLICITY EXACTLY `n + 2`.** The lower bound is the twin class — the whole vertex set is one —
and the upper bound is §2. **No "first" is claimed**, and the first draft of this docstring claimed
one: counted (`ERRATUM 450`, and `ERRATUM 469` is why it was counted),
`CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` already gives an exact multiplicity —
the number `2` — for a non-zero eigenvalue on the cycle. What is new is the **route**: this is a
multiplicity pinned by **squeezing** a lower bound against an upper one, where every earlier exact
multiplicity in this estate was computed as the cardinality of a fibre. -/
theorem finrank_top_eq (n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' ((⊤ : SimpleGraph (Fin (n + 3))).lapMatrix ℝ)
      - ((n : ℝ) + 3) • LinearMap.id)) = n + 2 := by
  have hval : (((⊤ : SimpleGraph (Fin (n + 3))).degree ⟨0, by omega⟩ : ℝ) + 1) = (n : ℝ) + 3 := by
    rw [degree_top]
    push_cast
    ring
  have hlow := LaplacianTwinClass.card_sub_one_le_finrank_of_closed_class
    (G := (⊤ : SimpleGraph (Fin (n + 3)))) (S := Finset.univ) (u₀ := ⟨0, by omega⟩)
    (fun u _ => (LaplacianClosedTwins.closed_top u).trans
      (LaplacianClosedTwins.closed_top _).symm)
  rw [hval, Finset.card_univ, Fintype.card_fin] at hlow
  have hup := finrank_le_of_connected (G := (⊤ : SimpleGraph (Fin (n + 3))))
    SimpleGraph.connected_top (ν := (n : ℝ) + 3) (by positivity)
  rw [Fintype.card_fin] at hup
  omega

end LaplacianMultiplicityBound
