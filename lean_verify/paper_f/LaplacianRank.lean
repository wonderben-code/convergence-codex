import LaplacianSignlessKernel

/-!
# The ranks of `L = D − A` and `Q = D + A`, counted by components

Two counts already exist and neither has ever been stated as a rank. Mathlib's
`card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` gives the **kernel** dimension of the
ordinary Laplacian as the number of connected components, and
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` gives the kernel dimension of the
signless Laplacian as the number of **two-colourable** components. Rank-nullity turns each into a
statement about the rank, which is the form the textbooks state and the form a caller wanting a
dimension of an image needs.

> **`rank_lapMatrix_add_card_connectedComponent`** — `rank L + #components = |V|`.
>
> **`rank_signlessLap_add_card_bipComp`** — `rank Q + #(two-colourable components) = |V|`.
>
> **`rank_lapMatrix_le_rank_signlessLap`** — and therefore `rank L ≤ rank Q`, on **every**
> finite graph, because the two-colourable components are a subtype of the components.

**THE ADDITIVE FORM IS THE STATEMENT AND THE SUBTRACTED FORM IS THE COROLLARY**, not the other way
round. `Fintype.card V - Fintype.card G.ConnectedComponent` is truncated subtraction on `ℕ`, so
the subtracted form is only equivalent to the additive one once the inequality is known; stating the
sum first means the corollary is a rewrite rather than a second proof, and means the theorem says
what it means when a reader meets it out of context.

**WHAT IS NOT PROVED HERE, so the file is not read as more than it is.** Nothing about eigenvalues.
The rank of a positive semidefinite matrix is the number of nonzero eigenvalues with multiplicity,
and both of these are positive semidefinite (`SimpleGraph.posSemidef_lapMatrix`,
`LaplacianSignlessDefinite.signlessLap_posSemidef`), so each theorem below has a spectral
reading — **that reading is not formalised and no file claims it.** What is proved is the rank
of a matrix, by rank-nullity from a kernel dimension somebody else counted.
-/

namespace LaplacianRank

open Matrix SimpleGraph LaplacianSignless LaplacianSignlessDefinite LaplacianSignlessKernel

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **RANK-NULLITY FOR A SQUARE MATRIX OVER ANY FIELD**, in the `toLin'` form both kernel counts
are stated in. Mathlib's `LinearMap.finrank_range_add_finrank_ker` is the content; what this adds is
the translation, since `Matrix.rank` is defined through `mulVecLin` and the counts are stated
through `Matrix.toLin'`. The two are equal by `Matrix.toLin'_apply'` and that is the whole proof.

**STATED OVER A FIELD FROM 2026-08-30, AND IT WAS `ℝ` ONLY BEFORE** (`ERRATUM 337`: extract, do not
copy). `RealComplexRank` wants exactly this statement over `ℂ` in order to compare a real matrix's
rank with its complexification's, and the proof never used a single property of `ℝ`. Every caller
below is unchanged and instantiates at `K = ℝ`. -/
theorem rank_add_finrank_ker {K : Type*} [Field K] (A : Matrix V V K) :
    A.rank + Module.finrank K (LinearMap.ker (Matrix.toLin' A)) = Fintype.card V := by
  have h : A.rank = Module.finrank K (LinearMap.range (Matrix.toLin' A)) := by
    rw [Matrix.toLin'_apply']
    rfl
  rw [h, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE RANK OF THE ORDINARY LAPLACIAN.** `rank L + #components = |V|`, for every finite graph
and with no hypothesis. Mathlib counts the kernel; this is that count as a rank. -/
theorem rank_lapMatrix_add_card_connectedComponent :
    (G.lapMatrix ℝ).rank + Fintype.card G.ConnectedComponent = Fintype.card V := by
  rw [G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  exact rank_add_finrank_ker _

/-- **THE RANK OF THE SIGNLESS LAPLACIAN.** `rank Q + #(two-colourable components) = |V|`, for
every finite graph and with no hypothesis. The index set is the smaller one, and
`LaplacianSignlessKernel`'s header says why: a constant is in `L`'s kernel on every component,
while only a bipartite component contributes to `Q`'s. -/
theorem rank_signlessLap_add_card_bipComp :
    (signlessLap G).rank + Fintype.card (BipComp G) = Fintype.card V := by
  rw [card_bipartiteComponent_eq_finrank_ker G]
  exact rank_add_finrank_ker _

/-- **THE SUBTRACTED FORM**, a corollary of the sum and not a second proof. -/
theorem rank_lapMatrix :
    (G.lapMatrix ℝ).rank = Fintype.card V - Fintype.card G.ConnectedComponent := by
  have h := rank_lapMatrix_add_card_connectedComponent G
  omega

/-- **THE SUBTRACTED FORM FOR `Q`.** -/
theorem rank_signlessLap :
    (signlessLap G).rank = Fintype.card V - Fintype.card (BipComp G) := by
  have h := rank_signlessLap_add_card_bipComp G
  omega

/-- **THE TWO-COLOURABLE COMPONENTS ARE AT MOST ALL THE COMPONENTS**, which is a `Fintype.card`
fact about a subtype and is stated because the comparison below is the only place either count is
put beside the other. -/
theorem card_bipComp_le_card_connectedComponent :
    Fintype.card (BipComp G) ≤ Fintype.card G.ConnectedComponent :=
  Fintype.card_subtype_le _

/-- **AND SO `rank L ≤ rank Q` ON EVERY FINITE GRAPH.** Not an estimate and not a spectral
statement: the two ranks are `|V|` minus two component counts, and one count is a subtype of the
other. Equality holds exactly when every component is two-colourable, i.e. when `G` is bipartite —
`rank_eq_iff_forall_colorable` below. -/
theorem rank_lapMatrix_le_rank_signlessLap :
    (G.lapMatrix ℝ).rank ≤ (signlessLap G).rank := by
  have hL := rank_lapMatrix_add_card_connectedComponent G
  have hQ := rank_signlessLap_add_card_bipComp G
  have hc := card_bipComp_le_card_connectedComponent G
  omega

/-- **THE EQUALITY CASE.** The two ranks agree exactly when every connected component is
two-colourable. Stated with the counts rather than with a bipartiteness predicate, because that is
what the two theorems above actually compare. -/
theorem rank_eq_iff_card_eq :
    (G.lapMatrix ℝ).rank = (signlessLap G).rank
      ↔ Fintype.card (BipComp G) = Fintype.card G.ConnectedComponent := by
  have hL := rank_lapMatrix_add_card_connectedComponent G
  have hQ := rank_signlessLap_add_card_bipComp G
  omega

/-- **FULL RANK IS POSITIVE DEFINITENESS**, which is `LaplacianSignlessKernel`'s zero case read
through rank-nullity. `Q` has rank `|V|` exactly when no component is two-colourable. -/
theorem rank_signlessLap_eq_card_iff_posDef :
    (signlessLap G).rank = Fintype.card V ↔ (signlessLap G).PosDef := by
  rw [← finrank_ker_eq_zero_iff_posDef G, ← card_bipartiteComponent_eq_finrank_ker G]
  have hQ := rank_signlessLap_add_card_bipComp G
  omega

/-- **AND `L` IS NEVER OF FULL RANK ON A NONEMPTY GRAPH**, because a component always exists and
always contributes a constant. The contrast with the line above is the whole point of the pair:
`Q` can be nonsingular and `L` cannot. -/
theorem rank_lapMatrix_lt_card [Nonempty V] :
    (G.lapMatrix ℝ).rank < Fintype.card V := by
  have hL := rank_lapMatrix_add_card_connectedComponent G
  have : 0 < Fintype.card G.ConnectedComponent :=
    Fintype.card_pos_iff.2 ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  omega

end

end LaplacianRank
