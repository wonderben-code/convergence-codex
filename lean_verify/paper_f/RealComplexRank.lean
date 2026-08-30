import RealComplexKernel
import LaplacianRank

/-!
# The rank version: complexifying a real matrix does not change its rank

`RealComplexKernel` closed the item that asked whether a real matrix's kernel keeps its dimension
under complexification, and it closed it **without** the fact the item had sketched — that
`Matrix.rank` is invariant under base change — because the pinned Mathlib has no such lemma and the
kernel route needed none. That file then fenced the omission in terms:

> **No statement about `Matrix.rank` under base change.** The rank statement follows from
> `finrank_ker_cx` and `LaplacianRank.rank_add_finrank_ker` **only after that lemma is generalised
> from `ℝ` to an arbitrary field**, which it is not, and **that generalisation is not done here**.

Both halves of that sentence are discharged here, and it took the shape the sentence predicted.

> **`LaplacianRank.rank_add_finrank_ker` is now stated over any field** — generalised in place
> (`ERRATUM 337`), its proof unchanged to the character, because it never used a property of `ℝ`.
> Every existing caller instantiates at `K = ℝ` and none moved.
>
> **`rank_cx`** — hence `(cx A).rank = A.rank` for every real square matrix: rank-nullity over `ℂ`,
> rank-nullity over `ℝ`, and `finrank_ker_cx` between the two nullities. Three facts and `omega`.
>
> **`cx_rank_lapMatrix_add_card_connectedComponent`, `cx_rank_signlessLap_add_card_bipComp`** — so
> `LaplacianRank`'s two counting theorems hold for the **complexified** Laplacians, with the same
> component counts on the right. These are the first statements in the estate relating a complex
> matrix's rank to a graph's combinatorics.

**WHY THE SKETCH WAS RIGHT THIS TIME AND WHAT THAT IS WORTH.** The item filed two units ago guessed
that the route ran through base-change invariance of the rank; that guess was wrong about the
*kernel* statement, which needed no rank at all. It was right about this one — but only because
this statement **is** the rank statement, so the sketch was not a prediction so much as a
restatement. **No credit is claimed for the forecast**, and the record of the earlier miss stands
where it was written.

## What is NOT here

**This is not base-change invariance of rank in general.** `rank_cx` is about `ℝ → ℂ` and about the
estate's own `MatrixLoewner.cx`; nothing below is stated for an arbitrary field extension or an
arbitrary ring hom, and the proof route — real dimensions counted twice — **does not generalise to
one**, since it uses `finrank ℝ ℂ = 2`.

**No non-square case.** `rank_add_finrank_ker` is stated for `Matrix V V K`, so everything here is,
and the rectangular statement is not touched.

**No new graph theorem.** The two corollaries move `LaplacianRank`'s counts across the field and
add no combinatorics; the component counts on their right-hand sides are the ones already proved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealComplexRank

open Matrix SimpleGraph LaplacianSignless LaplacianSignlessKernel
open RealComplexKernel

/-- **COMPLEXIFYING A REAL SQUARE MATRIX DOES NOT CHANGE ITS RANK.** Rank-nullity on each side and
`finrank_ker_cx` between the two nullities. **No `DecidableEq` in the statement**: `Matrix.rank`
does not need one, and the `toLin'` the proof passes through gets it from `classical` — the linter
asked at the first build, as it has three times this session. -/
theorem rank_cx {V : Type*} [Fintype V] (A : Matrix V V ℝ) :
    (MatrixLoewner.cx A).rank = A.rank := by
  classical
  have hC := LaplacianRank.rank_add_finrank_ker (MatrixLoewner.cx A)
  have hR := LaplacianRank.rank_add_finrank_ker A
  have hk := finrank_ker_cx A
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **THE ORDINARY LAPLACIAN'S RANK, OVER `ℂ`.** `rank (cx L) + #components = |V|`, for every
finite graph and with no hypothesis. -/
theorem cx_rank_lapMatrix_add_card_connectedComponent (G : SimpleGraph V) [DecidableRel G.Adj] :
    (MatrixLoewner.cx (G.lapMatrix ℝ)).rank + Fintype.card G.ConnectedComponent
      = Fintype.card V := by
  rw [rank_cx]
  exact LaplacianRank.rank_lapMatrix_add_card_connectedComponent G

/-- **AND THE SIGNLESS LAPLACIAN'S**, with the two-colourable components on the right. -/
theorem cx_rank_signlessLap_add_card_bipComp (G : SimpleGraph V) [DecidableRel G.Adj] :
    (MatrixLoewner.cx (signlessLap G)).rank + Fintype.card (BipComp G) = Fintype.card V := by
  rw [rank_cx]
  exact LaplacianRank.rank_signlessLap_add_card_bipComp G

end RealComplexRank
