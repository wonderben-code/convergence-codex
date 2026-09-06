import FieldLaplacianSimple
import FieldSymmetryEdgeless

/-!
# Walking through the door, and showing it is a door and not a wall

`FieldLaplacianSimple` restated the whole symmetry chain on a hypothesis about the graph's
Laplacian — *every eigenspace is at most a line* — and fenced the honest thing: **the door is open
and nothing has been carried through it, not even the line.** Two questions follow, and both are
answered here. Does any graph satisfy the hypothesis? And does any graph fail it?

## What is proved

**`finrank_lapMatrix_le_one_line`** — **the path graph satisfies it**, stated with no mass and no
propagator in it. The estate already had the bound for the *massive* operator on a line
(`FieldSimpleCriterion.finrank_le_one_line`) and it holds at **every** mass including `0`, where the
massive operator **is** the Laplacian; `FieldLaplacianSimple.ker_massive_eq` at `m = 0` is the whole
step.

**`card_symmetries_line_via_lapMatrix`, `graphAut_involutive_line_via_lapMatrix`** — **so the count
and the involution theorem hold on the path graph through the graph-only route.** These duplicate
`FieldLineCount.card_symmetries_line` and `FieldSimpleAut.graphAut_involutive_line` **on purpose**:
the point is not the conclusions, which were already had, but that the **new hypothesis reaches
them**. A door nobody has walked through is not known to be a door.

**`ker_lapMatrix_zero_of_no_adj`, `not_finrank_le_one_of_no_adj`** — **and the edgeless graph on two
or more vertices fails it**, maximally: its Laplacian is `0`, so the eigenspace at `0` is the whole
space. **So the hypothesis is a real dividing line** — not vacuous, not universal — and the two
extremes are both realised by graphs this estate has already studied.

## What is NOT here

**NO GRAPH OTHER THAN THE PATH IS SHOWN TO SATISFY IT.** That is unchanged, and it is the standing
question on `UNLOCK_WATCHLIST`. **Nothing here is a characterisation**, and finding a second example
would not be one either.

**THE CONVERSE OF THE CRITERION IS STILL NOT PROVED.** *Every eigenspace is at most a line* implies
a simple spectrum (`FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one`); the reverse — a
simple spectrum implies every eigenspace is at most a line — is true for a symmetric matrix because
the eigenspaces span, and **is not proved anywhere in this estate**. It is the same missing step
`FieldLaplacianSimple` fenced. Not attempted, no cost claimed (`ERRATUM 246`).

⚠ **IT IS PROVED THE SAME DAY, AND THE PARAGRAPH ABOVE IS KEPT AS WRITTEN** (`ERRATUM 94`).
`FieldSimpleConverse.finrank_massive_le_one_of_eigenvalues_injective` is the reverse implication,
by exactly the argument the paragraph names; `FieldSimpleConverse.finrank_lapMatrix_le_one_iff`
makes this file's hypothesis and a simple propagator spectrum **the same condition**, and
`FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective` gives the counting form with no mass
and no hypothesis at all. **The characterisation fence above it does not move.**

**THE EDGELESS RESULT IS NOT A DICHOTOMY.** It exhibits one failing family; it does **not** say the
hypothesis fails exactly on graphs with a degenerate spectrum, nor connect to
`FieldSymmetryEdgeless`'s dichotomy beyond sharing its hypothesis. **No claim is made that the two
statements about edgeless graphs are two faces of one theorem**, though they plainly rhyme.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a non-zero mass is taken by
`card_symmetries_line_via_lapMatrix` and `graphAut_involutive_line_via_lapMatrix` — **two of the
five** — and only because the results they invoke do. `finrank_lapMatrix_le_one_line`,
`ker_lapMatrix_zero_of_no_adj` and `not_finrank_le_one_of_no_adj` take **no mass at all**: they are
statements about a Laplacian, and the first is proved *by setting the mass to zero*, which is
allowed precisely because `finrank_le_one_line` never needed it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldLaplacianInstance

open Matrix GraphLaplacian BoxGraph FieldSimpleCriterion FieldLaplacianSimple MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Walking through the door: the path graph -/

/-- **THE PATH GRAPH'S LAPLACIAN HAS EVERY EIGENSPACE A LINE**, stated with no mass and no
propagator in it. -/
theorem finrank_lapMatrix_le_one_line (k : ℕ) (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph 1 (k + 1)).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  have h := finrank_le_one_line k 0 ν
  rw [ker_massive_eq] at h
  have hz : (ν - (0 : ℝ) ^ 2) = ν := by norm_num
  rwa [hz] at h

/-- **SO THE COUNT HOLDS ON THE PATH GRAPH THROUGH THE GRAPH-ONLY HYPOTHESIS.** -/
theorem card_symmetries_line_via_lapMatrix {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    Nat.card (FieldLineCount.symmetries (boxGraph 1 (k + 1)) mass)
      = 2 ^ Fintype.card (Site 1 (k + 1)) :=
  card_symmetries_of_lapMatrix hmass (finrank_lapMatrix_le_one_line k)

/-- **AND SO DOES THE INVOLUTION THEOREM.** -/
theorem graphAut_involutive_line_via_lapMatrix {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0)
    {θ : Site 1 (k + 1) ≃ Site 1 (k + 1)}
    (hθ : FieldAutInvariance.IsGraphAut (boxGraph 1 (k + 1)) θ) (p : Site 1 (k + 1)) :
    θ (θ p) = p :=
  graphAut_involutive_of_lapMatrix hmass (finrank_lapMatrix_le_one_line k) hθ p

/-! ## 2. And the hypothesis is a real dividing line: it fails on the edgeless graph -/

theorem ker_lapMatrix_zero_of_no_adj (h : ∀ i j : V, ¬ G.Adj i j) :
    LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id) = ⊤ := by
  rw [FieldSymmetryEdgeless.lapMatrix_eq_zero_of_no_adj h]
  ext x
  simp

/-- **ON AN EDGELESS GRAPH WITH TWO OR MORE VERTICES THE HYPOTHESIS FAILS**: the eigenspace at
zero is the whole space. -/
theorem not_finrank_le_one_of_no_adj (h : ∀ i j : V, ¬ G.Adj i j)
    (hcard : 2 ≤ Fintype.card V) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  have h0 := hdim 0
  rw [ker_lapMatrix_zero_of_no_adj h, finrank_top, Module.finrank_pi] at h0
  omega

end FieldLaplacianInstance
