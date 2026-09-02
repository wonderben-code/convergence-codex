import SqrtGreenOpNorm

/-!
# The operator norm of the graph Laplacian, and what it costs W1's second alternative

`LaplacianDegreeBound.lapMatrix_le_smul_one` bounds `G.lapMatrix ℝ` **in the Loewner order** by
`2Δ • 1`, and `massive_le_smul_one` does the same for `massive G m`. Neither says anything about a
norm, because until `PosSemidefNormBound.l2_opNorm_le` this estate could not turn one into the
other over `ℝ`. This file spends that theorem at the estate's central operator.

**WHY THIS FILE EXISTS AND NOT AS A COROLLARY IN PASSING.** `PROOF_STRATEGY` §6 question 1 — *what
did this just unlock?* — asked against `WALLS.md` rather than answered from memory. W1 names
"Neumann" three times and **two of the three are superseded, which the block itself records and a
faster reading would have missed** (`ERRATUM 421`): the entrywise-non-negativity route was done by
`GraphGreenPositive.nonneg_of_mulVec_nonneg`, a discrete maximum principle, and the random-walk
route carries an `AMENDED 9 AUG 2026` saying it "was never costed and never needed: the proof went
by the half-space decomposition and the Loewner order instead". **The one that stands is W1's own
`WHAT WOULD HAVE TO EXIST`**: *"a bound on the **Neumann tail of the Green function**, of which
`green_eq_two_terms` is now the exact closed form"*, in a wall whose diagnosis is that *"the
remaining step is an **estimate** … what is left will not convert"* to algebra. That is the live
consumer, and §3 supplies one of its factors.

**WHAT THE COSTING SAYS.**
* **The analytic half of a Neumann-type estimate is now one line.** `norm_lapMatrix_le` :
  `‖G.lapMatrix ℝ‖ ≤ 2Δ` from a degree bound, and on the box `≤ 4d` **at every side length**.
  Nothing in the pinned Mathlib states a bound of that shape — three spellings probed, 0 matches
  each, evidence only as good as the patterns (`ERRATUM 79`) — and nothing under `paper_f/` did.
* **§3 IS THE FACTOR W1 ACTUALLY NAMES.** `green_eq_two_terms` writes the tail as
  `green · A · Dinv · A · Dinv`, and `norm_green_le` : `‖green G m‖ ≤ (m²)⁻¹` bounds the first
  factor, at every finite graph and with no degree hypothesis. **Nothing anywhere in this estate
  or the pinned library bounded `‖green‖` before** — probed, 0 matches.
* **THE OTHER TWO FACTORS ARE NOT PROVED HERE AND ARE NAMED SO THAT NOBODY HAS TO GUESS.**
  `‖Dinv G m‖` is a diagonal matrix's norm and `Matrix.l2_opNorm_diagonal` gives it without this
  file's tool; `‖G.adjMatrix ℝ‖` is **not** reachable from `l2_opNorm_le`, because the adjacency
  matrix is not positive semidefinite and the theorem's first hypothesis fails. Neither is
  attempted, neither is costed (`ERRATUM 246`), and no estimate is offered (`ERRATUM 183`).
* **AND BOUNDING THE TAIL IS STILL NOT W1'S STEP.** The wall asks for the tail to be smaller than
  the cross form's negative direction — a COMPARISON between two quantities — and this file
  computes no cross form and makes no comparison. **A factor of a bound is not the bound, and a
  bound is not the comparison.**
* **A NEUMANN CRITERION, WITH ITS REGIME VISIBLE.** `norm_lapMatrix_boxGraph_lt_of_lt` gives
  `‖lapMatrix‖ < m²` under `4d < m²`, a **large-mass** condition. **A sufficient condition failing
  is not divergence**: outside it nothing here claims anything, and reading the bound as an
  obstruction would be a fence mistaken for a theorem.
* **The combinatorial half is untouched** — nothing here relates `lapMatrix ^ k` to walks.

**W1 DOES NOT MOVE, AND NEITHER DOES ANY OTHER WALL.** No measure, no limit, no compactness appears
in this file; it contains five inequalities about finite matrices. **No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianOpNorm

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The Loewner bounds spent as norm bounds -/

/-- **`‖G.lapMatrix ℝ‖ ≤ 2Δ` FROM A DEGREE BOUND.** The Laplacian is positive semidefinite and
`LaplacianDegreeBound.lapMatrix_le_smul_one` puts it below `2Δ • 1`, so
`PosSemidefNormBound.l2_opNorm_le` applies. **The norm is the `l²` operator norm.** -/
theorem norm_lapMatrix_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) :
    ‖G.lapMatrix ℝ‖ ≤ 2 * Δ :=
  PosSemidefNormBound.l2_opNorm_le (SimpleGraph.posSemidef_lapMatrix ℝ G).nonneg
    (LaplacianDegreeBound.lapMatrix_le_smul_one G hΔ)

/-- **`‖massive G m‖ ≤ 2Δ + m²`**, the same step at the operator the propagator inverts. -/
theorem norm_massive_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) : ‖massive G m‖ ≤ 2 * Δ + m ^ 2 :=
  PosSemidefNormBound.l2_opNorm_le (massive_posDef G hm).posSemidef.nonneg
    (LaplacianDegreeBound.massive_le_smul_one G hΔ m)

open BoxGraph BoxDegree in
/-- **ON THE BOX THE CONSTANT DOES NOT SEE THE SIDE LENGTH**: `‖lapMatrix (boxGraph d n) ℝ‖ ≤ 4d`
for every `n ≥ 1`. The hypothesis `1 ≤ n` is the one `ERRATUM 426` names — `Site d n` is empty when
`d > 0` and `n = 0`, and the norm bound is unavailable there. -/
theorem norm_lapMatrix_boxGraph_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(boxGraph d n).lapMatrix ℝ‖ ≤ 4 * (d : ℝ) := by
  haveI : Nonempty (Site d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hΔ : ∀ p : Site d n, ((boxGraph d n).degree p : ℝ) ≤ 2 * (d : ℝ) := by
    intro p
    have h := boxGraph_degree_le (d := d) (n := n) p
    have h' : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have h := norm_lapMatrix_le (boxGraph d n) hΔ
  have harith : 2 * (2 * (d : ℝ)) = 4 * (d : ℝ) := by ring
  rwa [harith] at h

/-! ## 2. The Neumann criterion, stated so that its regime is visible -/

/-- **THE CONDITION A NEUMANN SERIES FOR `green` WOULD NEED**, `‖lapMatrix‖ < m²`, holds as soon as
`2Δ < m²`. **It is a sufficient condition and this file proves nothing about its failure**: outside
it, nothing here says the series diverges, and no such claim is made. -/
theorem norm_lapMatrix_lt_of_lt [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hlt : 2 * Δ < m ^ 2) : ‖G.lapMatrix ℝ‖ < m ^ 2 :=
  lt_of_le_of_lt (norm_lapMatrix_le G hΔ) hlt

open BoxGraph in
/-- The same on the box, where the condition reads `4d < m²` — **a large-mass regime, and not the
one `WALLS.md`'s W1 block is about.** -/
theorem norm_lapMatrix_boxGraph_lt_of_lt (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {m : ℝ}
    (hlt : 4 * (d : ℝ) < m ^ 2) : ‖(boxGraph d n).lapMatrix ℝ‖ < m ^ 2 :=
  lt_of_le_of_lt (norm_lapMatrix_boxGraph_le d hn) hlt

/-! ## 3. The factor of W1's Neumann tail that this tool supplies -/

/-- **`‖green G m‖ ≤ (m²)⁻¹`, AT EVERY FINITE GRAPH AND WITH NO DEGREE HYPOTHESIS.**
`GreenLargeMass.green_le_smul_one` is the Loewner statement and `GraphLaplacian.green_posDef` the
positivity, so `PosSemidefNormBound.l2_opNorm_le` applies directly. **This is the first factor of
`GreenExpansion.green_eq_two_terms`'s tail `green · A · Dinv · A · Dinv`**, which is what W1's
`WHAT WOULD HAVE TO EXIST` asks for a bound on. The other two factors are not bounded here; see
this file's header, which names them and says why one of them is out of this theorem's reach. -/
theorem norm_green_le [Nonempty V] {m : ℝ} (hm : m ≠ 0) : ‖green G m‖ ≤ (m ^ 2)⁻¹ :=
  PosSemidefNormBound.l2_opNorm_le (green_posDef G hm).posSemidef.nonneg
    (GreenLargeMass.green_le_smul_one G hm)

end LaplacianOpNorm
