/-
  LatticeLaplacian.lean — the finite-volume lattice Laplacian on the n×n box,
  and its inverse as a covariance.

  WHY, and it is a cross-wall unlock rather than another W3 stair.
  `PROOF_STRATEGY` §6 question 1 asks after every unit what it unlocked.
  Seven units on W3 built `IsingContourSeparation.latticeGraph` — the box as
  a `SimpleGraph`. Asked across walls, that gives this:

  **`WALLS.md` W1 names its missing piece as "a formalised finite-volume
  lattice Laplacian with its inverse-as-covariance", and adds "then the OS2
  packaging applies verbatim — that layer is done and waiting".** The
  Laplacian of a graph is a function of the graph. The graph now exists, and
  Mathlib has `SimpleGraph.lapMatrix`, which this project had never
  imported.

  WHAT THIS FILE PROVES:
  1. **`lattLap`** — the Laplacian `D − A` of the box, with `lattLap_posSemidef`,
     `lattLap_isSymm`, and `lattLap_quadratic_form`, the sum-of-squares
     identity that says what the quadratic form IS.
  2. **`lattLap_mulVec_eq_zero_iff_const`** — its kernel is exactly the
     constants. **This is the zero mode**, and it is where the estate's own
     `latticeGraph_connected` does the work: on a disconnected box the
     kernel would be larger.
  3. **`lattLap_not_posDef`** — so the MASSLESS operator is not positive
     definite. The mass is necessary, stated as a theorem rather than
     assumed.
  4. **`massive_posDef`** — `−Δ + m²` IS positive definite for `m ≠ 0`,
     hence invertible (`massive_isUnit`), and **`green_posDef`: the Green
     function `(−Δ + m²)⁻¹` is a positive-definite kernel — a legitimate
     Gaussian covariance.** That is W1's first conjunct.

  WHAT THIS DOES NOT DO, and it is the half W1 actually turns on.
  **It does not prove REFLECTION POSITIVITY of this Green function.** W1's
  failing step is precisely that: the rank-one-time ⊙ spectator-OU
  factorisation that carried the entire OU-product staircase is, in W1's own
  words, "structurally unavailable" for `(−Δ + m²)⁻¹`, and nothing here
  changes that. **A covariance existing is not a covariance being
  reflection-positive.** There is no chessboard estimate, no random-walk
  representation and no summability argument in this file. What has changed
  is that the object W1 says must exist now does, so the failing step can be
  stated against it instead of about it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourSeparation
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace LatticeLaplacian

open IsingFiniteVolume IsingContourSeparation Matrix

variable {n : ℕ}

/-! ## 1. The Laplacian of the box -/

/-- **The finite-volume lattice Laplacian** `−Δ = D − A` on the n×n box.
    This is the object `WALLS.md` W1 says must exist. -/
def lattLap (n : ℕ) : Matrix (Site n) (Site n) ℝ :=
  (latticeGraph n).lapMatrix ℝ

theorem lattLap_isSymm (n : ℕ) : (lattLap n).IsSymm :=
  (latticeGraph n).isSymm_lapMatrix (R := ℝ)

theorem lattLap_posSemidef (n : ℕ) : (lattLap n).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix _ _

/-- **What the quadratic form is**: half the sum of `(x_p − x_q)²` over
    ordered adjacent pairs. Mathlib's identity, restated against the box so
    the physics reading is visible — this is the discrete Dirichlet energy,
    and it is why `−Δ` is positive semidefinite. -/
theorem lattLap_quadratic_form (x : Site n → ℝ) :
    Matrix.toLinearMap₂' ℝ (lattLap n) x x
      = (∑ p : Site n, ∑ q : Site n,
          if (latticeGraph n).Adj p q then (x p - x q) ^ 2 else 0) / 2 :=
  (latticeGraph n).lapMatrix_toLinearMap₂' ℝ x

/-! ## 2. The zero mode

Where the estate's own connectivity theorem earns its place: on a
disconnected box the kernel would be larger than the constants, and §3 would
be false.
-/

theorem lattLap_mulVec_const (n : ℕ) (c : ℝ) :
    lattLap n *ᵥ (fun _ => c) = 0 :=
  (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
    (G := latticeGraph n) (x := fun _ => c)).mpr fun _ _ _ => rfl

/-- **THE KERNEL IS EXACTLY THE CONSTANTS.** The forward direction is
    Mathlib's reachability criterion combined with
    `IsingContourSeparation.latticeGraph_connected`. -/
theorem lattLap_mulVec_eq_zero_iff_const (hn : 0 < n) (x : Site n → ℝ) :
    lattLap n *ᵥ x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro h
    have hreach := (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
      (G := latticeGraph n) (x := x)).mp h
    refine ⟨x (⟨0, hn⟩, ⟨0, hn⟩), funext fun p => ?_⟩
    exact hreach p _ ((latticeGraph_connected hn).preconnected p _)
  · rintro ⟨c, rfl⟩
    exact lattLap_mulVec_const n c

/-- **So the massless operator is NOT positive definite** — the constants
    are a zero mode. The mass in §3 is necessary, and this says so rather
    than leaving it to be assumed. -/
theorem lattLap_not_posDef (hn : 0 < n) : ¬ (lattLap n).PosDef := by
  intro hpd
  have hdet : IsUnit (lattLap n).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  have hzero : (fun _ : Site n => (1:ℝ)) = 0 :=
    calc (fun _ : Site n => (1:ℝ))
        = (1 : Matrix (Site n) (Site n) ℝ) *ᵥ (fun _ => 1) := (Matrix.one_mulVec _).symm
      _ = ((lattLap n)⁻¹ * lattLap n) *ᵥ (fun _ => 1) := by
            rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (lattLap n)⁻¹ *ᵥ (lattLap n *ᵥ (fun _ => 1)) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [lattLap_mulVec_const n 1, Matrix.mulVec_zero]
  have := congrFun hzero (⟨0, hn⟩, ⟨0, hn⟩)
  norm_num at this

/-! ## 3. The massive operator and its inverse -/

/-- **`−Δ + m²`**, the massive lattice operator whose inverse is the Green
    function the physics wants. -/
def massive (n : ℕ) (m : ℝ) : Matrix (Site n) (Site n) ℝ :=
  lattLap n + Matrix.diagonal (fun _ => m ^ 2)

theorem massive_isSymm (n : ℕ) (m : ℝ) : (massive n m).IsSymm :=
  (lattLap_isSymm n).add (Matrix.isSymm_diagonal _)

theorem diagonal_massSq_posDef (n : ℕ) {m : ℝ} (hm : m ≠ 0) :
    (Matrix.diagonal (fun _ : Site n => m ^ 2)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun _ => by positivity

/-- **THE MASSIVE OPERATOR IS POSITIVE DEFINITE** for every nonzero mass:
    positive semidefinite Laplacian plus a positive multiple of the
    identity. -/
theorem massive_posDef (n : ℕ) {m : ℝ} (hm : m ≠ 0) : (massive n m).PosDef :=
  Matrix.PosDef.posSemidef_add (lattLap_posSemidef n) (diagonal_massSq_posDef n hm)

theorem massive_isUnit (n : ℕ) {m : ℝ} (hm : m ≠ 0) : IsUnit (massive n m) :=
  (massive_posDef n hm).isUnit

/-- **THE GREEN FUNCTION** of the finite-volume massive lattice field. -/
noncomputable def green (n : ℕ) (m : ℝ) : Matrix (Site n) (Site n) ℝ :=
  (massive n m)⁻¹

/-- **THE GREEN FUNCTION IS A POSITIVE-DEFINITE KERNEL** — so it is a
    legitimate Gaussian covariance, which is what `WALLS.md` W1 asks to
    exist. Read §4 before reading more into it than that. -/
theorem green_posDef (n : ℕ) {m : ℝ} (hm : m ≠ 0) : (green n m).PosDef :=
  (massive_posDef n hm).inv

theorem green_isSymm (n : ℕ) {m : ℝ} (hm : m ≠ 0) : (green n m).IsSymm := by
  have h := (green_posDef n hm).isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem green_mul_massive (n : ℕ) {m : ℝ} (hm : m ≠ 0) :
    green n m * massive n m = 1 :=
  Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (massive_isUnit n hm))

/-! ### The boundary condition, and a cross-check against the W3 staircase

`adj` is FREE-boundary: a corner site has two neighbours, an edge site three,
an interior site four. That is inherited from `IsingFiniteVolume` and is a
modelling choice a reader has to know — periodic boundaries would give every
site degree four and a different operator.

The trace makes it visible, and ties the new object to the old one: the
trace of the Laplacian is the sum of the degrees, which is exactly
`IsingContourEnergy.bondCount`, the ordered-bond count the whole W3
staircase is normalised against. **If either object had the wrong
adjacency the two would disagree.**
-/

theorem trace_lattLap (n : ℕ) :
    Matrix.trace (lattLap n) = (IsingContourEnergy.bondCount n : ℝ) := by
  classical
  have hdiag : ∀ p : Site n, lattLap n p p = ((latticeGraph n).degree p : ℝ) := by
    intro p
    simp [lattLap, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      IsingFiniteVolume.adj_irrefl p]
  have hdeg : Matrix.trace (lattLap n)
      = ((∑ p : Site n, (latticeGraph n).degree p : ℕ) : ℝ) := by
    rw [Matrix.trace]
    push_cast
    exact Finset.sum_congr rfl fun p _ => hdiag p
  have hsum : (∑ p : Site n, (latticeGraph n).degree p)
      = 2 * (latticeGraph n).edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hbond : IsingContourEnergy.bondCount n
      = 2 * (latticeGraph n).edgeFinset.card := by
    rw [IsingContourEnergy.bondCount_eq_card, SimpleGraph.two_mul_card_edgeFinset]
    congr 1
  rw [hdeg, hsum, hbond]

/-- The 2×2 anchor, against a number the estate computed independently:
    `IsingContourEnergy.bondCount_two = 8`. Periodic boundaries would give
    `4 · 4 = 16`, so this pins the boundary condition numerically. -/
theorem trace_lattLap_two : Matrix.trace (lattLap 2) = 8 := by
  rw [trace_lattLap, IsingContourEnergy.bondCount_two]
  norm_num

/-! ## 4. Review round 71 — the ways this could be hollow

**"This could be claimed as progress on W1 when it is not."** W1 has two
parts and this is the first. Its `What would have to exist` line reads: "a
formalised finite-volume lattice Laplacian with its inverse-as-covariance
and a chessboard estimate, OR the random-walk representation with
summability." **This file supplies the Laplacian and the
inverse-as-covariance. It supplies neither of the two alternatives that
follow the word `and`/`OR`, and those are the whole difficulty.** W1's exact
failing step — that reflection positivity of `(−Δ + m²)⁻¹` does not factor
coordinate-by-coordinate, so the trick carrying the entire OU-product
staircase is structurally unavailable — is untouched, and no theorem here
bears on it.

**"The object could be the wrong one."** Four checks, and the draft of this
paragraph claimed the wrong thing about one of them, so here they are with
what each actually detects. `lattLap_quadratic_form`: the quadratic form is
the discrete Dirichlet energy, which is what a lattice Laplacian is.
`lattLap_mulVec_eq_zero_iff_const`: the kernel is the constants — **this
detects DISCONNECTION, not a wrong adjacency**; a different but still
connected graph would pass it, and the draft said otherwise.
`lattLap_not_posDef`: the massless operator is genuinely degenerate, so the
mass is not decorative. And the one that does pin the adjacency:
**`trace_lattLap` says the trace equals `IsingContourEnergy.bondCount`**,
the ordered-bond count the entire W3 staircase is normalised against, with
`trace_lattLap_two = 8` against a number that file computed by `decide`.
Periodic boundaries would give `16`. Two independently built objects agree
on a number, which is the check the other three are not.

**"§2 could be Mathlib's theorem with a wrapper."** The forward direction
is, and the header says so. What is NOT Mathlib's is the input:
Mathlib gives "kernel = functions constant on connected components", and
turning that into "kernel = constants" needs the box to BE connected, which
is `IsingContourSeparation.latticeGraph_connected` — proved in this estate
two units ago, by `Fin` arithmetic that no library supplies.

**"The `m ≠ 0` hypothesis could be hiding a gap."** It is not hidden, it is
`lattLap_not_posDef`: at `m = 0` the statement being proved is FALSE, not
merely unproved, because the constants are a zero mode. That theorem exists
so a reader does not have to wonder whether the hypothesis is technical.
-/

end LatticeLaplacian
