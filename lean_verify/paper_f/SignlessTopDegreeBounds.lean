import SignlessPerronSimple
import PerronBound

/-!
# The top of the signless spectrum, between the degrees

**WHAT THE PERRON UNIT MADE WORTH ASKING.** `SignlessPerronSimple` proved the top of a connected
graph's signless spectrum is a **simple** eigenvalue and said nothing about **where** it is. The
classical answer is a sandwich between the degrees, and the estate has both halves of the
machinery and had never put a number on this operator's spectral radius at all — grepped, and
`LaplacianSignlessDefinite.dotProduct_signlessLap_of_degree` is the only theorem in `paper_f`
relating `Q` to a degree.

**THE TWO BOUNDS COME FROM OPPOSITE ENDS OF THE ESTATE.** The upper one is
`PerronBound.abs_le_of_rowSum_le` — every eigenvalue of a non-negative matrix is bounded by the
largest row sum — and `Q`'s row sum at a vertex is **twice its degree**, the diagonal contributing
the degree and the off-diagonal one for each neighbour. The lower one is Rayleigh's easy half,
`RayleighMatrix.quadForm_le_of_eigenvalues_le` at the **all-ones vector**, which turns the
inequality into a statement about the *sum* of the degrees.

**AND THEY PINCH.** On a `k`-regular graph the maximum degree is `k` and the degree sum is `nk`, so
both bounds read `2k` and **`topEigen = 2k` exactly**. So neither bound can be improved, and the
sharpness is exhibited rather than asserted.

## What is proved

**`rowSum_signlessLap`** — the row sum of `Q` at `i` is `2 · deg i`. Not previously stated.

**`topEigen_le_two_maxDegree`** — the top of the spectrum is at most twice the maximum degree.

**`sum_degree_le_topEigen_mul_card`** — and at least the average of twice the degrees:
`2 ∑ᵢ deg i ≤ topEigen · |V|`, stated without division.

**`topEigen_regular`** — **on a `k`-regular graph `topEigen = 2k`**, so both bounds are attained.

## What is NOT here

* **NO SECOND EIGENVALUE AND NO GAP, as of 2026-09-13 (entry 18).** This bounds the top and says
  nothing about the rest, exactly as the Perron unit did.
* **NO CONNECTEDNESS ANYWHERE, and that is worth noticing.** Neither bound needs it — they hold on
  every finite graph with a vertex. `SignlessPerronSimple`'s simplicity needs connectedness; the
  *location* of the top does not.
* **NO LOWER BOUND BY THE MAXIMUM DEGREE.** The classical sharpening `topEigen ≥ Δ + 1` is true and
  is **not proved here**: it needs a test vector supported on a vertex and its neighbourhood
  rather than the all-ones vector, and nothing here builds one (`ERRATUM 246`).
  ⚠ **THE LAST CLAUSE IS FALSE ABOUT THE ESTATE AND IS KEPT AS WRITTEN** (`ERRATUM 94`,
  `ERRATUM 531`, one unit later). `paper_f/LaplacianDeltaPlusOne.lean` builds exactly such a
  vector — `Δ·e_v − ∑_{u ∼ v} e_u` — and spends it on **the same bound for the ordinary
  Laplacian**. It is a different matrix and a different vector (its neighbours are negative,
  which is what `(xᵢ − xⱼ)²` wants), so `SignlessMaxDegreeBound` is not a duplicate of it; but
  the sentence should have said *nothing here builds one for `Q`*, and a reader taking it at face
  value starts from scratch.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency; the three bounds additionally take `Nonempty V`, and the regular case
takes `G.IsRegularOfDegree k`. **No connectedness.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessTopDegreeBounds

open Matrix SimpleGraph LaplacianSignless RayleighMatrix SignlessPerronSimple
open RayleighVariational

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rowSum_signlessLap (i : V) : ∑ j, signlessLap G i j = 2 * (G.degree i : ℝ) := by
  simp only [signlessLap, Matrix.add_apply, Finset.sum_add_distrib]
  rw [show (∑ j, (G.degMatrix ℝ) i j) = (G.degree i : ℝ) by
    simp [SimpleGraph.degMatrix, Matrix.diagonal]]
  rw [show (∑ j, (G.adjMatrix ℝ) i j) = (G.degree i : ℝ) by
    have h := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := i)
    simpa [Matrix.mulVec, dotProduct] using h]
  ring

theorem topEigen_le_two_maxDegree [Nonempty V] :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      ≤ 2 * (G.maxDegree : ℝ) := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  obtain ⟨i₀, hi₀⟩ := exists_topEigen hQ
  set b := hQ.eigenvectorBasis i₀ with hb
  have hne : (WithLp.ofLp b) ≠ 0 := by
    intro h
    have hn : ‖b‖ = 1 := hQ.eigenvectorBasis.orthonormal.1 i₀
    rw [show b = (0 : EuclideanSpace ℝ V) from by ext v; exact congrFun h v] at hn
    simp at hn
  have heig : signlessLap G *ᵥ (WithLp.ofLp b) = topEigen hQ • (WithLp.ofLp b) := by
    have := RayleighMatrix.mv_eigenvectorBasis hQ i₀
    rw [hi₀] at this
    exact (mv_iff (signlessLap G) (topEigen hQ) (WithLp.ofLp b)).1 (by simpa using this)
  have habs := PerronBound.abs_le_of_rowSum_le (SignlessPrimitive.sl_nonneg G) heig hne
    (C := 2 * (G.maxDegree : ℝ))
    (fun i => by rw [rowSum_signlessLap]; gcongr; exact_mod_cast G.degree_le_maxDegree i)
  exact (abs_le.mp habs).2

theorem sum_degree_le_topEigen_mul_card [Nonempty V] :
    2 * (∑ i : V, (G.degree i : ℝ))
      ≤ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) * Fintype.card V := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  set v : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ)) with hv
  have hq := RayleighMatrix.quadForm_le_of_eigenvalues_le hQ (le_topEigen hQ) v
  have hlhs : (inner ℝ v (RayleighMatrix.mv (signlessLap G) v) : ℝ)
      = 2 * ∑ i : V, (G.degree i : ℝ) := by
    rw [RayleighMatrix.inner_expand]
    simp only [hv, RayleighMatrix.mv_row, WithLp.ofLp_toLp, one_mul, mul_one]
    rw [show (∑ i : V, ∑ j, signlessLap G i j) = ∑ i : V, 2 * (G.degree i : ℝ) from
      Finset.sum_congr rfl fun i _ => rowSum_signlessLap G i, ← Finset.mul_sum]
  have hrhs : (inner ℝ v v : ℝ) = Fintype.card V := by
    rw [RayleighMatrix.inner_expand]; simp [hv, Finset.card_univ]
  rw [hlhs, hrhs] at hq
  exact hq

theorem topEigen_regular [Nonempty V] {k : ℕ} (hreg : G.IsRegularOfDegree k) :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) = 2 * (k : ℝ) := by
  classical
  have hmax : G.maxDegree = k := by
    refine le_antisymm (G.maxDegree_le_of_forall_degree_le _ fun v => (hreg v).le) ?_
    obtain ⟨v⟩ := ‹Nonempty V›
    rw [← hreg v]; exact G.degree_le_maxDegree v
  have hup := topEigen_le_two_maxDegree G
  rw [hmax] at hup
  have hlo := sum_degree_le_topEigen_mul_card G
  rw [show (∑ i : V, (G.degree i : ℝ)) = (Fintype.card V : ℝ) * k by
    simp [hreg _, Finset.sum_const, Finset.card_univ]] at hlo
  have hcard : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  nlinarith [hup, hlo, hcard]

end SignlessTopDegreeBounds
