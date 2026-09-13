import LaplacianSignlessDefinite

/-!
# The signless Laplacian of a connected graph is primitive

**THE STEP THE PREVIOUS UNIT NAMED AS A BUILD.** `SignlessFlatConnected` closed the flat-spectrum
question for connected **two-colourable** graphs and located the rest of it exactly: the
non-two-colourable case wants **Perron–Frobenius for a non-negative irreducible matrix**, which
Mathlib does not have — it has `Matrix.IsIrreducible` and `isIrreducible_iff_exists_pow_pos` and
**no simplicity statement of any kind** — while this estate's `PerronSimple.top_eigenspace_dim_one`
proves simplicity and requires **every entry strictly positive**, which `Q = D + A` never is. The
route named there was five steps. **This file is the first three, and they are what closes the
gap between the two libraries**: not irreducibility, but **primitivity** — a single power that is
entrywise positive, which is exactly the hypothesis `PerronSimple` already takes.

**WHY A POSITIVE DIAGONAL IS THE WHOLE TRICK.** `Q`'s diagonal is the degree, so on a connected
graph with two or more vertices **every diagonal entry is positive**. Then positivity of a power's
entry is **monotone**: `(Q^{k+1})_{ij} ≥ (Q^k)_{ij} · Q_{jj} > 0`, every term of the sum being
non-negative. So a walk of any length gives a positive entry at that length, and padding with the
diagonal carries it up to a **uniform** exponent. Irreducibility alone gives a different exponent
for each pair and no single positive power; the diagonal is what makes them one.

**AND THE EXPONENT IS `Fintype.card V`**, because a connected graph's shortest walk between two
vertices bypasses to a path, and a path is shorter than the vertex count.

## What is proved

**`sl_nonneg`, `sl_adj_pos`, `sl_diag_pos`** — the entries: `Q` is entrywise non-negative, positive
across an edge, and positive on the diagonal at a vertex of positive degree.

**`pow_pos_succ`, `pow_pos_mono`** — positivity of an entry of `Q^k` **persists** as `k` grows,
given a positive diagonal. This is the step irreducibility cannot supply.

**`pow_pos_of_walk`** — a walk from `i` to `j` of length `n` makes `(Q^n)_{ij}` positive, by
induction along the walk and needing no hypothesis at all.

**`degree_pos_of_connected`** — on a connected graph with at least two vertices every degree is
positive.

**`pow_card_pos`** — **THE FILE'S THEOREM**: for such a graph, **`Q ^ Fintype.card V` is entrywise
positive**. `Q` is primitive.

## What is NOT here

* **NO PERRON–FROBENIUS, as of 2026-09-13 (entry 16).** This supplies the hypothesis
  `PerronSimple.top_eigenspace_dim_one` takes; **applying it is the next unit** and needs two
  further steps the route named — that `Q ^ card V` is Hermitian with top eigenvalue `M ^ card V`,
  and that `Q`'s top eigenspace sits inside that power's. Neither is attempted here and no
  declaration below mentions an eigenvalue.
* **NOTHING ABOUT IRREDUCIBILITY.** Mathlib's `Matrix.IsIrreducible` is **not used and not
  established** for `Q`; the argument here goes straight from walks to a positive power and never
  needs the weaker property. That is a deliberate choice and not an oversight — irreducibility is
  the classical hypothesis and it is the wrong one to carry when the diagonal is positive anyway.
* **THE EXPONENT IS NOT CLAIMED SHARP.** `Fintype.card V` is what a path bound gives; the diameter
  plus one would do, and nothing here computes a diameter.
* **NOTHING FOR A DISCONNECTED GRAPH**, where no power is entrywise positive, and nothing for the
  one-vertex graph, where there are no edges and the degree is zero.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency; `pow_card_pos` and `degree_pos_of_connected` additionally take
`Nontrivial V` and `G.Connected`. **`pow_pos_of_walk` takes neither** — a walk is enough.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessPrimitive

open Matrix SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The entries -/

theorem sl_nonneg (i j : V) : 0 ≤ signlessLap G i j := by
  simp only [signlessLap, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  split <;> split <;> positivity

theorem sl_adj_pos {i j : V} (h : G.Adj i j) : 0 < signlessLap G i j := by
  have hne : i ≠ j := h.ne
  simp [signlessLap, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, hne, h]

/-- **THE DIAGONAL IS THE DEGREE**, which is what makes the argument below work. -/
theorem sl_diag_pos {i : V} (h : 0 < G.degree i) : 0 < signlessLap G i i := by
  simp only [signlessLap, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply_eq,
    SimpleGraph.adjMatrix_apply, G.irrefl, if_false, add_zero]
  exact_mod_cast h

theorem pow_nonneg' (k : ℕ) (i j : V) : 0 ≤ ((signlessLap G) ^ k) i j :=
  Matrix.pow_apply_nonneg (sl_nonneg G) k i j

/-! ## 2. Positivity persists, because the diagonal is positive -/

theorem pow_pos_succ {k : ℕ} {i j : V} (hk : 0 < ((signlessLap G) ^ k) i j)
    (hj : 0 < G.degree j) : 0 < ((signlessLap G) ^ (k + 1)) i j := by
  rw [pow_succ, Matrix.mul_apply]
  refine Finset.sum_pos' (fun l _ => mul_nonneg (pow_nonneg' G k i l) (sl_nonneg G l j))
    ⟨j, Finset.mem_univ j, mul_pos hk (sl_diag_pos G hj)⟩

theorem pow_pos_mono (hdeg : ∀ v : V, 0 < G.degree v) {k m : ℕ} (hkm : k ≤ m) {i j : V}
    (hk : 0 < ((signlessLap G) ^ k) i j) : 0 < ((signlessLap G) ^ m) i j := by
  induction m with
  | zero =>
    have hk0 : k = 0 := Nat.le_zero.mp hkm
    subst hk0; exact hk
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · exact pow_pos_succ G (ih (by omega)) (hdeg j)
    · have hkn : k = n + 1 := by omega
      subst hkn; exact hk

/-! ## 3. A walk gives a positive entry at its own length -/

theorem pow_pos_of_walk {i j : V} (w : G.Walk i j) :
    0 < ((signlessLap G) ^ w.length) i j := by
  induction w with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ', Matrix.mul_apply]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (sl_nonneg G a l) (pow_nonneg' G p.length l c))
      ⟨b, Finset.mem_univ b, mul_pos (sl_adj_pos G h) ih⟩

/-! ## 4. So a connected graph's signless Laplacian is primitive -/

omit [DecidableEq V] in
theorem degree_pos_of_connected [Nontrivial V] (hconn : G.Connected) (v : V) :
    0 < G.degree v := by
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨w⟩ := hconn.preconnected v u
  rw [G.degree_pos_iff_exists_adj]
  cases w with
  | nil => exact absurd rfl hu
  | cons h _ => exact ⟨_, h⟩

/-- **`Q ^ card V` IS ENTRYWISE POSITIVE**, which is the hypothesis `PerronSimple` takes. -/
theorem pow_card_pos [Nontrivial V] (hconn : G.Connected) (i j : V) :
    0 < ((signlessLap G) ^ Fintype.card V) i j := by
  obtain ⟨w⟩ := hconn.preconnected i j
  have hlen : w.bypass.length < Fintype.card V := w.bypass_isPath.length_lt
  exact pow_pos_mono G (degree_pos_of_connected G hconn) (by omega)
    (pow_pos_of_walk G w.bypass)

end SignlessPrimitive
