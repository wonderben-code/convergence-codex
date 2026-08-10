import RowCatch

/-!
# The ray, and Peierls' enclosure step with a bounded anchor

`RowCatch` proved the enclosure geometry from a hypothesis about a **count** — the broken
bonds of a row, left of a column. The estate's enclosure step delivers something else: odd
**crossings along a walk** from the site to the corner
(`SurroundsParity.odd_crossings_iff_down`, and the pigeonhole
`SurroundsParity.exists_odd_of_odd_sum` over a circuit decomposition, which is how
`DualUnique.exists_circuit_surrounding` is built). This file builds the walk that identifies
the two, and then re-runs that assembly with **this** walk in place of the arbitrary one
connectivity supplies.

## The walk

From `x = (a, b)`, go **left along row `b`** to the left edge, then **down the left edge**
to the corner. Both legs are explicit recursions on a natural number, and each leg does one
job:

* the leftward ray's crossings **are** `RowParity.cntD`, bond for bond — the `k`-th step of
  the ray crosses exactly `sideD` of the `k`-th plaquette of the row;
* the descent crosses **nothing**, because every bond on the left edge has both feet on the
  boundary of the box, and a `+`-boundary configuration breaks no such bond.

That the walk ends at `SurroundsParity.origin` is what lets the parity theorem be applied to
it: `odd_crossings_iff_down` takes the walk as an argument and holds for every one, so it
holds for this one. Nothing about the walk is special except that its crossings are
computable.

## The result

> **Under `+` boundary conditions, if `x` is down then some circuit of the dual
> decomposition has a plaquette within `L + 1` of `x` in the first coordinate and within one
> in the second, where `L` is that circuit's length.**

and the anchor is delivered **as a member of `PlaqLocal.ball` at radius `L + 1`** about the
plaquette at `x`, so `PlaqLocal.card_ball_le` bounds the anchor set by `(2L + 3) ^ 2` with
nothing left to arrange. **That is the enclosure step in the form Peierls needs it**, and it
is what `SurroundLocal` said was missing four units ago, when the anchor set was a walk
across the box.

## What is still missing

**The comparison itself.** Three things, and none of them is begun: the Gibbs weight of a
circuit of length `L`; the summation over `L`; and — for a numerical prefactor rather than a
bound on closed walks — counting *circuits* where `PlaqLocal.card_closed_walks_ball_le`
counts closed walks, which over-counts by the two traversals of each circuit and by walks
that are not circuits at all. `IsingBoundaryField.MagnetisationBound` is untouched.

Also unproved and unassumed, and no longer on the path: `∃ τ, bonds σ H = contour τ`, the
statement that a circuit's bonds are a cut (ERRATUM 83).
-/

namespace RayWalk

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique CircuitSides
open RowParity RowCatch PlaqLocal SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Sites of a row and of the left edge -/

/-- The site at column `k` of row `b`. -/
def col (b : Fin n) (k : ℕ) (hk : k < n) : Site n := (⟨k, hk⟩, b)

/-- The site at row `c` of the left edge. -/
def edge (c : ℕ) (hc : c < n) : Site n := (⟨0, by omega⟩, ⟨c, hc⟩)

theorem col_zero (b : Fin n) (hk : 0 < n) : col b 0 hk = edge b.val b.isLt := rfl

theorem isBoundary_edge (c : ℕ) (hc : c < n) : isBoundary (edge c hc) = true := by
  simp [isBoundary, edge]

/-! ## 2. The leftward ray

One step per column, and its crossings are `RowParity.cntD` bond for bond. -/

/-- One step left along a row. -/
theorem adj_col (b : Fin n) (k : ℕ) (hk : k + 1 < n) :
    (latticeGraph n).Adj (col b (k + 1) hk) (col b k (by omega)) :=
  Or.inr ⟨rfl, Or.inr rfl⟩

/-- The walk from column `k` of row `b` to the left edge. -/
def leftRay (b : Fin n) : (k : ℕ) → (hk : k < n) →
    (latticeGraph n).Walk (col b k hk) (edge b.val b.isLt)
  | 0, _ => Walk.nil
  | (k + 1), hk => Walk.cons (adj_col b k hk) (leftRay b k (by omega))

@[simp] theorem leftRay_zero (b : Fin n) (hk : 0 < n) :
    leftRay b 0 hk = Walk.nil := rfl

@[simp] theorem leftRay_succ (b : Fin n) (k : ℕ) (hk : k + 1 < n) :
    leftRay b (k + 1) hk = Walk.cons (adj_col b k hk) (leftRay b k (by omega)) := rfl

/-- **The `k`-th step of the ray crosses exactly the `k`-th bottom side of the row.** -/
theorem sideD_rowP_eq (b : Fin n) (hj : b.val + 1 < n) (k : ℕ) (hk : k + 1 < n) :
    sideD (rowP b.val hj k) = s(col b (k + 1) hk, col b k (by omega)) := by
  rw [show rowP b.val hj k = ⟨k, b.val, hk, hj⟩ from
    Plaq.ext (by simp only [rowP]; omega) rfl]
  rfl

/-- **The ray's crossings are the row count.** -/
theorem crossings_leftRay (γ : Finset (Sym2 (Site n))) (b : Fin n) (hj : b.val + 1 < n) :
    ∀ (k : ℕ) (hk : k < n),
      crossings γ (leftRay b k hk) =
        ∑ m ∈ Finset.range k, if sideD (rowP b.val hj m) ∈ γ then 1 else 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [leftRay_succ, crossings_cons, ih (by omega), Finset.sum_range_succ,
      sideD_rowP_eq b hj k (by omega)]
    omega

/-! ## 3. The descent, which crosses nothing

Every bond of the left edge joins two boundary sites, and
`DualObstruction.notMem_contour_of_plusBoundary` says a `+`-boundary configuration breaks no
such bond. -/

/-- One step down the left edge. -/
theorem adj_edge (c : ℕ) (hc : c + 1 < n) :
    (latticeGraph n).Adj (edge (c + 1) hc) (edge c (by omega)) :=
  Or.inl ⟨rfl, Or.inr rfl⟩

/-- The walk down the left edge, from row `c` to the corner. -/
def downEdge : (c : ℕ) → (hc : c < n) → (latticeGraph n).Walk (edge c hc) (edge 0 (by omega))
  | 0, _ => Walk.nil
  | (c + 1), hc => Walk.cons (adj_edge c hc) (downEdge c (by omega))

@[simp] theorem downEdge_zero (hc : 0 < n) :
    (downEdge 0 hc : (latticeGraph n).Walk _ _) = Walk.nil := rfl

@[simp] theorem downEdge_succ (c : ℕ) (hc : c + 1 < n) :
    (downEdge (c + 1) hc : (latticeGraph n).Walk _ _) =
      Walk.cons (adj_edge c hc) (downEdge c (by omega)) := rfl

/-- **The descent crosses no bond of the contour.** -/
theorem crossings_downEdge {σ : Config n} (hσ : PlusBoundary σ) :
    ∀ (c : ℕ) (hc : c < n), crossings (contour σ) (downEdge c hc) = 0 := by
  intro c
  induction c with
  | zero => intro _; simp [downEdge]
  | succ c ih =>
    intro hc
    rw [downEdge_succ, crossings_cons, ih (by omega),
      if_neg (notMem_contour_of_plusBoundary hσ (isBoundary_edge (c + 1) hc)
        (isBoundary_edge c (by omega)))]

/-- And hence none of any circuit's, since `bonds` is a subset of the contour. -/
theorem crossings_downEdge_bonds {σ : Config n} (hσ : PlusBoundary σ)
    (H : SimpleGraph (Plaq n)) :
    ∀ (c : ℕ) (hc : c < n), crossings (bonds σ H) (downEdge c hc) = 0 := by
  intro c
  induction c with
  | zero => intro _; simp [downEdge]
  | succ c ih =>
    intro hc
    rw [downEdge_succ, crossings_cons, ih (by omega),
      if_neg fun hmem => notMem_contour_of_plusBoundary hσ (isBoundary_edge (c + 1) hc)
        (isBoundary_edge c (by omega)) (bonds_subset σ H hmem)]

/-! ## 4. The whole walk, and its crossings -/

theorem crossings_append (γ : Finset (Sym2 (Site n))) {u v w : Site n}
    (p : (latticeGraph n).Walk u v) (q : (latticeGraph n).Walk v w) :
    crossings γ (p.append q) = crossings γ p + crossings γ q := by
  induction p with
  | nil => simp
  | cons h p ih => rw [Walk.cons_append, crossings_cons, crossings_cons, ih]; omega

/-- **The ray to the corner**: left along the row, then down the left edge. -/
def ray (b : Fin n) (k : ℕ) (hk : k < n) :
    (latticeGraph n).Walk (col b k hk) (edge 0 (by omega)) :=
  (leftRay b k hk).append (downEdge b.val b.isLt)

/-- The ray ends at the corner: `edge 0` and `SurroundsParity.origin` are the same site. -/
theorem edge_zero_eq_origin (h : 0 < n) :
    (edge 0 h : Site n) = SurroundsParity.origin h := rfl

/-- **The crossings of the ray are the row count**, the descent having contributed
nothing. -/
theorem crossings_ray {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    (b : Fin n) (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ H) (ray b k hk) = cntD σ H b.val hj k := by
  have h0 := crossings_downEdge_bonds hσ H b.val b.isLt
  rw [ray, crossings_append, h0, Nat.add_zero, crossings_leftRay _ b hj k hk]
  rfl

/-! ## 5. Peierls' enclosure step, with an anchor bounded by the circuit's length -/

/-- A down site is not on the boundary, so its row has a row of plaquettes above it. -/
theorem row_lt_of_down {σ : Config n} (hσ : PlusBoundary σ) {x : Site n} (hx : σ x = false) :
    x.2.val + 1 < n := by
  by_contra hcon
  have hb : isBoundary x = true := by
    have := x.2.isLt
    simp only [isBoundary, decide_eq_true_eq]
    omega
  rw [hσ x hb] at hx
  exact Bool.noConfusion hx

/-- And its column has a column of plaquettes to the right, for the same reason. -/
theorem col_lt_of_down {σ : Config n} (hσ : PlusBoundary σ) {x : Site n} (hx : σ x = false) :
    x.1.val + 1 < n := by
  by_contra hcon
  have hb : isBoundary x = true := by
    have := x.1.isLt
    simp only [isBoundary, decide_eq_true_eq]
    omega
  rw [hσ x hb] at hx
  exact Bool.noConfusion hx

/-- The plaquette whose bottom-left corner is `x`. It exists because a down site is not on
the boundary. -/
def plaqAt {σ : Config n} (hσ : PlusBoundary σ) {x : Site n} (hx : σ x = false) : Plaq n :=
  ⟨x.1.val, x.2.val, col_lt_of_down hσ hx, row_lt_of_down hσ hx⟩

/-- **THE ENCLOSURE STEP, WITH A BOUNDED ANCHOR.** Under `+` boundary conditions, if `x` is
down then the dual contour splits into circuits one of which has a plaquette **within
`L + 1` of `x`**, where `L` is that circuit's own length — in the first coordinate, and
within one in the second.

The anchor set is therefore a ball of radius `L + 1`, whose size `PlaqLocal.card_ball_le`
bounds by `(2L + 3) ^ 2`: **a function of `L` alone, with no dependence on the size of the
box.** That is the shape Peierls' comparison needs, and the comparison itself — the Gibbs
weight of a circuit, and the summation over `L` — is not begun. -/
theorem exists_circuit_near_of_down {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = false) :
    ∃ (L : List (SimpleGraph (Plaq n))) (H : SimpleGraph (Plaq n)) (v : Plaq n)
      (p : H.Walk v v) (P : Plaq n),
      (∀ K ∈ L, IsCycleGraph K) ∧ L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = dualGraph σ ∧
        H ∈ L ∧ p.IsCycle ∧ (p.toSubgraph.spanningCoe : SimpleGraph (Plaq n)) = H ∧
        P ∈ p.support ∧
        P.i ≤ x.1.val ∧ x.1.val ≤ P.i + p.length + 1 ∧
        P.j ≤ x.2.val + 1 ∧ x.2.val ≤ P.j + 1 ∧
        P ∈ PlaqLocal.ball (plaqAt hσ hx) (p.length + 1) := by
  classical
  obtain ⟨Ls, hcyc, hpair, hsup⟩ := exists_dual_cycle_decomposition hσ
  have hj : x.2.val + 1 < n := row_lt_of_down hσ hx
  have hxcol : x.1.val < n := x.1.isLt
  -- the walk from `x` to the corner: left along its row, then down the left edge
  have hxeq : x = col x.2 x.1.val hxcol := rfl
  have hodd : ¬ Even (crossings ((Ls.map (bonds σ)).foldr (· ∪ ·) ∅) (ray x.2 x.1.val hxcol)) := by
    rw [← bonds_foldr, hsup, bonds_dualGraph hσ]
    exact (SurroundsParity.odd_crossings_iff_down hσ
      (SurroundsParity.isBoundary_origin _) _).mpr hx
  obtain ⟨γ, hγmem, hγ⟩ :=
    SurroundsParity.exists_odd_of_odd_sum (pairwise_disjoint_bonds hpair) _ hodd
  obtain ⟨H, hHL, rfl⟩ := List.mem_map.mp hγmem
  obtain ⟨v, p, hp, hH⟩ := hcyc H hHL
  have hle : H ≤ dualGraph σ := hsup ▸ le_foldr_sup_of_mem hHL
  have hcnt : cntD σ H x.2.val hj x.1.val % 2 = 1 := by
    rw [← crossings_ray hσ H x.2 hj x.1.val hxcol]
    exact Nat.not_even_iff.mp hγ
  obtain ⟨P, hPs, h1, h2, h3, h4⟩ :=
    exists_plaq_near_of_odd hσ hle (hcyc H hHL) hj (by omega) hH hcnt
  exact ⟨Ls, H, v, p, P, hcyc, hpair, hsup, hHL, hp, hH, hPs, h1, h2, h3, h4,
    mem_ball.mpr ⟨by simp only [plaqAt]; omega, by simp only [plaqAt]; omega,
      by simp only [plaqAt]; omega, by simp only [plaqAt]; omega⟩⟩

end RayWalk
