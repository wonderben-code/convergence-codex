import RowParity
import PlaqLocal

/-!
# A circuit crossed oddly to the left of a site passes within `L + 1` of it

This is the enclosure step's geometry, and it is the point the Peierls estimate has been
walking towards: **a circuit cannot cross a site's row oddly on one side and stay far
away.** Precisely, with `L` the circuit's length and `x = (a, j)` a site of the box:

> if the bonds of the circuit strictly to the left of `x` in row `j` are **odd** in number,
> then the circuit has a plaquette `P` with `P.i ≤ a ≤ P.i + L + 1` and `P.j` within one of
> `j`.

**Nothing in that bound mentions `n`**, which was the whole difficulty: the anchor set of a
surrounding circuit of length `L` is confined to a ball of radius `L + 1`, whose size
`PlaqLocal.card_ball_le` bounds by `(2L + 3) ^ 2`. **The numerical prefactor is not
assembled here** — that needs the count of *circuits* rather than of closed walks, and this
estate counts walks (`PlaqLocal.card_closed_walks_ball_le`).

## The three steps, and where each comes from

1. **Both sides are caught.** `RowParity.even_row` says the whole row is crossed evenly, so
   an odd count to the left forces an odd — in particular nonzero — count to the right.
   Two `Finset` arguments turn "nonzero" into "here is a column": `Finset.sum_eq_zero` for
   the left and `Finset.sum_subset` for the right.
2. **A broken bond names a plaquette of the circuit.** `DualBonds.mem_bonds` gives a
   plaquette and a direction whose side is that bond, and `PlaqLocal.near_partnerOf` places
   that plaquette within one of the column it was found in — in every direction at once, so
   no case analysis on which of the two plaquettes flanking the bond was returned.
3. **Two plaquettes of one circuit are within its length.**
   `PlaqLocal.near_of_mem_support_closed_pair`, transported from the circuit to the dual
   graph by `Walk.mapLe`, which preserves support and length.

Then `x` sits between the two columns, so it is within the same distance of the left one.

## The slack of one, and why it is left in

Step 2 places the plaquette within **one** of its column rather than exactly at it, because
the bond could be the top side of the plaquette below as easily as the bottom side of the
plaquette above; pinning it down needs a case analysis on `opp` and buys nothing. That is
where the `+ 1` in `L + 1`, and the `j + 1` in the row bound, come from. A Peierls sum does
not care about an additive constant in the radius, and the estimate this file exists to
feed reads only "a function of `L` alone".

## What is still missing

**The hypothesis is a count, not the word "surrounds".** This file assumes the odd count in
row `j` directly. Connecting it to `DualUnique.odd_count_circuits_iff_down` — which gives
odd *crossings along a walk* from `x` to the corner — needs the walk to be **chosen** as the
leftward ray followed by a descent of the left edge, and the crossing count along that walk
identified with `RowParity.cntD`. The descent contributes nothing, every bond on it having
both feet on the boundary; **that identification is one explicit walk construction and it is
not done here.**

After it: the Gibbs weight of a circuit of length `L`, and the summation over `L`.
`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SimpleGraph.Walk

set_option backward.isDefEq.respectTransparency false in
/-- **Mapping a walk into a supergraph does not change its length.** Mathlib has
`support_mapLe_eq_support`, `edges_mapLe_eq_edges` and `edgeSet_mapLe_eq_edgeSet` for
`mapLe` but not this one — `length_mapLe` occurs **zero** times in the library, measured by
grep over all of `Mathlib/` — and `length_map` does not fire through the abbreviation
without the transparency option Mathlib itself uses for the other three. An upstreaming
candidate. -/
theorem length_mapLe {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G') {u v : V}
    (p : G.Walk u v) : (p.mapLe h).length = p.length := by simp

end SimpleGraph.Walk

namespace RowCatch

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique CircuitSides RowParity
open PlaqLocal SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. An odd count on the left, and a nonzero count on the right -/

theorem exists_lt_of_odd (σ : Config n) (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n)
    {a : ℕ} (hodd : cntD σ H j hj a % 2 = 1) :
    ∃ k, k < a ∧ sideD (rowP j hj k) ∈ bonds σ H := by
  by_contra hcon
  push Not at hcon
  have h0 : cntD σ H j hj a = 0 :=
    Finset.sum_eq_zero fun k hk => if_neg (hcon k (Finset.mem_range.mp hk))
  omega

theorem exists_ge_of_odd (σ : Config n) (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n)
    {a : ℕ} (ha : a ≤ n - 1) (heven : cntD σ H j hj (n - 1) % 2 = 0)
    (hodd : cntD σ H j hj a % 2 = 1) :
    ∃ k, a ≤ k ∧ k < n - 1 ∧ sideD (rowP j hj k) ∈ bonds σ H := by
  by_contra hcon
  push Not at hcon
  have hsub : Finset.range a ⊆ Finset.range (n - 1) := fun x hx =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
  have heq := Finset.sum_subset (f := fun k => if sideD (rowP j hj k) ∈ bonds σ H then 1 else 0)
    hsub fun k hk hk' =>
      if_neg (hcon k (by simpa using hk') (Finset.mem_range.mp hk))
  rw [show (∑ k ∈ Finset.range a, if sideD (rowP j hj k) ∈ bonds σ H then 1 else 0) =
      cntD σ H j hj a from rfl,
    show (∑ k ∈ Finset.range (n - 1), if sideD (rowP j hj k) ∈ bonds σ H then 1 else 0) =
      cntD σ H j hj (n - 1) from rfl] at heq
  omega

/-! ## 2. A broken bond names a plaquette of the circuit, within one of its column

No case analysis on which of the two plaquettes flanking the bond is returned: whichever it
is, it is a partner of the one the bond was read from, and partners are within one in every
coordinate. -/

theorem exists_plaq_of_mem_bonds {σ : Config n} {H : SimpleGraph (Plaq n)} {j k : ℕ}
    (hj : j + 1 < n) (h : sideD (rowP j hj k) ∈ bonds σ H) :
    ∃ P : Plaq n, Near P (rowP j hj k) 1 ∧ ∃ Q, H.Adj P Q := by
  obtain ⟨-, P, d, hadj, hside⟩ := mem_bonds.mp h
  refine ⟨P, ?_, partnerOf P d, hadj⟩
  have hne : sideOf P d = sideOf (rowP j hj k) 3 := hside
  rcases sideOf_eq_cases hne with ⟨hP, -⟩ | ⟨hP, -⟩
  · rw [hP]
    exact Near.refl P 1
  · rw [hP]
    exact near_partnerOf P d

/-! ## 3. Two plaquettes of one circuit are within its length

`PlaqLocal` proved this for closed walks of the dual graph; a circuit is a closed walk of a
subgraph, and `Walk.mapLe` moves it up while preserving both support and length. -/

theorem mem_support_of_adj {H : SimpleGraph (Plaq n)} {v : Plaq n} {p : H.Walk v v}
    (hH : (p.toSubgraph.spanningCoe : SimpleGraph (Plaq n)) = H) {P Q : Plaq n}
    (hadj : H.Adj P Q) : P ∈ p.support := by
  rw [← hH] at hadj
  exact p.fst_mem_support_of_mem_edges (Walk.adj_toSubgraph_iff_mem_edges.mp hadj)

theorem near_of_mem_support_cycle {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) {v : Plaq n} {p : H.Walk v v} {R R' : Plaq n}
    (hR : R ∈ p.support) (hR' : R' ∈ p.support) : Near R R' p.length := by
  have h1 : R ∈ (p.mapLe hle).support := by rwa [Walk.support_mapLe_eq_support]
  have h2 : R' ∈ (p.mapLe hle).support := by rwa [Walk.support_mapLe_eq_support]
  have hpair := near_of_mem_support_closed_pair (p.mapLe hle) h1 h2
  rwa [Walk.length_mapLe] at hpair

/-! ## 4. So the circuit passes within its own length of the site -/

/-- **THE ENCLOSURE GEOMETRY.** If a circuit's bonds in row `j` strictly left of column `a`
are odd in number, the circuit has a plaquette at column at most `a` and at least
`a - (L + 1)`, where `L` is its length, and at row within one of `j`.

Everything in the bound is `L`: no `n`, so the plaquettes a surrounding circuit of length
`L` can be anchored at lie in a ball of radius `L + 1`, whose size `PlaqLocal.card_ball_le`
bounds by a function of `L` alone. That is what a Peierls sum needs; assembling it into a
number is not done here. -/
theorem exists_plaq_near_of_odd {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {j a : ℕ}
    (hj : j + 1 < n) (ha : a ≤ n - 1) {v : Plaq n} {p : H.Walk v v}
    (hH : (p.toSubgraph.spanningCoe : SimpleGraph (Plaq n)) = H)
    (hodd : cntD σ H j hj a % 2 = 1) :
    ∃ P : Plaq n, P ∈ p.support ∧ P.i ≤ a ∧ a ≤ P.i + p.length + 1 ∧
      P.j ≤ j + 1 ∧ j ≤ P.j + 1 := by
  obtain ⟨k₁, hk₁, hb₁⟩ := exists_lt_of_odd σ H hj hodd
  obtain ⟨k₂, hk₂, hk₂', hb₂⟩ :=
    exists_ge_of_odd σ H hj ha (even_row hσ hle hcyc j hj) hodd
  obtain ⟨P₁, hn₁, Q₁, hadj₁⟩ := exists_plaq_of_mem_bonds hj hb₁
  obtain ⟨P₂, hn₂, Q₂, hadj₂⟩ := exists_plaq_of_mem_bonds hj hb₂
  have hs₁ : P₁ ∈ p.support := mem_support_of_adj hH hadj₁
  have hs₂ : P₂ ∈ p.support := mem_support_of_adj hH hadj₂
  have hpair := near_of_mem_support_cycle hle hs₁ hs₂
  have hi₁ : (rowP j hj k₁).i = k₁ := rowP_i hj (by omega)
  have hi₂ : (rowP j hj k₂).i = k₂ := rowP_i hj (by omega)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := hn₁
  obtain ⟨d₁, d₂, d₃, d₄⟩ := hn₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := hpair
  simp only [rowP_j] at c₃ c₄ d₃ d₄
  exact ⟨P₁, hs₁, by omega, by omega, by omega, by omega⟩

end RowCatch
