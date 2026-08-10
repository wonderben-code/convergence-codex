import IsingContourClosed
import DualObstruction

/-!
# "Surrounds", by crossing parity — and every down site has a piece around it

`WALLS.md` W3 records "surrounds" as the last thing on the Peierls wall, and records that
neither this estate nor Mathlib has any notion of enclosure: no planar graphs, no Jordan
curve, no winding number. That is true of the *topological* notion. **It is not the
notion Peierls uses.**

Peierls uses **crossing parity**: a site is inside a contour when a path from it to the
outside crosses that contour an odd number of times. That needs no topology at all, and
this estate has had the hard half of it since **2026-08-09** (measured from git, not
recalled) — `IsingContourClosed.even_crossings_iff` gives the parity along *any* walk,
exactly.

So this file is the rung under "surrounds", not a definition of a new topological object:

* crossing counts **add** over a disjoint decomposition of a bond set;
* for the contour, the parity from `x` to a boundary site is odd **exactly when `x` is
  down**, under `+` boundary conditions — so the notion is well posed and identified;
* hence **the number of pieces of any disjoint decomposition with odd parity at `x` is
  itself odd exactly when `x` is down** — so in particular at least one piece is. That is
  Peierls' "every down site is enclosed by a contour", as a count rather than an
  existence claim, because the estimate downstream starts from a count.

## What is deliberately general here

The decomposition is an arbitrary pairwise-disjoint list of bond sets whose union is the
contour. Nothing in this file mentions the dual lattice, plaquettes or circuits. That is
not modesty: the pigeonhole is genuinely about bond sets, and stating it at that
generality is what keeps it independent of how the pieces were obtained.

## What is missing, precisely

**The pieces produced by `DualGraph.exists_dual_cycle_decomposition` are circuits in the
dual — lists of `SimpleGraph (Plaq n)` — and this file wants `Finset (Sym2 (Site n))`.**
The map is obvious (a dual edge crosses exactly one primal bond, namely the side it was
built from) and it is **not built here**: it needs the image of a dual subgraph under
`sideOf`, and the proof that those images are disjoint and cover the contour. That is one
named construction, and it is the whole distance between this file and Peierls' geometry.

**And one honest limit on the word "surrounds" itself.** Path-independence is proved for
the *whole* contour (`crossings_parity_indep`) and is **not** proved, and is not true in
general, for an individual piece of an arbitrary decomposition — a bond set that is not a
cut has a parity that depends on the path. So "piece `γ` surrounds `x`" here means "odd
along the walk chosen", and the walk is fixed once per site, which is exactly how the
textbook argument fixes a ray. Making it intrinsic would need each piece to be a cut,
which is what planar duality would supply and what is not built.

Also still missing, and untouched: the `3 ^ |γ|` count. Knowing how many pieces surround
`x` says nothing about how many pieces of a given length can.
`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SurroundsParity

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingBoundaryField DualObstruction

variable {n : ℕ}

/-! ## 1. Crossing counts add over disjoint bond sets -/

@[simp] theorem crossings_empty {x b : Site n} (w : (latticeGraph n).Walk x b) :
    crossings (∅ : Finset (Sym2 (Site n))) w = 0 := by
  simp [crossings]

theorem crossings_union {γ δ : Finset (Sym2 (Site n))} (hd : Disjoint γ δ) {x b : Site n}
    (w : (latticeGraph n).Walk x b) :
    crossings (γ ∪ δ) w = crossings γ w + crossings δ w := by
  induction w with
  | nil => simp
  | @cons a c d h p ih =>
    rw [crossings_cons, crossings_cons, crossings_cons, ih]
    by_cases hg : s(a, c) ∈ γ
    · have hnd : s(a, c) ∉ δ := Finset.disjoint_left.mp hd hg
      rw [if_pos (Finset.mem_union_left _ hg), if_pos hg, if_neg hnd]
      omega
    · by_cases hde : s(a, c) ∈ δ
      · rw [if_pos (Finset.mem_union_right _ hde), if_neg hg, if_pos hde]
        omega
      · rw [if_neg (by simp [hg, hde]), if_neg hg, if_neg hde]
        omega

theorem disjoint_foldr_union {γ : Finset (Sym2 (Site n))} {L : List (Finset (Sym2 (Site n)))}
    (h : ∀ δ ∈ L, Disjoint γ δ) : Disjoint γ (L.foldr (· ∪ ·) ∅) := by
  induction L with
  | nil => simp
  | cons δ L ih =>
    rw [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨h δ (List.mem_cons_self ..), ih fun ε hε => h ε (List.mem_cons_of_mem _ hε)⟩

/-- Over a pairwise-disjoint list of bond sets, the crossing counts add. -/
theorem crossings_foldr_union {L : List (Finset (Sym2 (Site n)))} (hp : L.Pairwise Disjoint)
    {x b : Site n} (w : (latticeGraph n).Walk x b) :
    crossings (L.foldr (· ∪ ·) ∅) w = (L.map fun γ => crossings γ w).sum := by
  induction L with
  | nil => simp
  | cons γ L ih =>
    obtain ⟨hγ, hp'⟩ := List.pairwise_cons.mp hp
    rw [List.foldr_cons, crossings_union (disjoint_foldr_union hγ), ih hp',
      List.map_cons, List.sum_cons]

/-! ## 2. Counting the odd pieces

Not just "some piece is odd" but **how many**: the parity of the total is the parity of
the *number of odd pieces*. That is the bookkeeping Peierls runs on, and the weaker
"some" statement is a corollary of it. -/

/-- Over a list of naturals, the sum is even exactly when an even number of the terms
are odd. Pure arithmetic, stated for a general `f` because that is what it is. -/
theorem even_sum_iff_even_countP {α : Type*} (f : α → ℕ) (L : List α) :
    Even (L.map f).sum ↔ Even (L.countP fun a => decide ¬ Even (f a)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    by_cases h : Even (f a)
    · simp only [h, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
        Nat.add_zero]
      rw [Nat.even_add, ih]
      simp [h]
    · simp only [h, not_false_eq_true, decide_true, if_true]
      rw [Nat.even_add, ih, Nat.even_add_one]
      simp [h]

/-- **The number of pieces crossed an odd number of times has the same parity as the
total.** -/
theorem even_countP_odd_pieces_iff {L : List (Finset (Sym2 (Site n)))}
    (hp : L.Pairwise Disjoint) {x b : Site n} (w : (latticeGraph n).Walk x b) :
    Even (L.countP fun γ => decide ¬ Even (crossings γ w)) ↔
      Even (crossings (L.foldr (· ∪ ·) ∅) w) := by
  rw [crossings_foldr_union hp, even_sum_iff_even_countP]

/-- If the total is odd, some piece is. The corollary the enclosure step uses. -/
theorem exists_odd_of_odd_sum {L : List (Finset (Sym2 (Site n)))} (hp : L.Pairwise Disjoint)
    {x b : Site n} (w : (latticeGraph n).Walk x b)
    (hodd : ¬ Even (crossings (L.foldr (· ∪ ·) ∅) w)) :
    ∃ γ ∈ L, ¬ Even (crossings γ w) := by
  by_contra hcon
  have hall : ∀ γ ∈ L, Even (crossings γ w) := by
    intro γ hγ
    by_contra h
    exact hcon ⟨γ, hγ, h⟩
  refine hodd ?_
  rw [crossings_foldr_union hp]
  clear hodd hp hcon
  induction L with
  | nil => simp
  | cons γ L ih =>
    rw [List.map_cons, List.sum_cons]
    exact Even.add (hall γ (List.mem_cons_self ..))
      (ih fun δ hδ => hall δ (List.mem_cons_of_mem _ hδ))

/-! ## 3. Crossing parity is the spin

`IsingContourClosed.even_crossings_iff` is the whole content: the parity along a walk is
exactly whether the endpoints agree. Two consequences, and both are what make "odd
crossing parity" a usable stand-in for "surrounds". -/

/-- **Odd parity means the endpoints disagree.** -/
theorem odd_crossings_iff_ne (σ : Config n) {x b : Site n}
    (w : (latticeGraph n).Walk x b) :
    ¬ Even (crossings (contour σ) w) ↔ σ x ≠ σ b := by
  rw [even_crossings_iff]

/-- **The parity does not depend on the walk** — for the contour. This is what would need
a topological argument for a general bond set, and needs none here. -/
theorem crossings_parity_indep (σ : Config n) {x b : Site n}
    (w w' : (latticeGraph n).Walk x b) :
    Even (crossings (contour σ) w) ↔ Even (crossings (contour σ) w') := by
  rw [even_crossings_iff, even_crossings_iff]

/-- **Under `+` boundary conditions, a walk from `x` to a boundary site crosses the
contour an odd number of times exactly when `x` is down.** So "the contour surrounds `x`",
read as crossing parity, *is* the statement that `x` is a down site — no choice of
definition is being smuggled in. -/
theorem odd_crossings_iff_down {σ : Config n} (hσ : PlusBoundary σ) {x b : Site n}
    (hb : isBoundary b = true) (w : (latticeGraph n).Walk x b) :
    ¬ Even (crossings (contour σ) w) ↔ σ x = false := by
  rw [odd_crossings_iff_ne, hσ b hb]
  cases hx : σ x <;> simp

/-! ## 4. Every down site has a piece of the contour around it

The assembly. The box is connected (`IsingContourSeparation.latticeGraph_connected`), so a
walk from `x` to the corner exists; the corner is a boundary site
(`IsingBoundaryField.isBoundary_corner`); `+` boundary conditions make the parity odd; and
the pigeonhole hands back a piece. -/

/-- The corner of the box, as a site. -/
def origin (hn : 0 < n) : Site n := (⟨0, hn⟩, ⟨0, hn⟩)

theorem isBoundary_origin (hn : 0 < n) : isBoundary (origin hn) = true :=
  isBoundary_corner n hn

/-- **PEIERLS' ENCLOSURE STEP.** Under `+` boundary conditions, if `x` is down then for
any way of splitting the contour into pairwise-disjoint bond sets, **some one of them is
crossed an odd number of times** by a walk from `x` to the corner.

The decomposition is arbitrary — nothing here knows it came from circuits. Turning "some
bond set with odd parity" into "some *circuit* surrounding `x`" needs the map from dual
edges to the primal bonds they cross, which is not built; see the header. -/
theorem exists_odd_piece_of_down {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = false)
    {L : List (Finset (Sym2 (Site n)))} (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ∪ ·) ∅ = contour σ) :
    ∃ (w : (latticeGraph n).Walk x (origin hn)) (γ : Finset (Sym2 (Site n))),
      γ ∈ L ∧ ¬ Even (crossings γ w) := by
  obtain ⟨w⟩ := (latticeGraph_connected hn).preconnected x (origin hn)
  have hodd : ¬ Even (crossings (L.foldr (· ∪ ·) ∅) w) := by
    rw [hsup]
    exact (odd_crossings_iff_down hσ (isBoundary_origin hn) w).mpr hx
  obtain ⟨γ, hγL, hγ⟩ := exists_odd_of_odd_sum hp w hodd
  exact ⟨w, γ, hγL, hγ⟩

/-- **The sharp form: the NUMBER of pieces around `x` is odd exactly when `x` is down.**
Stronger than the existence statement above, and it is the shape the Peierls estimate
actually needs — an inequality on how many contours enclose a site starts from a count,
not from "at least one". -/
theorem odd_countP_iff_down {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} {L : List (Finset (Sym2 (Site n)))} (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ∪ ·) ∅ = contour σ) (w : (latticeGraph n).Walk x (origin hn)) :
    ¬ Even (L.countP fun γ => decide ¬ Even (crossings γ w)) ↔ σ x = false := by
  rw [even_countP_odd_pieces_iff hp, hsup, odd_crossings_iff_down hσ (isBoundary_origin hn)]

/-- The other half of that biconditional, spelled out: **if `x` is up, an even number of
pieces are crossed oddly** — possibly none, possibly two, and this file does not decide
which. What it does say is that the total parity is even, so the route above genuinely
uses the hypothesis rather than holding for every site. -/
theorem even_countP_of_up {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = true) {L : List (Finset (Sym2 (Site n)))}
    (hp : L.Pairwise Disjoint) (hsup : L.foldr (· ∪ ·) ∅ = contour σ)
    (w : (latticeGraph n).Walk x (origin hn)) :
    Even (L.countP fun γ => decide ¬ Even (crossings γ w)) := by
  by_contra hodd
  rw [odd_countP_iff_down hσ hn hp hsup, hx] at hodd
  exact Bool.noConfusion hodd

/-- And for the whole contour: an up site is crossed evenly. -/
theorem not_odd_crossings_of_up {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n)
    {x : Site n} (hx : σ x = true) (w : (latticeGraph n).Walk x (origin hn)) :
    Even (crossings (contour σ) w) := by
  by_contra hodd
  rw [odd_crossings_iff_down hσ (isBoundary_origin hn) w] at hodd
  rw [hx] at hodd
  exact Bool.noConfusion hodd

end SurroundsParity
