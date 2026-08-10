import SurroundLocal

/-!
# A dual circuit of length `L` stays within `L / 2` of itself

`SurroundLocal` ended by naming the statement its own bound was missing:

> a closed curve of length `L` around a point stays within `L` of it.

That statement has two halves, and they are not equally hard. This file proves the
**geometric** half, which needs nothing but the shape of the four partner maps:

> a closed walk of length `L` in the dual lattice visits only plaquettes within `L / 2`
> of its basepoint — in each coordinate, so within `L` of each other.

and it draws the consequence the entropy count was waiting for: **the number of closed
dual walks of length `L` based within `r` of a fixed plaquette is at most
`(2r + 1) ^ 2 * 4 ^ L`, uniformly in the size of the box.** With `r := L` that is a
Peierls-shaped bound — a polynomial in `L` times a constant to the `L`.

`WalkCount` already bounded the walks through **one** plaquette by `4 ^ L`, which does not
grow with `n` either. What grew with `n` was the set of plaquettes worth starting at:
`SurroundLocal` could only anchor a surrounding circuit somewhere on the walk from `x` to
the corner, and that walk is as long as the box. **It is the anchor count that this file
makes independent of `n`**, by replacing "somewhere on a walk across the box" with
"somewhere in a ball of radius `r`".

## Why the coordinates move by at most one

`DualGraph`'s partner maps are total and truncate: `leftP` subtracts one in `ℕ` and
`rightP` takes a `min`. Either way the first coordinate changes by at most one and the
second not at all, or the other way about. So the whole of §1 is arithmetic on the four
coordinate inequalities, and no boundary condition appears anywhere in this file.

## Why `L / 2` and not `L`

A vertex `R` of a closed walk splits it into a walk from the basepoint to `R` and a walk
from `R` back, of lengths summing to `L`; the coordinate bound applies to each, so the
displacement is at most **both** of them, hence at most `L / 2`. That is the textbook's
"a closed curve of length `L` has diameter at most `L / 2`", proved here by
`Walk.take_spec` rather than by a metric argument.

## What is still missing, and it is now one statement about parity, not about geometry

The half **not** proved here is the enclosure half: that a circuit which *surrounds* `x`
has a plaquette near `x` at all. `SurroundLocal.exists_plaq_on_walk` anchors a surrounding
circuit to the walk from `x` to the corner, but says nothing about *where* on that walk,
and this file's diameter bound is measured from the anchor. So the gap is now exactly the
distance from `x` to the nearest crossing, and nothing here bounds it.

The route the textbook takes is to cross `x`'s ray in both directions, which needs the
crossing parity of **one circuit** to be independent of the path. `SurroundsParity`
records that this holds for the whole contour and is not proved for an individual piece;
in this estate's own vocabulary the statement that would supply it is

> for a circuit `H` of the decomposition, `∃ τ : Config n, bonds σ H = contour τ`

after which `IsingContourClosed.even_crossings_iff` gives path-independence for `H` for
free — that last step is a two-line consequence and the only reason for writing the
missing statement in this particular form. Whether the statement itself holds for every
circuit of a finite box, boundary-hugging ones included, is **not checked here**: it is
what the textbook's planar duality asserts, and it is written down so that the next
attempt starts at a statement rather than at a topic. It is **not proved here and not
assumed anywhere**.

`IsingBoundaryField.MagnetisationBound` is untouched, and the Gibbs weight of a circuit
and the summation over `L` are not begun.
-/

namespace PlaqLocal

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph SimpleGraph

/- `ball` below filters over `Plaq n`, whose `Fintype` instance is itself noncomputable,
so there is no decidable instance to state instead and the classical one is the honest
choice rather than a shortcut. -/
set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Plaquettes within `r` of each other

The `ℓ^∞` relation, written out rather than packaged as a metric: every use below is an
`omega` on the four inequalities, and a `Dist` instance would only hide them. -/

/-- `Q` differs from `P` by at most `r` in each coordinate. -/
def Near (P Q : Plaq n) (r : ℕ) : Prop :=
  Q.i ≤ P.i + r ∧ P.i ≤ Q.i + r ∧ Q.j ≤ P.j + r ∧ P.j ≤ Q.j + r

theorem Near.refl (P : Plaq n) (r : ℕ) : Near P P r :=
  ⟨by omega, by omega, by omega, by omega⟩

theorem Near.mono {P Q : Plaq n} {r s : ℕ} (hrs : r ≤ s) (h : Near P Q r) : Near P Q s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem Near.symm {P Q : Plaq n} {r : ℕ} (h : Near P Q r) : Near Q P r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem Near.trans {P Q R : Plaq n} {r s : ℕ} (h : Near P Q r) (h' : Near Q R s) :
    Near P R (r + s) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **A step across a side moves each coordinate by at most one.** The truncating `min`
in `rightP` and the truncating subtraction in `leftP` are why this needs no hypothesis:
where the partner does not exist the map is the identity, which is nearer still. -/
theorem near_partnerOf (P : Plaq n) (d : Fin 4) : Near P (partnerOf P d) 1 := by
  have hi := P.hi
  have hj := P.hj
  fin_cases d <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [partnerOf, leftP_i, leftP_j, upP_i, upP_j, rightP_i, rightP_j,
      downP_i, downP_j] <;>
    omega

/-- **Dual neighbours are within one of each other.** -/
theorem near_of_adj {σ : Config n} {P Q : Plaq n} (h : (dualGraph σ).Adj P Q) :
    Near P Q 1 := by
  obtain ⟨d, -, rfl, -⟩ := h
  exact near_partnerOf P d

/-! ## 2. A walk of length `L` moves at most `L`

Induction on the walk, one step at a time. Stated for every vertex of the walk and not
just its endpoint, because that is what the circuit bound needs. -/

/-- **Every plaquette of a walk is within its length of the start.** -/
theorem near_of_mem_support {σ : Config n} {P Q : Plaq n} (w : (dualGraph σ).Walk P Q) :
    ∀ R ∈ w.support, Near P R w.length := by
  induction w with
  | nil =>
    intro R hR
    rw [Walk.support_nil, List.mem_singleton] at hR
    subst hR
    exact Near.refl _ _
  | @cons a b c hab p ih =>
    intro R hR
    rw [Walk.support_cons, List.mem_cons] at hR
    rw [Walk.length_cons]
    rcases hR with rfl | hR
    · exact Near.refl _ _
    · exact Near.mono (by omega) ((near_of_adj hab).trans (ih R hR))

/-- The endpoint, as the special case. -/
theorem near_endpoint {σ : Config n} {P Q : Plaq n} (w : (dualGraph σ).Walk P Q) :
    Near P Q w.length :=
  near_of_mem_support w Q w.end_mem_support

/-! ## 3. A closed walk of length `L` has radius `L / 2`

The sharpening, and it is the shape the textbook uses. A vertex of a closed walk is
reached both ways round; the two arcs have lengths summing to `L`, so the displacement is
bounded by each of them and hence by half their sum. -/

/-- **A closed dual walk of length `L` stays within `L / 2` of its basepoint.** This is
the provable half of "a closed curve of length `L` around a point stays within `L` of
it": the diameter half. -/
theorem near_of_mem_support_closed {σ : Config n} {P : Plaq n} (w : (dualGraph σ).Walk P P)
    {R : Plaq n} (hR : R ∈ w.support) : Near P R (w.length / 2) := by
  have h1 : Near P R (w.takeUntil R hR).length :=
    near_of_mem_support _ R (Walk.end_mem_support _)
  have h2 : Near R P (w.dropUntil R hR).length :=
    near_of_mem_support _ P (Walk.end_mem_support _)
  have hsum : (w.takeUntil R hR).length + (w.dropUntil R hR).length = w.length := by
    rw [← Walk.length_append, Walk.take_spec]
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Any two plaquettes of a closed walk of length `L` are within `L` of each other.** -/
theorem near_of_mem_support_closed_pair {σ : Config n} {P : Plaq n}
    (w : (dualGraph σ).Walk P P) {R R' : Plaq n} (hR : R ∈ w.support)
    (hR' : R' ∈ w.support) : Near R R' w.length := by
  have h1 := (near_of_mem_support_closed w hR).symm
  have h2 := near_of_mem_support_closed w hR'
  exact Near.mono (by omega) (h1.trans h2)

/-! ## 4. The ball, and how few plaquettes it holds -/

/-- The plaquettes within `r` of `P` in each coordinate. -/
noncomputable def ball (P : Plaq n) (r : ℕ) : Finset (Plaq n) :=
  Finset.univ.filter fun Q => Near P Q r

@[simp] theorem mem_ball {P Q : Plaq n} {r : ℕ} : Q ∈ ball P r ↔ Near P Q r := by
  simp [ball]

/-- **A ball of radius `r` holds at most `(2r + 1) ^ 2` plaquettes** — and the bound does
not mention `n`, which is the whole point of proving it. The injection is the obvious
one, "coordinates relative to `P`", and it is injective only because the `Near`
hypothesis keeps the truncated subtraction honest. -/
theorem card_ball_le (P : Plaq n) (r : ℕ) : (ball P r).card ≤ (2 * r + 1) ^ 2 := by
  have hcard : (ball P r).card ≤
      ((Finset.range (2 * r + 1)) ×ˢ (Finset.range (2 * r + 1))).card := by
    refine Finset.card_le_card_of_injOn (fun Q => (Q.i + r - P.i, Q.j + r - P.j)) ?_ ?_
    · intro Q hQ
      rw [Finset.mem_coe, mem_ball] at hQ
      obtain ⟨h1, h2, h3, h4⟩ := hQ
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      omega
    · intro Q hQ Q' hQ' hEq
      rw [Finset.mem_coe, mem_ball] at hQ hQ'
      obtain ⟨h1, h2, h3, h4⟩ := hQ
      obtain ⟨g1, g2, g3, g4⟩ := hQ'
      have e1 := congrArg Prod.fst hEq
      have e2 := congrArg Prod.snd hEq
      simp only at e1 e2
      exact Plaq.ext (by omega) (by omega)
  calc (ball P r).card ≤ ((Finset.range (2 * r + 1)) ×ˢ (Finset.range (2 * r + 1))).card :=
        hcard
    _ = (2 * r + 1) * (2 * r + 1) := by rw [Finset.card_product, Finset.card_range]
    _ = (2 * r + 1) ^ 2 := by ring

/-- A closed walk lies in the ball of half its length about its basepoint. -/
theorem support_subset_ball {σ : Config n} {P : Plaq n} (w : (dualGraph σ).Walk P P) :
    ∀ R ∈ w.support, R ∈ ball P (w.length / 2) :=
  fun _R hR => mem_ball.mpr (near_of_mem_support_closed w hR)

/-- And a closed walk based within `r` of `P` lies in the ball of radius
`r + length / 2` about `P`. This is the form the enclosure step will consume: *once* a
surrounding circuit is known to pass within `r` of a site, all of it is known to. -/
theorem support_subset_ball_of_near {σ : Config n} {P Q : Plaq n} {r : ℕ}
    (w : (dualGraph σ).Walk Q Q) (h : Near P Q r) :
    ∀ R ∈ w.support, R ∈ ball P (r + w.length / 2) :=
  fun _R hR => mem_ball.mpr (h.trans (near_of_mem_support_closed w hR))

/-! ## 5. The entropy count, with a prefactor that does not grow with the box

`WalkCount.card_closed_walks_le` counts the closed walks of length `L` at **one**
plaquette. §4 counts the plaquettes worth starting at. Their product is the bound. -/

/-- **At most `(2r + 1) ^ 2 * 4 ^ L` closed dual walks of length `L` are based within `r`
of a fixed plaquette.** Nothing in the bound mentions `n`. -/
theorem card_closed_walks_ball_le (σ : Config n) (P : Plaq n) (r L : ℕ) :
    ∑ Q ∈ ball P r, ((dualGraph σ).finsetWalkLength L Q Q).card ≤ (2 * r + 1) ^ 2 * 4 ^ L := by
  calc ∑ Q ∈ ball P r, ((dualGraph σ).finsetWalkLength L Q Q).card
      ≤ ∑ _Q ∈ ball P r, 4 ^ L :=
        Finset.sum_le_sum fun Q _ => WalkCount.card_closed_walks_le σ L Q
    _ = (ball P r).card * 4 ^ L := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * r + 1) ^ 2 * 4 ^ L := Nat.mul_le_mul_right _ (card_ball_le P r)

/-- **The Peierls shape**: taking the radius to be the length itself — which §3 says is
generous, `L / 2` would do — there are at most `(2L + 1) ^ 2 * 4 ^ L` closed dual walks of
length `L` based at a plaquette within `L` of a fixed one.

This is the first bound on this wall that is **uniform in the size of the box**. What it
is not is the Peierls estimate: it counts walks near a plaquette, and the estimate needs
walks *surrounding a site*, which is the half §6 names. -/
theorem card_closed_walks_near_le (σ : Config n) (P : Plaq n) (L : ℕ) :
    ∑ Q ∈ ball P L, ((dualGraph σ).finsetWalkLength L Q Q).card ≤ (2 * L + 1) ^ 2 * 4 ^ L :=
  card_closed_walks_ball_le σ P L L

/-! ## 6. What is missing, as a statement rather than a remark

Assembling §5 into a bound on **surrounding** circuits needs one thing that is not here:
that a circuit which surrounds `x` passes within a bounded distance of `x`.
`SurroundLocal.exists_plaq_on_walk` gives an anchor — a plaquette of the circuit with a
side on the walk from `x` to the corner — and §3 gives that the rest of the circuit is
within `L / 2` of that anchor. So the entire remaining gap is the distance from `x` to
its anchor, and the anchor is only known to be *somewhere* on a walk whose length grows
with the box.

The textbook closes that gap by crossing the ray from `x` in both directions, which
requires the crossing parity of a **single circuit** to be path-independent.
`SurroundsParity`'s header records that path-independence is proved for the whole contour
and is false in general for an arbitrary bond set. The statement that would supply it for
a circuit, in this estate's vocabulary, is

  `∃ τ : Config n, bonds σ H = contour τ`

for each circuit `H` of the decomposition — after which
`IsingContourClosed.even_crossings_iff` supplies path-independence directly, since the
parity along a walk then reads off `τ` at the two ends and nothing else. That is planar
duality in one line, and whether it survives at the edge of a finite box is not checked
here either. It is not proved here, it is not assumed here, and nothing above depends on
it. -/

end PlaqLocal
