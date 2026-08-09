/-
  IsingContourEnergy.lean — the energy half of Peierls, and the first formal
  contour object in the estate.

  WHY. `WALLS.md`'s W3 names its failing step precisely: "the contour
  machinery (contours as geometric objects, the energy-entropy count, the
  `3^{|γ|}` bound) has no formal counterpart anywhere". A grep of `paper_f/`
  for `broken`, `contour` and `disagree` on 9 August returned nothing, so
  that was true by search and not merely by memory.

  **Peierls has an ENERGY half and an ENTROPY half, and they are not equally
  hard.** The entropy half — counting how many contours of a given length
  pass through a site — is the voluminous geometry W3 is categorised under.
  The energy half is a finite identity about a double sum. This file is the
  energy half, and it carries the contour with it.

  WHAT THIS FILE PROVES:
  1. **`brokenCount`** — the number of ORDERED adjacent disagreeing pairs of
     a configuration, and `brokenCount_eq_card`, which says it is the
     cardinality of an explicit `Finset`.
  2. **`brokenGraph` and `contour`** — the broken bonds ARE a simple graph,
     and the contour is its `SimpleGraph.edgeFinset`: an honest `Finset` of
     unordered bonds, Mathlib's own object, with Mathlib's whole graph API
     already attached to it. `brokenCount_eq_two_mul_contour` connects the
     two: the ordered count is exactly twice the contour length, which is
     also why the ordered count is even (`brokenCount_even`).
  3. **`isingH_eq_ground_add_contour`** — `isingH n σ = isingH n allTrue +
     4·|γ(σ)|`. **This is the energy half of Peierls**: the excess energy
     over the aligned configuration is a fixed positive constant times the
     length of the contour, and nothing else about σ enters.
  4. **`isingH_ground_le`** — therefore the aligned configuration is a
     GROUND STATE: it minimises `isingH` over all configurations, and
     `isingH_eq_ground_iff` says the minimisers are exactly the
     contour-free configurations. The estate did not have this.
     `IsingBoundaryField.allTrue_lower_energy` compares all-up with all-down
     in the presence of the field; this compares all-up with EVERYTHING, and
     needs no field.
  5. **`const_forced` and `contour_const_forced`** — the constants `2` and
     `4` are not conventions, they are forced. On any box with a bond in it,
     no other real number satisfies the identity at the chessboard. The
     instrument is that the chessboard and aligned energies are BOTH
     computed straight from `spin` (`isingH_chess_eq`, `isingH_allTrue_eq`),
     with no reference to §3, so feeding them back in leaves the constant
     nowhere to go. Those two formulas also re-derive
     `IsingFiniteVolume`'s own 2×2 anchors — `isingH_two_allTrue_recovered`,
     `isingH_chess_pos_recovered` — which is the check that they are right.

  WHAT THIS DOES NOT DO, and W3's height is stated honestly in `WALLS.md`
  rather than shaded here. **The contour is built as an EDGE SET, not as a
  family of circuits.** Peierls needs the geometry: that the broken bonds of
  a `+`-boundary configuration containing a `−` site form closed circuits in
  the dual lattice, that those circuits separate, and that a circuit of
  length `L` through a fixed site can be chosen in at most `3^L` ways. None
  of connectedness, planar duality, dual-lattice embedding or the `3^{|γ|}`
  count is here, and the entropy half is where the volume of work is. **This
  does not prove `IsingBoundaryField.MagnetisationBound` and does not
  shorten the distance to it by much.** What it does is make one clause of
  W3's "has no formal counterpart anywhere" false, and leave the next person
  an energy identity and a `SimpleGraph` instead of nothing.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingBoundaryField
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace IsingContourEnergy

open IsingFiniteVolume

/-! ## 1. The broken bonds

A bond is *broken* when its two endpoints disagree. Counted over ORDERED
pairs, to match `isingH`'s own double-counting convention — the one
`IsingFiniteVolume` pinned with the 2×2 anchor (4 bonds, 8 ordered pairs,
aligned energy −8).
-/

/-- The number of ordered adjacent pairs whose spins disagree. -/
def brokenCount {n : ℕ} (σ : Config n) : ℕ :=
  ∑ p : Site n, ∑ q : Site n, if adj p q ∧ σ p ≠ σ q then 1 else 0

/-- The same thing as the cardinality of an explicit set of ordered bonds. -/
theorem brokenCount_eq_card {n : ℕ} (σ : Config n) :
    brokenCount σ
      = (Finset.univ.filter
          (fun pq : Site n × Site n => adj pq.1 pq.2 ∧ σ pq.1 ≠ σ pq.2)).card := by
  classical
  rw [brokenCount, Finset.card_filter, ← Finset.sum_product']
  rfl

/-- The aligned configuration breaks nothing. -/
theorem brokenCount_allTrue (n : ℕ) : brokenCount (fun _ : Site n => true) = 0 := by
  simp [brokenCount]

/-! ## 2. The contour

The broken bonds of a configuration form a `SimpleGraph` on the sites:
`adj` is symmetric, and disagreement is symmetric and rules out loops for
free. The contour is that graph's edge set — unordered bonds, each counted
once, as a `Finset (Sym2 (Site n))`.

Building it this way rather than as a bespoke `Finset` is the point. It is
Mathlib's object, so Mathlib's graph API — `Walk`, `Subgraph`,
`ConnectedComponent`, `degree` — applies to it without further work, and
that API is exactly what the geometric half of Peierls has to consume.
-/

/-- **The broken-bond graph**: sites are adjacent in it when the lattice
    bond between them is broken. Loopless because a site cannot disagree
    with itself, so the irreflexivity is free and does not even use
    `IsingFiniteVolume.adj_irrefl`. -/
def brokenGraph {n : ℕ} (σ : Config n) : SimpleGraph (Site n) where
  Adj p q := adj p q ∧ σ p ≠ σ q
  symm := by
    intro p q h
    exact ⟨(adj_symm p q).mp h.1, fun hc => h.2 hc.symm⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

@[simp] theorem brokenGraph_adj {n : ℕ} (σ : Config n) (p q : Site n) :
    (brokenGraph σ).Adj p q ↔ (adj p q ∧ σ p ≠ σ q) := Iff.rfl

instance instDecidableBrokenAdj {n : ℕ} (σ : Config n) :
    DecidableRel (brokenGraph σ).Adj :=
  fun p q => inferInstanceAs (Decidable (adj p q ∧ σ p ≠ σ q))

/-- **THE CONTOUR** of a configuration: the set of broken bonds, unordered,
    each counted once. `|γ(σ)|` in the Peierls literature. -/
def contour {n : ℕ} (σ : Config n) : Finset (Sym2 (Site n)) :=
  (brokenGraph σ).edgeFinset

theorem mem_contour {n : ℕ} (σ : Config n) (p q : Site n) :
    s(p, q) ∈ contour σ ↔ (adj p q ∧ σ p ≠ σ q) := by
  rw [contour, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, brokenGraph_adj]

/-- **The ordered count is twice the contour length.** Mathlib's
    `two_mul_card_edgeFinset` does the work; the content on our side is that
    `brokenCount` really is the ordered-pair count of a simple graph. -/
theorem brokenCount_eq_two_mul_contour {n : ℕ} (σ : Config n) :
    brokenCount σ = 2 * (contour σ).card := by
  classical
  rw [brokenCount_eq_card, contour, SimpleGraph.two_mul_card_edgeFinset]
  -- the two filters differ only in how the pair is destructured
  congr 1

/-- **Every unordered bond is counted twice**, so the ordered count is even.
    This is the double-count convention showing up where it should. Had the
    parity come out odd, `brokenCount` and `isingH` would have been counting
    different things and §3 would be wrong by a factor of two. -/
theorem brokenCount_even {n : ℕ} (σ : Config n) : Even (brokenCount σ) := by
  rw [brokenCount_eq_two_mul_contour]
  exact ⟨_, two_mul _⟩

/-- The aligned configuration has no contour. -/
theorem contour_allTrue (n : ℕ) : contour (fun _ : Site n => true) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  refine Sym2.ind (fun p q => ?_)
  rw [mem_contour]
  rintro ⟨-, h⟩
  exact h rfl

/-! ## 3. The energy–contour identity

The whole content is one pointwise fact, checked in three cases:

  `[adj p q]·s_p·s_q = [adj p q] − 2·[adj p q ∧ σ p ≠ σ q]`

— zero on both sides off the adjacency, `1 = 1 − 0` on an agreeing bond,
`−1 = 1 − 2` on a broken one. Summing it is the theorem.
-/

/-- The pointwise identity the whole file rests on. -/
theorem spin_mul_eq {n : ℕ} (σ : Config n) (p q : Site n) :
    (if adj p q then spin (σ p) * spin (σ q) else 0)
      = (if adj p q then (1:ℝ) else 0)
        - 2 * (if adj p q ∧ σ p ≠ σ q then (1:ℝ) else 0) := by
  classical
  by_cases hadj : adj p q
  · by_cases hne : σ p ≠ σ q
    · have hsp : spin (σ p) * spin (σ q) = -1 := by
        cases hp : σ p <;> cases hq : σ q <;>
          simp_all [spin]
      rw [if_pos hadj, if_pos hadj, if_pos ⟨hadj, hne⟩, hsp]
      norm_num
    · push Not at hne
      have hsp : spin (σ p) * spin (σ q) = 1 := by
        rw [hne]
        cases hq : σ q <;> simp [spin]
      rw [if_pos hadj, if_pos hadj, if_neg (by tauto), hsp]
      norm_num
  · rw [if_neg hadj, if_neg hadj, if_neg (by tauto)]
    norm_num

/-- The energy of a configuration exceeds the aligned energy by exactly
    twice the number of broken ORDERED pairs. -/
theorem isingH_eq_ground_add_broken {n : ℕ} (σ : Config n) :
    isingH n σ = isingH n (fun _ => true) + 2 * (brokenCount σ : ℝ) := by
  classical
  have hsum : ∀ p : Site n,
      (∑ q : Site n, if adj p q then spin (σ p) * spin (σ q) else 0)
        = (∑ q : Site n, if adj p q then (1:ℝ) else 0)
          - 2 * ∑ q : Site n, (if adj p q ∧ σ p ≠ σ q then (1:ℝ) else 0) := by
    intro p
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => spin_mul_eq σ p q
  have hground : ∀ p : Site n,
      (∑ q : Site n, if adj p q then spin ((fun _ : Site n => true) p)
          * spin ((fun _ : Site n => true) q) else 0)
        = ∑ q : Site n, if adj p q then (1:ℝ) else 0 := by
    intro p
    exact Finset.sum_congr rfl fun q _ => by simp [spin]
  have hcast : ((brokenCount σ : ℕ) : ℝ)
      = ∑ p : Site n, ∑ q : Site n, (if adj p q ∧ σ p ≠ σ q then (1:ℝ) else 0) := by
    rw [brokenCount]
    push_cast
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      split <;> norm_num
  rw [isingH, isingH, hcast]
  simp_rw [hsum, hground]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- **THE ENERGY–CONTOUR IDENTITY, and the energy half of Peierls.** The
    energy of a configuration exceeds the ground energy by `4` per unit of
    contour length — a fixed positive constant times `|γ(σ)|`, with nothing
    else about `σ` entering. In a Peierls estimate this is the factor that
    gets exponentiated to `e^{-4β|γ|}` and raced against the entropy. -/
theorem isingH_eq_ground_add_contour {n : ℕ} (σ : Config n) :
    isingH n σ = isingH n (fun _ => true) + 4 * ((contour σ).card : ℝ) := by
  rw [isingH_eq_ground_add_broken σ, brokenCount_eq_two_mul_contour]
  push_cast
  ring

/-! ## 4. What the identity immediately gives -/

/-- **THE ALIGNED CONFIGURATION IS A GROUND STATE.** It minimises `isingH`
    over ALL configurations — not merely below the all-down configuration,
    and with no field present. Immediate from §3, because the excess is a
    non-negative multiple of a cardinality. The estate did not have this. -/
theorem isingH_ground_le {n : ℕ} (σ : Config n) :
    isingH n (fun _ => true) ≤ isingH n σ := by
  rw [isingH_eq_ground_add_contour σ]
  have : (0:ℝ) ≤ 4 * ((contour σ).card : ℝ) := by positivity
  linarith

/-- **And the minimisers are exactly the contour-free configurations.** The
    ground states of the free-boundary Ising box are characterised, not just
    bounded below. -/
theorem isingH_eq_ground_iff {n : ℕ} (σ : Config n) :
    isingH n σ = isingH n (fun _ => true) ↔ contour σ = ∅ := by
  rw [isingH_eq_ground_add_contour σ, ← Finset.card_eq_zero]
  constructor
  · intro h
    have h4 : ((contour σ).card : ℝ) = 0 := by linarith
    exact_mod_cast h4
  · intro h
    rw [h]
    norm_num

/-- The excess energy of a configuration, as a non-negative quantity, named
    because it is what a Peierls estimate exponentiates. -/
theorem excess_nonneg {n : ℕ} (σ : Config n) :
    0 ≤ isingH n σ - isingH n (fun _ => true) := by
  have := isingH_ground_le σ
  linarith

/-- **The excess is determined by the contour alone.** Two configurations
    with contours of the same length have the same energy — the statement
    that makes "energy is a function of the contour" precise, and the form a
    Peierls sum consumes. -/
theorem isingH_eq_of_contour_card_eq {n : ℕ} {σ τ : Config n}
    (h : (contour σ).card = (contour τ).card) : isingH n σ = isingH n τ := by
  rw [isingH_eq_ground_add_contour σ, isingH_eq_ground_add_contour τ, h]

/-! ## 5. The constant is forced

A normalisation constant asserted in a header is worth nothing; the question
is whether anything would break if it were wrong. It would, and this section
proves so rather than saying so.

The instrument is the chessboard, which breaks EVERY bond. Its energy and
the aligned energy are both computed directly from `spin`, with no reference
to §3 — one is `+|bonds|`, the other `−|bonds|`. Feeding those two numbers
back into §3 leaves the constant with nowhere to go: `const_forced` and
`contour_const_forced` say that on any box with at least one bond, `2` and
`4` are the ONLY constants for which the identity can hold. A factor-of-two
slip is not merely unlikely here, it is refuted.
-/

/-- The total number of ORDERED bonds in the box — `brokenCount`'s
    denominator, counted the same way so the two are comparable. -/
def bondCount (n : ℕ) : ℕ :=
  ∑ p : Site n, ∑ q : Site n, if adj p q then 1 else 0

theorem bondCount_eq_card (n : ℕ) :
    bondCount n
      = (Finset.univ.filter (fun pq : Site n × Site n => adj pq.1 pq.2)).card := by
  classical
  rw [bondCount, Finset.card_filter, ← Finset.sum_product']
  rfl

theorem sum_bond_eq (n : ℕ) :
    ∑ p : Site n, ∑ q : Site n, (if adj p q then (1:ℝ) else 0) = (bondCount n : ℝ) := by
  rw [bondCount]
  push_cast
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    split <;> norm_num

/-- The aligned energy is exactly minus the bond count. Direct from `spin`;
    §3 is not used. -/
theorem isingH_allTrue_eq (n : ℕ) :
    isingH n (fun _ => true) = -(bondCount n : ℝ) := by
  have hp : ∀ p q : Site n,
      (if adj p q then spin ((fun _ : Site n => true) p)
          * spin ((fun _ : Site n => true) q) else 0)
        = (if adj p q then (1:ℝ) else 0) := by
    intro p q
    by_cases hadj : adj p q
    · rw [if_pos hadj, if_pos hadj]; norm_num [spin]
    · rw [if_neg hadj, if_neg hadj]
  rw [isingH]
  simp_rw [hp]
  rw [sum_bond_eq]

/-- The chessboard energy is exactly plus the bond count. Direct from
    `IsingFiniteVolume.spin_chess_adj`; §3 is not used. -/
theorem isingH_chess_eq (n : ℕ) : isingH n (chess n) = (bondCount n : ℝ) := by
  have hp : ∀ p q : Site n,
      (if adj p q then spin (chess n p) * spin (chess n q) else 0)
        = (-1 : ℝ) * (if adj p q then (1:ℝ) else 0) := by
    intro p q
    by_cases hadj : adj p q
    · rw [if_pos hadj, if_pos hadj, spin_chess_adj hadj]; norm_num
    · rw [if_neg hadj, if_neg hadj]; norm_num
  rw [isingH]
  simp_rw [hp, ← Finset.mul_sum]
  rw [sum_bond_eq]
  ring

/-- Adjacent sites disagree on the chessboard. -/
theorem chess_ne_of_adj {n : ℕ} {p q : Site n} (h : adj p q) :
    chess n p ≠ chess n q := by
  have hpar := adj_parity h
  unfold chess
  by_cases hp : (p.1.val + p.2.val) % 2 = 0 <;>
    by_cases hq : (q.1.val + q.2.val) % 2 = 0
  · exact absurd (hp.trans hq.symm) hpar
  · simp [hp, hq]
  · simp [hp, hq]
  · exact absurd (by omega : (p.1.val + p.2.val) % 2 = (q.1.val + q.2.val) % 2) hpar

/-- Every bond is in the chessboard contour. -/
theorem mem_contour_chess {n : ℕ} {p q : Site n} (h : adj p q) :
    s(p, q) ∈ contour (chess n) :=
  (mem_contour _ p q).mpr ⟨h, chess_ne_of_adj h⟩

/-- The chessboard breaks every bond. -/
theorem brokenCount_chess (n : ℕ) : brokenCount (chess n) = bondCount n := by
  rw [brokenCount, bondCount]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hadj : adj p q
  · rw [if_pos hadj, if_pos ⟨hadj, chess_ne_of_adj hadj⟩]
  · rw [if_neg hadj, if_neg (by tauto)]

/-- Boxes of side at least 2 have a bond. Free from the estate's
    `IsingFiniteVolume.isingH_allTrue_neg` once the aligned energy is known
    to be minus the bond count. -/
theorem bondCount_pos (n : ℕ) (hn : 2 ≤ n) : 0 < bondCount n := by
  have h := isingH_allTrue_neg n hn
  rw [isingH_allTrue_eq] at h
  have hR : (0:ℝ) < (bondCount n : ℝ) := by linarith
  exact_mod_cast hR

/-- **THE CONSTANT `2` IN §3 IS FORCED.** No other real number satisfies the
    §3 identity at the chessboard on a box with a bond in it. -/
theorem const_forced (n : ℕ) (hn : 2 ≤ n) (c : ℝ)
    (h : isingH n (chess n)
          = isingH n (fun _ => true) + c * (brokenCount (chess n) : ℝ)) :
    c = 2 := by
  rw [isingH_chess_eq, isingH_allTrue_eq, brokenCount_chess] at h
  have hR : (0:ℝ) < (bondCount n : ℝ) := by exact_mod_cast bondCount_pos n hn
  have h2 : c * (bondCount n : ℝ) = 2 * (bondCount n : ℝ) := by linarith
  exact mul_right_cancel₀ (ne_of_gt hR) h2

/-- **AND THE CONSTANT `4` IS FORCED** — the one that actually appears in
    the Peierls exponent. -/
theorem contour_const_forced (n : ℕ) (hn : 2 ≤ n) (c : ℝ)
    (h : isingH n (chess n)
          = isingH n (fun _ => true) + c * ((contour (chess n)).card : ℝ)) :
    c = 4 := by
  have hB : bondCount n = 2 * (contour (chess n)).card := by
    rw [← brokenCount_chess, brokenCount_eq_two_mul_contour]
  have hpos := bondCount_pos n hn
  have hK : 0 < (contour (chess n)).card := by omega
  have hKR : (0:ℝ) < ((contour (chess n)).card : ℝ) := by exact_mod_cast hK
  rw [isingH_chess_eq, isingH_allTrue_eq, hB] at h
  push_cast at h
  have h2 : c * ((contour (chess n)).card : ℝ)
      = 4 * ((contour (chess n)).card : ℝ) := by linarith
  exact mul_right_cancel₀ (ne_of_gt hKR) h2

/-! ### The 2×2 box, against the estate's own numbers

`IsingFiniteVolume` fixed its conventions with two computations on the 2×2
box. Both are now consequences of the general formulas above, which is the
check that the formulas are the right ones.
-/

theorem bondCount_two : bondCount 2 = 8 := by decide

/-- `IsingFiniteVolume.isingH_two_allTrue` recovered through the general
    formula instead of through its own bespoke argument. -/
theorem isingH_two_allTrue_recovered : isingH 2 (fun _ => true) = -8 := by
  rw [isingH_allTrue_eq, bondCount_two]
  norm_num

/-- `IsingFiniteVolume.isingH_chess_pos` recovered the same way, and
    sharpened from an inequality to an identity. -/
theorem isingH_chess_pos_recovered (n : ℕ) (hn : 2 ≤ n) : 0 < isingH n (chess n) := by
  rw [isingH_chess_eq]
  exact_mod_cast bondCount_pos n hn

theorem brokenCount_chess_two : brokenCount (chess 2) = 8 := by
  rw [brokenCount_chess, bondCount_two]

/-- **The 2×2 chessboard contour has 4 edges**: the 4 bonds of the box, each
    counted once. -/
theorem contour_chess_two : (contour (chess 2)).card = 4 := by
  have h := brokenCount_eq_two_mul_contour (chess 2)
  rw [brokenCount_chess_two] at h
  omega

theorem isingH_chess_two : isingH 2 (chess 2) = 8 := by
  rw [isingH_chess_eq, bondCount_two]
  norm_num

/-! ## 6. Review round 64 — the ways this could be hollow

**"`contour` could be the wrong object."** It is pinned three ways.
`mem_contour` says membership is exactly "this bond is broken", so it is not
an accident of a construction; `brokenCount_eq_two_mul_contour` ties it to
the ordered count that `isingH` actually sums over, so the two conventions
provably agree; and §5 computes it on the 2×2 box and gets `4`, the number
of bonds there. The parity corollary `brokenCount_even` is what would have
failed first had `brokenGraph` been counting something else.

**"The identity could be vacuous — true for a degenerate reason."**
`contour_allTrue` gives one end and §5 gives the other, with a nonzero
contour and a nonzero excess at every box size. `isingH_eq_ground_iff` shows
the identity is tight: equality holds exactly on the empty contour.

**"The constant could be off by a factor."** This is the worry the first
draft of this file answered with a parity remark and a hand-wave, which is
not an answer. `const_forced` and `contour_const_forced` answer it: on any
box with a bond, `2` and `4` are the unique constants for which the identity
can hold. They are provable because `isingH_chess_eq` and
`isingH_allTrue_eq` compute both energies from `spin` alone, so they are not
downstream of the identity being checked.

**"§4 could be restating `IsingBoundaryField.allTrue_lower_energy`."** It is
not. That theorem compares all-up with all-DOWN and needs `h > 0`: it is
about the field selecting between the two aligned states. This compares
all-up with EVERY configuration and uses no field. Neither implies the
other.

**"The `SimpleGraph` could be decoration."** It is load-bearing, though not
irreplaceable, and the difference matters. `brokenCount_even` is proved
through Mathlib's `two_mul_card_edgeFinset`, a fact about darts and edges of
a simple graph. A search for a Mathlib lemma of the shape "fixed-point-free
involution on a `Finset` ⟹ even card" found nothing — `exact?` failed and
grepping the `Even`/`card` and `Involutive` families turned up only
unrelated results — so without the graph the parity would have wanted a
strong induction, which is a route, just a longer one. What the graph buys
beyond brevity is that `contour` is now a Mathlib object with Mathlib's
graph API on it, which is the API the geometric half will need.

**"This could be claimed as progress on W3 when it is not."** The honest
accounting is in the header and in `WALLS.md`: this is the ENERGY half, the
contour is an edge set and not a family of circuits, the entropy half is
untouched, and `MagnetisationBound` is no closer to proved. What changed is
that one clause of "has no formal counterpart anywhere" is now false.
-/

end IsingContourEnergy
