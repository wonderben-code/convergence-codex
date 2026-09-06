import EvenDegreesBoundary

/-!
# The characterisation, both ways: the even-degree condition **is** one value on the boundary

`EvenDegreesBoundary` proved one direction — `EvenDegrees (dualGraph σ)` forces every boundary
site other than the four corners to carry the same spin — and fenced the converse as unproved,
naming what it would need: the trichotomy *every plaquette is interior, one-rim or corner*.

> **`evenDegrees_iff_boundaryConstOffCorner`** — for `2 < n`,
> `EvenDegrees (dualGraph σ) ↔ BoundaryConstOffCorner σ`.

So the hypothesis `RayCircuitSurrounding` uses in place of `PlusBoundary` is now known **exactly**:
the interior is free, the four corner spins are free, and every other boundary site carries one
common value.

## What is proved

**`outward_iff`** — the trichotomy's engine: direction `d` of `P` faces out **exactly** when `d`
is `0` and `P.i = 0`, or `1` and `P.j + 2 = n`, or `2` and `P.i + 2 = n`, or `3` and `P.j = 0`.
Four `fin_cases` against the four `*_eq_self_iff`. The four `not_outward_of_*` read it backwards;
they are named for their hypotheses because `PieceBranchesRealised` already has
`not_outward_zero`, `not_outward_one` and `not_outward_two` for the **one** plaquette `plaqEdge`
of a `4 × 4` box, and these are the general statements about an arbitrary plaquette.

**`sideL_notMem_of_const`** and its three partners — a one-rim plaquette's outward side has both
endpoints on the boundary and neither at a corner, so the hypothesis makes them equal and the side
unbroken.

**`corner_bl_iff_of_const`** and its three partners — at a corner plaquette the two outward sides
**share the corner site**, and their other two endpoints are non-corner boundary sites, so the
hypothesis makes those equal and the two sides broken together or not at all. The corner's own
spin never enters.

**`evenDegrees_of_boundaryConstOffCorner`** — the converse, nine cases, one per position of the
plaquette. Each case rewrites the four `if`s in direction order `0, 1, 2, 3`, because `if_neg`'s
condition is **not** determined by its argument and each rewrite therefore lands on the leading
one — going out of order silently rewrites the wrong term.

**`evenDegrees_iff_boundaryConstOffCorner`** — the two halves, joined.

## What is NOT here

**THE FOUR CORNER SPINS ARE FREE, AND THAT IS NOW A CONSEQUENCE RATHER THAN A GAP** — but it is
**not stated as a theorem**: no declaration here exhibits two configurations differing only at a
corner and satisfying the condition together. It follows from the biconditional, since
`BoundaryConstOffCorner` quantifies only over non-corner sites, and **the reader has to do that
step**. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING BELOW `2 < n`.** At `n = 2` the single plaquette faces out in all four directions
(`EvenDegreesReach.all_outward_two`) and the trichotomy fails; **no version of the biconditional
is asserted there.**

**NO COUNT AND NO PROPORTION** (`ERRATUM 477`). How many configurations satisfy the condition is
not computed.

**NO THEOREM IS ADDED TO THE PEIERLS CHAIN.** This describes a hypothesis the chain already
carries, exactly. `ExtendedDual`'s four-rim construction is still the repair and is still
untouched, and the `3 ^ |γ|` count is untouched. **W3 does not move. No wall moves. No published
tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `outward_iff`, the four
`not_outward_*`, the six site lemmas and the four `side*_notMem_of_const` take **nothing** about
`n`; the four corner lemmas and both halves of the characterisation take **`2 < n`**. No
`PlusBoundary` anywhere.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace EvenDegreesConverse

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField DualObstruction DualGraph ExtendedDual DualDegreeExact
open EvenDegreesReach EvenDegreesBoundary SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-- The hypothesis: one value on the boundary away from the four corners. -/
def BoundaryConstOffCorner (σ : Config n) : Prop :=
  ∀ p q : Site n, isBoundary p = true → ¬ IsCorner p →
    isBoundary q = true → ¬ IsCorner q → σ p = σ q

/-! ## 1. Which directions face out -/

theorem outward_iff (P : Plaq n) (d : Fin 4) :
    Outward P d ↔ (d = 0 ∧ P.i = 0) ∨ (d = 1 ∧ P.j + 2 = n) ∨ (d = 2 ∧ P.i + 2 = n)
      ∨ (d = 3 ∧ P.j = 0) := by
  fin_cases d
  · exact ⟨fun h => Or.inl ⟨rfl, (leftP_eq_self_iff P).mp h⟩,
      fun h => (leftP_eq_self_iff P).mpr (by rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        first | exact h | exact absurd h (by decide))⟩
  · exact ⟨fun h => Or.inr (Or.inl ⟨rfl, (upP_eq_self_iff P).mp h⟩),
      fun h => (upP_eq_self_iff P).mpr (by rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        first | exact h | exact absurd h (by decide))⟩
  · exact ⟨fun h => Or.inr (Or.inr (Or.inl ⟨rfl, (rightP_eq_self_iff P).mp h⟩)),
      fun h => (rightP_eq_self_iff P).mpr (by rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;>
        first | exact h | exact absurd h (by decide))⟩
  · exact ⟨fun h => Or.inr (Or.inr (Or.inr ⟨rfl, (downP_eq_self_iff P).mp h⟩)),
      fun h => (downP_eq_self_iff P).mpr (by rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;>
        first | exact h | exact absurd h (by decide))⟩

/-! ## 2. The site facts each rim bond needs -/

theorem isBoundary_of_fst_eq_zero {p : Site n} (h : p.1.val = 0) : isBoundary p = true := by
  simp only [isBoundary, decide_eq_true_eq]; omega

theorem isBoundary_of_fst_last {p : Site n} (h : p.1.val + 1 = n) : isBoundary p = true := by
  simp only [isBoundary, decide_eq_true_eq]; omega

theorem isBoundary_of_snd_eq_zero {p : Site n} (h : p.2.val = 0) : isBoundary p = true := by
  simp only [isBoundary, decide_eq_true_eq]; omega

theorem isBoundary_of_snd_last {p : Site n} (h : p.2.val + 1 = n) : isBoundary p = true := by
  simp only [isBoundary, decide_eq_true_eq]; omega

theorem not_isCorner_of_snd_interior {p : Site n} (h1 : 0 < p.2.val) (h2 : p.2.val + 1 < n) :
    ¬ IsCorner p := by
  rintro ⟨-, h | h⟩ <;> omega

theorem not_isCorner_of_fst_interior {p : Site n} (h1 : 0 < p.1.val) (h2 : p.1.val + 1 < n) :
    ¬ IsCorner p := by
  rintro ⟨h | h, -⟩ <;> omega

/-! ## 3. A one-rim plaquette's outward side is unbroken -/

theorem sideL_notMem_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) {P : Plaq n}
    (hi : P.i = 0) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) : sideL P ∉ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  rw [sideL, mem_contour]
  push Not
  intro _
  exact hc _ _ (isBoundary_of_fst_eq_zero (by simp [bl, hi]))
    (not_isCorner_of_snd_interior (by simp [bl] ; omega) (by simp [bl] ; omega))
    (isBoundary_of_fst_eq_zero (by simp [tl, hi]))
    (not_isCorner_of_snd_interior (by simp [tl]) (by simp [tl] ; omega))

theorem sideR_notMem_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) {P : Plaq n}
    (hi : P.i + 2 = n) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) : sideR P ∉ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  rw [sideR, mem_contour]
  push Not
  intro _
  exact hc _ _ (isBoundary_of_fst_last (by simp [tr] ; omega))
    (not_isCorner_of_snd_interior (by simp [tr]) (by simp [tr] ; omega))
    (isBoundary_of_fst_last (by simp [br] ; omega))
    (not_isCorner_of_snd_interior (by simp [br] ; omega) (by simp [br] ; omega))

theorem sideD_notMem_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) {P : Plaq n}
    (hj : P.j = 0) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) : sideD P ∉ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  rw [sideD, mem_contour]
  push Not
  intro _
  exact hc _ _ (isBoundary_of_snd_eq_zero (by simp [br, hj]))
    (not_isCorner_of_fst_interior (by simp [br]) (by simp [br] ; omega))
    (isBoundary_of_snd_eq_zero (by simp [bl, hj]))
    (not_isCorner_of_fst_interior (by simp [bl] ; omega) (by simp [bl] ; omega))

theorem sideU_notMem_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) {P : Plaq n}
    (hj : P.j + 2 = n) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) : sideU P ∉ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  rw [sideU, mem_contour]
  push Not
  intro _
  exact hc _ _ (isBoundary_of_snd_last (by simp [tl] ; omega))
    (not_isCorner_of_fst_interior (by simp [tl] ; omega) (by simp [tl] ; omega))
    (isBoundary_of_snd_last (by simp [tr] ; omega))
    (not_isCorner_of_fst_interior (by simp [tr]) (by simp [tr] ; omega))

/-! ## 4. At a corner plaquette the two outward sides are broken together -/

theorem corner_bl_iff_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) (hn : 2 < n)
    {P : Plaq n} (hi : P.i = 0) (hj : P.j = 0) :
    sideL P ∈ contour σ ↔ sideD P ∈ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  have heq : σ (tl P.i P.j P.hi P.hj) = σ (br P.i P.j P.hi P.hj) :=
    hc _ _ (isBoundary_of_fst_eq_zero (by simp [tl, hi]))
      (not_isCorner_of_snd_interior (by simp [tl]) (by simp [tl] ; omega))
      (isBoundary_of_snd_eq_zero (by simp [br, hj]))
      (not_isCorner_of_fst_interior (by simp [br]) (by simp [br] ; omega))
  rw [sideL, sideD, mem_contour, mem_contour]
  exact ⟨fun h => ⟨adj_sideD P, by rw [heq] at h; exact fun e => h.2 e.symm⟩,
    fun h => ⟨adj_sideL P, by rw [← heq] at h; exact fun e => h.2 e.symm⟩⟩

theorem corner_tl_iff_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) (hn : 2 < n)
    {P : Plaq n} (hi : P.i = 0) (hj : P.j + 2 = n) :
    sideL P ∈ contour σ ↔ sideU P ∈ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  have heq : σ (bl P.i P.j P.hi P.hj) = σ (tr P.i P.j P.hi P.hj) :=
    hc _ _ (isBoundary_of_fst_eq_zero (by simp [bl, hi]))
      (not_isCorner_of_snd_interior (by simp [bl] ; omega) (by simp [bl] ; omega))
      (isBoundary_of_snd_last (by simp [tr] ; omega))
      (not_isCorner_of_fst_interior (by simp [tr]) (by simp [tr] ; omega))
  rw [sideL, sideU, mem_contour, mem_contour]
  exact ⟨fun h => ⟨adj_sideU P, by rw [heq] at h; exact fun e => h.2 e.symm⟩,
    fun h => ⟨adj_sideL P, by rw [← heq] at h; exact fun e => h.2 e.symm⟩⟩

theorem corner_br_iff_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) (hn : 2 < n)
    {P : Plaq n} (hi : P.i + 2 = n) (hj : P.j = 0) :
    sideR P ∈ contour σ ↔ sideD P ∈ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  have heq : σ (tr P.i P.j P.hi P.hj) = σ (bl P.i P.j P.hi P.hj) :=
    hc _ _ (isBoundary_of_fst_last (by simp [tr] ; omega))
      (not_isCorner_of_snd_interior (by simp [tr]) (by simp [tr] ; omega))
      (isBoundary_of_snd_eq_zero (by simp [bl, hj]))
      (not_isCorner_of_fst_interior (by simp [bl] ; omega) (by simp [bl] ; omega))
  rw [sideR, sideD, mem_contour, mem_contour]
  exact ⟨fun h => ⟨adj_sideD P, by rw [heq] at h; exact h.2.symm⟩,
    fun h => ⟨adj_sideR P, by rw [heq]; exact h.2.symm⟩⟩

theorem corner_tr_iff_of_const {σ : Config n} (hc : BoundaryConstOffCorner σ) (hn : 2 < n)
    {P : Plaq n} (hi : P.i + 2 = n) (hj : P.j + 2 = n) :
    sideR P ∈ contour σ ↔ sideU P ∈ contour σ := by
  have h1 := P.hi
  have h2 := P.hj
  have heq : σ (br P.i P.j P.hi P.hj) = σ (tl P.i P.j P.hi P.hj) :=
    hc _ _ (isBoundary_of_fst_last (by simp [br] ; omega))
      (not_isCorner_of_snd_interior (by simp [br] ; omega) (by simp [br] ; omega))
      (isBoundary_of_snd_last (by simp [tl] ; omega))
      (not_isCorner_of_fst_interior (by simp [tl] ; omega) (by simp [tl] ; omega))
  rw [sideR, sideU, mem_contour, mem_contour]
  exact ⟨fun h => ⟨adj_sideU P, by rw [← heq]; exact fun e => h.2 e.symm⟩,
    fun h => ⟨adj_sideR P, by rw [heq]; exact fun e => h.2 e.symm⟩⟩

/-! ## 5. Which directions are NOT outward -/

theorem not_outward_of_fst_ne_zero {P : Plaq n} (h : P.i ≠ 0) : ¬ Outward P 0 := by
  intro ho
  rcases (outward_iff P 0).mp ho with ⟨-, h0⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h h0
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem not_outward_of_snd_ne_last {P : Plaq n} (h : P.j + 2 ≠ n) : ¬ Outward P 1 := by
  intro ho
  rcases (outward_iff P 1).mp ho with ⟨h0, -⟩ | ⟨-, h0⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact absurd h0 (by decide)
  · exact h h0
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)

theorem not_outward_of_fst_ne_last {P : Plaq n} (h : P.i + 2 ≠ n) : ¬ Outward P 2 := by
  intro ho
  rcases (outward_iff P 2).mp ho with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, h0⟩ | ⟨h0, -⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact h h0
  · exact absurd h0 (by decide)

theorem not_outward_of_snd_ne_zero {P : Plaq n} (h : P.j ≠ 0) : ¬ Outward P 3 := by
  intro ho
  rcases (outward_iff P 3).mp ho with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, h0⟩
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact h h0

/-! ## 6. The converse -/

/-- **ONE VALUE ON THE BOUNDARY AWAY FROM THE CORNERS IS ENOUGH.** Nine cases, one per position of
the plaquette: interior, one of four rims, one of four corners. The four `if`s are rewritten in
direction order `0, 1, 2, 3` throughout, because `if_neg`'s condition is not determined by its
argument and each rewrite therefore lands on the leading one. -/
theorem evenDegrees_of_boundaryConstOffCorner {σ : Config n} (hc : BoundaryConstOffCorner σ)
    (hn : 2 < n) : EvenDegrees (dualGraph σ) := by
  refine (evenDegrees_dualGraph_iff σ).mpr fun P => ?_
  rw [Finset.card_filter, Fin.sum_univ_four]
  have h1 := P.hi
  have h2 := P.hj
  by_cases hi0 : P.i = 0
  · by_cases hj0 : P.j = 0
    · by_cases hb : sideL P ∈ contour σ
      · rw [if_pos ⟨hb, (leftP_eq_self_iff P).mpr hi0⟩,
          if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
          if_pos ⟨(corner_bl_iff_of_const hc hn hi0 hj0).mp hb, (downP_eq_self_iff P).mpr hj0⟩]
        exact ⟨1, rfl⟩
      · rw [if_neg (fun h => hb h.1),
          if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => hb ((corner_bl_iff_of_const hc hn hi0 hj0).mpr h.1))]
        exact ⟨0, rfl⟩
    · by_cases hj2 : P.j + 2 = n
      · by_cases hb : sideL P ∈ contour σ
        · rw [if_pos ⟨hb, (leftP_eq_self_iff P).mpr hi0⟩,
            if_pos ⟨(corner_tl_iff_of_const hc hn hi0 hj2).mp hb, (upP_eq_self_iff P).mpr hj2⟩,
            if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
          exact ⟨1, rfl⟩
        · rw [if_neg (fun h => hb h.1),
            if_neg (fun h => hb ((corner_tl_iff_of_const hc hn hi0 hj2).mpr h.1)),
            if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
          exact ⟨0, rfl⟩
      · rw [if_neg (fun h => sideL_notMem_of_const hc hi0 (by omega) (by omega) h.1),
          if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
        exact ⟨0, rfl⟩
  · by_cases hi2 : P.i + 2 = n
    · by_cases hj0 : P.j = 0
      · by_cases hb : sideR P ∈ contour σ
        · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
            if_pos ⟨hb, (rightP_eq_self_iff P).mpr hi2⟩,
            if_pos ⟨(corner_br_iff_of_const hc hn hi2 hj0).mp hb, (downP_eq_self_iff P).mpr hj0⟩]
          exact ⟨1, rfl⟩
        · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => hb h.1),
            if_neg (fun h => hb ((corner_br_iff_of_const hc hn hi2 hj0).mpr h.1))]
          exact ⟨0, rfl⟩
      · by_cases hj2 : P.j + 2 = n
        · by_cases hb : sideR P ∈ contour σ
          · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
              if_pos ⟨(corner_tr_iff_of_const hc hn hi2 hj2).mp hb,
                (upP_eq_self_iff P).mpr hj2⟩,
              if_pos ⟨hb, (rightP_eq_self_iff P).mpr hi2⟩,
              if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
            exact ⟨1, rfl⟩
          · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
              if_neg (fun h => hb ((corner_tr_iff_of_const hc hn hi2 hj2).mpr h.1)),
              if_neg (fun h => hb h.1),
              if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
            exact ⟨0, rfl⟩
        · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => sideR_notMem_of_const hc hi2 (by omega) (by omega) h.1),
            if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
          exact ⟨0, rfl⟩
    · by_cases hj0 : P.j = 0
      · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
          if_neg (fun h => sideD_notMem_of_const hc hj0 (by omega) (by omega) h.1)]
        exact ⟨0, rfl⟩
      · by_cases hj2 : P.j + 2 = n
        · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
            if_neg (fun h => sideU_notMem_of_const hc hj2 (by omega) (by omega) h.1),
            if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
          exact ⟨0, rfl⟩
        · rw [if_neg (fun h => not_outward_of_fst_ne_zero (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_fst_ne_last (P := P) (by omega) h.2),
            if_neg (fun h => not_outward_of_snd_ne_zero (P := P) (by omega) h.2)]
          exact ⟨0, rfl⟩

/-- **THE CHARACTERISATION.** -/
theorem evenDegrees_iff_boundaryConstOffCorner (σ : Config n) (hn : 2 < n) :
    EvenDegrees (dualGraph σ) ↔ BoundaryConstOffCorner σ :=
  ⟨fun hev _ _ hbp hcp hbq hcq =>
    EvenDegreesBoundary.const_offCorner_of_evenDegrees hev hn hbp hcp hbq hcq,
   fun hc => evenDegrees_of_boundaryConstOffCorner hc hn⟩

end EvenDegreesConverse
