import EvenDegreesReach

/-!
# The global statement `EvenDegreesReach` left unassembled

`EvenDegreesReach` proved that `EvenDegrees (dualGraph σ)` — the hypothesis
`RayCircuitSurrounding` uses in place of `PlusBoundary` — forbids a broken bond along the interior
of any rim and forces the two rim neighbours of each corner to agree, and fenced the obvious
consequence as unassembled. This is that consequence.

> **`const_offCorner_of_evenDegrees`** — under `EvenDegrees (dualGraph σ)` and `2 < n`, **every
> boundary site that is not a corner carries the same spin.**

The fence named the cost exactly: a **ranged** induction plus four corner glue steps.
`const_of_step_from` is the ranged induction, the four `*_const` run it on each rim over
`1 ≤ k ≤ n - 2`, and `bottom_anchor`, `right_anchor`, `top_anchor` are the glue —
`EvenDegreesReach`'s corner couplings, composed with the rim constancies, carry all four rims to
the single value `σ (0, 1)`.

## What is NOT here

**THE CONVERSE IS STILL NOT PROVED.** Nothing says a configuration constant on the boundary away
from the corners **satisfies** `EvenDegrees (dualGraph σ)`. That needs the trichotomy *every
plaquette is interior, one-rim or corner*, which `EvenDegreesReach.all_outward_two` shows is false
at `n = 2` and which is **not proved** above it. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**NOTHING IS SAID ABOUT THE FOUR CORNERS.** No theorem here constrains a corner spin, and **that
is a statement about these theorems, not about the condition**: whether the corners are genuinely
free needs the converse above.

**NO COUNT AND NO PROPORTION** (`ERRATUM 477`).

**NO THEOREM IS ADDED TO THE PEIERLS CHAIN.** This describes a hypothesis the chain already
carries. **W3 does not move. No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `const_of_step_from` takes **nothing**
beyond its own range; every other theorem takes **`EvenDegrees (dualGraph σ)` and `2 < n`**, and
the four `*_const` take in addition the range `1 ≤ k` and `k + 2 ≤ n`. No `PlusBoundary`.

## ⚠ THE CONVERSE WAS PROVED THE SAME HOUR. Annotated 6 September 2026

*What is NOT here* says the converse is not proved and names what it needs: the trichotomy *every
plaquette is interior, one-rim or corner*. `paper_f/EvenDegreesConverse.lean`, which **imports this
file**, supplies exactly that (`outward_iff`) and the converse with it, so

> **`evenDegrees_iff_boundaryConstOffCorner`** — for `2 < n`,
> `EvenDegrees (dualGraph σ) ↔ BoundaryConstOffCorner σ`.

**And the second fence above is answered by the first.** *Nothing is said about the four corners*
was a statement about these theorems; with the biconditional it becomes a consequence — the
right-hand side quantifies only over non-corner sites, so the corner spins are free. That file
records that the last step is left to the reader and states no theorem for it.

The remaining fences stand: **no count, no proportion, nothing below `2 < n`**, and no theorem is
added to the Peierls chain by either file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace EvenDegreesBoundary

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField DualObstruction DualGraph ExtendedDual DualDegreeExact
open EvenDegreesReach SimpleGraph

variable {n : ℕ}

/-! ## 1. A ranged version of the induction -/

/-- `NoBrokenOutwardCharacterised.const_of_step` over a range: steps from `lo` to `hi` make the
function constant there. -/
theorem const_of_step_from (f : Fin n → Bool) {lo hi : ℕ} (hlo : lo < n)
    (h : ∀ (k : ℕ) (hk : k + 1 < n), lo ≤ k → k + 1 ≤ hi → f ⟨k, by omega⟩ = f ⟨k + 1, hk⟩) :
    ∀ (k : ℕ), lo ≤ k → k ≤ hi → ∀ (hk : k < n), f ⟨k, hk⟩ = f ⟨lo, hlo⟩ := by
  intro k hlo'
  induction k, hlo' using Nat.le_induction with
  | base => intro _ _; rfl
  | succ m hm ih =>
    intro hhi hk
    rw [← h m hk hm hhi]
    exact ih (by omega) (by omega)

/-! ## 2. Each rim is constant away from its corners -/

theorem left_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 2 ≤ n) :
    σ ((⟨0, by omega⟩ : Fin n), (⟨j, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) := by
  have h0 : 0 < n := by omega
  refine const_of_step_from (lo := 1) (hi := n - 2)
    (fun t : Fin n => σ ((⟨0, h0⟩ : Fin n), t)) (by omega) ?_ j h1 (by omega) (by omega)
  intro k hk hk1 hk2
  exact left_rim_const (j := k) hev (by omega) (by omega)

theorem bottom_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 2 ≤ n) :
    σ ((⟨i, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))
      = σ ((⟨1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have h0 : 0 < n := by omega
  refine const_of_step_from (lo := 1) (hi := n - 2)
    (fun t : Fin n => σ (t, (⟨0, h0⟩ : Fin n))) (by omega) ?_ i h1 (by omega) (by omega)
  intro k hk hk1 hk2
  exact bottom_rim_const (i := k) hev (by omega) (by omega)

theorem right_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 2 ≤ n) :
    σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨j, by omega⟩ : Fin n))
      = σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) := by
  have hR : n - 2 + 1 < n := by omega
  refine const_of_step_from (lo := 1) (hi := n - 2)
    (fun t : Fin n => σ ((⟨n - 2 + 1, hR⟩ : Fin n), t)) (by omega) ?_ j h1 (by omega) (by omega)
  intro k hk hk1 hk2
  exact right_rim_const (j := k) hev (by omega) (by omega) (by omega)

theorem top_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 2 ≤ n) :
    σ ((⟨i, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n))
      = σ ((⟨1, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n)) := by
  have hR : n - 2 + 1 < n := by omega
  refine const_of_step_from (lo := 1) (hi := n - 2)
    (fun t : Fin n => σ (t, (⟨n - 2 + 1, hR⟩ : Fin n))) (by omega) ?_ i h1 (by omega) (by omega)
  intro k hk hk1 hk2
  exact top_rim_const (i := k) hev (by omega) (by omega) (by omega)

/-! ## 3. The corners glue the four rims to one value -/

/-- The value the whole non-corner boundary takes: the site just above the bottom-left corner. -/
theorem bottom_anchor {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ ((⟨1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) :=
  (corner_bl_coupling hev hn).symm

theorem right_anchor {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) :=
  (corner_br_coupling hev hn).trans
    ((bottom_const hev hn (i := n - 2) (by omega) (by omega)).trans (bottom_anchor hev hn))

theorem top_anchor {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ ((⟨1, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) :=
  (corner_tl_coupling hev hn).symm.trans (left_const hev hn (j := n - 2) (by omega) (by omega))

/-! ## 4. So the whole boundary, off the corners, carries one value -/

/-- A corner of the box: on a first-coordinate rim **and** on a second-coordinate rim. -/
def IsCorner (p : Site n) : Prop :=
  (p.1.val = 0 ∨ p.1.val + 1 = n) ∧ (p.2.val = 0 ∨ p.2.val + 1 = n)

/-- **EVERY BOUNDARY SITE THAT IS NOT A CORNER CARRIES THE SAME SPIN.** -/
theorem eq_anchor_of_boundary_offCorner {σ : Config n} (hev : EvenDegrees (dualGraph σ))
    (hn : 2 < n) {p : Site n} (hb : isBoundary p = true) (hc : ¬ IsCorner p) :
    σ p = σ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hR : n - 2 + 1 < n := by omega
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  rw [isBoundary, decide_eq_true_eq] at hb
  rw [IsCorner, not_and_or, not_or, not_or] at hc
  rcases hb with h | h | h | h
  · have hy : p = ((⟨0, h0⟩ : Fin n), p.2) := Prod.ext_iff.mpr ⟨Fin.ext h, rfl⟩
    have hj : 1 ≤ p.2.val ∧ p.2.val + 2 ≤ n := by
      rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · omega
      · omega
    calc σ p = σ ((⟨0, h0⟩ : Fin n), p.2) := by rw [← hy]
      _ = _ := left_const hev hn (j := p.2.val) hj.1 hj.2
  · have hy : p = ((⟨n - 2 + 1, hR⟩ : Fin n), p.2) :=
      Prod.ext_iff.mpr ⟨Fin.ext (show p.1.val = n - 2 + 1 by omega), rfl⟩
    have hj : 1 ≤ p.2.val ∧ p.2.val + 2 ≤ n := by
      rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · omega
      · omega
    calc σ p = σ ((⟨n - 2 + 1, hR⟩ : Fin n), p.2) := by rw [← hy]
      _ = σ ((⟨n - 2 + 1, hR⟩ : Fin n), (⟨1, h1⟩ : Fin n)) :=
          right_const hev hn (j := p.2.val) hj.1 hj.2
      _ = _ := right_anchor hev hn
  · have hy : p = (p.1, (⟨0, h0⟩ : Fin n)) := Prod.ext_iff.mpr ⟨rfl, Fin.ext h⟩
    have hi : 1 ≤ p.1.val ∧ p.1.val + 2 ≤ n := by
      rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · omega
      · omega
    calc σ p = σ (p.1, (⟨0, h0⟩ : Fin n)) := by rw [← hy]
      _ = σ ((⟨1, h1⟩ : Fin n), (⟨0, h0⟩ : Fin n)) :=
          bottom_const hev hn (i := p.1.val) hi.1 hi.2
      _ = _ := bottom_anchor hev hn
  · have hy : p = (p.1, (⟨n - 2 + 1, hR⟩ : Fin n)) :=
      Prod.ext_iff.mpr ⟨rfl, Fin.ext (show p.2.val = n - 2 + 1 by omega)⟩
    have hi : 1 ≤ p.1.val ∧ p.1.val + 2 ≤ n := by
      rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · omega
      · omega
    calc σ p = σ (p.1, (⟨n - 2 + 1, hR⟩ : Fin n)) := by rw [← hy]
      _ = σ ((⟨1, h1⟩ : Fin n), (⟨n - 2 + 1, hR⟩ : Fin n)) :=
          top_const hev hn (i := p.1.val) hi.1 hi.2
      _ = _ := top_anchor hev hn

/-- **THE GLOBAL STATEMENT `EvenDegreesReach` LEFT UNASSEMBLED.** -/
theorem const_offCorner_of_evenDegrees {σ : Config n} (hev : EvenDegrees (dualGraph σ))
    (hn : 2 < n) {p q : Site n} (hbp : isBoundary p = true) (hcp : ¬ IsCorner p)
    (hbq : isBoundary q = true) (hcq : ¬ IsCorner q) : σ p = σ q :=
  (eq_anchor_of_boundary_offCorner hev hn hbp hcp).trans
    (eq_anchor_of_boundary_offCorner hev hn hbq hcq).symm

end EvenDegreesBoundary
