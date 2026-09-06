import CriterionStrictlyWeaker
import RimBoundary

/-!
# The criterion, characterised exactly: it is `+` or `−` on the boundary and nothing else

`BondsContourCriterion` extracted `NoBrokenOutward` — *no broken side faces out of the box* — as
the exact condition under which the dual graph's bond set is the contour. It did not ask what the
condition **is**; `CriterionStrictlyWeaker` did, one unit later, and fenced it: *"the obvious
guess, that it holds exactly when every edge of the box is constant, is **not proved**. Not
attempted, no cost claimed"*. That fence is the only one in the estate, and this file answers it.

**The guess was right, and this file proves it**, with no hypothesis on the box size:

> **`noBrokenOutward_iff`** — `NoBrokenOutward σ ↔ PlusBoundary σ ∨ PlusBoundary (flip σ)`

The configuration is up at every boundary site, or down at every boundary site, and there is no
third possibility.

## Why it is true, in one paragraph

`RimBoundary.outward_side_isBoundary` already gives one direction: an outward side has both ends
on the boundary, so a configuration constant there breaks none of them. The other direction is
the converse geometry, which the estate did not have: **every rim bond of the box IS an outward
side of a plaquette**, exhibited rather than assumed — the vertical bond from `(0, k)` to
`(0, k+1)` is the left side of the plaquette at `(0, k)`, and `leftP_eq_self_iff` says that side
faces out. So the criterion forbids every rim bond from being broken, and the four rims are four
paths meeting at the corners, so `σ` cannot change anywhere along the edge of the box.

## What is proved

**`noBrokenOutward_of_boundary_const`** — the easy direction. This is
`RimBoundary.no_rim_edge_of_boundary_const`'s argument stated about the criterion rather than
about `extDual`'s rim edges, which is where that file used it.

**`left_step`, `top_step`, `right_step`, `bottom_step`** — **the converse geometry**: on each of
the four rims, consecutive sites carry the same spin. Each names the plaquette whose side the
bond is and gets `Outward` from the matching `*_eq_self_iff`. Note the statement being used is
**not** true of every bond with both ends on the boundary — in a `3 × 3` box the bond from
`(0,1)` to `(1,1)` has both ends on the boundary and is no plaquette's outward side — so each
case names its own plaquette and its own direction.

**`const_of_step`** — and a function on `Fin n` agreeing at consecutive arguments is constant.
One induction, used four times.

**`const_left`, `const_bottom`, `const_right`, `const_top`, `const_boundary`** — so `σ` agrees
with its value at the corner at every boundary site, the last two routed through a corner because
the right and top rims meet the anchor only there.

**`boundary_const_of_noBrokenOutward`** — **and that holds at every `n`**: below `1 < n` the rims
do not exist and none is needed, a box with `n ≤ 1` having at most one site.

**`noBrokenOutward_iff_boundary_const`** — **the criterion IS constancy on the boundary.**

**`noBrokenOutward_iff`** — **and therefore it is `+` or its flip**, since a `Bool` constant on a
set with at most one element is one of two things — the degenerate boxes included, and this is
why the theorem needs no hypothesis at all.

**`bonds_dualGraph_iff_plusBoundary_or_flip`** — read back onto the object the criterion was
extracted for: **the dual graph's bond set is the contour exactly when the configuration is
constant on the edge of the box.**

**`no_spin_from_criterion`** — **and no hypothesis about outward sides determines a boundary
spin.** `BondsContourCriterion` said this as a reading of its own proof; here it is a theorem,
refuted on a named configuration. `flip_not_both_plusBoundary_spin` exhibits the separating pair.

## What this settles about the two units before it

**`CriterionStrictlyWeaker.flip_strictly_weaker` found ALL of them.** That theorem moved the
whole `+` class off `PlusBoundary` and into the criterion; `noBrokenOutward_iff` says the
criterion contains **nothing else**. The class is exactly the `+` configurations and their flips.

**AND IT SAYS WHY NOTHING FOLLOWS FOR THE SPIN.** The criterion is invariant under the global
flip (`CriterionStrictlyWeaker.noBrokenOutward_flip`), and no invariant of that kind can tell `+`
from `−`. The second job `PlusBoundary` was doing in `DualBonds.odd_crossings_bonds_of_down` —
the walk's endpoint being **up** — is therefore not merely *not supplied* by this criterion; it
is **provably unreachable** from it, and `no_spin_from_criterion` is that proof.

## What is NOT here

**NOTHING IS REPAIRED.** On a configuration that fails the criterion the missing bonds are still
missing, and `ExtendedDual`'s four-rim construction is still the repair and is still untouched.
Knowing exactly which configurations fail — those that change value along the edge of the box —
repairs none of them.

**W3 DOES NOT MOVE.** A hypothesis is described exactly; it is not weakened, and the theorem it
feeds is unchanged. The one thing this file adds to the wall is **negative**:
`no_spin_from_criterion` says the route through this criterion cannot reach the spin, so that
route is closed rather than open.

**NO NEW WITNESS AND NO NEW GRAPH.** Every configuration in the class was already reachable:
`DualDegreeExact.flip_strict_extension` exhibited the flips, and this file adds none. What is new
is the word **exactly**.

**NO CLAIM ABOUT WHICH CONTOURS ARISE.** The characterisation is of the configurations, not of
their contours: *which* bond sets are contours of a boundary-constant configuration is **not
described, not attempted, no cost claimed** (`ERRATUM 246`).

**TWO SENTENCES OF A DRAFT OF THIS HEADER WERE FALSE, AND BOTH WERE ABOUT THIS ESTATE RATHER THAN
ABOUT THE MATHEMATICS** (`ERRATUM 476`). One fenced the degenerate case, saying the biconditional
fails at `n ≤ 1`; it does not, because the disjunct `PlusBoundary (flip σ)` covers the one-site
box — checking that is what removed `1 < n` from the characterisation. The other attributed the
guess-fence above to `BondsContourCriterion`, which never made it. Both were caught in review and
neither was pushed.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): the four characterisation theorems —
`noBrokenOutward_iff_boundary_const`, `noBrokenOutward_iff`,
`bonds_dualGraph_iff_plusBoundary_or_flip`, `boundary_const_of_noBrokenOutward` — and both
directions feeding them take **nothing at all**; `no_spin_from_criterion` takes **`0 < n`**, which
is what makes a boundary site exist; the four rim steps and the five `const_*` lemmas take
**`1 < n`**, which is what makes a plaquette exist. No `PlusBoundary` anywhere but in the
conclusions, no finiteness beyond the box, no decidability.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/
namespace NoBrokenOutwardCharacterised

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField DualObstruction DualGraph ExtendedDual
open BondsContourCriterion RimBoundary

variable {n : ℕ}

/-! ## 1. Constancy on the boundary kills every broken outward side

`RimBoundary.no_rim_edge_of_boundary_const` is this argument, used there to remove a rim edge of
`extDual`. Stated about the criterion it is the easy half of the characterisation, and it needs
nothing about `n`. -/

theorem noBrokenOutward_of_boundary_const {σ : Config n}
    (hconst : ∀ p q : Site n, isBoundary p = true → isBoundary q = true → σ p = σ q) :
    NoBrokenOutward σ := by
  intro P d hmem hout
  have hb := outward_side_isBoundary hout
  revert hmem hb
  refine Sym2.ind (fun a b hmem hb => ?_) (sideOf P d)
  rw [mem_contour] at hmem
  exact hmem.2 (hconst a b (hb a (Sym2.mem_mk_left a b)) (hb b (Sym2.mem_mk_right a b)))

/-! ## 2. The converse geometry: every rim bond is an outward side

This is what the estate did not have. `outward_side_isBoundary` sends outward sides to the
boundary; nothing sent boundary bonds back. Note the statement is **not** true of every bond with
both ends on the boundary — in a `3 × 3` box the bond from `(0,1)` to `(1,1)` has both ends on the
boundary and is no plaquette's outward side — so each of the four cases names its own plaquette
and its own direction. -/

/-- Column zero: consecutive sites carry the same spin. The bond is the **left** side of the
plaquette at `(0, k)`, which faces out because that plaquette's `i` is zero. -/
theorem left_step {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n)
    {k : ℕ} (hk : k + 1 < n) :
    σ ((⟨0, by omega⟩ : Fin n), (⟨k, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨k + 1, hk⟩ : Fin n)) := by
  have hP : (0 : ℕ) + 1 < n := by omega
  have hout : Outward (⟨0, k, hP, hk⟩ : Plaq n) 0 := (leftP_eq_self_iff _).mpr rfl
  have hnot : sideOf (⟨0, k, hP, hk⟩ : Plaq n) 0 ∉ contour σ := fun hm => hno _ 0 hm hout
  rw [show sideOf (⟨0, k, hP, hk⟩ : Plaq n) 0 = sideL (⟨0, k, hP, hk⟩ : Plaq n) from rfl,
    sideL, mem_contour] at hnot
  push Not at hnot
  exact hnot (adj_sideL _)

/-- The top row: consecutive sites carry the same spin. The bond is the **top** side of the
plaquette at `(k, n - 2)`, whose row index is written `n - 2 + 1` throughout so that no
truncated subtraction has to be reconciled with the plaquette the bond comes from. -/
theorem top_step {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n)
    {k : ℕ} (hk : k + 1 < n) :
    σ ((⟨k, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n))
      = σ ((⟨k + 1, hk⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n)) := by
  have hQ : n - 2 + 1 < n := by omega
  have hout : Outward (⟨k, n - 2, hk, hQ⟩ : Plaq n) 1 :=
    (upP_eq_self_iff _).mpr (show n - 2 + 2 = n by omega)
  have hnot : sideOf (⟨k, n - 2, hk, hQ⟩ : Plaq n) 1 ∉ contour σ := fun hm => hno _ 1 hm hout
  rw [show sideOf (⟨k, n - 2, hk, hQ⟩ : Plaq n) 1 = sideU (⟨k, n - 2, hk, hQ⟩ : Plaq n) from rfl,
    sideU, mem_contour] at hnot
  push Not at hnot
  exact hnot (adj_sideU _)

/-- The right column: consecutive sites carry the same spin. The bond is the **right** side of
the plaquette at `(n - 2, k)`, its column index again written `n - 2 + 1`. -/
theorem right_step {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n)
    {k : ℕ} (hk : k + 1 < n) :
    σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨k, by omega⟩ : Fin n))
      = σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨k + 1, hk⟩ : Fin n)) := by
  have hP : n - 2 + 1 < n := by omega
  have hout : Outward (⟨n - 2, k, hP, hk⟩ : Plaq n) 2 :=
    (rightP_eq_self_iff _).mpr (show n - 2 + 2 = n by omega)
  have hnot : sideOf (⟨n - 2, k, hP, hk⟩ : Plaq n) 2 ∉ contour σ := fun hm => hno _ 2 hm hout
  rw [show sideOf (⟨n - 2, k, hP, hk⟩ : Plaq n) 2 = sideR (⟨n - 2, k, hP, hk⟩ : Plaq n) from rfl,
    sideR, mem_contour] at hnot
  push Not at hnot
  exact (hnot (adj_sideR _)).symm

/-- Row zero: consecutive sites carry the same spin. The bond is the **bottom** side of the
plaquette at `(k, 0)`. -/
theorem bottom_step {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n)
    {k : ℕ} (hk : k + 1 < n) :
    σ ((⟨k, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))
      = σ ((⟨k + 1, hk⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hQ : (0 : ℕ) + 1 < n := by omega
  have hout : Outward (⟨k, 0, hk, hQ⟩ : Plaq n) 3 := (downP_eq_self_iff _).mpr rfl
  have hnot : sideOf (⟨k, 0, hk, hQ⟩ : Plaq n) 3 ∉ contour σ := fun hm => hno _ 3 hm hout
  rw [show sideOf (⟨k, 0, hk, hQ⟩ : Plaq n) 3 = sideD (⟨k, 0, hk, hQ⟩ : Plaq n) from rfl,
    sideD, mem_contour] at hnot
  push Not at hnot
  exact (hnot (adj_sideD _)).symm

/-! ## 3. And so each rim is constant, and the four rims meet at the corners -/

/-- A function on `Fin n` that agrees at consecutive arguments is constant. The induction is
written once and used on all four rims. -/
theorem const_of_step (hn : 0 < n) (f : Fin n → Bool)
    (h : ∀ (k : ℕ) (hk1 : k + 1 < n), f ⟨k, by omega⟩ = f ⟨k + 1, hk1⟩) :
    ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = f ⟨0, hn⟩ := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [← h m hm]
    exact ih (by omega)

theorem const_left {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n) {y : Site n}
    (hy : y.1.val = 0) :
    σ y = σ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hn0 : 0 < n := by omega
  have key := const_of_step hn0 (fun t : Fin n => σ ((⟨0, hn0⟩ : Fin n), t))
    (fun k hk1 => left_step hno hn hk1) y.2.val y.2.isLt
  have hy' : y = ((⟨0, hn0⟩ : Fin n), y.2) := Prod.ext_iff.mpr ⟨Fin.ext hy, rfl⟩
  calc σ y = σ ((⟨0, hn0⟩ : Fin n), y.2) := by rw [← hy']
    _ = _ := key

theorem const_bottom {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n) {y : Site n}
    (hy : y.2.val = 0) :
    σ y = σ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hn0 : 0 < n := by omega
  have key := const_of_step hn0 (fun t : Fin n => σ (t, (⟨0, hn0⟩ : Fin n)))
    (fun k hk1 => bottom_step hno hn hk1) y.1.val y.1.isLt
  have hy' : y = (y.1, (⟨0, hn0⟩ : Fin n)) := Prod.ext_iff.mpr ⟨rfl, Fin.ext hy⟩
  calc σ y = σ (y.1, (⟨0, hn0⟩ : Fin n)) := by rw [← hy']
    _ = _ := key

/-- The right rim meets the anchor only at the bottom-right corner, so this one is two steps. -/
theorem const_right {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n) {y : Site n}
    (hy : y.1.val + 1 = n) :
    σ y = σ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hn0 : 0 < n := by omega
  have hlt : n - 2 + 1 < n := by omega
  have key := const_of_step hn0 (fun t : Fin n => σ ((⟨n - 2 + 1, hlt⟩ : Fin n), t))
    (fun k hk1 => right_step hno hn hk1) y.2.val y.2.isLt
  have hy' : y = ((⟨n - 2 + 1, hlt⟩ : Fin n), y.2) :=
    Prod.ext_iff.mpr ⟨Fin.ext (show y.1.val = n - 2 + 1 by omega), rfl⟩
  have hcorner : σ ((⟨n - 2 + 1, hlt⟩ : Fin n), (⟨0, hn0⟩ : Fin n))
      = σ ((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)) := const_bottom hno hn rfl
  calc σ y = σ ((⟨n - 2 + 1, hlt⟩ : Fin n), y.2) := by rw [← hy']
    _ = σ ((⟨n - 2 + 1, hlt⟩ : Fin n), (⟨0, hn0⟩ : Fin n)) := key
    _ = _ := hcorner

/-- The top rim meets the anchor only at the top-left corner. -/
theorem const_top {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n) {y : Site n}
    (hy : y.2.val + 1 = n) :
    σ y = σ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hn0 : 0 < n := by omega
  have hlt : n - 2 + 1 < n := by omega
  have key := const_of_step hn0 (fun t : Fin n => σ (t, (⟨n - 2 + 1, hlt⟩ : Fin n)))
    (fun k hk1 => top_step hno hn hk1) y.1.val y.1.isLt
  have hy' : y = (y.1, (⟨n - 2 + 1, hlt⟩ : Fin n)) :=
    Prod.ext_iff.mpr ⟨rfl, Fin.ext (show y.2.val = n - 2 + 1 by omega)⟩
  have hcorner : σ ((⟨0, hn0⟩ : Fin n), (⟨n - 2 + 1, hlt⟩ : Fin n))
      = σ ((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)) := const_left hno hn rfl
  calc σ y = σ (y.1, (⟨n - 2 + 1, hlt⟩ : Fin n)) := by rw [← hy']
    _ = σ ((⟨0, hn0⟩ : Fin n), (⟨n - 2 + 1, hlt⟩ : Fin n)) := key
    _ = _ := hcorner

/-- **THE CRITERION FORCES `σ` TO ITS CORNER VALUE AT EVERY BOUNDARY SITE.** -/
theorem const_boundary {σ : Config n} (hno : NoBrokenOutward σ) (hn : 1 < n) {y : Site n}
    (hy : isBoundary y = true) :
    σ y = σ ((⟨0, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  rw [isBoundary, decide_eq_true_eq] at hy
  rcases hy with h | h | h | h
  · exact const_left hno hn h
  · exact const_right hno hn h
  · exact const_bottom hno hn h
  · exact const_top hno hn h

/-- **AND SO `σ` IS CONSTANT ON THE BOUNDARY — AT EVERY `n`.** Below `1 < n` the rims do not
exist, and none is needed: a box with `n ≤ 1` has at most one site. -/
theorem boundary_const_of_noBrokenOutward {σ : Config n} (hno : NoBrokenOutward σ) :
    ∀ p q : Site n, isBoundary p = true → isBoundary q = true → σ p = σ q := by
  intro p q hp hq
  by_cases hn : 1 < n
  · exact (const_boundary hno hn hp).trans (const_boundary hno hn hq).symm
  · have h1 := p.1.isLt
    have h2 := p.2.isLt
    have h3 := q.1.isLt
    have h4 := q.2.isLt
    have hpq : p = q := Prod.ext_iff.mpr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    rw [hpq]

/-! ## 4. The characterisation, at every box size -/

/-- **THE CRITERION IS EXACTLY CONSTANCY ALONG THE EDGE OF THE BOX.** -/
theorem noBrokenOutward_iff_boundary_const (σ : Config n) :
    NoBrokenOutward σ ↔
      ∀ p q : Site n, isBoundary p = true → isBoundary q = true → σ p = σ q :=
  ⟨boundary_const_of_noBrokenOutward, noBrokenOutward_of_boundary_const⟩

theorem plusBoundary_or_flip_of_boundary_const {σ : Config n}
    (h : ∀ p q : Site n, isBoundary p = true → isBoundary q = true → σ p = σ q) :
    PlusBoundary σ ∨ PlusBoundary (flip σ) := by
  by_cases hn0 : 0 < n
  · have hc := isBoundary_corner n hn0
    cases hcv : σ (⟨⟨0, hn0⟩, ⟨0, hn0⟩⟩ : Site n) with
    | true => exact Or.inl fun p hp => (h p _ hp hc).trans hcv
    | false =>
      refine Or.inr fun p hp => ?_
      have hval := (h p _ hp hc).trans hcv
      simp [IsingFiniteVolume.flip, hval]
  · exact Or.inl fun p _ => absurd p.1.isLt (by omega)

theorem boundary_const_of_plusBoundary_or_flip {σ : Config n}
    (h : PlusBoundary σ ∨ PlusBoundary (flip σ)) :
    ∀ p q : Site n, isBoundary p = true → isBoundary q = true → σ p = σ q := by
  rcases h with h | h
  · exact fun p q hp hq => by rw [h p hp, h q hq]
  · intro p q hp hq
    have h1 := h p hp
    have h2 := h q hq
    simp only [IsingFiniteVolume.flip, Bool.not_eq_true'] at h1 h2
    rw [h1, h2]

/-- **AND SO THE CRITERION IS `+` OR `−`, AND NOTHING ELSE — WITH NO HYPOTHESIS ON `n`.** -/
theorem noBrokenOutward_iff (σ : Config n) :
    NoBrokenOutward σ ↔ (PlusBoundary σ ∨ PlusBoundary (flip σ)) :=
  (noBrokenOutward_iff_boundary_const σ).trans
    ⟨plusBoundary_or_flip_of_boundary_const, boundary_const_of_plusBoundary_or_flip⟩

/-- Read back onto the object the criterion was extracted for. -/
theorem bonds_dualGraph_iff_plusBoundary_or_flip (σ : Config n) :
    DualBonds.bonds σ (dualGraph σ) = contour σ ↔ (PlusBoundary σ ∨ PlusBoundary (flip σ)) :=
  (bonds_dualGraph_iff σ).trans (noBrokenOutward_iff σ)

/-! ## 5. And the spin is provably out of reach of the criterion

`BondsContourCriterion` isolated the second job `PlusBoundary` was doing in
`DualBonds.odd_crossings_bonds_of_down` — the walk's endpoint being **up** — and carried it as an
explicit hypothesis, saying no criterion about outward sides could supply it. That was a reading
of the proof. §4 turns it into a theorem: the criterion is invariant under the global flip, and
the flip reverses every spin. -/

/-- **NO HYPOTHESIS ABOUT OUTWARD SIDES DETERMINES A BOUNDARY SPIN.** The all-up configuration's
flip satisfies the criterion and is down at the corner, so the implication fails on it. -/
theorem no_spin_from_criterion (hn : 0 < n) :
    ¬ ∀ (τ : Config n) (b : Site n), NoBrokenOutward τ → isBoundary b = true → τ b = true := by
  intro h
  have h1 := h (flip fun _ => true) (⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n)
    (CriterionStrictlyWeaker.noBrokenOutward_flip_of_plusBoundary plusBoundary_allTrue)
    (isBoundary_corner n hn)
  simp [IsingFiniteVolume.flip] at h1

/-- The two configurations that separate them, named: a `+` configuration and its flip agree on
the criterion and disagree at every boundary site. -/
theorem flip_not_both_plusBoundary_spin {σ : Config n} (hσ : PlusBoundary σ)
    {b : Site n} (hb : isBoundary b = true) :
    NoBrokenOutward σ ∧ NoBrokenOutward (flip σ) ∧ σ b = true ∧ flip σ b = false := by
  refine ⟨noBrokenOutward_of_plusBoundary hσ,
    CriterionStrictlyWeaker.noBrokenOutward_flip_of_plusBoundary hσ, hσ b hb, ?_⟩
  simp [IsingFiniteVolume.flip, hσ b hb]

end NoBrokenOutwardCharacterised
