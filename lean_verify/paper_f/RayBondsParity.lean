import BondsDeficit
import RayWalk

/-!
# The enclosure step along a row, with no boundary condition at all

`BondsDeficit` proved that for **every** configuration the dual graph's bond set is the contour
with the outward-facing bonds deleted, and that a walk from a down site to an up site crosses that
bond set an odd number of times **as soon as it crosses the outward part evenly**. It left the new
hypothesis unexamined, and observed that on the walk `DualBonds.odd_crossings_bonds_of_down` uses
— which ends at the corner — it cannot be met by routing, because every bond at the corner faces
out.

**This file takes a different walk, and on it the hypothesis is free.** `RayWalk.leftRay` runs
along a **row** to the left edge of the box, and its steps are the bottom sides of the plaquettes
of that row. `not_outwardBond_sideD_of_interior_row` proves none of those faces out as soon as the
row is above the bottom — so such a ray crosses no outward bond **at all**, and the parity
condition holds with nothing to check.

> **`even_crossings_bonds_leftRay_iff`** — for **every** configuration, every interior row and
> every column: the dual graph's bonds are crossed evenly along the ray **exactly when the two
> ends of the ray carry the same spin**.

> **`odd_crossings_bonds_leftRay_of_down`** — so a **down** site whose row meets the left edge at
> an **up** site is enclosed, with **no condition on the configuration anywhere else in the box**.

`DualBonds.odd_crossings_bonds_of_down` needed `PlusBoundary`; this needs the spin at **one**
site, the one the walk ends at. That is the irreducible half, and §5 says how irreducible:
`no_spin_from_flip_invariant` proves **no condition on the configuration that survives flipping
every spin can determine a spin anywhere** — which covers `NoBrokenOutward`, the even-degree
condition on the dual graph, and every other property of the contour alone. It is carried here as
the explicit hypothesis it always was.

## What is proved

**`not_outwardBond_sideD_of_interior_row`** — **the geometry.** A horizontal bond in a row above
the bottom is no plaquette's outward side. Four cases: against a left or right side it fails on
the *columns* alone, with no appeal to outwardness at all; against another bottom side it needs
`Q.j = 0` and the row is not zero; against a top side it needs `Q.j + 2 = n`, which puts the bond
in row `n - 1`, and no plaquette has its bottom side there.

**`crossings_outwardPart_leftRay`** — so the ray's outward crossings are **zero**, not merely
even.

**`even_crossings_bonds_leftRay_iff`, `odd_crossings_bonds_leftRay_of_down`** — the two statements
above.

**`no_spin_from_flip_invariant`, `no_spin_from_contour_condition`** — **and the endpoint
hypothesis is irreducible for a whole family of replacements**: no condition on `σ` that survives
the global flip, and holds of something, can imply that a boundary site is up — and the second
theorem specialises that to **every** condition written about the contour alone, which is where
this chain's hypotheses live.

**`outwardBond_sideD_of_bottom_row`, `crossings_bonds_leftRay_bottom_eq_zero`** — **and the
excluded row is excluded for a reason, which is proved rather than asserted.** In row zero every
bond the ray crosses **is** an outward bond, so the dual graph's bonds are crossed **exactly zero
times** there whatever the configuration does. The ray along the bottom row sees nothing; the
hypothesis `0 < b.val` is not an artefact of the proof.

**The top row needs no exclusion of mine**: `RayWalk.crossings_leftRay` already requires
`b.val + 1 < n`, because a plaquette in row `j` needs `j + 1 < n` and there is no plaquette in the
last row to have a bottom side there.

## What is NOT here

**THE ENDPOINT SPIN IS STILL A HYPOTHESIS, AND §5 PROVES IT HAS TO BE.**
`σ (edge b.val b.isLt) = true` is a fact about one site, and `no_spin_from_flip_invariant` shows
no flip-invariant condition on `σ` implies it. **Nothing here weakens it and no condition of that
shape could.** What is **not** shown is that no condition of *any* shape could: a hypothesis that
is not flip-invariant — `PlusBoundary` itself, for one — supplies it at once. The theorem bounds a
family, not the whole space of hypotheses.

**THIS IS ONE WALK, NOT A COVERING.** The Peierls argument needs a contour *surrounding* `x`, and
what is produced is one odd crossing count along one ray. `SurroundsParity.odd_countP_iff_down`
turns odd crossing counts into an enclosing piece **only for a decomposition into pairwise
disjoint bond sets**, and **no decomposition is supplied here**. The step from this to *some
circuit surrounds `x`* is exactly what `DualUnique` does under `+`, and it is **not redone** for
the general case. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING IS REPAIRED.** The outward bonds are still missing from the dual graph; this file
chooses a walk that does not meet them. `ExtendedDual`'s four-rim construction is still the repair
and is still untouched.

**W3 DOES NOT MOVE.** `IsingBoundaryField.MagnetisationBound` needs the `3 ^ |γ|` count and the
circuit decomposition. Neither is touched.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `not_outwardBond_sideD_of_interior_row`
takes **`0 < P.j`** and the plaquette's own bounds; the three ray theorems take **`0 < b.val`** and
**`b.val + 1 < n`**, the second being `RayWalk.crossings_leftRay`'s own; and
`odd_crossings_bonds_leftRay_of_down` takes in addition **the two endpoint spins**. No
`PlusBoundary`, no `NoBrokenOutward`, no condition on `σ` away from the ray's two ends.

## ⚠ THE DECOMPOSITION THIS HEADER SAYS IS NOT SUPPLIED WAS SUPPLIED THE SAME HOUR.
Annotated 6 September 2026

*What is NOT here* says the step from one odd crossing count to *some circuit surrounds `x`* needs
a pairwise-disjoint decomposition, that none is supplied, and that it is `DualUnique`'s work under
`+` and is **not redone**. `paper_f/RayCircuitSurrounding.lean`, which **imports this file**, redoes
it:

* **`odd_count_circuits_leftRay_iff`** — `DualUnique.odd_count_circuits_iff_down`'s statement along
  a ray with **no condition on `σ`**, because every ingredient of that theorem except the crossing
  count was already free of `PlusBoundary`, and this file supplies the crossing count.
* **`exists_odd_path_or_cycle_piece_leftRay`** — and with **no hypothesis on `σ` at all** beyond the
  ray's two endpoints, some piece is crossed oddly and is a single path or a single cycle
  (`OddPieceSelect.exists_odd_path_or_cycle_piece` composed with the theorem below).
* **`exists_circuit_surrounding_leftRay`** — and under `EvenDegrees (dualGraph σ)` the piece is a
  **cycle**.

**The paragraph's caution survives the closure and is sharpened there**: a path is not an
enclosure, so the hypothesis-free version is weaker in *content* and not only in hypotheses
(`ERRATUM 97`), and the piece still depends on the walk.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace RayBondsParity

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open PlaquetteLattice IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph DualBonds BondsContourGap BondsDeficit
open RowParity RayWalk SimpleGraph

/- The same classical instance `DualBonds` and `BondsDeficit` open, for the same predicate over
`Plaq n`, whose `Fintype` is noncomputable. -/
set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A horizontal bond above the bottom row faces nothing out -/

/-- **A BOTTOM SIDE IN A ROW ABOVE ZERO IS NO PLAQUETTE'S OUTWARD SIDE.** -/
theorem not_outwardBond_sideD_of_interior_row {P : Plaq n} (h0 : 0 < P.j) :
    ¬ OutwardBond (sideD P) := by
  rintro ⟨Q, d, hside, hout⟩
  have hi := P.hi
  have hj := P.hj
  have hqi := Q.hi
  have hqj := Q.hj
  fin_cases d
  · simp only [sideOf, sideL, sideD, bl, tl, br, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff] at hside
    omega
  · have h : Q.j + 2 = n := (upP_eq_self_iff Q).mp hout
    simp only [sideOf, sideU, sideD, tl, tr, br, bl, Sym2.eq_iff, Prod.ext_iff,
      Fin.ext_iff] at hside
    omega
  · simp only [sideOf, sideR, sideD, tr, br, bl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff] at hside
    omega
  · have h : Q.j = 0 := (downP_eq_self_iff Q).mp hout
    simp only [sideOf, sideD, br, bl, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff] at hside
    omega

/-! ## 2. So a ray along an interior row crosses no outward bond -/

theorem crossings_outwardPart_leftRay (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (outwardPart σ) (leftRay b k hk) = 0 := by
  rw [crossings_leftRay _ b hj k hk]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg]
  intro hmem
  exact not_outwardBond_sideD_of_interior_row (P := rowP b.val hj m) hb0
    (mem_outwardPart.mp hmem).2

/-! ## 3. The enclosure step, on every configuration -/

/-- **THE PARITY ALONG A ROW, FOR EVERY CONFIGURATION.** -/
theorem even_crossings_bonds_leftRay_iff (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    Even (crossings (bonds σ (dualGraph σ)) (leftRay b k hk))
      ↔ σ (col b k hk) = σ (edge b.val b.isLt) := by
  have h := even_crossings_bonds_iff σ (leftRay b k hk)
  rw [crossings_outwardPart_leftRay σ b hb0 hj k hk] at h
  simpa using h

/-- **A DOWN SITE WHOSE ROW MEETS THE LEFT EDGE AT AN UP SITE IS ENCLOSED**, with no condition on
the configuration anywhere else in the box. -/
theorem odd_crossings_bonds_leftRay_of_down (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ¬ Even (crossings (bonds σ (dualGraph σ)) (leftRay b k hk)) := by
  rw [even_crossings_bonds_leftRay_iff σ b hb0 hj k hk, hx, he]
  exact Bool.noConfusion

/-! ## 4. And the excluded row is excluded for a reason

In row zero every bond the ray crosses is an outward bond, so the dual graph has none of them and
the ray sees nothing at all. The hypothesis `0 < b.val` is not an artefact of the proof. -/

theorem outwardBond_sideD_of_bottom_row {P : Plaq n} (h : P.j = 0) : OutwardBond (sideD P) :=
  ⟨P, 3, rfl, (downP_eq_self_iff P).mpr h⟩

/-- **ALONG THE BOTTOM ROW THE DUAL GRAPH'S BONDS ARE CROSSED EXACTLY ZERO TIMES**, whatever the
configuration does. -/
theorem crossings_bonds_leftRay_bottom_eq_zero (σ : Config n) (b : Fin n) (hb0 : b.val = 0)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ (dualGraph σ)) (leftRay b k hk) = 0 := by
  rw [crossings_leftRay _ b hj k hk]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg]
  exact sideOf_notMem_bonds_of_outward σ
    (P := rowP b.val hj m) (d := 3) ((downP_eq_self_iff _).mpr hb0)

/-! ## 5. Why the endpoint hypothesis cannot be replaced by a condition on the contour

`NoBrokenOutwardCharacterised.no_spin_from_criterion` refutes the implication for
`NoBrokenOutward` on a named configuration. The same argument needs nothing about that predicate
except that the global flip preserves it — and every condition on the contour alone has that
property, by `IsingContourInvariant.contour_flip`. -/

/-- **NO FLIP-INVARIANT CONDITION DETERMINES A SPIN.** If `p` survives flipping every spin and
holds of something, then `p` cannot imply that a boundary site is up: the witness and its flip
disagree there. -/
theorem no_spin_from_flip_invariant (hn : 0 < n) {p : Config n → Prop}
    (hflip : ∀ τ, p τ → p (flip τ)) {τ₀ : Config n} (h0 : p τ₀) :
    ¬ ∀ (τ : Config n) (b : Site n), p τ → isBoundary b = true → τ b = true := by
  intro h
  have hc := isBoundary_corner n hn
  have h1 := h τ₀ _ h0 hc
  have h2 := h (flip τ₀) _ (hflip τ₀ h0) hc
  rw [IsingFiniteVolume.flip, h1] at h2
  exact Bool.noConfusion h2

/-- **AND THAT COVERS EVERY CONDITION ON THE CONTOUR ALONE**, since the flip does not move the
contour (`IsingContourInvariant.contour_flip`). `NoBrokenOutward` is one such condition
(`BondsContourCriterion.NoBrokenOutward` mentions `contour σ` and nothing else) and so is
`EvenDegrees (dualGraph σ)`, by `DualDegreeExact.dualGraph_congr`. -/
theorem no_spin_from_contour_condition (hn : 0 < n) (q : Finset (Sym2 (Site n)) → Prop)
    {τ₀ : Config n} (h0 : q (contour τ₀)) :
    ¬ ∀ (τ : Config n) (b : Site n), q (contour τ) → isBoundary b = true → τ b = true :=
  no_spin_from_flip_invariant hn (p := fun τ => q (contour τ))
    (fun τ h => show q (contour (flip τ)) by
      rw [IsingContourInvariant.contour_flip]; exact h) h0

end RayBondsParity
