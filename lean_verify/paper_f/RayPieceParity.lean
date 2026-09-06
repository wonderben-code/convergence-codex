import RowParityLocate
import RayWalk

/-!
# The ray's crossings of one piece, which is the bridge four fences have asked for

`EvenRowParity`, `RowParityCorrection` and `RowParityLocate` each carry a section headed **NO
RAY**, whose body says the ray argument — the one that runs a ray from a site and concludes the
site is **down** — is `RayWalk`'s and is not touched. **The heading is superseded here and the
body is not.** A ray appears; the argument does not.

`RayWalk.crossings_leftRay` computes the crossings of the leftward ray for an **arbitrary** bond
set as a sum of bottom-side indicators along a row — which is `RowParity.cntD`'s definition
verbatim. So every row-parity theorem of the last four units is a statement about a **ray** with no
further work, once the two sums are identified.

## What is proved

**`crossings_leftRay_eq_cntD`** — **the ray's crossings of a piece are that piece's row count.**
Stated for an arbitrary subgraph `H` of the dual and an arbitrary length `k`; the two sides are the
same sum, and the proof is `RayWalk.crossings_leftRay` against `RowParity.cntD`'s definition.

**`even_crossings_ray_of_no_endpoint_below`** — **so the full leftward ray from a site crosses a
piece an EVEN number of times when no exceptional plaquette lies below it**, and

**`odd_crossings_ray_of_odd_below`** — **an ODD number when the correction below it is odd.**

For a path graph, whose two exceptional plaquettes are its endpoints
(`PathGraphDegree.exists_endpoints_of_isPathGraph`), the pair reads: **the ray from a site crosses a
path piece oddly exactly when the site's row is strictly between the path's two ends.** That is the
open-path counterpart of the fact `RowParity.even_row` gives for a circuit, now stated about a ray
rather than about a row.

## What is NOT here

**THE SITE'S SPIN IS NOT REACHED, AND THAT IS THE REMAINING GAP.**
`SurroundsParity.odd_crossings_iff_down` links crossing parity to *`x` is down* — but for the
**whole contour**, not for one piece, and this file proves nothing about the whole contour.
Assembling the two needs the crossings of a **decomposition** to sum to the crossings of the whole
(`SurroundsParity.crossings_foldr_union`) **and** a decomposition of the contour into pieces to
apply it to; **neither step is taken here**. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NO CLUSTER, NO COVERING, NO PIECE NEAR `x`.** Residue (b) of `S3b-ii` needs a piece **near the
site** running out to a rim; what is here is a parity, for a piece given in advance. **Residue (b)
is not closed and no part of it is claimed.**

**THE RAY IS THE LEFTWARD ONE AND ITS LENGTH IS ARBITRARY.** Nothing here says the ray reaches the
edge of the box, nor that the parity is independent of the ray chosen — the latter is
`SurroundsParity.crossings_parity_indep` and it is proved **for the contour**, not for a piece.

**W3 DOES NOT MOVE.** A sum is identified with another sum.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `crossings_leftRay_eq_cntD` takes
**nothing but the row index being in range** — no `PlusBoundary`, no degree hypothesis, no
subgraph condition at all. The two corollaries inherit `RowParityLocate`'s, which are
`H ≤ dualGraph σ` and `PlusBoundary σ`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace RayPieceParity

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open IsingBoundaryField DualObstruction PlaquetteLattice DualGraph DualBonds
open CircuitSides RowParity RowParityCorrection RowParityLocate RayWalk SimpleGraph

variable {n : ℕ}

/-! ## 1. The bridge -/

/-- **THE RAY'S CROSSINGS OF A PIECE ARE THAT PIECE'S ROW COUNT.** Both sides are the same sum of
bottom-side indicators along the row. -/
theorem crossings_leftRay_eq_cntD (σ : Config n) (H : SimpleGraph (Plaq n)) (b : Fin n)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ H) (leftRay b k hk) = cntD σ H b.val hj k :=
  crossings_leftRay (bonds σ H) b hj k hk

/-! ## 2. So the row parities are ray parities -/

/-- **THE FULL LEFTWARD RAY CROSSES A PIECE EVENLY WHEN NO EXCEPTIONAL PLAQUETTE LIES BELOW IT.** -/
theorem even_crossings_ray_of_no_endpoint_below {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) {A B : Plaq n}
    (hAB : ∀ P : Plaq n, P ≠ A → P ≠ B → Even ((H.neighborSet P).ncard))
    (b : Fin n) (hj : b.val + 1 < n) (hk : n - 1 < n)
    (hA : ¬ A.j < b.val) (hB : ¬ B.j < b.val) :
    crossings (bonds σ H) (leftRay b (n - 1) hk) % 2 = 0 := by
  rw [crossings_leftRay_eq_cntD σ H b hj]
  exact even_cntD_of_no_endpoint_below hσ hle hAB hj hA hB

/-- **AND ODDLY WHEN THE CORRECTION BELOW IT IS ODD.** For a path graph this is: the ray from a
site crosses the piece oddly exactly when the site's row is strictly between the path's two ends. -/
theorem odd_crossings_ray_of_odd_below {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (b : Fin n) (hj : b.val + 1 < n)
    (hk : n - 1 < n) (hodd : Odd (degBelow H b.val)) :
    crossings (bonds σ H) (leftRay b (n - 1) hk) % 2 = 1 := by
  rw [crossings_leftRay_eq_cntD σ H b hj]
  exact odd_cntD_of_one_endpoint_below hσ hle hj hodd

end RayPieceParity
