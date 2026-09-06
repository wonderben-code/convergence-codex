import RayPieceParity
import LeftPartDecomposition
import DualUnique

/-!
# Selecting the odd piece, with no boundary condition

`RayPieceParity` named what assembling its parity with the site's spin would need: *the crossings of
a decomposition to sum to the crossings of the whole, and a decomposition of the contour to apply it
to.* **Both exist, and were not composed.** `DualUnique` has `bonds_sup`, `bonds_disjoint`,
`bonds_foldr` and `pairwise_disjoint_bonds`; `SurroundsParity` has `crossings_foldr_union` and
`exists_odd_of_odd_sum`; and `LeftPartDecomposition` supplies a decomposition of **any** finite
graph, `Plaq n` included.

**This composes them.** The result is the piece-selection step of a Peierls argument **with no
boundary condition on the configuration**, and with the pieces allowed to be **paths** as well as
circuits.

## What is proved

**`exists_odd_piece_of_decomposition`** — given any edge-disjoint decomposition of `dualGraph σ` and
any walk crossing its bond set an odd number of times, **some piece of the decomposition is crossed
an odd number of times**. `bonds_foldr` turns the decomposition of graphs into a decomposition of
bond sets, `pairwise_disjoint_bonds` keeps it disjoint, and `exists_odd_of_odd_sum` does the
pigeonhole.

**`exists_odd_path_or_cycle_piece`** — **so some piece is crossed oddly and is either the edge set
of a single path or the edge set of a single cycle**, by
`LeftPartDecomposition.exists_path_cycle_decomposition` applied to `dualGraph σ`. **No
`PlusBoundary`**, and the piece's kind comes back with it.

## What is NOT here

**THE SITE'S SPIN IS STILL NOT REACHED, AND THE REASON IS NOT THE ONE I HAD BEEN NAMING.**
`DualBonds.odd_crossings_bonds_of_down` links a down site to odd crossings of
`bonds σ (dualGraph σ)` — but it takes `PlusBoundary σ`, because **off that boundary condition
`bonds σ (dualGraph σ)` is not the contour**: an outward-facing broken side has no partner plaquette
and so contributes no dual edge. That is `OuterFaceObstruction`'s subject and it is **untouched**.
So the hypothesis *the walk crosses the bond set oddly* is, off `+`, **not known to follow from `x`
being down**, and nothing here supplies it. **Not attempted, no cost claimed** (`ERRATUM 246`).

**THE PIECE IS NOT LOCATED.** Residue (b) of `S3b-ii` wants a piece **near the site** running out to
a rim. This returns *some* piece, from a decomposition chosen by the Euler theorem, with **no
control over which** and no bound on its distance from anything. **Residue (b) is not closed and no
part of it is claimed.**

**NOTHING SAYS THE ODD PIECE IS A PATH RATHER THAN A CYCLE.** The dichotomy is returned as a
disjunction; **ruling out the cycle case would need the ray's crossings of a cycle piece to be
even**, which `RowParityLocate` gives only for the **full-width** ray, and the ray from an interior
site is not that. **This is a real gap and not a formality.**

**W3 DOES NOT MOVE.** Two existing theorems are composed with a third.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no `PlusBoundary` anywhere in this
file**, and no hypothesis on the walk beyond its crossing parity. That absence is the point — the
existing enclosure step, `DualUnique.odd_count_circuits_iff_down`, takes `PlusBoundary` and gives a
sharper conclusion; this takes none and gives a weaker one.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace OddPieceSelect

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open IsingContourSeparation
open IsingBoundaryField DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique
open SurroundsParity SimpleGraph

variable {n : ℕ}

/-! ## 1. The pigeonhole, transported along `bonds` -/

/-- **SOME PIECE OF THE DECOMPOSITION IS CROSSED AN ODD NUMBER OF TIMES.** -/
theorem exists_odd_piece_of_decomposition {σ : Config n} {L : List (SimpleGraph (Plaq n))}
    (hp : L.Pairwise Disjoint) (hjoin : L.foldr (· ⊔ ·) ⊥ = dualGraph σ)
    {x b : Site n} (w : (latticeGraph n).Walk x b)
    (hodd : ¬ Even (crossings (bonds σ (dualGraph σ)) w)) :
    ∃ H ∈ L, ¬ Even (crossings (bonds σ H) w) := by
  rw [← hjoin, bonds_foldr] at hodd
  obtain ⟨γ, hγ, hodd'⟩ := exists_odd_of_odd_sum (pairwise_disjoint_bonds hp) w hodd
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hγ
  exact ⟨H, hH, hodd'⟩

/-! ## 2. And the pieces are paths and cycles, with no boundary condition -/

/-- **SO SOME PIECE IS CROSSED ODDLY AND IS THE EDGE SET OF A SINGLE PATH OR OF A SINGLE CYCLE.**
No hypothesis on the configuration. -/
theorem exists_odd_path_or_cycle_piece (σ : Config n) {x b : Site n}
    (w : (latticeGraph n).Walk x b)
    (hodd : ¬ Even (crossings (bonds σ (dualGraph σ)) w)) :
    ∃ H : SimpleGraph (Plaq n), (IsPathGraph H ∨ IsCycleGraph H) ∧
      ¬ Even (crossings (bonds σ H) w) := by
  obtain ⟨L, hkind, hp, hjoin⟩ :=
    LeftPartDecomposition.exists_path_cycle_decomposition (dualGraph σ)
  obtain ⟨H, hH, hoddH⟩ := exists_odd_piece_of_decomposition hp hjoin w hodd
  exact ⟨H, hkind H hH, hoddH⟩

end OddPieceSelect
