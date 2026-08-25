/-
  IsingChainClosedForm.lean — the chain's energy, written as a sum instead of a recursion.

  WHY. `IsingChainDecay.chainE` is defined by recursion: level `k + 1` is level `k` with one more
  site hung off it. The box's model is a **sum** over interaction terms. The two will have to be
  compared, and comparing a recursion with a sum is not a comparison — one of them has to be
  rewritten. This file rewrites the chain side, which is the side that can be rewritten once and
  for all, independently of any box.

  `chainE_eq`: `chainE E J 0 m σ` is the base model's energy at the tower's last position, plus `J`
  times the sum, over the `m` consecutive pairs of positions, of the product of the two spins.
  Nothing here is about the Ising box; it is a statement about the chain construction alone.

  **THE POSITIONS ARE THE PREVIOUS UNIT'S, NOT NEW ONES.** `siteAt` is `IsingChainIndex`'s
  equivalence read backwards, and the two facts driving the induction are that one's
  `chainEquivFin_some` and `chainEquivFin_none` — adding a site pushes every position up by one and
  the new site takes position `0`. That is exactly what makes the bonds come out as *consecutive*
  pairs `(j, j+1)` rather than some other pairing, which is the whole content of the closed form.

  **THE BASE TYPE IS `Fin 1`, WHICH IS A CHOICE AND NOT A THEOREM**, carried over from
  `IsingChainIndex` for the same reason: it is what makes the tower's positions come out as
  `Fin (m + 1)`. A chain hanging off a larger base is a different statement and this file does not
  make it.

  WHAT REMAINS. The box side is not touched here. Showing that
  `IsingRegionSplit`'s region energy for the walk's model is this sum — with `J = β` on each walk
  bond and the base carrying the boundary field — is the next step, is **not attempted**, and its
  cost is not claimed (`ERRATUM 246`). **No wall moves and nothing here is a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingChainIndex

namespace IsingChainClosedForm

open Finset Real
open IsingTransfer2D IsingChainDecay IsingPendantSite IsingChainIndex

/-- The tower's site at position `j`. -/
def siteAt (m : ℕ) (j : Fin (m + 1)) : chainSite (Fin 1) m := (chainEquivFin m).symm j

theorem siteAt_zero (m : ℕ) : siteAt (m + 1) 0 = none := by
  rw [siteAt, Equiv.symm_apply_eq, chainEquivFin_none]

theorem siteAt_succ (m : ℕ) (y : Fin (m + 1)) : siteAt (m + 1) y.succ = some (siteAt m y) := by
  rw [siteAt, siteAt, Equiv.symm_apply_eq, chainEquivFin_some, Equiv.apply_symm_apply]

theorem siteAt_one (m : ℕ) :
    siteAt (m + 1) (0 : Fin (m + 1)).succ = some (lastSite (Fin 1) 0 m) := by
  rw [siteAt_succ]
  congr 1
  rw [siteAt, Equiv.symm_apply_eq, chainEquivFin_lastSite]

/-- **THE CHAIN'S ENERGY, AS A SUM.** The base model at the last position, plus `J` on each of the
`m` consecutive pairs. The bonds are consecutive because `IsingChainIndex.chainEquivFin_some` says
adding a site shifts every position up by one — that fact, and not the arithmetic, is what makes
this closed form true. -/
theorem chainE_eq (E : (Fin 1 → Bool) → ℝ) (J : ℝ) :
    ∀ (m : ℕ) (σ : chainSite (Fin 1) m → Bool),
      chainE E J 0 m σ
        = E (fun _ => σ (siteAt m (Fin.last m)))
          + J * ∑ j : Fin m, spin (σ (siteAt m j.castSucc)) * spin (σ (siteAt m j.succ))
  | 0, σ => by
      have hs : σ = fun _ => σ (siteAt 0 (Fin.last 0)) := by
        funext v; congr 1; exact Subsingleton.elim v _
      simp only [chainE, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
      exact congrArg E hs
  | m + 1, σ => by
      rw [chainE, pendantE, chainE_eq E J m (fun x => σ (some x)), Fin.sum_univ_succ]
      have hlast : siteAt (m + 1) (Fin.last (m + 1)) = some (siteAt m (Fin.last m)) := by
        rw [← Fin.succ_last, siteAt_succ]
      have hnew : spin (σ (siteAt (m + 1) (0 : Fin (m + 1)).castSucc))
            * spin (σ (siteAt (m + 1) (0 : Fin (m + 1)).succ))
          = spin (σ (some (lastSite (Fin 1) 0 m))) * spin (σ none) := by
        rw [Fin.castSucc_zero, siteAt_zero, siteAt_one]
        ring
      have hold : ∀ j : Fin m,
          spin (σ (siteAt (m + 1) (j.succ).castSucc)) * spin (σ (siteAt (m + 1) (j.succ).succ))
            = spin (σ (some (siteAt m j.castSucc))) * spin (σ (some (siteAt m j.succ))) := by
        intro j
        rw [← Fin.succ_castSucc, siteAt_succ, siteAt_succ]
      rw [hlast, hnew, Finset.sum_congr rfl (fun j _ => hold j)]
      ring

/-- **THE SHAPE THE BOX'S WALK MODEL ACTUALLY HAS**: a field of strength `c` at the base and `J` on
every bond. Named here rather than left to the reader to specialise, so that the comparison the next
step must make is between two written-down sums and not between a sum and an instruction. -/
theorem chainE_field (c J : ℝ) (m : ℕ) (σ : chainSite (Fin 1) m → Bool) :
    chainE (fun τ => c * spin (τ 0)) J 0 m σ
      = c * spin (σ (siteAt m (Fin.last m)))
        + J * ∑ j : Fin m, spin (σ (siteAt m j.castSucc)) * spin (σ (siteAt m j.succ)) := by
  rw [chainE_eq]

end IsingChainClosedForm
