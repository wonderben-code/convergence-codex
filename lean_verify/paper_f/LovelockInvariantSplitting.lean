import LovelockCurvProjectionAdjoint
import LovelockActInverse

/-!
# An explicit `O(n)`-invariant orthogonal splitting, and what it is not

`LovelockActInverse` proved that the `ip`-orthogonal complement of an `act`-stable set is
`act`-stable, and then said carefully what was still missing:

> **This is one ingredient of complete reducibility and not complete reducibility.** The other —
> that the set and its complement together are everything — is a statement about subspaces, and no
> subspace type for four-index arrays exists here.

**For `Curv` that other ingredient is now supplied, and not by choosing a carrier.**
`LovelockCurvProjection.curvProj` splits every four-index array explicitly as
`curvProj A + (A − curvProj A)`; `LovelockCurvProjectionAdjoint.ip_residue` says the second piece
is orthogonal to `Curv`; and this file adds the one fact that makes the splitting a splitting **of
representations** rather than of arrays.

## What is proved

* **`act_curvProj`** — **the projection commutes with every frame change.** Proved from the
  characterisation rather than from the formula: `act Q (curvProj A)` is an algebraic curvature
  tensor, it pairs with `Curv` exactly as `act Q A` does (two applications of
  `LovelockActInverse.ip_act_transp` around one of `ip_curvProj`), and
  `LovelockCurvProjectionUnique.curvProj_unique` finishes;
* `act_residue` — so the residue moves to the residue;
* **`act_perp`** — and the complement is `act`-stable, which is `LovelockActInverse`'s general
  lemma instantiated at `IsAlgCurv` via `AlgebraicCurvature.isAlgCurv_act`;
* **`splitting_unique`** — **the splitting is the only one**: any decomposition of `A` into an
  algebraic curvature tensor plus something orthogonal to `Curv` has `curvProj A` as its first
  piece.

## So the four-index arrays now split four ways, equivariantly and orthogonally

`LovelockProjections` and `LovelockEquivariance` split `Curv` into **Weyl ⊕ traceless-Ricci ⊕
scalar**, orthogonally (`LovelockOrthogonality`) and equivariantly (`act_weylPart` and its two
siblings). With this file, `ℝ^{n⁴}` itself splits as **Weyl ⊕ traceless-Ricci ⊕ scalar ⊕ Curv^⊥**,
every summand `act`-stable and every pair orthogonal, **built by hand: no averaging, no Haar
measure, no finiteness, and no carrier.**

## And that is still not what `WALLS` §W5.0 §5b needs

**Complete reducibility in the sense Schur consumes is the decomposition into *irreducibles*.** This
is a decomposition into four explicit summands, and **nothing here says any of them is
irreducible** — the Weyl summand's irreducibility over `ℝ` is exactly the open question, and
`Curv^⊥` is visibly not irreducible (it carries at least the totally antisymmetric part and the
Bianchi residue as separate invariant pieces, neither of which is computed here).

**`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.** What this file
retires is a sentence about a missing carrier, not the wall.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockInvariantSplitting

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerPositive
  LovelockInnerInvariant LovelockActInverse LovelockFrameInverse LovelockCurvProjection
  LovelockCurvProjectionUnique LovelockCurvProjectionAdjoint LovelockEquivariantAdjoint Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The projection is equivariant -/

/-- **THE PROJECTION COMMUTES WITH EVERY FRAME CHANGE.** -/
theorem act_curvProj (hQ : IsOrth Q) (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (curvProj A) a b c d = curvProj (act Q A) a b c d := by
  refine curvProj_unique (isAlgCurv_act Q (isAlgCurv_curvProj A)) ?_ a b c d
  intro B hB
  rw [ip_act_transp hQ, ip_curvProj (isAlgCurv_act (transp Q) hB) A,
    ← ip_act_transp hQ]

/-- **AND SO DOES THE RESIDUE.** -/
theorem act_residue (hQ : IsOrth Q) (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (fun x y z w => A x y z w - curvProj A x y z w) a b c d
      = act Q A a b c d - curvProj (act Q A) a b c d := by
  have hsub : act Q (fun x y z w => A x y z w - curvProj A x y z w) a b c d
      = act Q A a b c d - act Q (curvProj A) a b c d := by
    simp only [act, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsub, act_curvProj hQ]

/-! ## 2. And so the splitting is one of representations -/

/-- **THE COMPLEMENT IS `act`-STABLE TOO.** -/
theorem act_perp (hQ : IsOrth Q) {E : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hE : ∀ B, IsAlgCurv B → ip E B = 0) (B : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hB : IsAlgCurv B) : ip (act Q E) B = 0 :=
  orth_of_invariant hQ (fun P _ _ hR => isAlgCurv_act P hR) hE B hB

/-- **AND THE SPLITTING IS THE ONLY ONE.** -/
theorem splitting_unique {A X : Fin n → Fin n → Fin n → Fin n → ℝ} (hX : IsAlgCurv X)
    (hperp : ∀ B, IsAlgCurv B → ip (fun x y z w => A x y z w - X x y z w) B = 0)
    (a b c d : Fin n) : X a b c d = curvProj A a b c d := by
  refine curvProj_unique hX ?_ a b c d
  intro B hB
  have h := hperp B hB
  rw [ip_sub_left] at h
  linarith

end LovelockInvariantSplitting
