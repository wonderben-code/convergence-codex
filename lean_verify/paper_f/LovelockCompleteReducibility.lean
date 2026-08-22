import LovelockCurvProjectionOrthogonal
import LovelockActInverse

/-!
# Complete reducibility, and the sentence that said it needed a carrier

`LovelockActInverse.orth_of_invariant` proved half of Maschke's theorem for the `act`
representation on four-index arrays — the orthogonal complement of an `act`-stable set is
`act`-stable — **without averaging, without Haar measure and without finiteness**, because
`LovelockInnerPositive` and `LovelockInnerInvariant` had already supplied the invariant
positive-definite form that averaging is normally used to construct. And it said what was missing:

> **This is one ingredient of complete reducibility and not complete reducibility.** The other —
> that the set and its complement together are everything — is a statement about subspaces, and
> **no subspace type for four-index arrays exists here.**

`LovelockInnerSpace.arrEquiv` and `LovelockCurvProjectionOrthogonal.algCurv` supply one, so this
file closes it.

## What is proved

* **`actE`** — the change of frame carried to `EuclideanSpace ℝ (ArrIdx n)`, and **`Stable`**, the
  property of a submodule being closed under every orthogonal change of frame;
* **`inner_actE_left`** — `⟪actE Q x, y⟫ = ⟪x, actE Qᵀ y⟫`, which is `ip_act_transp` read through
  `inner_arrEquiv`. This is the adjoint identity the whole argument turns on;
* **`stable_orthogonal`** — the orthogonal complement of a stable submodule is stable. This is
  `orth_of_invariant`, restated where the objects are subspaces rather than predicates;
* **`exists_stable_complement`** — **COMPLETE REDUCIBILITY: every `act`-stable submodule of
  four-index arrays has an `act`-stable complement**, `Kᗮ`, with `IsCompl K Kᗮ`. That is Maschke
  for this representation, and the "and it is everything" half is Mathlib's
  `isCompl_orthogonal_of_hasOrthogonalProjection` on the carrier that now exists;
* **`stable_algCurv`** and **`exists_stable_complement_algCurv`** — the instantiation
  (`ERRATUM 201`): the algebraic curvature tensors are stable, by `isAlgCurv_act`, and therefore
  have a stable complement inside all four-index arrays.

## What this is NOT, and the wall does not move

**Complete reducibility is not `KillsWeyl`, and this file does not claim otherwise.** `WALLS` §W5.0
§5d already says why: **Schur's lemma needs the Weyl summand IRREDUCIBLE**, and nothing here
approaches irreducibility — a stable complement exists for every stable subspace, which is exactly
the statement that says nothing about which subspaces are minimal. **The watchlist item does not
move.**

**And the instantiation stops short of the one that would matter.** The natural next instance is
the **Weyl summand as a submodule**, whose stability is `LovelockActInverse.weylSet_act` — but that
is a statement about a *set*, and turning it into a `Submodule` needs `weylPart` to be additive and
homogeneous. **Neither lemma exists in this estate**: `weylPart` is linear because `ricci` and
`scal` are, and nobody has written it down. That is named here rather than assumed, and it is a
unit of work, not a wall.

**⚠ SUPERSEDED THE SAME DAY — `LovelockWeylSubmodule` WROTE THEM AND DID THE INSTANTIATION.**
Kept per `ERRATUM 94`, and **the sentence was right on both counts**: the two lemmas were absent,
and it was a unit of work rather than a wall. `weylPart_add` and `weylPart_smul` are there, built
from four linearity lemmas the estate already had in four different files; `weylSub` is the Weyl
summand as a submodule, `stable_weylSub` its stability, and `exists_stable_complement_weylSub` the
instantiation. **What still stands is the paragraph above it** — a stable complement for the Weyl
summand is still not `KillsWeyl`, Schur needs it **irreducible**, and the watchlist item does not
move. `ERRATUM 228`'s rule.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockCompleteReducibility

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerSpace
  LovelockEquivariance LovelockFrameInverse LovelockActInverse
  LovelockCurvProjectionOrthogonal

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The action on the carrier -/

/-- **THE CHANGE OF FRAME, ON THE CARRIER.** `act` conjugated by `arrEquiv`. -/
noncomputable def actE (Q : Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (ArrIdx n)) :
    EuclideanSpace ℝ (ArrIdx n) :=
  arrEquiv n (act Q ((arrEquiv n).symm x))

@[simp] theorem actE_arrEquiv (Q : Fin n → Fin n → ℝ)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    actE Q (arrEquiv n R) = arrEquiv n (act Q R) := rfl

/-- **A SUBMODULE IS STABLE** when every orthogonal change of frame maps it into itself. -/
def Stable (K : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n))) : Prop :=
  ∀ Q : Fin n → Fin n → ℝ, IsOrth Q → ∀ x ∈ K, actE Q x ∈ K

/-! ## 2. The adjoint identity the argument turns on -/

/-- **`⟪actE Q x, y⟫ = ⟪x, actE Qᵀ y⟫`** — `ip_act_transp` read through `inner_arrEquiv`. -/
theorem inner_actE_left (hQ : IsOrth Q) (x y : EuclideanSpace ℝ (ArrIdx n)) :
    inner ℝ (actE Q x) y = inner ℝ x (actE (transp Q) y) := by
  have hx : x = arrEquiv n ((arrEquiv n).symm x) := ((arrEquiv n).apply_symm_apply x).symm
  have hy : y = arrEquiv n ((arrEquiv n).symm y) := ((arrEquiv n).apply_symm_apply y).symm
  calc inner ℝ (actE Q x) y
      = inner ℝ (arrEquiv n (act Q ((arrEquiv n).symm x)))
          (arrEquiv n ((arrEquiv n).symm y)) := by rw [← hy]; rfl
    _ = ip (act Q ((arrEquiv n).symm x)) ((arrEquiv n).symm y) := inner_arrEquiv _ _
    _ = ip ((arrEquiv n).symm x) (act (transp Q) ((arrEquiv n).symm y)) := ip_act_transp hQ _ _
    _ = inner ℝ (arrEquiv n ((arrEquiv n).symm x))
          (arrEquiv n (act (transp Q) ((arrEquiv n).symm y))) := (inner_arrEquiv _ _).symm
    _ = inner ℝ x (actE (transp Q) y) := by rw [← hx]; rfl

/-! ## 3. Complete reducibility -/

/-- **THE ORTHOGONAL COMPLEMENT OF A STABLE SUBMODULE IS STABLE.** `orth_of_invariant`, restated
where the objects are subspaces. -/
theorem stable_orthogonal {K : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n))} (hK : Stable K) :
    Stable Kᗮ := by
  intro Q hQ x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [real_inner_comm, inner_actE_left hQ, real_inner_comm]
  exact (Submodule.mem_orthogonal K x).1 hx _ (hK (transp Q) (isOrth_transp hQ) u hu)

/-- **COMPLETE REDUCIBILITY.** Every `act`-stable submodule of four-index arrays has an
`act`-stable complement. No averaging, no Haar measure, no finiteness of a group: the invariant
positive-definite form does the work, and the "they are everything" half is Mathlib's, on the
carrier `LovelockInnerSpace` supplied.

**This is not `KillsWeyl` and not a step toward it** — Schur needs the Weyl summand *irreducible*,
and a stable complement for every stable subspace says nothing about which are minimal. -/
theorem exists_stable_complement (K : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)))
    [K.HasOrthogonalProjection] (hK : Stable K) :
    ∃ K' : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)), Stable K' ∧ IsCompl K K' :=
  ⟨Kᗮ, stable_orthogonal hK, Submodule.isCompl_orthogonal_of_hasOrthogonalProjection⟩

/-! ## 4. The instantiation (`ERRATUM 201`) -/

/-- **THE ALGEBRAIC CURVATURE TENSORS ARE STABLE**, by `isAlgCurv_act`. -/
theorem stable_algCurv : Stable (algCurv n) := fun Q _ _ hx => isAlgCurv_act Q hx

/-- **AND THEREFORE HAVE A STABLE COMPLEMENT** inside all four-index arrays. -/
theorem exists_stable_complement_algCurv :
    ∃ K' : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)), Stable K' ∧ IsCompl (algCurv n) K' :=
  exists_stable_complement _ stable_algCurv

end LovelockCompleteReducibility
