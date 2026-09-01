import LovelockInnerInvariant
import LovelockFrameInverse

/-!
# Undoing a frame change on four-index arrays, and the step Maschke's theorem exists to reach

`LovelockFrameInverse` proved that a frame change on **2-tensors** can be undone —
`act2_transp_act2`, `eq_of_act2_eq` — and stopped there because that is what the diagonalisation
argument consumed. The four-index twin was never stated. `LovelockActComposition` has since proved
`act_one` and `act_mul`, so it is now three lines rather than a repeat of the 2-tensor computation.

## What is proved

* `transp_mul_self` — `Qᵀ · Q = 1` in Mathlib's spelling, from `IsOrth.cols`;
* **`act_transp_act`** and **`eq_of_act_eq`** — the four-index twins of `LovelockFrameInverse`'s two
  theorems. One restrictive hypothesis removed: the *arity*;
* **`ip_act_transp`** — `⟨act Q A, B⟩ = ⟨A, act Qᵀ B⟩`. **`act Qᵀ` is the `ip`-adjoint of
  `act Q`**, which is what `LovelockInnerInvariant`'s invariance says once one argument is moved
  rather than both;
* **`orth_of_invariant`** — **the orthogonal complement of an `act`-stable set is `act`-stable**;
* `weylSet_act` and **`ip_weylPart_eq_zero_act`** — the Weyl summand is such a set, so the previous
  item is not a statement about the empty predicate.

## What `orth_of_invariant` is, and the sentence in `WALLS` it bears on

`WALLS` §W5.0 §5b blocked complete reducibility on Mathlib's `Maschke.lean` taking `[Fintype G]`
and `Invariants.average` dividing by the group order, `O(n)` being infinite. **That is accurate
about Mathlib and it is worth being precise about what it explains.** Averaging over a finite group
is how one *manufactures* an invariant inner product when none is given; with an invariant product
in hand, the step averaging exists to reach — that the orthogonal complement of an invariant
subspace is invariant — **is two rewrites and needs no averaging, no Haar measure and no
finiteness.** `LovelockInnerPositive` and `LovelockInnerInvariant` put such a product in hand this
morning. `orth_of_invariant` is that step, stated on a predicate.

**IT IS NOT COMPLETE REDUCIBILITY, and the difference is the whole distance.** Complete
reducibility needs two things: the complement is invariant, *and* the two together are everything.
**Only the first is here.** The second is a statement about subspaces, and the estate has no
subspace type for four-index arrays — `LovelockReduction` §1's standing reason, a decision about
carriers rather than a mathematical obstruction, but a decision that has not been taken.

**⚠ SUPERSEDED 2026-08-22 — THE DECISION WAS TAKEN AND THE SECOND HALF IS PROVED.** Kept per
`ERRATUM 94`. `LovelockInnerSpace.arrEquiv` chose a carrier without placing an instance on the
array type, and `LovelockCompleteReducibility.exists_stable_complement` is the whole statement:
**every `act`-stable submodule of four-index arrays has an `act`-stable complement.** The
"together they are everything" half is Mathlib's
`Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`; **the invariance half is
`orth_of_invariant` below**, restated where the objects are subspaces. **What still stands is the
paragraph after this one**, and it is the one that matters: complete reducibility is still not
`KillsWeyl`, Schur needs the Weyl summand **irreducible**, and nothing approaches that — **the
watchlist item does not move.** `ERRATUM 228`'s rule: the correction lands in every place, so the
same note is on `orth_of_invariant`'s own docstring below.

**AND COMPLETE REDUCIBILITY WOULD NOT BE `KillsWeyl` EITHER.** Schur's lemma needs the Weyl
summand **irreducible**, which no argument here approaches, and over `ℝ` its sharp form needs more
still (§5b's first bullet). **The watchlist item does not move**, and this file is written so that
the phrase *"the Maschke blocker is gone"* is not what anybody takes from it: what is gone is one
named reason for one of the two ingredients of one of the two hypotheses of the theorem that would
finish it.

## Where it sits on the route

`WALLS` §W5.0 §5d numbers the candidate route's rungs. **This file is rung 3**, and it also removes
one restatement of rung 4's gap: `ip_act_transp` carries no `IsAlgCurv` anywhere, so the frame
change's adjoint is unconditional even though `T`'s equivariance is not.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.


## ⚠ "THE ESTATE HAS NO SUBSPACE TYPE FOR FOUR-INDEX ARRAYS" IS FALSE. Annotated 1 September 2026

Kept as written (`ERRATUM 94`, `ERRATUM 391`). **`LovelockCompleteReducibility` (2026-08-22 15:13)
proves that every `act`-stable SUBMODULE of four-index arrays has an `act`-stable complement**, and
instantiates it at `algCurv`; `LovelockWeylSubmodule` (15:22 the same day) then supplies the Weyl
summand as a `Submodule`, off `weylPart`'s additivity and homogeneity. So the carrier decision this
paragraph calls *"a decision that has not been taken"* was taken a week later.

**And the second clause is answered too, which is the sharper half.** This section says complete
reducibility needs *"the complement is invariant, and the two together are everything"*, and that
*"only the first is here"*. `LovelockCompleteReducibility` is named for exactly the missing half,
and it cites **this file's** `weylSet_act` on the way — the successor names the predecessor and the
predecessor never learns, which is `ERRATUM 389`'s one-directional habit.
-/

namespace LovelockActInverse

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality
  LovelockActComposition LovelockFrameInverse LovelockInnerInvariant Matrix Finset Kronecker

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The frame change is invertible on four-index arrays

`LovelockFrameInverse` did this on 2-tensors by hand, from `IsOrth.cols`, before the composition
law existed. With `act_mul` and `act_one` it is a rewrite.
-/

/-- `IsOrth.cols`, in Mathlib's matrix spelling. -/
theorem transp_mul_self (hQ : IsOrth Q) :
    Matrix.of (transp Q) * Matrix.of Q = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.of_apply, transp, Matrix.one_apply]
  rw [hQ.cols x y]
  by_cases h : x = y
  · simp [delta, h]
  · simp [delta, h]

/-- **UNDOING A FRAME CHANGE ON A FOUR-INDEX ARRAY.** The twin of
`LovelockFrameInverse.act2_transp_act2`, which was proved by hand because `act_mul` did not exist
yet. -/
theorem act_transp_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act (transp Q) (act Q R) a b c d = R a b c d := by
  rw [← act_mul]
  have h1 : (fun x y => (Matrix.of (transp Q) * Matrix.of Q) x y)
      = fun x y => (1 : Matrix (Fin n) (Fin n) ℝ) x y := by
    rw [transp_mul_self hQ]
  rw [h1, act_one]

/-- **AND SO THE FRAME CHANGE IS INJECTIVE.** The twin of
`LovelockFrameInverse.eq_of_act2_eq`. -/
theorem eq_of_act_eq (hQ : IsOrth Q) {A B : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h : ∀ a b c d, act Q A a b c d = act Q B a b c d) (a b c d : Fin n) :
    A a b c d = B a b c d := by
  have hfun : act Q A = act Q B :=
    funext fun x => funext fun y => funext fun z => funext fun w => h x y z w
  calc A a b c d = act (transp Q) (act Q A) a b c d := (act_transp_act hQ A a b c d).symm
    _ = act (transp Q) (act Q B) a b c d := by rw [hfun]
    _ = B a b c d := act_transp_act hQ B a b c d

/-! ## 2. The adjoint of a frame change -/

/-- **`act Qᵀ` IS THE `ip`-ADJOINT OF `act Q`.** `LovelockInnerInvariant.ip_act` moves both
arguments at once; this moves one. No `IsAlgCurv` and no symmetry — the statement is about the
action and the form, not about curvature. -/
theorem ip_act_transp (hQ : IsOrth Q) (A B : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (act Q A) B = ip A (act (transp Q) B) := by
  have hB : act Q (act (transp Q) B) = B := by
    funext a b c d
    exact act_transp_act (isOrth_transp hQ) B a b c d
  calc ip (act Q A) B = ip (act Q A) (act Q (act (transp Q) B)) := by rw [hB]
    _ = ip A (act (transp Q) B) := ip_act hQ _ _

/-! ## 3. The step averaging exists to reach

Read the header before reading this section as more than it is.
-/

/-- **THE ORTHOGONAL COMPLEMENT OF AN `act`-STABLE SET IS `act`-STABLE.** If `A` is `ip`-orthogonal
to everything satisfying `V`, so is `act Q A`, for every orthogonal `Q`. **Two rewrites, no
averaging, no Haar measure, no finiteness** — because `LovelockInnerPositive` and
`LovelockInnerInvariant` already supply the invariant positive-definite form that averaging is
normally used to construct.

**This is one ingredient of complete reducibility and not complete reducibility.** The other — that
the set and its complement together are everything — is a statement about subspaces, and no
subspace type for four-index arrays exists here. See the header.

**⚠ SUPERSEDED — `LovelockCompleteReducibility.exists_stable_complement` IS COMPLETE
REDUCIBILITY**, on the carrier `LovelockInnerSpace` supplied, with `stable_orthogonal` this very
theorem restated for subspaces. Kept per `ERRATUM 94`. **Still not `KillsWeyl`**: Schur needs
irreducibility. `ERRATUM 228`. -/
theorem orth_of_invariant (hQ : IsOrth Q) {V : (Fin n → Fin n → Fin n → Fin n → ℝ) → Prop}
    (hV : ∀ P, IsOrth P → ∀ R, V R → V (act P R))
    {A : Fin n → Fin n → Fin n → Fin n → ℝ} (hA : ∀ R, V R → ip A R = 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (hR : V R) :
    ip (act Q A) R = 0 := by
  rw [ip_act_transp hQ]
  exact hA _ (hV (transp Q) (isOrth_transp hQ) R hR)

/-- **THE WEYL SUMMAND IS AN `act`-STABLE SET**, by `act_weylPart` and `isAlgCurv_act`. Stated so
that `orth_of_invariant` is not a theorem about a predicate nothing satisfies. -/
theorem weylSet_act (hQ : IsOrth Q) {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h : ∃ X, IsAlgCurv X ∧ R = weylPart X) :
    ∃ X, IsAlgCurv X ∧ act Q R = weylPart X := by
  obtain ⟨X, hX, rfl⟩ := h
  exact ⟨act Q X, isAlgCurv_act Q hX,
    funext fun a => funext fun b => funext fun c => funext fun d => act_weylPart hQ X a b c d⟩

/-- **AND THEREFORE, AT THE WEYL SUMMAND:** an array orthogonal to every Weyl part stays orthogonal
to every Weyl part after a frame change. The instance of `orth_of_invariant` that a route to
`KillsWeyl` would use, written out because a general lemma with one instance is worth less than the
instance. -/
theorem ip_weylPart_eq_zero_act (hQ : IsOrth Q) {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hA : ∀ X, IsAlgCurv X → ip A (weylPart X) = 0)
    (X : Fin n → Fin n → Fin n → Fin n → ℝ) (hX : IsAlgCurv X) :
    ip (act Q A) (weylPart X) = 0 := by
  rw [ip_act_transp hQ]
  have hw : act (transp Q) (weylPart X) = weylPart (act (transp Q) X) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      act_weylPart (isOrth_transp hQ) X a b c d
  rw [hw]
  exact hA _ (isAlgCurv_act _ hX)

end LovelockActInverse
