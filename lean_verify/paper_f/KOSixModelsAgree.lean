/-
  KOSixModelsAgree: the two models of the four-block space are isomorphic, and the two
  algebra actions correspond — a prose disclaimer turned into a theorem

  SPINE LINK L18. `KOSixInnerProduct` built the inner-product model
  `HfE n = EuclideanSpace ℂ (Fin n × Fin 4)` and a genuine unital ⋆-action on it, and closed
  its own header with a disclaimer:

  > *"No equivalence to `Hf n` is proved. `HfE n` is `EuclideanSpace ℂ (Fin n × Fin 4)` and
  > `Hf n` is a nested product; they are abstractly isomorphic and the isomorphism is not
  > constructed here, so nothing in `KOSixSpectralTriple` is transported. The agreement with
  > `piRepC` is at the level of the definition — `a` on blocks 0 and 1, `ā` on blocks 2 and 3
  > — and is stated in this comment rather than as a theorem, deliberately, because the
  > theorem needs the isomorphism."*

  **This unit builds the isomorphism and proves that agreement.** The disclaimer said what was
  missing precisely enough to be a work order, which is the point of writing disclaimers that
  way — and the claim it protected was TRUE, so this is a promotion rather than a correction.

  WHAT IS PROVED.
  * **`blockEquiv : HfE n ≃ₗ[ℂ] Hf n`** — the reindexing, built in two halves so that only
    one of them is new work: `WithLp.linearEquiv` is Mathlib's, stripping the `L²` wrapper off
    `EuclideanSpace`, and `hfSliceEquiv` — named at the third attempt, `splitEquiv` being
    taken by `PairingGlue` and `sliceEquiv` by `LatticeSliceCount` — is the pure reindexing
    `((Fin n × Fin 4) → ℂ) ≃ₗ[ℂ] Hf n` that sends `v` to the four slices
    `fun i => v (i, b)`.
  * **`blockEquiv_apply`** and **`blockEquiv_symm_apply`** — both directions computed, so
    later units can rewrite rather than unfold.
  * **`piRep_corresponds`** — **the theorem the disclaimer promised**:
    `blockEquiv (piRepRing a v) = piRepC a (blockEquiv v)`. The two actions are the same map
    read through the two spellings of the space, so `KOSixRepairedAction`'s results about
    `piRepC` and `KOSixInnerProduct`'s about `piRepRing` are results about one object.
  * **`blockDiagonal_mulVec`** — `blockDiagonal` acting on a vector, blockwise. Mathlib has
    `blockDiagonal_mul` but **no `blockDiagonal_mulVec`**: `grep` over the whole environment
    dump returns nothing, so the one this unit needs is stated here. That is the second
    `blockDiagonal`-family gap this pair of units has hit, after `mbar_mul`.

  **AND WHAT IS DELIBERATELY NOT ADDED.** A first draft of this header promised a
  `piRepC_transported_ring_hom` — the repaired action's ring-hom properties re-derived on
  `Hf n` by transport, "as a check that the isomorphism is the right one". **It was dropped
  before the file was written, because it would have been a worse check than the one already
  here.** `piRep_corresponds` pins the isomorphism against both actions at every point;
  re-deriving `piRepC_add` from `piRepRing`'s additivity would only re-prove a theorem
  `KOSixRepairedAction` already has directly, and a second proof of a settled fact is not
  evidence about the isomorphism. Recorded because the header said it and the file does not.

  WHY THIS IS WORTH A UNIT AND NOT A REMARK. Two files now make claims about "the four-block
  space" while meaning two different types. Without the isomorphism those claim-sets are
  disjoint and a reader is entitled to ask which space the estate's spectral triple lives on.
  **`ERRATUM 565` was exactly the failure of citing true theorems about a different object**;
  an unproved identification between two models is the same hazard one level up. With
  `piRep_corresponds` the question has an answer that is machine-checked rather than
  editorial.

  WHAT IS **NOT** CLAIMED.
  * **`Hf n` still has no inner product**, and this does not give it one. The isomorphism is
    `ℂ`-LINEAR, not isometric — `Hf n` carries no norm to be isometric with respect to. So
    `piRepRing_star` does **not** transport to a statement about `Hf n`, and nothing here
    makes `Hf n` usable as a `Triple`'s `H`.
  * **The instance diamond is untouched.** `IsScalarTower ℝ ℂ (EuclideanSpace ℂ ι)` still does
    not resolve, so a `Triple` is still not assembled and four of its five fields are still
    unbuilt. This unit changes none of that; it connects two models, it does not climb.
  * **`J`, `γ`, `D` and `piOp` are not transported.** `KOSixSpectralTriple.J` is antilinear
    and `blockEquiv` is a `ℂ`-linear equivalence, so conjugating `J` by it gives an antilinear
    map on `HfE n`. ~~which `Module.End ℂ (HfE n)` cannot hold, exactly as
    `KOSixInnerProduct`'s header says.~~ **That framing was wrong — `ERRATUM 571`.** An
    antilinear map on `HfE n` is perfectly expressible, as `HfE n →ₛₗ[starRingEnd ℂ] HfE n`,
    and `KOSixRealStructureE.Jmap` is one. What remains true is that **this unit does not
    build the transport**, which is a statement about what was done and not about what can
    be.
  * **No KO-dimension, order condition, or connection to `CascadeHilbert`, `CascadeAlgebra` or
    the 96** — L18's standing residue.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import KOSixInnerProduct

namespace KOSixModelsAgree

open Matrix ComplexConjugate KOSixSpectralTriple KOSixInnerProduct

noncomputable section

variable {n : ℕ}

/-! ## 1. The reindexing -/

/-- The pure reindexing half: a function on `Fin n × Fin 4` is four functions on `Fin n`.
No `L²` structure is involved, which is why this is the only new work — Mathlib's
`WithLp.linearEquiv` supplies the other half. -/
def hfSliceEquiv : ((Fin n × Fin 4) → ℂ) ≃ₗ[ℂ] Hf n where
  toFun v := ((fun i => v (i, 0), fun i => v (i, 1)), (fun i => v (i, 2), fun i => v (i, 3)))
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := fun p =>
    if p.2 = 0 then w.1.1 p.1
    else if p.2 = 1 then w.1.2 p.1
    else if p.2 = 2 then w.2.1 p.1
    else w.2.2 p.1
  left_inv v := by
    funext p
    obtain ⟨i, b⟩ := p
    fin_cases b <;> simp
  right_inv w := by rfl

/-- **The isomorphism.** `EuclideanSpace ℂ (Fin n × Fin 4)` and the nested four-block product
are the same `ℂ`-space, spelled differently. -/
def blockEquiv : HfE n ≃ₗ[ℂ] Hf n :=
  (WithLp.linearEquiv 2 ℂ ((Fin n × Fin 4) → ℂ)).trans hfSliceEquiv

@[simp]
theorem blockEquiv_apply (v : HfE n) :
    blockEquiv v = ((fun i => v (i, 0), fun i => v (i, 1)),
      (fun i => v (i, 2), fun i => v (i, 3))) := rfl

@[simp]
theorem blockEquiv_symm_apply (w : Hf n) (i : Fin n) (b : Fin 4) :
    (blockEquiv.symm w) (i, b)
      = if b = 0 then w.1.1 i else if b = 1 then w.1.2 i
        else if b = 2 then w.2.1 i else w.2.2 i := rfl

/-! ## 2. The two actions correspond -/

/-- **`blockDiagonal` acting on a vector, blockwise.** Mathlib has `blockDiagonal_mul` but
**no `blockDiagonal_mulVec`** — `grep 'blockDiagonal.*mulVec\|mulVec.*blockDiagonal'` over the
whole environment dump returns nothing — so the one this unit needs is stated here. -/
theorem blockDiagonal_mulVec {m o : Type*} [Fintype m] [Fintype o] [DecidableEq o]
    (M : o → Matrix m m ℂ) (w : (m × o) → ℂ) (i : m) (b : o) :
    (Matrix.blockDiagonal M).mulVec w (i, b) = (M b).mulVec (fun j => w (j, b)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

theorem fourBlock_mulVec (a : Matrix (Fin n) (Fin n) ℂ) (w : (Fin n × Fin 4) → ℂ)
    (i : Fin n) (b : Fin 4) :
    (fourBlock a).mulVec w (i, b)
      = (if b.val < 2 then a else mbar a).mulVec (fun j => w (j, b)) i :=
  blockDiagonal_mulVec _ w i b

/-- **THE THEOREM `KOSixInnerProduct`'s DISCLAIMER PROMISED.** The block-diagonal action on
the re-indexed space and the repaired action on the nested product are the same map read
through the two spellings. So the two files' results are results about one object. -/
theorem piRep_corresponds (a : Matrix (Fin n) (Fin n) ℂ) (v : HfE n) :
    blockEquiv (piRepRing a v) = KOSixRepairedAction.piRepC a (blockEquiv v) := by
  rw [blockEquiv_apply, blockEquiv_apply, KOSixRepairedAction.piRepC_apply]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    · funext i
      rw [piRepRing_apply]
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (fourBlock a)) v).ofLp _ = _
      rw [Matrix.ofLp_toEuclideanCLM, fourBlock_mulVec]
      norm_num

end

end KOSixModelsAgree
