/-
  BimoduleRealStructure: the CCM identity `J π(a*) J = πOp(a)` at EVERY size, and the reason a
  bimodule escapes the obstruction the four-block space cannot

  SPINE LINKS L6 and L18. The unit before this one proved that the estate's repaired KO-6 action
  is `J`-INVARIANT and that `J`-invariance collapses CCM's order-zero condition into
  commutativity of the image — so order-zero fails there, and the diagnosis recorded was *"the
  space is wrong, not the proof missing"*. **This file turns that diagnosis into a theorem, and
  removes a size restriction while doing it.**

  WHAT WAS RESTRICTIVE. The estate's only `J`-implemented right action lives at ONE size:
  `OppositeFromRealStructure.piOpW_via_prodSwap` proves `Jprod π(a*) Jprod = πOp(op a)` for
  `a : M₂(ℂ)` on `EuclideanSpace ℂ (Fin 2 × Fin 2)`, and `RealSpectralWitness` consumes it there.
  Everything in that proof is pointwise algebra — **no `fin_cases`, no enumeration of two
  elements** — which is the signal that the size was a convenience. Here it is an arbitrary
  finite `ι`.

  WHAT IS PROVED, at every `ι`.
  * **`piL`** and **`piR`** — the two Kronecker slots as actions on `EuclideanSpace ℂ (ι × ι)`,
    assembled from `OrderOneNontrivial`'s `kronLeft`, `kronRight` and `matAlg`, all three of
    which were already general in their index types. **Nothing here re-proves them**; the names
    are the ones that file's own header already uses in prose, so that prose now resolves to
    declarations.
  * **`piL_piR_commute`** — order-zero at every `ι`, cited from `kron_slots_commute` rather than
    re-derived: different Kronecker slots commute and that is the whole content.
  * **`Jbi`** — the conjugate transpose, as `ConjugatePermutation.conjPerm (Equiv.prodComm ι ι)`:
    an ANTILINEAR involution, which is expressible only because `ERRATUM 571`'s correction
    widened the estate's `J` to a semilinear map.
  * **`submatrix_prodComm_kronLeft`** and **`piR_eq_conj_piL`** — **the CCM identity at every
    size**: `Jbi π(a*) Jbi = πR(op a)`. The `n = 2` proof generalises verbatim once the index
    type is a variable, which is the whole of the work and is worth saying plainly.

  AND THE CONTRAST THAT CLOSES THE LOOP WITH THE UNIT BEFORE.
  * **`Jbi_not_piL_invariant`** — `Jbi` is **not** `piL`-invariant, in the exact sense
    `RepairedActionJInvariant.JInvariant` defines. If it were, the identity above would force
    `π(a*) = πR(op a)`, i.e. `a* ⊗ 1 = 1 ⊗ aᵀ`, which fails already at `σ₁` on a single entry.
  * So the two units together say something sharper than either alone: **order-zero is not a
    condition a real structure can satisfy by being well behaved; it needs `J` to MOVE the
    action onto the other slot.** The four-block space's `J` cannot — all it can do is swap the
    halves and conjugate, which leaves the repaired action fixed — and the bimodule's `J` can,
    because the two slots are genuinely different places to be.

  WHAT IS **NOT** CLAIMED.
  * **No Dirac operator, no grading, no spectral triple at general `ι`.** `piL`, `piR`, `Jbi`
    and order-zero are size-free; `RealSpectralWitness`'s `D` and `γ` are built from Pauli
    matrices and Kronecker products and are **not** generalised here. So this is the bimodule
    and its real structure at every size, not a triple at every size.
  * **Order-ONE is not addressed at general `ι`.** It is a statement about a `D`, and there is
    no `D` here.
  * **`Jbi_not_piL_invariant` is stated at `ι = Fin 2`**, not for every `ι` with at least two
    elements. The general statement needs a non-commutativity witness parametrised by `ι`, and
    the concrete one is what the contrast with the previous unit needs.
  * **Nothing about the four-block space is added.** The previous unit's result stands as it is:
    about that `J` and any action invariant under it, and not a proof that no real spectral
    triple exists there.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35), and L6's rung 2 is not climbed: a bimodule at
    every size does not constrain the factor list.

  0 sorry. 0 new axioms. 14 declarations, thirteen on
  `[propext, Classical.choice, Quot.sound]` and one — `prodComm_involutive` — on `Quot.sound`
  alone, because swapping a pair twice is `rfl` and the only quotient in sight is `Prod` itself.
-/

import OppositeFromRealStructure
import RepairedActionJInvariant

namespace BimoduleRealStructure

open Matrix MulOpposite OrderOneNontrivial ConjugatePermutation
open scoped Kronecker

noncomputable section

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-! ## 1. The two slots as actions, at any size -/

/-- The LEFT action `a ↦ a ⊗ 1` on `EuclideanSpace ℂ (ι × ι)`. -/
def piL : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (ι × ι)) :=
  (matAlg (ι × ι)).comp (kronLeft ι ι)

/-- The RIGHT action `op b ↦ 1 ⊗ bᵀ`, out of the OPPOSITE algebra. -/
def piR : (Matrix ι ι ℂ)ᵐᵒᵖ →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (ι × ι)) :=
  (matAlg (ι × ι)).comp (kronRight ι ι)

@[simp] theorem piL_apply (a : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × ι)) :
    piL ι a v = Matrix.toEuclideanCLM (𝕜 := ℂ) (a ⊗ₖ (1 : Matrix ι ι ℂ)) v := rfl

@[simp] theorem piR_apply (b : (Matrix ι ι ℂ)ᵐᵒᵖ) (v : EuclideanSpace ℂ (ι × ι)) :
    piR ι b v = Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 : Matrix ι ι ℂ) ⊗ₖ (unop b)ᵀ) v := rfl

/-- **Order-zero at every size**, and cited rather than re-derived: different Kronecker slots
commute, which is `OrderOneNontrivial.kron_slots_commute`. -/
theorem piL_piR_commute (a : Matrix ι ι ℂ) (b : (Matrix ι ι ℂ)ᵐᵒᵖ) :
    Commute (piL ι a) (piR ι b) := by
  change Commute ((matAlg (ι × ι)) (kronLeft ι ι a)) ((matAlg (ι × ι)) (kronRight ι ι b))
  exact (kron_slots_commute ι ι a b).map (matAlg (ι × ι))

/-- **The left slot is faithful at every non-empty size.** `a ⊗ 1` determines `a`, read off one
entry with the second index pinned. `[Nonempty ι]` is needed and is the only place it is: over an
empty index type the matrix algebra is trivial and there is nothing to be faithful about. -/
theorem kronLeft_injective' [Nonempty ι] : Function.Injective (kronLeft ι ι) := by
  intro a b h
  obtain ⟨i0⟩ := ‹Nonempty ι›
  ext i j
  have h' : a ⊗ₖ (1 : Matrix ι ι ℂ) = b ⊗ₖ (1 : Matrix ι ι ℂ) := h
  have he := congrArg (fun M => M (i, i0) (j, i0)) h'
  simpa [Matrix.kroneckerMap, Matrix.one_apply] using he

theorem piL_injective [Nonempty ι] : Function.Injective (piL ι) :=
  fun _ _ h => kronLeft_injective' ι (matAlg_injective (ι × ι) h)

/-! ## 2. The conjugate transpose as an antilinear involution -/

omit [Fintype ι] [DecidableEq ι] in
/-- Swapping the two slots is an involution. -/
theorem prodComm_involutive (p : ι × ι) :
    (Equiv.prodComm ι ι) ((Equiv.prodComm ι ι) p) = p := rfl

/-- **The conjugate transpose on `ι × ι`**, as an ANTILINEAR involution. Expressible only
because `ERRATUM 571`'s correction widened the estate's real structure to a semilinear map. -/
def Jbi : EuclideanSpace ℂ (ι × ι) →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (ι × ι) :=
  conjPerm (Equiv.prodComm ι ι)

omit [DecidableEq ι] in
theorem Jbi_involutive (v : EuclideanSpace ℂ (ι × ι)) : Jbi ι (Jbi ι v) = v :=
  conjPerm_involutive _ (prodComm_involutive ι) v

/-! ## 3. The CCM identity, at every size -/

omit [Fintype ι] in
/-- The matrix identity behind it: conjugating `a* ⊗ 1` by the slot swap gives `1 ⊗ aᵀ`. This is
`OppositeFromRealStructure.submatrix_prodSwap_kronLeft` with the size made a variable, and the
proof is unchanged — which is the evidence that `Fin 2` was never doing any work. -/
theorem submatrix_prodComm_kronLeft (a : Matrix ι ι ℂ) :
    (((star a) ⊗ₖ (1 : Matrix ι ι ℂ)).submatrix (Equiv.prodComm ι ι) (Equiv.prodComm ι ι)).map
        (starRingEnd ℂ) = (1 : Matrix ι ι ℂ) ⊗ₖ aᵀ := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp [Matrix.kroneckerMap, Matrix.one_apply, apply_ite (starRingEnd ℂ), mul_comm]

/-- **`J π(a*) J = πR(op a)`, at every size.** The right action is `J`-implemented, so the pair
`(π, πR)` is a real structure's pair and not two independent choices. -/
theorem piR_eq_conj_piL (a : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × ι)) :
    Jbi ι (piL ι (star a) (Jbi ι v)) = piR ι (op a) v := by
  rw [piL_apply, piR_apply, unop_op, Jbi,
    OppositeFromRealStructure.conjPerm_conj _ (prodComm_involutive ι),
    submatrix_prodComm_kronLeft]

/-! ## 4. And that is exactly what the four-block space cannot do -/

/-- **`Jbi` MOVES the action**, which is what the previous unit's obstruction requires and what
the four-block space's real structure cannot do. If `Jbi` were `piL`-invariant then the identity
above would force `a* ⊗ 1 = 1 ⊗ aᵀ`, and at `σ₁` that fails on a single entry. -/
theorem Jbi_not_piL_invariant :
    ¬ RepairedActionJInvariant.JInvariant (fun v => Jbi (Fin 2) v)
        (fun (a : Matrix (Fin 2) (Fin 2) ℂ) v => piL (Fin 2) a v) := by
  intro h
  have key : ∀ (a : Matrix (Fin 2) (Fin 2) ℂ) v,
      piL (Fin 2) (star a) v = piR (Fin 2) (op a) v := by
    intro a v
    rw [← piR_eq_conj_piL]
    exact (h (star a) v).symm
  have hend : (matAlg (Fin 2 × Fin 2))
        ((star SpectralTripleBimodule.pauli1) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (matAlg (Fin 2 × Fin 2))
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (SpectralTripleBimodule.pauli1)ᵀ) :=
    LinearMap.ext fun v => key SpectralTripleBimodule.pauli1 v
  have hmat := matAlg_injective (Fin 2 × Fin 2) hend
  have h01 := congrArg (fun M => M ((0 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (0 : Fin 2))) hmat
  simp [SpectralTripleBimodule.pauli1, Matrix.kroneckerMap, Matrix.one_apply] at h01

/-- **The two facts side by side, which is the whole content of this file.** The bimodule
satisfies order-zero at every size, AND its `J` is not action-invariant. The previous unit's
`orderZero_iff_commutative` applies only to `J`-INVARIANT actions, so there is no tension between
them — and the absence of tension is the mechanism rather than a technicality: **a real structure
earns order-zero by MOVING the action onto the other slot, not by leaving it where it is.** The
four-block space's `J` cannot move it; this one does. -/
theorem orderZero_and_J_moves :
    (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        Commute (piL (Fin 2) a) (piR (Fin 2) b))
      ∧ ¬ RepairedActionJInvariant.JInvariant (fun v => Jbi (Fin 2) v)
          (fun (a : Matrix (Fin 2) (Fin 2) ℂ) v => piL (Fin 2) a v) :=
  ⟨piL_piR_commute (Fin 2), Jbi_not_piL_invariant⟩

end

end BimoduleRealStructure
