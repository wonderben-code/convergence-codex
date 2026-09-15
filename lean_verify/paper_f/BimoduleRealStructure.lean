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

  AND A DIRAC OPERATOR AT EVERY SIZE (§5), which is the second half of this file and which
  removes the two size restrictions the first half left behind.
  * **`Dgen M = π(M) + πR(op M*)`** — the LEFT action of `M` plus the RIGHT action of `M*`,
    written in that form rather than as a Kronecker sum because the form is what the proofs run
    on. `RealSpectralWitness`'s `σ₃ ⊗ 1 + 1 ⊗ σ₃` is its `Fin 2` instance. **`M` is arbitrary**:
    no self-adjointness and no spectral hypothesis is imposed.
  * **`oneForm_Dgen`** — `⁅D, π a⁆ = π(⁅M, a⁆)`, because the right summand of `D` commutes with
    everything in the left slot.
  * **`orderOne_Dgen`** — **order-one at every size, for every `M`, and structurally**: the
    one-form lives in the LEFT Kronecker slot and `piR`'s image in the RIGHT one. That is the
    content of the order-one axiom for a regular bimodule, now at every size.
  * **`Jbi_conj_Dgen`** and **`Jbi_comm_Dgen`** — **`J D J = D`, hence `JD = DJ`, at every
    size**: the KO-dimension-6 sign, because the slot swap carries each summand of `D` onto the
    other.
  * **`orderOne_Dgen_has_content`** — and the one-form is non-zero at `M = σ₃`, `a = σ₁`, so
    order-one is satisfied with content and not vacuously (`ERRATUM 557`).

  AND THE EVEN-GRADING OBSTRUCTION AT EVERY SIZE (§6), which answers the question the previous
  section left open and corrects a recorded obstacle.
  * **`even_eq_piR`** — **the commutant, in three lines and without a double-commutant theorem.**
    `EvenGradingObstruction` recorded *"the two images generate everything is the double
    commutant, which this estate does not have"*, and called its entrywise substitute *"the one
    step that does not generalise as written"*. **On a MATRIX space no such theorem is needed**:
    every vector is `π(X) 1` for `X` the vector read as a matrix, so an operator commuting with
    every left multiplication is determined by its value at the identity and equals right
    multiplication by it. The remark was right about the writing and wrong about the step.
  * **`no_even_KO6_grading`** — **no even KO-6 grading exists on this bimodule at any non-empty
    size.** The three conditions are contradictory: `g` commutes with `π a` for EVERY `a` (which
    is what *even* means — it commutes with the algebra, not with `D`), `g * g = 1`, and
    `J g J = -g`. Every step is size-free: `even_eq_piR` makes `g` right multiplication by some
    `G`; `piR_eq_conj_piL` turns `J g J` into left multiplication by `G*`, so the `J`-condition
    reads `G* X = -X G` for every `X`; at `X = 1` that is `G* = -G`, and putting it back leaves
    `G X = X G` for every `X`, so `G` is CENTRAL, hence scalar by
    `StarStructureMatrix.matrix_center_scalar` — **generalised from `Fin m` to an arbitrary finite
    index type in this unit, with no change to its proof.** Then `G* = -G` gives `conj c = -c`
    and `g * g = 1` gives `c ^ 2 = 1`, so `normSq c = -1`. Unit 31's endgame at the level of a
    scalar rather than of one matrix entry.
  * **`no_even_KO6_grading_on_witness`** — and the subsumption is **checked, not asserted**:
    `OrderOneNontrivial.piW` is `piL (Fin 2)` and `OppositeFromRealStructure.Jprod` is
    `Jbi (Fin 2)` definitionally, so `EvenGradingObstruction`'s OPERATOR theorem is this one at
    one size. **Be exact about which of that file's two theorems this subsumes**, because they
    do not share a hypothesis: `no_even_KO6_grading_operator` assumes evenness against EVERY
    `a`, which is what §6 assumes, so that one is subsumed. **`no_even_KO6_grading_on_Hw` is
    not** — it needs only ONE instance of evenness, commuting with `σ₃ ⊗ 1`, so at `Fin 2` it is
    STRONGER than §6. The entrywise proof buys a weaker hypothesis and this one buys every size,
    and neither implies the other, so nothing is deleted.

  WHAT IS **NOT** CLAIMED.
  * **THE GRADING IS STILL ABSENT, AND WHAT IS LEFT IS AN AUTHOR'S DECISION RATHER THAN A GAP.**
    `γ` is the one piece of `RealSpectralWitness` not generalised here, and §6 does not supply
    one — it proves that an EVEN one cannot exist at any size. Whether that closes the question
    depends on whether the estate's notion of a real spectral triple should REQUIRE `γ` to be
    even, which is `PROGRESS_LOG` **DECISIONS NEEDED 12** and `WALLS` §W9.7, filed with three
    options and not decided. **What §6 changes about that decision is its price**: the entry
    records `γ`-evenness as *"provably unattainable on that witness's space"*, and it is now
    unattainable on the regular bimodule at **every** non-empty size, so option (a) — add both
    axioms — leaves no non-scalar witness at any size rather than only at size two. **The
    estate's own `gammaCcm` is not even** (`EvenGradingObstruction.gammaCcm_not_even`), so it is
    not ruled out by §6; it simply is not an even grading. **So this file is a bimodule with a
    real structure and a Dirac operator at every size, and not a spectral triple at every
    size.**
  * **Nothing is claimed about gradings that are not even.** §6's hypothesis is evenness, and an
    operator failing it is outside the theorem's scope, not shown to exist or not exist as part
    of a KO-6 triple.
  * **`Dgen` is not shown self-adjoint** and no hypothesis on `M` is imposed, so nothing here
    says `D` is an operator a spectral triple would accept — only that order-one and the
    `JD = DJ` sign hold for it whatever `M` is.
  * **Order-one is proved, its spectral consequences are not.** No finite-summability, no
    dimension spectrum, no residue.
  * **Nothing about the four-block space is added.** The previous unit's result stands as it is:
    about that `J` and any action invariant under it, and not a proof that no real spectral
    triple exists there.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35), and L6's rung 2 is not climbed: a bimodule at
    every size does not constrain the factor list.

  0 sorry. 0 new axioms. 33 declarations, all but one on
  `[propext, Classical.choice, Quot.sound]`; the exception is `prodComm_involutive`, on
  `Quot.sound` alone, because swapping a pair twice is `rfl` and the only quotient in sight is
  `Prod` itself.
-/

import OppositeFromRealStructure
import RepairedActionJInvariant
import StarStructureMatrix

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

/-- **`Jbi` MOVES the action, at every size with two distinct indices.** If `Jbi` were
`piL`-invariant then `piR_eq_conj_piL` would force `a* ⊗ 1 = 1 ⊗ aᵀ` for every `a`, and at
`a = Eᵢⱼ` with `i ≠ j` that fails on one entry: the left side has `Eⱼᵢ j i = 1` there and the right
side has the factor `1ⱼᵢ = 0`. **This is the hypothesis the previous unit's obstruction needs and
the four-block space's real structure cannot supply** — all it can do is swap the two halves and
conjugate, which leaves the repaired action exactly where it was. -/
theorem Jbi_moves_piL (i j : ι) (hij : i ≠ j) :
    ¬ RepairedActionJInvariant.JInvariant (fun v => Jbi ι v)
        (fun (a : Matrix ι ι ℂ) v => piL ι a v) := by
  intro h
  have key : ∀ (a : Matrix ι ι ℂ) v, piL ι (star a) v = piR ι (op a) v := by
    intro a v
    rw [← piR_eq_conj_piL]
    exact (h (star a) v).symm
  set E : Matrix ι ι ℂ := Matrix.of (fun p q => if p = i ∧ q = j then (1 : ℂ) else 0) with hE
  have hend : (matAlg (ι × ι)) ((star E) ⊗ₖ (1 : Matrix ι ι ℂ))
      = (matAlg (ι × ι)) ((1 : Matrix ι ι ℂ) ⊗ₖ Eᵀ) :=
    LinearMap.ext fun v => key E v
  have hmat := matAlg_injective (ι × ι) hend
  have h01 := congrArg (fun N => N (j, i) (i, i)) hmat
  simp [hE, Matrix.kroneckerMap, Matrix.one_apply, hij] at h01

/-- The instance at `ι = Fin 2`, kept because it is the one the previous unit's concrete
obstruction is stated against. -/
theorem Jbi_not_piL_invariant :
    ¬ RepairedActionJInvariant.JInvariant (fun v => Jbi (Fin 2) v)
        (fun (a : Matrix (Fin 2) (Fin 2) ℂ) v => piL (Fin 2) a v) :=
  Jbi_moves_piL (Fin 2) 0 1 (by decide)

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

/-! ## 5. A Dirac operator at every size, and order-one with it -/

omit [Fintype ι] in
/-- The mirror of `submatrix_prodComm_kronLeft`: the slot swap carries the RIGHT slot to the
LEFT one, conjugating as it goes. -/
theorem submatrix_prodComm_kronRight (a : Matrix ι ι ℂ) :
    (((1 : Matrix ι ι ℂ) ⊗ₖ a).submatrix (Equiv.prodComm ι ι) (Equiv.prodComm ι ι)).map
        (starRingEnd ℂ) = (a.map (starRingEnd ℂ)) ⊗ₖ (1 : Matrix ι ι ℂ) := by
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp [Matrix.kroneckerMap, Matrix.one_apply, apply_ite (starRingEnd ℂ), mul_comm]

/-- **A Dirac operator on the bimodule, at every size**: the LEFT action of `M` plus the RIGHT
action of `M*`. Written in exactly that form rather than as a Kronecker sum, because the form is
what the two theorems below run on — and because `π(M) + πR(op M*)` is the standard shape of a
bimodule Dirac operator, which `RealSpectralWitness`'s `σ₃ ⊗ 1 + 1 ⊗ σ₃` is the `Fin 2` instance
of. No self-adjointness or spectral hypothesis is imposed: `M` is arbitrary. -/
def Dgen (M : Matrix ι ι ℂ) : Module.End ℂ (EuclideanSpace ℂ (ι × ι)) :=
  piL ι M + piR ι (op (star M))

/-- **The one-form, computed at every size.** `⁅D, π a⁆` is the left action of the commutator
`⁅M, a⁆`, because the right summand of `D` commutes with everything in the left slot. -/
theorem oneForm_Dgen (M a : Matrix ι ι ℂ) :
    ⁅Dgen ι M, piL ι a⁆ = piL ι (M * a - a * M) := by
  have hc : piR ι (op (star M)) * piL ι a = piL ι a * piR ι (op (star M)) :=
    (piL_piR_commute ι a (op (star M))).symm.eq
  rw [Dgen, Ring.lie_def, add_mul, mul_add, hc, map_sub, map_mul, map_mul]
  abel

/-- **Order-one at every size, for every `M`, and it is structural.** The one-form lives in the
LEFT Kronecker slot and `piR`'s image lives in the RIGHT one, and different slots commute. So
every one-form built from the left action automatically commutes with the right action — which is
the content of the order-one axiom for a regular bimodule, now at every size rather than at
`Fin 2`. -/
theorem orderOne_Dgen (M a : Matrix ι ι ℂ) (b : (Matrix ι ι ℂ)ᵐᵒᵖ) :
    ⁅⁅Dgen ι M, piL ι a⁆, piR ι b⁆ = 0 := by
  rw [oneForm_Dgen]
  exact commute_iff_lie_eq.mp (piL_piR_commute ι _ b)

/-- **And `J D J = D`, at every size** — the KO-dimension-6 sign `JD = +DJ`. The slot swap carries
the left summand onto the right one and back, so the sum is fixed. Conjugating form first,
because that is what the two halves of `piR_eq_conj_piL` give directly. -/
theorem Jbi_conj_Dgen (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × ι)) :
    Jbi ι (Dgen ι M (Jbi ι v)) = Dgen ι M v := by
  have h1 : Jbi ι (piL ι M (Jbi ι v)) = piR ι (op (star M)) v := by
    have := piR_eq_conj_piL ι (star M) v
    rwa [star_star] at this
  have h2 : Jbi ι (piR ι (op (star M)) (Jbi ι v)) = piL ι M v := by
    have h3 : Jbi ι (piL ι M v) = piR ι (op (star M)) (Jbi ι v) := by
      have := piR_eq_conj_piL ι (star M) (Jbi ι v)
      rwa [star_star, Jbi_involutive] at this
    rw [← h3, Jbi_involutive]
  have hsum : Dgen ι M (Jbi ι v) = piL ι M (Jbi ι v) + piR ι (op (star M)) (Jbi ι v) := rfl
  rw [hsum, map_add, h1, h2, Dgen]
  exact (add_comm _ _).trans rfl

/-- The same identity in the shape a KO-6 sign table wants: `J` COMMUTES with `D`. -/
theorem Jbi_comm_Dgen (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × ι)) :
    Jbi ι (Dgen ι M v) = Dgen ι M (Jbi ι v) := by
  have h := Jbi_conj_Dgen ι M (Jbi ι v)
  rw [Jbi_involutive] at h
  exact h

/-- **And the one-form is not zero**, so order-one is satisfied with content rather than
vacuously (`ERRATUM 557`): at `ι = Fin 2`, `M = σ₃` and `a = σ₁` the commutator `⁅σ₃, σ₁⁆` has
entry `2` in position `(0, 1)`, and `piL` is faithful. -/
theorem orderOne_Dgen_has_content :
    ⁅Dgen (Fin 2) SpectralTripleBimodule.pauli3,
      piL (Fin 2) SpectralTripleBimodule.pauli1⁆ ≠ 0 := by
  rw [oneForm_Dgen]
  intro h
  have hz : SpectralTripleBimodule.pauli3 * SpectralTripleBimodule.pauli1
      - SpectralTripleBimodule.pauli1 * SpectralTripleBimodule.pauli3 = 0 := by
    have := piL_injective (Fin 2) (h.trans (map_zero (piL (Fin 2))).symm)
    exact this
  have h01 := congrArg (fun N => N (0 : Fin 2) (1 : Fin 2)) hz
  simp [SpectralTripleBimodule.pauli1, SpectralTripleBimodule.pauli3] at h01

/-! ## 6. No even KO-6 grading, at any size, and the double commutant was never needed -/

/-- A matrix read as a vector of the bimodule. -/
def vecOf (M : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (fun p => M p.1 p.2)

/-- And back. The two are mutually inverse on the nose. -/
def matOf (v : EuclideanSpace ℂ (ι × ι)) : Matrix ι ι ℂ := Matrix.of fun i j => v (i, j)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matOf_vecOf (M : Matrix ι ι ℂ) : matOf ι (vecOf ι M) = M := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem vecOf_matOf (v : EuclideanSpace ℂ (ι × ι)) : vecOf ι (matOf ι v) = v := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matOf_neg (v : EuclideanSpace ℂ (ι × ι)) :
    matOf ι (-v) = -(matOf ι v) := rfl

/-- **The left action is multiplication on the left.** -/
theorem piL_vecOf (a M : Matrix ι ι ℂ) : piL ι a (vecOf ι M) = vecOf ι (a * M) := by
  ext p
  obtain ⟨i, j⟩ := p
  simp [piL_apply, vecOf, Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

/-- **And the right action is multiplication on the right.** -/
theorem piR_vecOf (c M : Matrix ι ι ℂ) : piR ι (op c) (vecOf ι M) = vecOf ι (M * c) := by
  ext p
  obtain ⟨i, j⟩ := p
  simp [piR_apply, vecOf, Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.mul_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_comm]

/-- **THE COMMUTANT, IN THREE LINES AND WITHOUT A DOUBLE-COMMUTANT THEOREM.**
`EvenGradingObstruction` recorded *"the two images generate everything is the double commutant,
which this estate does not have"*, and said its entrywise substitute *"is the one step that does
not generalise as written"*. **On a MATRIX space the step needs no such theorem.** Every vector
is `π(X) 1` for `X` the vector read as a matrix, so an operator commuting with every left
multiplication is determined by its value at the identity: `g v = π(matOf v) (g 1)`, which is
right multiplication by `matOf (g 1)`. That is the general form of the step, and it is the same
three lines at every size. -/
theorem even_eq_piR (g : Module.End ℂ (EuclideanSpace ℂ (ι × ι)))
    (heven : ∀ a, g * piL ι a = piL ι a * g) (v : EuclideanSpace ℂ (ι × ι)) :
    g v = piR ι (op (matOf ι (g (vecOf ι 1)))) v := by
  have hv : piL ι (matOf ι v) (vecOf ι 1) = v := by rw [piL_vecOf, mul_one, vecOf_matOf]
  have h := congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (ι × ι)) => T (vecOf ι 1))
    (heven (matOf ι v))
  simp only [Module.End.mul_apply] at h
  rw [hv] at h
  have step : g v = vecOf ι (matOf ι v * matOf ι (g (vecOf ι 1))) := by
    rw [h]
    conv_lhs => rw [← vecOf_matOf ι (g (vecOf ι 1))]
    rw [piL_vecOf]
  have step2 : piR ι (op (matOf ι (g (vecOf ι 1)))) v
      = vecOf ι (matOf ι v * matOf ι (g (vecOf ι 1))) := by
    conv_lhs => rw [← vecOf_matOf ι v]
    rw [piR_vecOf]
  rw [step, step2]

omit [Fintype ι] in
/-- A scalar multiple of the identity determines its scalar, read off the diagonal. This is the
only place `[Nonempty ι]` is used below, and the reason is honest: over an empty index type the
matrix algebra is the zero ring and every scalar gives the same matrix. -/
theorem smul_one_inj_matrix [Nonempty ι] {c d : ℂ}
    (h : c • (1 : Matrix ι ι ℂ) = d • (1 : Matrix ι ι ℂ)) : c = d := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have he := congrArg (fun N => N i i) h
  simpa [Matrix.one_apply] using he

/-- **NO EVEN KO-6 GRADING EXISTS ON THIS BIMODULE, AT ANY NON-EMPTY SIZE.** The three
conditions are contradictory: `g` commutes with `π a` for EVERY `a` (which is what *even* means —
it commutes with the algebra, not with `D`), `g * g = 1`, and `J g J = -g`.

THE ROUTE, and every step is now size-free. `even_eq_piR` makes `g` right multiplication by some
`G`. `piR_eq_conj_piL` turns `J g J` into left multiplication by `G*`, so the `J`-condition reads
`G* X = -X G` for every `X`. At `X = 1` that is `G* = -G`, and substituting it back leaves
`G X = X G` for every `X` — so `G` is CENTRAL, hence scalar by
`StarStructureMatrix.matrix_center_scalar` (generalised from `Fin m` to an arbitrary finite index
type in this unit, with no change to its proof). Write `G = c • 1`. Then `G* = -G` gives
`conj c = -c` and `g * g = 1` gives `c ^ 2 = 1`, so `normSq c = (c * conj c).re = -1`, which is
negative. **Unit 31's endgame at the level of a scalar rather than of one matrix entry.** -/
theorem no_even_KO6_grading [Nonempty ι] (g : Module.End ℂ (EuclideanSpace ℂ (ι × ι)))
    (heven : ∀ a, g * piL ι a = piL ι a * g) (hsq : g * g = 1)
    (hJ : ∀ v, Jbi ι (g (Jbi ι v)) = -(g v)) : False := by
  have hg : ∀ v, g v = piR ι (op (matOf ι (g (vecOf ι 1)))) v := even_eq_piR ι g heven
  set G : Matrix ι ι ℂ := matOf ι (g (vecOf ι 1)) with hGdef
  have key : ∀ v, piL ι (star G) v = -(piR ι (op G) v) := by
    intro v
    have h := piR_eq_conj_piL ι G (Jbi ι v)
    rw [Jbi_involutive] at h
    have h2 : Jbi ι (piR ι (op G) (Jbi ι v)) = piL ι (star G) v := by
      rw [← h, Jbi_involutive]
    rw [← h2, ← hg, hJ, hg]
  have h1 : star G = -G := by
    have hv := key (vecOf ι 1)
    rw [piL_vecOf, piR_vecOf, mul_one, one_mul] at hv
    have := congrArg (matOf ι) hv
    simpa using this
  have hcentral : ∀ X : Matrix ι ι ℂ, G * X = X * G := by
    intro X
    have hv := key (vecOf ι X)
    rw [piL_vecOf, piR_vecOf, h1] at hv
    have h2 := congrArg (matOf ι) hv
    simp only [matOf_vecOf, matOf_neg] at h2
    rw [neg_mul] at h2
    exact neg_injective h2
  obtain ⟨c, hc⟩ := StarStructureMatrix.matrix_center_scalar G hcentral
  have hconj : (starRingEnd ℂ) c = -c := by
    have h3 : star G = (starRingEnd ℂ) c • (1 : Matrix ι ι ℂ) := by
      rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      rfl
    rw [h3, hc, ← neg_smul] at h1
    exact smul_one_inj_matrix ι h1
  have hGsq : G * G = 1 := by
    have h4 := congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (ι × ι)) => T (vecOf ι 1)) hsq
    simp only [Module.End.mul_apply, Module.End.one_apply] at h4
    rw [hg, hg] at h4
    rw [piR_vecOf, piR_vecOf, one_mul] at h4
    have h5 := congrArg (matOf ι) h4
    simpa using h5
  have hcsq : c * c = 1 := by
    rw [hc, smul_mul_smul_comm, one_mul] at hGsq
    refine smul_one_inj_matrix ι ?_
    rw [hGsq, one_smul]
  have hns : Complex.normSq c = -1 := by
    have h6 : c * (starRingEnd ℂ) c = -1 := by
      rw [hconj]
      rw [mul_neg, hcsq]
    have h7 := congrArg Complex.re h6
    simpa [Complex.mul_conj, Complex.normSq] using h7
  have := Complex.normSq_nonneg c
  rw [hns] at this
  norm_num at this

/-- **And the general theorem SUBSUMES `EvenGradingObstruction`'s, which is checked here rather
than asserted.** `OrderOneNontrivial.piW` is `piL (Fin 2)` and `OppositeFromRealStructure.Jprod`
is `Jbi (Fin 2)` — definitionally, both being `(matAlg _).comp (kronLeft _ _)` and
`conjPerm (Equiv.prodComm _ _)` — so `no_even_KO6_grading_operator` is this theorem at one size.
**So that file's entrywise proof is now redundant**, and its header's remark that the step *"does
not generalise as written"* was right about the writing and wrong about the step. Recorded here;
the refactor that would delete the entrywise proof is not done in this unit. -/
theorem no_even_KO6_grading_on_witness (g : Module.End ℂ OrderOneNontrivial.Hw)
    (heven : ∀ a, g * OrderOneNontrivial.piW a = OrderOneNontrivial.piW a * g)
    (hsq : g * g = 1)
    (hJ : ∀ v, OppositeFromRealStructure.Jprod (g (OppositeFromRealStructure.Jprod v))
      = -(g v)) : False :=
  no_even_KO6_grading (Fin 2) g heven hsq hJ

end

end BimoduleRealStructure
