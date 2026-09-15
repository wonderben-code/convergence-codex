/-
  RepairedActionJInvariant: the repair that made the KO-6 action an algebra representation
  makes it J-INVARIANT, and J-invariance collapses CCM's order-zero condition into
  commutativity of the image — which a faithful action of M₂(ℂ) cannot satisfy

  SPINE LINK L18. `UNLOCK_WATCHLIST`'s KO-6-real-structure item, blocker (iii), and this unit
  exists because a RE-SWEEP found that block's recorded closure falsified by later work.

  WHAT THE RE-SWEEP FOUND, and the finding is about the register before it is about mathematics.
  That item's blocker (iii) reads *"an algebra and its representation — the file has J, γ, D
  only, so it is not yet a spectral triple"*, and a dated re-sweep line under it records
  **blocker (iii) CLOSED**, on the grounds that `KOSixSpectralTriple.spectral_triple_axioms`
  supplies *"algebra Mₙ(ℂ), faithful unital ⋆-representation … commutant AND order-one
  conditions"*. **`ERRATUM 565` falsified that and nothing propagated the correction into the
  block.** Every conjunct of `spectral_triple_axioms` is about `piRep`, and
  `KOSixAlgebraAction.piRep_not_additive_in_matrix` proves `piRep` is **not additive in the
  matrix** — so it is not a ring homomorphism and not a representation of the algebra at all.
  Blocker (iii) is therefore NOT closed by that theorem, and this file says what is true instead.

  THE REPAIR AND WHAT IT COSTS. `KOSixRepairedAction.piRepC` is the repair: the entrywise
  CONJUGATE action on the two antiparticle blocks, which is additive, multiplicative and unital,
  and which `KOSixInnerProduct.piRepRing` packages as a genuine `RingHom` with the ⋆-condition
  and faithfulness. **So the algebra and its representation now exist.** This file prices the
  rest of blocker (iii) — the commutant condition — and the price is that it cannot be paid.

  * **`piOpC_eq_piRepC`** — `J π(b) J = π(b)`. The computation is four entries of
    `cvec (M *ᵥ cvec w) = (M.map conj) *ᵥ w`, and the reason is visible in the definitions: `J`
    swaps the particle and antiparticle halves AND conjugates, and `piRepC` differs between the
    halves by exactly a conjugation, so the two cancel. **The repaired action is the
    `J`-invariant one.**
  * **`orderZero_iff_commutative`** — and this is the general statement, with no algebra, no
    linearity and no Hilbert space in it: for ANY involution-like `J` and ANY action `π` that is
    `J`-invariant, CCM's order-zero condition `π(a) πOp(b) = πOp(b) π(a)` with
    `πOp(b) = J π(b) J` holds **if and only if** the image of `π` is commutative. `J`-invariance
    makes the manufactured opposite action *equal* to the action, so order-zero stops being a
    relation between two algebras and becomes commutativity of one.
  * **`no_Jinvariant_orderZero_of_noncommuting`** — so one non-commuting pair refutes order-zero
    outright.
  * **`piRepC_orderZero_fails`** — the instance, at `n = 2`, off `pauli1` and `pauli3`:
    `σ₁σ₃ = -σ₃σ₁` and both are non-zero, so the two composites differ on a single basis vector.
    **A FAITHFUL action of `M₂(ℂ)` has non-commutative image, and that is the whole obstruction.**

  SO THE HONEST STATE OF BLOCKER (iii), replacing the falsified closure. The algebra and its
  representation exist (`piRepRing`). The commutant condition **fails** for it, provably, and the
  diagnosis is not "the proof is missing" but *"the space is wrong"*: on `(ℂⁿ)⁴` the only thing
  `J` can do is swap the halves and conjugate, and against a `J`-invariant action that leaves
  order-zero asking for commutativity. What a real spectral triple needs is a `J` with
  `J π(a) J = π(a*)ᵒᵖ`, which needs a RIGHT action to be available — and that is why this
  campaign's own witness (`RealSpectralWitness.realWitness`) is built on a MATRIX space
  `EuclideanSpace ℂ (Fin 2 × Fin 2)`, where right multiplication exists, rather than on `(ℂⁿ)⁴`.

  WHAT IS **NOT** CLAIMED.
  * **This is not a proof that no real spectral triple exists on `(ℂⁿ)⁴`.** It is a proof about
    THIS `J` and any action invariant under it. A different `J` on the same space is not
    considered, and the four-block space is not shown to admit none.
  * **`piRep`'s own `commutant_condition` is not refuted and was never wrong as a
    `Prop`.** It is true, and `ERRATUM 565`'s point stands unchanged: it is true about a map that
    is not an algebra action, so it does not say *the algebra and its opposite commute*.
  * **Nothing is said about order-ONE for `piRepC`.** Order-zero fails, so the order-one
    condition is not reached; whether it would hold is not addressed.
  * **No cascade identification.** Blockers (i) and (ii) of that watchlist item — identifying the
    space with the cascade's 96 fermion degrees of freedom, and deriving `M` — are untouched and
    remain the author's decision.
  * **The grading and the signs are not re-examined.** `KOSixRealStructure`'s three KO-6 signs
    are about `J`, `γ` and `D` and are unaffected by anything here.

  0 sorry. 0 new axioms. 13 declarations, and **five of them depend on NO axioms at all** —
  `OrderZero`, `JInvariant`, `CommutativeImage`, `orderZero_iff_commutative` and
  `no_Jinvariant_orderZero_of_noncommuting`. That is the general core, and the empty axiom
  footprint is evidence for the claim above that it uses nothing but rewriting: there is no
  algebra, no module, no field and no choice in the collapse argument. The other eight touch
  `Matrix`, `ℂ` and the concrete witness, and rest on
  `[propext, Classical.choice, Quot.sound]`.
-/

import KOSixRepairedAction
import SpectralTripleBimodule

namespace RepairedActionJInvariant

open KOSixSpectralTriple (Hf J mbar)
open KOSixRealStructure (cvec cvec_cvec cvec_mulVec)
open KOSixRepairedAction (piRepC)

noncomputable section

/-! ## 1. The general statement: J-invariance collapses order-zero into commutativity -/

/-- **CCM's order-zero condition**, written for an action together with the opposite action that
a real structure manufactures from it: `π(a) ∘ (J π(b) J) = (J π(b) J) ∘ π(a)`. No algebra
structure, no linearity and no inner product appear, because none is used below. -/
def OrderZero {H A : Type*} (Jm : H → H) (pi : A → H → H) : Prop :=
  ∀ (a b : A) (v : H), pi a (Jm (pi b (Jm v))) = Jm (pi b (Jm (pi a v)))

/-- **`π` is `J`-invariant**: conjugating by `J` returns the same action. -/
def JInvariant {H A : Type*} (Jm : H → H) (pi : A → H → H) : Prop :=
  ∀ (a : A) (v : H), Jm (pi a (Jm v)) = pi a v

/-- The image of `π` is commutative. -/
def CommutativeImage {H A : Type*} (pi : A → H → H) : Prop :=
  ∀ (a b : A) (v : H), pi a (pi b v) = pi b (pi a v)

/-- **The collapse, and it is an `iff`.** For a `J`-invariant action the manufactured opposite
action IS the action, so order-zero stops being a relation between an algebra and its opposite
and becomes commutativity of the algebra's image. Two rewrites in each direction. -/
theorem orderZero_iff_commutative {H A : Type*} (Jm : H → H) (pi : A → H → H)
    (hinv : JInvariant Jm pi) : OrderZero Jm pi ↔ CommutativeImage pi := by
  constructor
  · intro h a b v
    have h1 := h a b v
    rw [hinv b v, hinv b (pi a v)] at h1
    exact h1
  · intro h a b v
    rw [hinv b v, hinv b (pi a v)]
    exact h a b v

/-- So a single non-commuting pair refutes order-zero outright. -/
theorem no_Jinvariant_orderZero_of_noncommuting {H A : Type*} (Jm : H → H) (pi : A → H → H)
    (hinv : JInvariant Jm pi) (a b : A) (v : H)
    (hne : pi a (pi b v) ≠ pi b (pi a v)) : ¬ OrderZero Jm pi :=
  fun h => hne ((orderZero_iff_commutative Jm pi hinv).mp h a b v)

/-! ## 2. The repaired action is the J-invariant one -/

variable {n : ℕ}

/-- Conjugating a matrix entrywise twice is the identity — the one arithmetic fact the
`J`-invariance computation needs, isolated so the four component goals close uniformly. -/
theorem map_conj_conj (M : Matrix (Fin n) (Fin n) ℂ) :
    M.map ((starRingEnd ℂ) ∘ (starRingEnd ℂ)) = M := by
  ext i j; simp

/-- The opposite action CCM manufactures from the REPAIRED action: `J π(b) J`. -/
def piOpC (b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n := J (piRepC b (J v))

/-- **`J π(b) J = π(b)`.** `J` swaps the particle and antiparticle halves and conjugates;
`piRepC` differs between the halves by exactly a conjugation; the two cancel. Four entries of
`cvec (M *ᵥ cvec w) = (M.map conj) *ᵥ w` and nothing else. -/
theorem piOpC_eq_piRepC (b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piOpC b v = piRepC b v := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp only [piOpC, KOSixSpectralTriple.J, piRepC, mbar] <;>
    rw [cvec_mulVec] <;> simp [cvec_cvec, map_conj_conj]

/-- The same fact in the shape the general lemma consumes. -/
theorem piRepC_jInvariant : JInvariant (J (n := n)) (piRepC (n := n)) := fun b v =>
  piOpC_eq_piRepC b v

/-! ## 3. And a faithful action of M₂(ℂ) cannot have commutative image -/

open SpectralTripleBimodule (pauli1 pauli3)

/-- The witness vector: the first particle block is the first basis vector, everything else `0`. -/
def firstParticleVec : Hf 2 :=
  (((fun i => if i = 0 then (1 : ℂ) else 0), fun _ => 0), (fun _ => 0, fun _ => 0))

/-- `σ₁σ₃` and `σ₃σ₁` differ on the first basis vector, so the image of `piRepC` is not
commutative at `n = 2`. -/
theorem piRepC_not_commutative :
    piRepC pauli1 (piRepC pauli3 firstParticleVec)
      ≠ piRepC pauli3 (piRepC pauli1 firstParticleVec) := by
  intro h
  have h1 := congrArg (fun w => w.1.1 1) h
  have hcontra : (1 : ℂ) = -1 := by
    simpa [piRepC, firstParticleVec, pauli1, pauli3, dotProduct, Fin.sum_univ_succ] using h1
  norm_num at hcontra

/-- **The repaired action cannot satisfy CCM's order-zero condition.** Structural, not
computational: the repair made the action `J`-invariant, `J`-invariance collapses the opposite
action onto the action, and order-zero then asks for a commutative image, which a faithful action
of `M₂(ℂ)` does not have. -/
theorem piRepC_orderZero_fails :
    ¬ OrderZero (J (n := 2)) (piRepC (n := 2)) :=
  no_Jinvariant_orderZero_of_noncommuting (J (n := 2)) (piRepC (n := 2))
    piRepC_jInvariant pauli1 pauli3 firstParticleVec piRepC_not_commutative

/-- Stated in the estate's own idiom as well, with `piOpC` in place of the unfolded conjugation,
so a reader of `KOSixSpectralTriple.commutant_condition` can compare the two directly. -/
theorem piRepC_commutant_condition_fails :
    ¬ (∀ (a b : Matrix (Fin 2) (Fin 2) ℂ) (v : Hf 2),
        piRepC a (piOpC b v) = piOpC b (piRepC a v)) := by
  intro h
  exact piRepC_orderZero_fails fun a b v => h a b v

end

end RepairedActionJInvariant
