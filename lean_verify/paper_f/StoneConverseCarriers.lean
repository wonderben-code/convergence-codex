/-
  StoneConverseCarriers: **Stone's converse, ON NAMED ALGEBRAS.** `StoneConverseLocal` proves it
  for an arbitrary C⋆-algebra and instantiates it at none; its header said so, and named two
  measured instance costs as the reason. This file lands the theorem on `Mₙ(ℂ)` at every finite
  size, on `CascadeGNS.M4` — the cascade's own spacetime-level algebra — on the bounded operators
  of any complex Hilbert space, on `ℂⁿ`'s operator algebra, and on the GNS space of the cascade's
  trace state. **`FiniteStone`'s forward direction and `StoneConverseLocal`'s converse now meet at
  a named carrier**, which neither file could say.

  **THERE IS NO NEW MATHEMATICS HERE, and that is the finding (`ERRATUM 594`).** Every theorem
  below is `StoneConverseLocal.exists_unique_global_generator` or
  `StoneConverseLocal.eq_unitaryGroup_iff` applied at a carrier, and each proof is one term. The
  previous unit recorded two instantiation attempts as failures, measured them, and recorded them
  as NOT CHASED rather than impossible — which was the right way to record them, and the chase
  took twenty minutes.
  * At `CStarMatrix (Fin 4) (Fin 4) ℂ`, `Norm` would not synthesise. **The instance exists**:
    `CStarMatrix.instCStarAlgebra`, and it asks for `[PartialOrder A] [StarOrderedRing A]` on the
    ENTRY algebra. For `A = ℂ` those are `ComplexOrder`'s SCOPED instances, so the whole failure
    was a missing `open scoped ComplexOrder`. `CascadeGNS.lean` has had that line since the day it
    was written, three lines above `abbrev M4 : Type := CStarMatrix (Fin 4) (Fin 4) ℂ`.
  * At `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`, `unitary` elaborated through
    `ContinuousLinearMap.monoidWithZero` while the lemmas wanted the C⋆ path. **The instance
    exists**: `CStarAlgebra (E →L[ℂ] E)` in `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`,
    twenty lines long, for any complete complex inner-product space. The import was missing, so
    the C⋆ path did not exist to be found and elaboration took the generic one.
  * **And the recorded sentence *"NOT a heartbeat problem (tested at 2000000)"* tested the wrong
    option.** With the import present, one instance search does exceed its budget —
    `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` — and the option that governs it is
    `synthInstance.maxHeartbeats`, whose default is 20000, not `maxHeartbeats`, which the test
    raised. Counted rather than estimated: **20000 fails, 21000 succeeds** — a five per cent
    shortfall — and this file elaborates in ten seconds. Section 3's four declarations each carry
    `set_option synthInstance.maxHeartbeats 400000 in` for headroom, scoped per declaration
    because Mathlib's style linter refuses an unscoped one and asks for a comment saying why.

  WHAT IS PROVED. Nine declarations, each a one-term application.
  * **`matrix_exists_unique_generator`, `matrix_eq_unitaryGroup_iff`** — Stone's converse and the
    full characterisation on `CStarMatrix n n ℂ` for **any** `Fintype` index with decidable
    equality, not just `Fin n`. A map `ℝ → unitary Mₙ(ℂ)` is a one-parameter group continuous at
    `0` exactly when it is `FiniteStone.unitaryGroup H`, and the `H` is unique.
  * **`matrixRingEquiv`** — Mathlib's `CStarMatrix.ofMatrixRingEquiv`, cited to fix what the type
    synonym changes and what it does not: the norm and the order, not the multiplication. So
    "unitary" and "self-adjoint" above mean what they mean for matrices.
  * **`cascade_exists_unique_generator`, `cascade_eq_unitaryGroup_iff`** — the same on
    `CascadeGNS.M4`, which IS `CStarMatrix (Fin 4) (Fin 4) ℂ` by definition. The carrier was not
    chosen to make the theorem land; it is the one the GNS unit already uses.
  * **`operator_exists_unique_generator`, `operator_eq_unitaryGroup_iff`** — on `B(E)` for any
    complete complex inner-product space `E`.
  * **`euclidean_exists_unique_generator`** — including `ℂⁿ`, which is the carrier
    `FiniteStone.cascade_schrodinger` uses for the forward direction.
  * **`gns_exists_unique_generator`** — and on the GNS space of the cascade's trace state.
  * **`operator_schrodinger`** — **THE SCHRÖDINGER EQUATION WITH NO GENERATOR SUPPLIED.**
    `FiniteStone.schrodinger_equation` needs an `H` as input; this needs only the group law and
    continuity at the single point `0`, and produces the `H`
    `exists_unique_global_generator` shows is unique. **`euclidean_schrodinger`** is the same at
    `ℂⁿ`, where `FiniteStone.cascade_schrodinger` needs a Hermitian matrix as input.
  * **`cascade_generator_eq_neg_I_smul_deriv`** — and on `CascadeGNS.M4` the energy operator of
    a norm-continuous evolution is `−i·dU/dt|₀`: computed by one differentiation rather than
    posited.

  WHAT IS **NOT** PROVED.
  * **Still the NORM-continuous Stone theorem.** Nothing here weakens `StoneConverseLocal`'s
    hypothesis, and on an infinite-dimensional `E` that hypothesis is a real restriction: `H` is a
    BOUNDED operator, and `B(E)`-norm continuity of `U` is strictly stronger than the strong
    operator continuity the classical theorem assumes. In FINITE dimension the two coincide, so
    for `Mₙ(ℂ)`, `CascadeGNS.M4` and `ℂⁿ` this is the whole theorem; for `B(E)` at large `E` it is
    not, and `StoneConverseLocal`'s header says why the gap is forced rather than accidental.

    > **^ THE SENTENCE "IN FINITE DIMENSION THE TWO COINCIDE" WAS PROSE AND IS NOW A THEOREM**
    > (2026-09-16, unit 64; the paragraph above is kept as written per `ERRATUM 94` because it is
    > true, not because it is wrong). `StoneStrongContinuity.continuousAt_iff_pointwise` proves
    > it, and `StoneStrongContinuity.exists_unique_global_generator_of_strong`,
    > `eq_unitaryGroup_iff_strong` and `schrodinger_of_strong` restate the three theorems of §3
    > below with continuity of the ORBITS at `0` in place of continuity in the operator norm —
    > `euclidean_*_of_strong` at `ℂⁿ` with no completeness or finite-dimensionality hypothesis at
    > all. **What has NOT changed is the substance**: the two hypotheses are equivalent on a
    > finite-dimensional carrier, so no group is newly reached; what changed is that Lean can now
    > consume the hypothesis an evolution law supplies. **The `B(E)` clause stands unweakened**,
    > and the C⋆ carriers of §1 and §2 keep the norm hypothesis for the reason that file states:
    > the weak hypothesis there is about states `φ (U t)` and needs a basis of the DUAL.
  * **`ASSUMPTIONS_LEDGER` 16 is NOT resolved.** That entry records this estate giving the
    cascade's spacetime level two different, non-isomorphic Hilbert spaces — `ℂ⁴` in `FiniteStone`
    and the 16-dimensional GNS space in `CascadeGNS` — and calls the choice an unstated
    assumption. It still is. What `euclidean_exists_unique_generator` and
    `gns_exists_unique_generator` say together is narrower and worth having: the converse holds on
    both, so nothing in Stone's theorem depends on which is chosen.
  * **Plain `Matrix n n ℂ` is NOT a carrier here, and that is Mathlib's deliberate choice rather
    than a gap.** `CStarAlgebra (Matrix (Fin 4) (Fin 4) ℂ)` does not synthesise, and it still does
    not after `open scoped Matrix.Norms.L2Operator` — that namespace supplies `NormedRing`,
    `NormedAlgebra` and `Matrix.instCStarRing` as scoped instances but no bundled `CStarAlgebra`
    instance, and `Mathlib/Analysis/CStarAlgebra/Matrix.lean` says why in its own docstring: *"a
    scoped instance … in order to avoid choosing a global norm for `Matrix`"*. Assembling the
    bundled class in this file would impose that choice on everything importing it, so it is not
    done. `CStarMatrix` is the type synonym that makes the choice explicitly, and it is what
    `CascadeGNS` already uses.
  * ~~**No Schrödinger equation, no derivative, nothing about the generator's spectrum.**
    `FiniteStone` has `hasDerivAt_unitaryGroup` and `schrodinger_equation` for the group BUILT
    from `H`; composing them with the converse to get "every norm-continuous group satisfies a
    Schrödinger equation" is one rewrite and is **not written here**.~~ **WRITTEN THE SAME DAY,
    IN THE SAME UNIT-AND-A-HALF**: it was one rewrite, and `PROOF_STRATEGY` §6's third question
    — *if the unit you just finished WAS a B, retry B→C right now* — is what made me do it
    instead of writing it down as a limit. `operator_schrodinger`, `euclidean_schrodinger` and
    `cascade_generator_eq_neg_I_smul_deriv` here; `hasDerivAt_of_group` and
    `generator_eq_neg_I_smul_deriv` in `StoneConverseLocal`. **NOTHING about the generator's
    SPECTRUM, which is still true** — no eigenvalues, no spectral measure, no functional calculus
    of `H` beyond what `argSelfAdjoint` already uses.
  * **Nothing about the Born rule, Gleason or Wigner**, L21's other residues.

  0 sorry. 0 new axioms. 12 declarations, all on `[propext, Classical.choice, Quot.sound]`.
-/

import StoneConverseLocal
import CascadeGNS
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace StoneConverseCarriers

open scoped ComplexOrder

noncomputable section

/-! ## 1. Matrix algebras -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Stone's converse on `Mₙ(ℂ)`, at every finite size and for every index type.** The carrier
is `CStarMatrix n n ℂ`, Mathlib's matrix type carrying the C⋆ (operator) norm rather than the
sup norm; `CStarMatrix.instCStarAlgebra` is what makes it apply, and it needs
`PartialOrder ℂ` and `StarOrderedRing ℂ`, which is what the `open scoped ComplexOrder` at the
top of this file supplies. -/
theorem matrix_exists_unique_generator (U : ℝ → unitary (CStarMatrix n n ℂ))
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (CStarMatrix n n ℂ),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U hc hgrp

/-- **And the characterisation, both directions, on `Mₙ(ℂ)`**: a map `ℝ → unitary Mₙ(ℂ)` is a
one-parameter group continuous at `0` exactly when it is `FiniteStone.unitaryGroup H`. The
forward direction is `FiniteStone`'s and the converse is `StoneConverseLocal`'s, and this is the
first statement in the estate where the two meet at a NAMED algebra. -/
theorem matrix_eq_unitaryGroup_iff (U : ℝ → unitary (CStarMatrix n n ℂ)) :
    (ContinuousAt U 0 ∧ ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint (CStarMatrix n n ℂ), U = FiniteStone.unitaryGroup H :=
  StoneConverseLocal.eq_unitaryGroup_iff U

/-- The carrier's underlying RING is the ordinary matrix ring — Mathlib's `ofMatrixRingEquiv`,
cited to say exactly what the type synonym changes and what it does not. It changes the norm
(operator, not sup) and the order; it does not change the multiplication, so "unitary" and
"self-adjoint" above mean what they mean for matrices. -/
def matrixRingEquiv : Matrix n n ℂ ≃+* CStarMatrix n n ℂ :=
  CStarMatrix.ofMatrixRingEquiv

end Matrices

/-! ## 2. The cascade's own spacetime-level algebra -/

/-- **Stone's converse on `CascadeGNS.M4`**, which is `CStarMatrix (Fin 4) (Fin 4) ℂ` by
definition — the algebra the GNS unit puts the cascade's spacetime level on. So the theorem
lands on a carrier this estate already uses for something else, rather than on a carrier chosen
to make it land. -/
theorem cascade_exists_unique_generator (U : ℝ → unitary CascadeGNS.M4)
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint CascadeGNS.M4, ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U hc hgrp

/-- And the characterisation there. -/
theorem cascade_eq_unitaryGroup_iff (U : ℝ → unitary CascadeGNS.M4) :
    (ContinuousAt U 0 ∧ ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint CascadeGNS.M4, U = FiniteStone.unitaryGroup H :=
  StoneConverseLocal.eq_unitaryGroup_iff U

/-- **And the derivative on `CascadeGNS.M4`**: the generator is recovered as
`H = −i·dU/dt|₀`, so on the cascade's own algebra the energy operator of a norm-continuous
evolution is computed by one differentiation rather than posited. -/
theorem cascade_generator_eq_neg_I_smul_deriv (U : ℝ → unitary CascadeGNS.M4)
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint CascadeGNS.M4, (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      HasDerivAt (fun s => ((U s : CascadeGNS.M4))) (Complex.I • (H : CascadeGNS.M4)) 0 ∧
      ∀ L : CascadeGNS.M4,
        HasDerivAt (fun s => ((U s : CascadeGNS.M4))) L 0 → (H : CascadeGNS.M4) = -Complex.I • L :=
  StoneConverseLocal.generator_eq_neg_I_smul_deriv U hc hgrp

/-! ## 3. Bounded operators on a complex Hilbert space -/

section Operators

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default: measured, 20000
-- fails and 21000 succeeds, so this is headroom on a 5% shortfall (`ERRATUM 594`).
/-- **Stone's converse on `B(E)` for any complex Hilbert space `E`** — bounded operators, with
`CStarAlgebra (E →L[ℂ] E)` from `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`. This is the
statement the previous unit recorded as blocked by an instance-path mismatch; the mismatch was
the missing import (see `ERRATUM 594`). -/
theorem operator_exists_unique_generator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : ℝ → unitary (E →L[ℂ] E))
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (E →L[ℂ] E), ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U hc hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default: measured, 20000
-- fails and 21000 succeeds, so this is headroom on a 5% shortfall (`ERRATUM 594`).
/-- And the characterisation there. -/
theorem operator_eq_unitaryGroup_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : ℝ → unitary (E →L[ℂ] E)) :
    (ContinuousAt U 0 ∧ ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint (E →L[ℂ] E), U = FiniteStone.unitaryGroup H :=
  StoneConverseLocal.eq_unitaryGroup_iff U

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default: measured, 20000
-- fails and 21000 succeeds, so this is headroom on a 5% shortfall (`ERRATUM 594`).
/-- **Including `ℂⁿ` itself**, which is the carrier `FiniteStone.cascade_schrodinger` uses for
the forward direction. The two directions now meet there too. -/
theorem euclidean_exists_unique_generator (n : ℕ)
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U hc hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default: measured, 20000
-- fails and 21000 succeeds, so this is headroom on a 5% shortfall (`ERRATUM 594`).
/-- **And on the GNS space of the cascade's trace state**, the 16-dimensional Hilbert space
`CascadeGNS` builds. `ASSUMPTIONS_LEDGER` 16 records that this estate gives the cascade's
spacetime level two different Hilbert spaces — `ℂ⁴` and this one — and calls the choice an
unresolved assumption. **This does not resolve it.** What it says is narrower and worth having:
the converse holds on both, so nothing in Stone's theorem depends on which is chosen. -/
theorem gns_exists_unique_generator
    (U : ℝ → unitary (CascadeGNS.traceState.GNS →L[ℂ] CascadeGNS.traceState.GNS))
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (CascadeGNS.traceState.GNS →L[ℂ] CascadeGNS.traceState.GNS),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U hc hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default: measured, 20000
-- fails and 21000 succeeds, so this is headroom on a 5% shortfall (`ERRATUM 594`).
/-- **THE SCHRÖDINGER EQUATION WITH NO GENERATOR SUPPLIED.** `FiniteStone.schrodinger_equation`
proves `d/dt (U t ψ) = iH (U t ψ)` for the group built from a given `H`. Composed with
`StoneConverseLocal.exists_global_generator` it says: **every** one-parameter unitary group on a
complex Hilbert space that is continuous at the single point `0` obeys a Schrödinger equation, for
a `H` nobody had to provide and which `exists_unique_global_generator` shows is unique. -/
theorem operator_schrodinger {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : ℝ → unitary (E →L[ℂ] E)) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (E →L[ℂ] E), (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : E) (t : ℝ),
        HasDerivAt (fun s => ((U s : E →L[ℂ] E)) ψ)
          ((Complex.I • (H : E →L[ℂ] E) * ((U t : E →L[ℂ] E))) ψ) t := by
  obtain ⟨H, hH⟩ := StoneConverseLocal.exists_global_generator U hc hgrp
  refine ⟨H, hH, fun ψ t => ?_⟩
  have key := FiniteStone.schrodinger_equation H ψ t
  simp only [FiniteStone.unitaryGroup] at key
  simpa only [← hH] using key

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall as above (`ERRATUM 594`).
/-- **And at `ℂⁿ`**, which is `FiniteStone.cascade_schrodinger`'s carrier. That theorem needs a
Hermitian matrix as input; this one needs only the group law and continuity at one point. -/
theorem euclidean_schrodinger (n : ℕ)
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin n)) (t : ℝ),
        HasDerivAt
          (fun s => ((U s : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) ψ)
          ((Complex.I • (H : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
            * ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))) ψ) t :=
  operator_schrodinger U hc hgrp

end Operators

end

end StoneConverseCarriers
