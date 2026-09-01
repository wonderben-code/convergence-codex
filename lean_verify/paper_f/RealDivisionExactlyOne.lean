import RealDivisionQuaternionCase
import RealDivisionTrichotomy

/-!
# Deepening Frobenius: *exactly* one of the three, not *at least* one

`RealDivisionQuaternionCase.frobenius` is a **disjunction**: a finite-dimensional real division
algebra is `ℝ` or `ℂ` or `ℍ`. Read carelessly that is the whole theorem; read carefully it does not
exclude a `D` isomorphic to two of them, and *"there are exactly three"* is a claim it does not
make. **This file makes it.** It is the standing order to deepen a result by strengthening what it
says rather than by restating it.

**The invariants are `RealDivisionTrichotomy`'s and are not rebuilt.** That file separated the three
families at the level of MATRIX algebras — `Mₘ(K) ≇ Mₙ(K')`, at every pair of nonempty finite index
types — and its two invariants are stated generally enough to be used at the base directly, which is
what happens here. **The base-level statements themselves are new**: no declaration under `paper_f/`
carried `ℝ ≇ ℂ`, `ℍ ≇ ℂ` or `ℝ ≇ ℍ` before this file, checked by grep rather than recalled
(`ERRATUM 396`, `ERRATUM 400`), and deriving them from the matrix versions would need a
`Matrix Unit Unit K ≃+* K` bridge that is longer than the two-line proofs below.

> **§1. `ℂ` has a central square root of `-1`.** `hasCentralSqrtNegOne_complex` — `Complex.I`, and
> the centrality is commutativity. `ℝ` and `ℍ` do not, because their centres are the real scalars
> (`RealDivisionTrichotomy.centreIsReal_real`, `centreIsReal_quaternion`) and no real squares to
> `-1`. That settles two of the three pairs, **and settles them as RING statements** — no
> `ℝ`-linearity is asked of the isomorphism.
>
> **§2. `ℝ ≇ ℍ` is the pair neither that invariant reaches**, since both have real centre. What
> settles it is real dimension, which `RealDivisionTrichotomy.finrank_eq_of_ringEquiv` makes a
> **ring** invariant between real-centred `ℝ`-algebras: `1 ≠ 4`.
>
> **§3. `exactly_one_of_three`.** The disjunction with the other two branches shown empty in each
> case. **No `Fin 3 → Type` dispatch is built**, for the reason `RealSimpleAlgebra` gives: that
> shape is `ASSUMPTIONS 49`'s and belongs to the author. Written out, the statement is longer and
> makes no decision.

**WHAT THIS IS.** *Exactly* three, rather than *at most* three-with-repeats. It is what a reader
takes `frobenius` to mean and is not what `frobenius` says.

**WHAT THIS IS NOT** (`ERRATUM 60`). It adds no algebra: every step is an invariant already proved
in this estate, applied at index type `Unit` instead of a general one. It does not touch
`RealDivisionTrichotomy`'s matrix statements, which are strictly stronger in their own direction and
are what `CentralIdemInvariant` consumes. And it says nothing about **which** of the three a given
`D` is — that is a computation for each `D` and is not attempted here (`ERRATUM 194`,
`ERRATUM 246`). **No published tag moves and nothing in the earlier files is restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionExactlyOne

open scoped Quaternion
open RealDivisionTrichotomy

/-! ### §1. The `ℂ` column -/

/-- `ℂ` has a central square root of `-1`: `Complex.I`, central because `ℂ` is commutative. -/
theorem hasCentralSqrtNegOne_complex : HasCentralSqrtNegOne ℂ :=
  ⟨Complex.I, by simp [Set.center_eq_univ], Complex.I_mul_I⟩

/-- **`ℝ ≇ ℂ` as rings.** -/
theorem isEmpty_ringEquiv_real_complex : IsEmpty (ℝ ≃+* ℂ) :=
  ⟨fun φ => not_hasCentralSqrtNegOne centreIsReal_real
    (HasCentralSqrtNegOne.of_ringEquiv φ.symm hasCentralSqrtNegOne_complex)⟩

/-- **`ℍ ≇ ℂ` as rings.** -/
theorem isEmpty_ringEquiv_quaternion_complex : IsEmpty (ℍ[ℝ] ≃+* ℂ) :=
  ⟨fun φ => not_hasCentralSqrtNegOne centreIsReal_quaternion
    (HasCentralSqrtNegOne.of_ringEquiv φ.symm hasCentralSqrtNegOne_complex)⟩

/-! ### §2. The pair the centre cannot separate -/

/-- **`ℝ ≇ ℍ` as rings** — both have real centre, so the centre invariant is silent and real
dimension decides: `1 ≠ 4`. -/
theorem isEmpty_ringEquiv_real_quaternion : IsEmpty (ℝ ≃+* ℍ[ℝ]) := by
  refine ⟨fun φ => ?_⟩
  have h := finrank_eq_of_ringEquiv centreIsReal_quaternion φ
  rw [Module.finrank_self, Quaternion.finrank_eq_four] at h
  exact absurd h (by norm_num)

/-! ### §3. Exactly one -/

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-- **EXACTLY ONE OF THE THREE.** `frobenius` says at least one; the three non-isomorphisms above
say no `D` is two of them. -/
theorem exactly_one_of_three :
    (Nonempty (ℝ ≃ₐ[ℝ] D) ∧ IsEmpty (ℂ ≃ₐ[ℝ] D) ∧ IsEmpty (ℍ[ℝ] ≃ₐ[ℝ] D)) ∨
      (IsEmpty (ℝ ≃ₐ[ℝ] D) ∧ Nonempty (ℂ ≃ₐ[ℝ] D) ∧ IsEmpty (ℍ[ℝ] ≃ₐ[ℝ] D)) ∨
      (IsEmpty (ℝ ≃ₐ[ℝ] D) ∧ IsEmpty (ℂ ≃ₐ[ℝ] D) ∧ Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D)) := by
  rcases RealDivisionQuaternionCase.frobenius (D := D) with hr | hc | hq
  · obtain ⟨f⟩ := hr
    refine Or.inl ⟨⟨f⟩, ⟨fun g => ?_⟩, ⟨fun g => ?_⟩⟩
    · exact isEmpty_ringEquiv_real_complex.false (g.trans f.symm).symm.toRingEquiv
    · exact isEmpty_ringEquiv_real_quaternion.false (f.trans g.symm).toRingEquiv
  · obtain ⟨f⟩ := hc
    refine Or.inr (Or.inl ⟨⟨fun g => ?_⟩, ⟨f⟩, ⟨fun g => ?_⟩⟩)
    · exact isEmpty_ringEquiv_real_complex.false (g.trans f.symm).toRingEquiv
    · exact isEmpty_ringEquiv_quaternion_complex.false (g.trans f.symm).toRingEquiv
  · obtain ⟨f⟩ := hq
    refine Or.inr (Or.inr ⟨⟨fun g => ?_⟩, ⟨fun g => ?_⟩, ⟨f⟩⟩)
    · exact isEmpty_ringEquiv_real_quaternion.false (g.trans f.symm).toRingEquiv
    · exact isEmpty_ringEquiv_quaternion_complex.false (f.trans g.symm).toRingEquiv

end RealDivisionExactlyOne
