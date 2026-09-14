/-
  PatiSalamOrthogonal: "one invariant form normalises every generator" — as one form,
  not as three scalars that agree

  SPINE LINKS L16 → L17. The residue L16 hands L17, ranked 3 of 12 in the recompute's
  Caesar order and labelled *tractable, unblocks 3*.

  WHAT WAS THERE, AND WHAT WAS MISSING. `PatiSalamOnSixteen` proves the three DIAGONAL
  trace identities on the chiral 16 — `trace (su4Rep X * su4Rep Y) = 4 · Tr(XY)` and the
  two `sl₂` analogues — and `index_ratio_one`, that the ratio of any two is `1`.
  `PatiSalamTraceForm` then upgraded each of the three to a value of Mathlib's
  `LieModule.traceForm`, with ad-invariance from `lie_traceForm_eq_zero`. **Six trace
  products were never computed at all**: the MIXED ones. And a query confirms it —
  `grep 'trace (su4Rep.*su2\|trace (su2LRep.*su2RRep'` over `PatiSalamOnSixteen` returns
  nothing. Without them "one invariant form normalises every generator" is three
  statements about three algebras that happen to share a constant; **with them it is one
  statement about one form on the product.**

  THE SIX MIXED TERMS, computed rather than assumed.
  * **`trace_su4_su2L`**: `Tr(π(X) π(A)) = Tr X · Tr A`. Not zero in general — and that is
    the point. `su4Rep X`'s upper block is `X ⊗ 1` and `su2LRep A` is `1 ⊗ A` there, so
    `Matrix.mul_kronecker_mul` collapses the product to `X ⊗ A` and
    `Matrix.trace_kronecker` splits its trace.
  * **`trace_su4_su2R`**: `-(Tr X · Tr B)`, with the sign from the `4̄` block's `-Xᵀ`.
  * **`trace_su2L_su2R`** and **`trace_su2R_su2L`**: **identically zero, with no
    hypothesis**, because the two `sl₂` factors live on different blocks and their matrix
    product is `0` (`PatiSalamOnSixteen.su2LRep_mul_su2RRep`).
  * The two remaining orders follow by `Matrix.trace_mul_comm`.

  **SO THE ORTHOGONALITY IS EXACTLY THE TRACELESSNESS CONDITION**, and it is worth saying
  which way round: the two `sl₂` factors are orthogonal to each other for free, and
  `sl₄` is orthogonal to both **precisely when `Tr X = 0`** — which is the condition that
  makes `X` an element of `sl₄` rather than of `gl₄`. The gauge generators are traceless,
  so on the gauge algebra the form is diagonal; on `gl₄` it is not, and
  `trace_su4_su2L_ne_zero_of_trace_ne` exhibits a pair where it fails. **A residue that
  turns out to be a hypothesis is worth more than one that turns out to be an obstacle.**

  THE THEOREM THE RESIDUE ASKED FOR. **`psRep_trace_orthogonal_sum`**: for traceless `X`,
  `Y` and ANY `A, A', B, B'`,

  > `Tr₁₆(ρ(X,A,B) · ρ(Y,A',B')) = 4·Tr(XY) + 4·Tr(AA') + 4·Tr(BB')`

  — the trace form of the 16, restricted to the Pati–Salam product algebra, is the
  **orthogonal direct sum of the three factor forms, each with the same index 4**. That is
  what "one invariant form normalises every generator" means, and it is now one theorem
  rather than three plus a ratio. `psRep_trace_diagonal_iff_traceless` states the converse
  direction as a biconditional at fixed `A, B`, so the traceless condition is not just
  sufficient but necessary.

  WHAT IS **NOT** CLAIMED, and none of it moves.
  * **The coupling matching.** That the common normalisation extends to the abelian
    generator `Y` is `ASSUMPTIONS_LEDGER` 57, a `DECISIONS NEEDED` entry, and untouched.
    A single orthogonal form on the NON-ABELIAN product is a necessary condition for the
    matching, not the matching. `T₃L` and `Y` are `WeinbergIndex`'s diagonal `ℚ` matrices
    and are not elements of the factors used here.
  * **`so(10)`**, inside which the matching would be automatic, is absent from the estate
    by query — and an orthogonal direct sum with equal indices is exactly what such an
    embedding would need, which is why this is a step towards it and not a substitute.
  * **The chiral content.** That the 16 with its two blocks is a CONSEQUENCE of the
    cascade rather than the input `PSIndex` is L12's postulate (`ASSUMPTIONS_LEDGER` 5, 34).
  * **The abelian factor, and the gap is one level in from where it looks.** `psRep` has
    three factors. The `u(1)` IS already a Lie algebra in this estate — `SMInPatiSalam.SM`
    is `sl (Fin 3) ℂ × sl (Fin 2) ℂ × ℂ` and `smToPS : SM →ₗ⁅ℂ⁆ PS` is a genuine `LieHom`,
    so the bare `ℂ` slot carries the trivial bracket. **What is missing is its ACTION on the
    16**: `grep 'psRepU1\|u1Rep'` over `paper_f/` returns nothing, and `WeinbergIndex.Y` is
    a `Matrix PSIndex PSIndex ℚ` (a `Matrix.diagonal`), not a representation. So there is no
    `ρ_Y` to feed `LieModule.traceForm`, and the four-factor orthogonal sum cannot be
    stated — `UNLOCK_WATCHLIST` 260.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import PatiSalamOnSixteen

namespace PatiSalamOrthogonal

open Matrix SU4OnSixteen PatiSalamOnSixteen WeinbergIndex
open scoped Kronecker

noncomputable section

/-! ## 1. The six mixed trace products -/

/-- The `sl₄`–`sl₂_L` cross term is `Tr X · Tr A`. Both live on the left-handed block, as
`X ⊗ 1` and `1 ⊗ A`, so `mul_kronecker_mul` collapses the product to `X ⊗ A`. -/
theorem trace_su4_su2L (X : Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su4Rep X * su2LRep A) = trace X * trace A := by
  unfold su4Rep su2LRep
  rw [fromBlocks_multiply, trace_fromBlocks_any]
  simp only [Matrix.mul_zero, add_zero, trace_zero]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, trace_kronecker]

/-- The `sl₄`–`sl₂_R` cross term, with the sign from the `4̄` block's `-Xᵀ`. -/
theorem trace_su4_su2R (X : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su4Rep X * su2RRep B) = -(trace X * trace B) := by
  unfold su4Rep su2RRep
  rw [fromBlocks_multiply, trace_fromBlocks_any]
  simp only [Matrix.mul_zero, add_zero, zero_add, trace_zero]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, trace_kronecker]
  simp [Matrix.trace_neg, Matrix.trace_transpose]

theorem trace_su2L_su4 (X : Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2LRep A * su4Rep X) = trace X * trace A := by
  rw [Matrix.trace_mul_comm, trace_su4_su2L]

theorem trace_su2R_su4 (X : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2RRep B * su4Rep X) = -(trace X * trace B) := by
  rw [Matrix.trace_mul_comm, trace_su4_su2R]

/-- **The two `sl₂` factors are orthogonal with NO hypothesis**, because they live on
different blocks and their matrix product is `0`. -/
theorem trace_su2L_su2R (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2LRep A * su2RRep B) = 0 := by
  rw [su2LRep_mul_su2RRep, trace_zero]

theorem trace_su2R_su2L (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2RRep A * su2LRep B) = 0 := by
  rw [su2RRep_mul_su2LRep, trace_zero]

/-! ## 2. Orthogonality is exactly the traceless condition

Stated in both directions, because "the mixed terms vanish" is a hypothesis about `X`
rather than a property of the representation, and a reader should be able to see which. -/

/-- On `gl₄` the form is **not** diagonal: at `X = 1` and `A = 1` the `sl₄`–`sl₂_L` term
is `8`. So the traceless condition is doing work rather than decorating. -/
theorem trace_su4_su2L_ne_zero_of_trace_ne :
    trace (su4Rep (1 : Matrix (Fin 4) (Fin 4) ℂ) * su2LRep (1 : Matrix (Fin 2) (Fin 2) ℂ))
      ≠ 0 := by
  rw [trace_su4_su2L]
  simp

/-- All four `sl₄`-involving cross terms vanish **exactly** when `X` is traceless — for
every `A` and `B`, and with the `sl₂`–`sl₂` pair already zero. -/
theorem cross_terms_vanish_of_traceless (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hX : trace X = 0) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su4Rep X * su2LRep A) = 0
    ∧ trace (su4Rep X * su2RRep B) = 0
    ∧ trace (su2LRep A * su4Rep X) = 0
    ∧ trace (su2RRep B * su4Rep X) = 0
    ∧ trace (su2LRep A * su2RRep B) = 0
    ∧ trace (su2RRep B * su2LRep A) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, trace_su2L_su2R A B, trace_su2R_su2L B A⟩
  · rw [trace_su4_su2L, hX, zero_mul]
  · rw [trace_su4_su2R, hX, zero_mul, neg_zero]
  · rw [trace_su2L_su4, hX, zero_mul]
  · rw [trace_su2R_su4, hX, zero_mul, neg_zero]

/-! ## 3. The theorem the residue asked for -/

/-- **ONE INVARIANT FORM, AS ONE FORM.** For traceless `X`, `Y` and any `A, A', B, B'`,
the trace form of the 16 restricted to the Pati–Salam product algebra is the **orthogonal
direct sum** of the three factor forms, each with the same index `4`:

`Tr₁₆(ρ(X,A,B) · ρ(Y,A',B')) = 4·Tr(XY) + 4·Tr(AA') + 4·Tr(BB')`.

`PatiSalamOnSixteen.index_ratio_one` said the three constants agree; this says there is
one form whose restriction to each factor carries that constant, with no cross terms. -/
theorem psRep_trace_orthogonal_sum (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (A A' B B' : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : trace X = 0) (hY : trace Y = 0) :
    trace (psRep (X, A, B) * psRep (Y, A', B'))
      = 4 * trace (X * Y) + 4 * trace (A * A') + 4 * trace (B * B') := by
  simp only [psRep, Matrix.add_mul, Matrix.mul_add, trace_add]
  rw [trace_su4Rep_mul, trace_su2LRep_mul, trace_su2RRep_mul,
    trace_su4_su2L, trace_su4_su2R, trace_su2L_su4, trace_su2R_su4,
    trace_su2L_su2R, trace_su2R_su2L, hX, hY]
  ring

/-- **A FEATURE OF THE CHIRAL STRUCTURE, found while stating the converse and worth its
own theorem.** The `sl₄`–`sl₂_L` and `sl₄`–`sl₂_R` cross terms carry **opposite signs** —
the first from the `4` block's `X`, the second from the `4̄` block's `−Xᵀ` — so when the
two `sl₂` arguments AGREE they cancel, and the form looks diagonal whether or not `X` is
traceless. A naive *"diagonality forces tracelessness"* claim would therefore have been
false, and the converse below has to separate the two `sl₂` arguments to see the
obstruction. -/
theorem su2_cross_terms_cancel (X : Matrix (Fin 4) (Fin 4) ℂ)
    (C : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su4Rep X * su2LRep C) + trace (su4Rep X * su2RRep C) = 0 := by
  rw [trace_su4_su2L, trace_su4_su2R]
  ring

/-- **AND THE CONVERSE, so the traceless hypothesis is necessary and not merely
convenient.** With the two `sl₂` arguments SEPARATED — `A' = 1`, `B' = 0`, so the
cancellation above cannot hide the cross term — the form is diagonal exactly when `X` is
traceless. -/
theorem psRep_trace_diagonal_iff_traceless (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (psRep (X, 0, 0) * psRep (Y, 1, 0)) = 4 * trace (X * Y) ↔ trace X = 0 := by
  have hexp : trace (psRep (X, 0, 0) * psRep (Y, 1, 0))
      = 4 * trace (X * Y) + trace X * trace (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [psRep, Matrix.add_mul, Matrix.mul_add, trace_add]
    rw [trace_su4Rep_mul, trace_su2LRep_mul, trace_su2RRep_mul,
      trace_su4_su2L, trace_su4_su2R, trace_su2L_su4, trace_su2R_su4,
      trace_su2L_su2R, trace_su2R_su2L]
    simp
  rw [hexp]
  constructor
  · intro h
    have h2 : trace X * trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by linear_combination h
    have hne : trace (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by simp
    exact (mul_eq_zero.mp h2).resolve_right hne
  · intro h
    rw [h, zero_mul, add_zero]

end

end PatiSalamOrthogonal
