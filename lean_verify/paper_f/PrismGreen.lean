/-
  PrismGreen.lean — the prism's blocks as matrices, and their inverses.

  WHY. `PrismTransfer` proved entrywise that the two-layer stack's `A + B` is
  the base graph's massive operator and `A − B` is the same operator at a
  shifted mass, and recorded two things it did not have: **no bundled matrix
  identity and no inverse**, so nothing downstream could invert either block.
  Its header also carries a recorded overclaim — two theorems its draft
  advertised and it does not contain — whose remaining leg was written out on
  `UNLOCK_WATCHLIST.md` in four steps.

  **This is steps (i) to (iii) of that leg, and it is not step (iv).** The
  identification is now a matrix equation and both blocks are inverted; the
  reflected-form evaluation and the strictness upgrade still are not proved,
  and the reason is stated below rather than deferred silently.

  WHAT THIS FILE PROVES:
  1. **`lowerEquiv`** — the lower layer of the stack IS the base vertex set,
     as an `Equiv`. The subtype `↥(lower V)` was the only thing standing
     between an entrywise identity and a matrix one.
  2. **`plusOp_submatrix`, `minusOp_submatrix`** — **the identification as
     MATRIX EQUATIONS**: `A + B` is `massive K m` and `A − B` is
     `massive K (√(m²+2))`, each read through `lowerEquiv`.
  3. **`plusOp_inv`, `minusOp_inv`** — **and therefore both blocks are
     inverted**: `(A + B)⁻¹` is the base graph's Green function at mass `m`,
     `(A − B)⁻¹` is it at mass `√(m²+2)`. This is the statement
     `PrismTransfer` said a downstream user could not have.
  4. **`plusOp_posSemidef`, `minusOp_posSemidef`** — both blocks are positive
     SEMIdefinite for nonzero mass, recovered from the base graph rather than
     from `GraphReflectionPositive`'s general argument. **Semidefinite and not
     definite, and the reason is a gap in Mathlib rather than in the
     mathematics**: `Matrix.posSemidef_submatrix_equiv` exists and has **no
     `PosDef` analogue** — searched for under that name and by inspecting
     `Mathlib/LinearAlgebra/Matrix/PosDef.lean`. The definite statement is
     already available in general from
     `GraphReflectionPositive.plusOp_posDef`, so nothing is lost; what is
     recorded is a small missing Mathlib lemma and an upstreaming candidate.

  WHAT THIS DOES NOT DO.
  * **Step (iv) is not here, and neither are the two theorems it would give.**
    `reflectedForm_prism_eq` needs the dot product in
    `GraphReflectionPositive.energy_symExt_eq` reindexed along `lowerEquiv`,
    which is mechanical and not written. `reflectionPositive_prism_strict`
    needs more than that: it needs **STRICT** antitonicity of matrix
    inversion, and the estate has only the non-strict form
    (`MatrixLoewner.posDef_inv_le_inv`). The natural route —
    `P⁻¹ − M⁻¹ = P⁻¹(M − P)M⁻¹` with `M − P = 2·1`, a product of two
    commuting positive definite matrices — is written down on the watchlist
    and **is not attempted here.** The overclaim recorded in
    `PrismTransfer`'s header therefore stands, with its leg shortened by
    three steps out of four.

    ⚠ **THE FOURTH STEP WAS TAKEN, AND THIS FILE DID NOT SAY SO UNTIL
    2026-08-28.** Everything in the bullet above was true when written and is
    **kept as written**; what was missing is the forward pointer, and a
    reader arriving at *"is not attempted here"* followed a dead end.
    `PrismReflectedForm.reflectedForm_prism_eq` is the reindexing this bullet
    calls mechanical, and `PrismStrict` supplies the strictness by the very
    route named here — `PrismStrict.inv_sub_inv` is
    `P⁻¹ − M⁻¹ = P⁻¹(M − P)M⁻¹`, and `PrismStrict.inv_sub_inv_posDef` closes
    it at `M = P + 1 + 1`, with `PrismStrict.PosDef.mul_self` doing the work
    that the "two commuting positive definite matrices" phrase was reaching
    for. The end of the chain is
    `PrismStrict.reflectionPositive_prism_strict`. **The leg is four steps out
    of four**, and `MatrixLoewner.posDef_inv_le_inv` is still the only
    NON-strict form — nothing above is withdrawn.
  * **Nothing about the reflection.** This file is linear algebra about two
    blocks; it does not mention `ReflectionPositive` and proves no positivity
    of any quadratic form in a reflected variable.
  * **Two layers, free field, finite graph**, all inherited.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PrismTransfer

namespace PrismGreen

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace PrismReflection PrismTransfer

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The lower layer is the base vertex set -/

/-- **The subtype, removed.** `GraphReflectionPositive.plusOp` is a matrix over
    `↥(lower V)`; this says that index type is `V`. -/
def lowerEquiv (V : Type*) [Fintype V] [DecidableEq V] : ↥(lower V) ≃ V where
  toFun x := (x : V × Bool).1
  invFun p := ⟨(p, false), by simp⟩
  left_inv := by
    rintro ⟨⟨xv, xb⟩, hx⟩
    simp only [mem_lower] at hx
    subst hx
    rfl
  right_inv _ := rfl

@[simp] theorem lowerEquiv_apply (x : ↥(lower V)) : lowerEquiv V x = (x : V × Bool).1 := rfl

@[simp] theorem lowerEquiv_symm_apply (p : V) :
    (((lowerEquiv V).symm p : ↥(lower V)) : V × Bool) = (p, false) := rfl

/-! ## 2. The blocks, as matrix equations -/

theorem plusOp_submatrix :
    GraphReflectionPositive.plusOp (prism K) m (swap (V := V)) (lower V)
      = (massive K m).submatrix (lowerEquiv V) (lowerEquiv V) := by
  ext x y
  obtain ⟨⟨xv, xb⟩, hx⟩ := x
  obtain ⟨⟨yv, yb⟩, hy⟩ := y
  simp only [mem_lower] at hx hy
  subst hx
  subst hy
  simpa [GraphReflectionPositive.plusOp] using plusOp_entry (m := m) K xv yv

theorem minusOp_submatrix :
    GraphReflectionPositive.minusOp (prism K) m (swap (V := V)) (lower V)
      = (massive K (Real.sqrt (m ^ 2 + 2))).submatrix (lowerEquiv V) (lowerEquiv V) := by
  ext x y
  obtain ⟨⟨xv, xb⟩, hx⟩ := x
  obtain ⟨⟨yv, yb⟩, hy⟩ := y
  simp only [mem_lower] at hx hy
  subst hx
  subst hy
  simpa [GraphReflectionPositive.minusOp] using minusOp_eq_massive_shift (m := m) K xv yv

/-! ## 3. And therefore both blocks are inverted

`PrismTransfer` said a downstream user could not invert either block. This is
the sentence that removes that.
-/

/-- **`(A + B)⁻¹` IS THE BASE GRAPH'S GREEN FUNCTION**, at the same mass. -/
theorem plusOp_inv :
    (GraphReflectionPositive.plusOp (prism K) m (swap (V := V)) (lower V))⁻¹
      = (green K m).submatrix (lowerEquiv V) (lowerEquiv V) := by
  rw [plusOp_submatrix, green, Matrix.inv_submatrix_equiv]

/-- **`(A − B)⁻¹` is the same Green function at the shifted mass.** -/
theorem minusOp_inv :
    (GraphReflectionPositive.minusOp (prism K) m (swap (V := V)) (lower V))⁻¹
      = (green K (Real.sqrt (m ^ 2 + 2))).submatrix (lowerEquiv V) (lowerEquiv V) := by
  rw [minusOp_submatrix, green, Matrix.inv_submatrix_equiv]

/-! ## 4. Positivity, from the base graph

`GraphReflectionPositive.plusOp_posDef` already proves the DEFINITE statement
in general, through the doubling lemma and the positivity of the whole stack's
operator. **Here the semidefinite one is recovered from the base graph
instead**, in one line, because §2 says the block IS a massive operator. Two
routes to one conclusion; the general one is load-bearing and this one is a
corollary of the identification, and **the value is the agreement rather than
the fact.**

**Semidefinite and not definite**, because `Matrix.posSemidef_submatrix_equiv`
has no `PosDef` analogue in Mathlib. That is a stated absence and it was
checked: searched by name across `Mathlib/`, and by reading
`Mathlib/LinearAlgebra/Matrix/PosDef.lean`, which mentions `submatrix` only in
the semidefinite lemma and one proof that uses it. Nothing is lost — the
definite form is available in general from `GraphReflectionPositive` — and the
missing lemma is recorded as an upstreaming candidate.
-/

theorem plusOp_posSemidef (hm : m ≠ 0) :
    (GraphReflectionPositive.plusOp (prism K) m (swap (V := V)) (lower V)).PosSemidef := by
  rw [plusOp_submatrix]
  exact (Matrix.posSemidef_submatrix_equiv (lowerEquiv V)).mpr (massive_posDef K hm).posSemidef

theorem minusOp_posSemidef (hm : m ≠ 0) :
    (GraphReflectionPositive.minusOp (prism K) m (swap (V := V)) (lower V)).PosSemidef := by
  rw [minusOp_submatrix]
  refine (Matrix.posSemidef_submatrix_equiv (lowerEquiv V)).mpr (massive_posDef K ?_).posSemidef
  positivity

/-! ## 5. Review round 91 — the ways this could be hollow

**"Is this just plumbing?"** Yes, and the previous file said so in advance:
its caveat read "no bundled matrix identity and no inverse … until that exists
a downstream user cannot invert either block." **This is that plumbing, named
by the file that needed it, before it was written.** Plumbing installed
against a written specification is different from plumbing invented to have
something to install.

**"How much of the seeded leg is done?"** Three steps of four, and the fourth
is NOT mechanical, which is why the count matters. Step (iv) — reindexing the
dot product in `energy_symExt_eq` — is mechanical and merely unwritten. But
`reflectionPositive_prism_strict`, one of the two theorems the leg exists to
reach, **needs strict antitonicity of matrix inversion and the estate has only
the non-strict form.** `MatrixLoewner.posDef_inv_le_inv` gives `≤`. So the
watchlist item is not three-quarters done in the sense that matters; it is
three-quarters done in Lean and still missing one genuine ingredient, and
saying "three of four steps" without that sentence would be the misleading
version.

**"§4 proves something already proved, and more weakly. Is that padding?"**
It proves a weaker form a second way and the docstring says which proof is
load-bearing and why the weaker form is what came out. The general
one, in `GraphReflectionPositive`, derives positivity of `A + B` from the
positivity of the whole stack via the doubling lemma; this one reads it off
the identification in one line. **The value is not the fact but the
agreement** — two routes to the same conclusion is the cheapest available
check that §2 identified the right matrix, and had they disagreed the error
would have been in §2.

**"Could `lowerEquiv` be the wrong bijection?"** It is forced: an element of
`↥(lower V)` is a vertex of the stack whose layer bit is `false`, so the only
data in it is the base vertex, and `left_inv` is where that is discharged —
it substitutes the bit and closes by `rfl`. If the half had been the UPPER
layer the same equiv with `true` would be needed, and none of §2–§4 would
change; that asymmetry is a fact about which half was named, not about the
mathematics.
-/

end PrismGreen
