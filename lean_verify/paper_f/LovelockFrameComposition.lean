import LovelockDiagonalise

/-!
# The composition law, on 2-tensors, and the caveat it half-discharges

`AlgebraicCurvature` has carried this since the day it was written:

> **It is called `act` and the composition law is NOT proved.** `act_delta` below checks that the
> identity frame change is the identity; that `act (Q · Qʹ) = act Q ∘ act Qʹ`, which is the other
> half of being a group action and what a `MulAction` instance would assert, is **not established
> here and is not used below** — every theorem in this section quantifies over a single `Q`.

`LovelockFrameInverse` proved **one instance** of it — `Qᵀ · Q = 1`, on 2-tensors — by direct
computation, and said so. `LovelockDiagonalise.act2_eq_conj` then identified `act2 Q S` as the
matrix conjugation `Q · S · Qᵀ`, and **that makes the general law on 2-tensors a rewrite**:

    act2 (Q · Qʹ) S  =  (Q Qʹ) S (Q Qʹ)ᵀ  =  Q (Qʹ S Qʹᵀ) Qᵀ  =  act2 Q (act2 Qʹ S)

## What is proved

* **`isOrth_iff`** — `IsOrth Q` **if and only if** `Q` is in Mathlib's orthogonal group. Both
  directions now exist (`AlgebraicCurvature.isOrth_of_mem_orthogonalGroup` and
  `LovelockDiagonalise.mem_orthogonalGroup_of_isOrth`), so the estate's predicate and the library's
  group are interchangeable rather than merely comparable;
* **`isOrth_mul`**, **`isOrth_one`** — hence `IsOrth` is closed under products and holds of the
  identity, which follows from the `Iff` and `orthogonalGroup` being a submonoid, and which no
  amount of index manipulation had given;
* **`act2_one`** — the identity frame change is the identity on 2-tensors, the `act2` analogue of
  `act_delta`;
* **`act2_mul`** — **the composition law on 2-tensors.**

`LovelockFrameInverse.act2_transp_act2` is now a special case, and `act2_transp_act2'` derives it
that way as a check that the two agree. The direct computation is kept: it is what
`LovelockDiagonalise` was built on, and re-deriving a proved theorem is not a reason to delete it.

## What is still NOT proved, stated precisely

**The four-index law `act (Q · Qʹ) R = act Q (act Qʹ R)` is untouched.** `act2_eq_conj`'s route
does not reach it: `act` is a fourfold contraction against a product index, not a matrix product,
so there is no `Matrix.mul` identity to rewrite with. The estate's caveat therefore stands **for
four-index arrays** and is discharged **only for 2-tensors**.

**It looks like Fubini on the product index, four slots at once** — and that is a sizing
judgement, of exactly the kind this group of files exists because one of mine was wrong. It is
recorded as a guess for a later unit to test, not as a promise. **Nothing in the estate uses the
four-index law**, which is why it is not attempted here rather than attempted and abandoned.

**And no `MulAction` instance is built.** The three laws above are what such an instance would
assert on 2-tensors, and bundling them would mean choosing a carrier — `↥(orthogonalGroup (Fin n)
ℝ)` acting on `Fin n → Fin n → ℝ` — that nothing in the estate consumes. `LovelockReduction` §1's
reason for stating rather than bundling applies.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockFrameComposition

open AlgebraicCurvature LovelockFrameInverse LovelockDiagonalise Matrix Finset

variable {n : ℕ} {Q Q' : Fin n → Fin n → ℝ}

/-! ## 1. The estate's predicate and the library's group are the same thing -/

/-- **`IsOrth` IS MEMBERSHIP IN THE ORTHOGONAL GROUP**, both ways. -/
theorem isOrth_iff : IsOrth Q ↔ Matrix.of Q ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨mem_orthogonalGroup_of_isOrth, isOrth_of_mem_orthogonalGroup⟩

/-- **AND THEREFORE `IsOrth` IS CLOSED UNDER PRODUCTS**, which is a submonoid fact and not an
index computation. -/
theorem isOrth_mul (hQ : IsOrth Q) (hQ' : IsOrth Q') :
    IsOrth fun a b => (Matrix.of Q * Matrix.of Q') a b :=
  isOrth_iff.mpr (Submonoid.mul_mem _ (isOrth_iff.mp hQ) (isOrth_iff.mp hQ'))

/-- The identity frame change is orthogonal. `AlgebraicCurvature.isOrth_delta` says the same for
`delta`; this is the `Matrix.one` spelling, which is what `act2_mul` composes with. -/
theorem isOrth_one : IsOrth fun a b => (1 : Matrix (Fin n) (Fin n) ℝ) a b :=
  isOrth_iff.mpr (Submonoid.one_mem _)

/-! ## 2. The composition law, on 2-tensors -/

/-- The identity frame change acts as the identity, the `act2` analogue of `act_delta`. -/
theorem act2_one (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (fun a b => (1 : Matrix (Fin n) (Fin n) ℝ) a b) S b c = S b c := by
  rw [act2_eq_conj]
  have h1 : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℝ) a b)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [h1, Matrix.transpose_one, one_mul, mul_one, Matrix.of_apply]

/-- **THE COMPOSITION LAW ON 2-TENSORS.** `AlgebraicCurvature`'s caveat, discharged for `act2`. -/
theorem act2_mul (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (fun a b => (Matrix.of Q * Matrix.of Q') a b) S b c = act2 Q (act2 Q' S) b c := by
  have hfun : (fun x y => act2 Q' S x y) = fun x y =>
      (Matrix.of Q' * Matrix.of S * (Matrix.of Q')ᵀ) x y := by
    funext x y; exact act2_eq_conj Q' S x y
  rw [act2_eq_conj, act2_eq_conj]
  have hof : (Matrix.of fun a b => (Matrix.of Q * Matrix.of Q') a b)
      = Matrix.of Q * Matrix.of Q' := rfl
  have hof2 : (Matrix.of fun x y => act2 Q' S x y)
      = Matrix.of Q' * Matrix.of S * (Matrix.of Q')ᵀ := by
    rw [hfun]; rfl
  rw [hof, hof2, Matrix.transpose_mul]
  simp only [mul_assoc]

/-- **AND `LovelockFrameInverse.act2_transp_act2` IS THE SPECIAL CASE `Qᵀ · Q = 1`.** Not new
content — a check that the general law and the direct computation agree, which is worth one
theorem because the direct computation is what `LovelockDiagonalise` was built on. -/
theorem act2_transp_act2' (hQ : IsOrth Q) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (transp Q) (act2 Q S) b c = S b c := by
  have hcomp := act2_mul (Q := transp Q) (Q' := Q) S b c
  have hmul : Matrix.of (transp Q) * Matrix.of Q = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have h : Matrix.of (transp Q) = (Matrix.of Q)ᵀ := rfl
    rw [h, ← Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ]
    exact isOrth_iff.mp hQ
  rw [hmul] at hcomp
  rw [← hcomp, act2_one]

end LovelockFrameComposition
