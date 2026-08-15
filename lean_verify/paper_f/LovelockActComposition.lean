import LovelockFrameComposition
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The four-index composition law, and the word "representations" caught up with

## ERRATUM 171: two headers in this group disagreed, and one of them was ahead of the proof

`AlgebraicCurvature`, §"How a four-index array transforms under `Q`":

> **It is called `act` and the composition law is NOT proved.** … that `act (Q · Qʹ) = act Q ∘ act
> Qʹ`, which is **the other half of being a group action** and what a `MulAction` instance would
> assert, is **not established here and is not used below**.

`LovelockEquivariance`, on the same object, two files later:

> it **commutes with every change of orthonormal frame**, which is what makes the three pieces
> *representations* rather than coordinates

and again at `act_weylPart`: *"the splitting of the previous layer is a splitting of
REPRESENTATIONS and not of coordinates."*

**By the estate's own words those two cannot both stand.** A representation needs the action law,
and `AlgebraicCurvature` says outright that half of it is missing. What `LovelockEquivariance`
actually proved is equivariance for each *single* orthogonal `Q`, which is the substance but not
the word. **This file removes the disagreement by proving the missing half**, per the standing
order to fold findings back by proving more rather than by softening prose.

`LovelockFrameComposition` recorded the guess this discharges:

> **It looks like Fubini on the product index, four slots at once** — and that is a sizing
> judgement … recorded as a guess for a later unit to test, not as a promise.

**The mechanism guessed was wrong; the sizing it was standing in for held.** There is no fourfold
Fubini — one reindexing of the product into two pairs and **one** `Finset.sum_comm` — because
`act` is *also* a conjugation, by the **Kronecker square** of the frame, and Mathlib's
`Matrix.mul_kronecker_mul` does the rest. The guess was a mechanism used as a proxy for
difficulty; the proxy was wrong and the conclusion it supported was right, which is worth
separating because next time it may go the other way.

## What is proved

* **`act_eq_conj`** — `act Q R a b c d = ((Q ⊗ₖ Q) · mat4 R · (Q ⊗ₖ Q)ᵀ) (a,b) (c,d)`, where
  `mat4` reads a four-index array as a matrix on pairs. This is the four-index twin of
  `LovelockDiagonalise.act2_eq_conj`, and the only step with any content;
* `mat4_act` — the same at matrix level;
* **`isOrth_kronecker`** — the Kronecker square of an orthogonal frame is orthogonal, so the
  conjugation above is by an honest orthogonal matrix on the doubled index set;
* **`act_one`** and **`act_mul`** — the identity and composition laws.

**AND NEITHER LAW NEEDS ORTHOGONALITY**, which is more than the erratum asked for and is stated
because a draft of this paragraph claimed less. `act_one` and `act_mul` carry no `IsOrth`
hypothesis at all: `act` is a monoid action of **every** square matrix under multiplication on
four-index arrays. `LovelockFrameComposition.isOrth_mul` and `isOrth_one` then say the orthogonal
frames are a submonoid, so the restriction is an action of `O(n)` — and it is *that* restriction,
together with `LovelockEquivariance`'s three intertwining theorems, that makes the three summands
subrepresentations in the ordinary sense.

This is the same shape as `LovelockProjections`' finding that none of its four trace identities
needs `IsAlgCurv`: the hypothesis that the surrounding theory carries is not the hypothesis the
computation uses.

## What is still NOT done

**No `MulAction` instance is bundled**, for the reason `LovelockReduction` §1 gives and
`LovelockFrameComposition` repeats: the carrier would be one nothing in the estate consumes. The
laws are stated; bundling them is a separate decision.

**And the identity law is not new mathematics.** `AlgebraicCurvature.act_delta` already had it in
the `delta` spelling; `act_one` is the `Matrix.one` spelling, stated because that is what
`act_mul` composes with. It is labelled here rather than presented as a result.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockActComposition

open AlgebraicCurvature LovelockFrameComposition Matrix Finset Kronecker

variable {n : ℕ} {Q Q' : Fin n → Fin n → ℝ}

/-! ## 1. A four-index array is a matrix on pairs

`ERRATUM 168`'s question, asked first: Mathlib has no name for this reindexing, and `paper_f` had
none either — `AnomalyTraces` uses `⊗ₖ` but never pairs up a four-index array. `Matrix.of` on the
curried form is the whole definition.
-/

/-- **THE FOUR-INDEX ARRAY, READ AS A MATRIX ON PAIRS.** -/
def mat4 (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := Matrix.of fun u v => R u.1 u.2 v.1 v.2

/-- **`act` IS CONJUGATION BY THE KRONECKER SQUARE OF THE FRAME.** The four-index twin of
`LovelockDiagonalise.act2_eq_conj`, and the only step in this file with content: the product index
of `act` is regrouped into two pairs, and the two `Q` factors of each pair are exactly one entry of
the Kronecker square. -/
theorem act_eq_conj (Q : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) :
    act Q R a b c d
      = ((Matrix.of Q ⊗ₖ Matrix.of Q) * mat4 R * (Matrix.of Q ⊗ₖ Matrix.of Q)ᵀ) (a, b) (c, d) := by
  have hL : act Q R a b c d
      = ∑ q : (Fin n × Fin n) × (Fin n × Fin n),
          Q a q.1.1 * Q b q.1.2 * Q c q.2.1 * Q d q.2.2 * R q.1.1 q.1.2 q.2.1 q.2.2 := by
    simp only [act]
    exact Fintype.sum_equiv
      ⟨fun p => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)),
       fun q => (q.1.1, q.1.2, q.2.1, q.2.2), fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl
  rw [hL, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.kroneckerMap_apply, mat4, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun s _ => by ring

/-- The same identity at matrix level, which is the form the composition proof rewrites with. -/
theorem mat4_act (Q : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    mat4 (act Q R)
      = (Matrix.of Q ⊗ₖ Matrix.of Q) * mat4 R * (Matrix.of Q ⊗ₖ Matrix.of Q)ᵀ := by
  ext u v
  exact act_eq_conj Q R u.1 u.2 v.1 v.2

/-- **AND THE CONJUGATING MATRIX IS ORTHOGONAL.** So the frame change on four-index arrays is a
conjugation by an orthogonal matrix on the doubled index set, exactly as on 2-tensors. **Not used
by the two laws below** — they need no orthogonality whatever — and stated because it is what makes
the header's word *representation* mean what it usually means: the action is by orthogonal
transformations of the larger space, not by arbitrary ones. -/
theorem isOrth_kronecker (hQ : IsOrth Q) :
    (Matrix.of Q ⊗ₖ Matrix.of Q) ∈ Matrix.orthogonalGroup (Fin n × Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have hQQ : Matrix.of Q * (Matrix.of Q)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (isOrth_iff.mp hQ)
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hQQ,
    Matrix.one_kronecker_one]

/-! ## 2. The two laws -/

/-- The identity frame change is the identity. **Not new mathematics** —
`AlgebraicCurvature.act_delta` has it in the `delta` spelling; this is the `Matrix.one` spelling,
which is what `act_mul` composes with. -/
theorem act_one (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act (fun x y => (1 : Matrix (Fin n) (Fin n) ℝ) x y) R a b c d = R a b c d := by
  rw [act_eq_conj]
  have h1 : (Matrix.of fun x y => (1 : Matrix (Fin n) (Fin n) ℝ) x y)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [h1, Matrix.one_kronecker_one, Matrix.transpose_one, one_mul, mul_one]
  rfl

/-- **THE COMPOSITION LAW ON FOUR-INDEX ARRAYS.** `AlgebraicCurvature`'s caveat, discharged.
`Matrix.mul_kronecker_mul` is the whole of it: the Kronecker square of a product is the product of
the Kronecker squares, so the two conjugations telescope. -/
theorem act_mul (Q Q' : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) :
    act (fun x y => (Matrix.of Q * Matrix.of Q') x y) R a b c d = act Q (act Q' R) a b c d := by
  rw [act_eq_conj, act_eq_conj, mat4_act]
  have hK : (Matrix.of fun x y => (Matrix.of Q * Matrix.of Q') x y)
      = Matrix.of Q * Matrix.of Q' := rfl
  rw [hK, Matrix.mul_kronecker_mul, Matrix.transpose_mul]
  simp only [mul_assoc]

end LovelockActComposition
