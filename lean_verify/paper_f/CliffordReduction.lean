import CliffordSignatureStep

/-!
# Every real Clifford algebra is a matrix algebra over a small one

`formalisation/reach_closure.py` reports that every `Cl(p,q)` with `p + q ≤ 80` reduces, by a
chain of this estate's own isomorphisms, to one of sixteen base cases — **3321 states, `0`
undetermined** (`WALLS §W7.2`). That is a Python computation over a bounded range.
`CliffordSignatureStep` put the five moves it applies into Lean at the signature index. **This
file runs the induction, in Lean, with no bound.**

> **`clifford_reduces_to_small`** — for every `p` and `q` there are `p'`, `q'` with
> `p' + q' ≤ 7` and a `k > 0` with `Cl(p,q) ≃ₐ[ℝ] M_k(Cl(p',q'))`.

## Why this shape, and why it is not the statement the watch-list calls impossible

The watch-list's real-classification item says a single theorem quantified over `p` and `q`
"does not exist, **because the eight targets are different types**" — `ℝ`, `ℂ`, `ℍ` and their
matrix algebras — and that choosing how to present the disjunction is `ASSUMPTIONS 49`'s
decision, which belongs to the author.

**This statement does not make that decision and does not need it.** Its right-hand side is
`M_k(Cl(p',q'))` with `p' + q' ≤ 7`: one type schema, with the base case left as a Clifford
algebra rather than named as a matrix algebra over a division ring. So it says *every real
Clifford algebra is a matrix algebra over one of the small ones*, and says nothing about which.
Naming the sixteen is exactly the step this file declines to take, and `ASSUMPTIONS 49` stays
open and untouched.

## What the induction uses, and what it does not

**Three of the five**, and which three is worth stating exactly:

* hyperbolic `(p+1, q+1) → (p, q)`, `M₂` — used whenever both indices are positive;
* eight-fold `(p+8, q) → (p, q)` and its mirror `(p, q+8) → (p, q)`, `M₁₆` — used on the axes.

The other two are unused for **different** reasons, and conflating them would be a mistake. The
`(0, +2)` step lands on `Cl(q,p) ⊗ ℍ`, which is not a matrix algebra over a Clifford algebra, so
it **cannot** appear in a statement of this shape. The `(+2, 0)` step lands on `M₂(Cl(q,p))` and
**could** appear — it is simply not needed, because the hyperbolic step covers every point with
both indices positive and the eight-folds cover the two axes.

**That the induction terminates on three moves is the finding.** `reach_closure.py` needs all
five, because it names sixteen specific answers and the two-steps are what carry a point across
the diagonal to a base case that has one. The weaker statement proved here — *a* small base
case, not a named one — needs three.

`matrixFlatten` is the composition step — `M_j(M_k(A)) ≃ₐ[ℝ] M_{j·k}(A)`, `Matrix.compAlgEquiv`
and one reindex. `CliffordModelPeriodicity.matrixPowFlatten` is the `j = m`, `k = m^i` case;
this is the general one and the estate did not have it.

## What is NOT proved

* Nothing identifies the base cases. `p' + q' ≤ 7` bounds them; it does not name them, and the
  sixteen names are `ASSUMPTIONS 49`'s decision.
* Nothing here bounds `k`. It is a product of `2`s and `16`s along the reduction chain and the
  statement is existential in it.
* The reduction is **not** claimed canonical: different case orders give different `(p', q', k)`,
  and `Nonempty` records existence, not choice.
-/

namespace CliffordReduction

open CliffordSignatureModel CliffordSignatureStep
open scoped Quaternion TensorProduct

noncomputable section

/-! ## 1. Flattening a matrix algebra over a matrix algebra -/

/-- **`M_j(M_k(A)) ≃ₐ[ℝ] M_{j·k}(A)`.** `CliffordModelPeriodicity.matrixPowFlatten` is the case
`k = j^i`; nothing in its proof used that, and this is the general statement. -/
def matrixFlatten (A : Type*) [Semiring A] [Algebra ℝ A] (j k : ℕ) :
    Matrix (Fin j) (Fin j) (Matrix (Fin k) (Fin k) A) ≃ₐ[ℝ]
      Matrix (Fin (j * k)) (Fin (j * k)) A :=
  (Matrix.compAlgEquiv (Fin j) (Fin k) A ℝ).trans
    (Matrix.reindexAlgEquiv ℝ A finProdFinEquiv)

/-- **`M₁(A) ≃ₐ[ℝ] A`, with `Fin 1`'s own instances.**

Mathlib's `Matrix.uniqueAlgEquiv` states this for any `Unique` index, but **derives** the
`Fintype` and `DecidableEq` from `Unique`, so its `Matrix (Fin 1) (Fin 1) A` carries
`Unique.fintype` and `decidableEq_of_subsingleton` where every other statement in this estate
carries `Fin.fintype 1` and `instDecidableEqFin 1`. Same type, different instances, and `exact`
reports an application type mismatch rather than an instance clash. **This is the `Fintype`
diamond that cost `IsingWalkExpect` six builds, in a second guise — and this time the mismatched
instance comes from Mathlib rather than from the estate.** Four lines is cheaper than fighting
it. -/
def matrixOne (A : Type*) [Semiring A] [Algebra ℝ A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[ℝ] A where
  toFun M := M 0 0
  invFun a := Matrix.of fun _ _ => a
  left_inv M := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl
  commutes' r := by simp [Matrix.algebraMap_matrix_apply]

/-! ## 2. One step down, whenever the total is at least eight -/

/-- **AT `p + q ≥ 8` A MOVE ALWAYS APPLIES, AND IT LANDS ON A MATRIX ALGEBRA.** Both indices
positive is the hyperbolic step; otherwise the total sits on one axis, is at least `8` there, and
the eight-fold move applies. -/
theorem reduces_one (p q : ℕ) (h : 8 ≤ p + q) :
    ∃ p' q' k : ℕ, p' + q' < p + q ∧ 0 < k ∧
      Nonempty (CliffordAlgebra (sigForm p q) ≃ₐ[ℝ]
        Matrix (Fin k) (Fin k) (CliffordAlgebra (sigForm p' q'))) := by
  by_cases hp : 0 < p
  · by_cases hq : 0 < q
    · obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
      exact ⟨a, b, 2, by omega, by norm_num, clifford_sig_step_hyp a b⟩
    · have hq0 : q = 0 := by omega
      subst hq0
      obtain ⟨c, rfl⟩ : ∃ c, p = c + 8 := ⟨p - 8, by omega⟩
      exact ⟨c, 0, 16, by omega, by norm_num, clifford_sig_periodicity_eight c 0⟩
  · have hp0 : p = 0 := by omega
    subst hp0
    obtain ⟨c, rfl⟩ : ∃ c, q = c + 8 := ⟨q - 8, by omega⟩
    exact ⟨0, c, 16, by omega, by norm_num, clifford_sig_periodicity_eight_neg 0 c⟩

/-! ## 3. The induction -/

/-- The induction, with the total carried as a fuel parameter so that the recursion is on `ℕ`. -/
private theorem reduces_aux : ∀ n p q : ℕ, p + q ≤ n →
    ∃ p' q' k : ℕ, p' + q' ≤ 7 ∧ 0 < k ∧
      Nonempty (CliffordAlgebra (sigForm p q) ≃ₐ[ℝ]
        Matrix (Fin k) (Fin k) (CliffordAlgebra (sigForm p' q'))) := by
  intro n
  induction n with
  | zero =>
      intro p q h
      exact ⟨p, q, 1, by omega, by norm_num,
        ⟨(matrixOne _).symm⟩⟩
  | succ n ih =>
      intro p q h
      by_cases hs : p + q ≤ 7
      · exact ⟨p, q, 1, hs, by norm_num,
          ⟨(matrixOne _).symm⟩⟩
      · obtain ⟨p₁, q₁, j, hlt, hj, ⟨e⟩⟩ := reduces_one p q (by omega)
        obtain ⟨p', q', k, hsmall, hk, ⟨f⟩⟩ := ih p₁ q₁ (by omega)
        exact ⟨p', q', j * k, hsmall, Nat.mul_pos hj hk,
          ⟨(e.trans (AlgEquiv.mapMatrix f)).trans (matrixFlatten _ j k)⟩⟩

/-- **EVERY REAL CLIFFORD ALGEBRA IS A MATRIX ALGEBRA OVER A SMALL ONE.** For every `p` and `q`
there are `p'`, `q'` with `p' + q' ≤ 7` and a `k > 0` with
`Cl(p, q) ≃ₐ[ℝ] M_k(Cl(p', q'))`.

Quantified over all `p` and `q`, with no bound, and **without naming the base cases** — which is
`ASSUMPTIONS 49`'s decision and is not taken here. `reach_closure.py` names them, over
`p + q ≤ 80`, in Python. -/
theorem clifford_reduces_to_small (p q : ℕ) :
    ∃ p' q' k : ℕ, p' + q' ≤ 7 ∧ 0 < k ∧
      Nonempty (CliffordAlgebra (sigForm p q) ≃ₐ[ℝ]
        Matrix (Fin k) (Fin k) (CliffordAlgebra (sigForm p' q'))) :=
  reduces_aux (p + q) p q le_rfl

end

end CliffordReduction
