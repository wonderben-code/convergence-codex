import LovelockFrameInverse
import WeylVanishesThree
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The refusal, discharged: `RicciProportional` proved, and Lovelock's classification at `n = 3`

`RicciProportional` was assessed and refused earlier in this campaign as *"needs Mathlib's spectral
theorem bridged to `IsOrth` plus a permutation-equivariance argument on diagonal traceless tensors,
substantial with uncertain plumbing"*. Five files later the permutation half is done and
`LovelockFrameInverse` reduced everything else to one named `Prop`:

    Diagonalisable n : ∀ S symmetric, ∃ Q, IsOrth Q ∧ act2 Q S is diagonal

**This file proves it, and the refusal's own words were the recipe.** The bridge is four short
lemmas, and Mathlib supplies the theorem in exactly the shape that is wanted.

## What is proved

* `act2_eq_conj` — **`act2` is matrix conjugation.** `act2 Q S = Q · S · Qᵀ`, entry by entry. This
  is the whole bridge between this estate's index notation and Mathlib's matrix algebra;
* `isHermitian_of_symm` — a symmetric real array is a Hermitian matrix, `star` on `ℝ` being
  trivial;
* **`mem_orthogonalGroup_of_isOrth`** — the converse of `AlgebraicCurvature`'s bridge, which the
  estate had never proved. It decides whether `hequiv` is the honest hypothesis: without it,
  nothing ruled out `IsOrth` admitting matrices *outside* `O(n)`, which would make `hequiv`
  stronger than `O(n)`-equivariance and every classification here weaker than it reads as. The two
  are equivalent;
* **`diagonalisable`** — `Diagonalisable n`, for every `n`. From
  `Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`, which says outright that conjugating
  by `star (eigenvectorUnitary)` gives a `Matrix.diagonal`. Orthogonality of that frame is
  `Unitary.coe_star_mul_self` through `AlgebraicCurvature.isOrth_of_mem_orthogonalGroup`, the
  bridge that has existed since the file was written and was never the difficulty;
* **`ricciProportional`** — `LovelockReduction.RicciProportional T α` **outright**, for
  `α = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀`. The second of the two `Prop`s the classification rested on
  is no longer open;
* **`classification_three`** — and therefore, with `WeylVanishesThree.killsWeyl_three` supplying
  the other `Prop` for free, **the Lovelock classification in dimension three, unconditionally**:
  an additive, homogeneous, equivariant `T` is `α · ricci + β · scal · δ`.

## What this does NOT do, and the watchlist item does not move

**`KillsWeyl` at `n ≥ 4` is untouched**, and it is the harder of the two — the statement that the
Weyl summand contains no copy of the symmetric-2-tensor representation, which is where the missing
invariant theory lives. `n = 3` falls out only because `WeylVanishesThree` shows the Weyl summand
is *identically zero* there, which is a fact about three dimensions and not a method. **The
watchlist item asks for `n ≥ 3` and names `n = 4` as the physically relevant case, so it stays
open.**

**Nor is `n = 3` a second `n = 2`.** `LovelockReduction.ricciProportional_two_of_zero` records that
at `n = 2` the statement is *vacuous*, the traceless Ricci tensor being identically zero there. At
`n = 3` it is not: `AlgebraicCurvature.ricci_not_smul_delta` needs exactly `3 ≤ n`, and §4 below
exhibits `ricci` itself as a non-zero map satisfying all three hypotheses — the §3 standard, so
that the theorem is not about a class whose only evident member is the zero map.

**Two consistency checks, labelled as checks and used by nothing.** §4 computes the
classification's constants at `T = ricci`: `α` must be `1`, and the `scal · δ` coefficient must then
vanish. Both do. They are here because an index slip anywhere in the five-file assembly would have
produced some other number and nothing else would have complained.

**And the composition law is still not proved.** `LovelockFrameInverse` proved the one instance
`Qᵀ · Q = 1` on 2-tensors; `AlgebraicCurvature`'s statement that `act (Q · Qʹ) = act Q ∘ act Qʹ` is
not established stands unchanged, and nothing here needs it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockDiagonalise

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockDiagonalWitness
  LovelockDiagonalSum LovelockFrameInverse LovelockReduction Matrix Finset

variable {n : ℕ}

/-! ## 1. The bridge to Mathlib's matrices

Three lemmas, and the first is the only one with content: the estate's `act2` is conjugation.
-/

/-- **`act2` IS MATRIX CONJUGATION.** -/
theorem act2_eq_conj (Q S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 Q S b c = (Matrix.of Q * Matrix.of S * (Matrix.of Q)ᵀ) b c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, act2, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c' _ => by ring

/-- Over `ℝ` the star is trivial, so transposing the adjoint gives the matrix back. -/
theorem star_transpose_real (U : Matrix (Fin n) (Fin n) ℝ) : (star U)ᵀ = U := by
  funext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.transpose_apply]

/-- A symmetric real array is a Hermitian matrix. -/
theorem isHermitian_of_symm {S : Fin n → Fin n → ℝ} (hs : ∀ x y, S x y = S y x) :
    (Matrix.of S).IsHermitian := by
  have h : (Matrix.of S)ᴴ = Matrix.of S := by
    funext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact hs j i
  exact h

/-- **AND THE CONVERSE OF THE ESTATE'S BRIDGE**, which decides whether `hequiv` is the honest
hypothesis. `AlgebraicCurvature` proves `mem_orthogonalGroup → IsOrth` and never the other
direction, so until now nothing ruled out `IsOrth` admitting matrices outside `O(n)` — which would
have made `hequiv` a *stronger* assumption than `O(n)`-equivariance and the classification a weaker
theorem than it reads as. It does not: the two are equivalent, and `hequiv` is exactly
`O(n)`-equivariance. -/
theorem mem_orthogonalGroup_of_isOrth {Q : Fin n → Fin n → ℝ} (hQ : IsOrth Q) :
    Matrix.of Q ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [hQ.rows x y]
  simp [delta]

/-! ## 2. Step 3, discharged

`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary` says that conjugating a Hermitian
matrix by `star (eigenvectorUnitary)` produces a `Matrix.diagonal`. That is `Diagonalisable`'s
conclusion once `act2` is recognised as conjugation and the unitary is recognised as orthogonal.
-/

/-- **THE REFUSAL, DISCHARGED.** Every symmetric 2-tensor is diagonal in some orthogonal frame. -/
theorem diagonalisable (n : ℕ) : Diagonalisable n := by
  classical
  intro S hs
  have hH : (Matrix.of S).IsHermitian := isHermitian_of_symm hs
  have key := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at key
  have horth : (star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))
      ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, star_transpose_real]
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  refine ⟨fun a b => (star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) a b,
    isOrth_of_mem_orthogonalGroup horth, ?_⟩
  intro b c hbc
  rw [act2_eq_conj]
  have hof : (Matrix.of fun a b => (star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) a b)
      = star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [hof, star_transpose_real, key, Matrix.diagonal_apply_ne _ hbc]

/-! ## 3. And therefore `RicciProportional`, and the classification at `n = 3` -/

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **THE SECOND OF `LovelockReduction`'s TWO OPEN `Prop`s, PROVED.** -/
theorem ricciProportional (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) :
    RicciProportional T (T (ricciSeed (hIJ i₀ j₀)) i₀ i₀) :=
  ricciProportional_of_diagonalisable hn2 hadd hsmul hequiv hij₀ (diagonalisable n)

/-- **LOVELOCK'S CLASSIFICATION IN DIMENSION THREE, UNCONDITIONALLY.** `WeylVanishesThree` makes
`KillsWeyl` free at `n = 3`; §2 makes `RicciProportional` free at every `n ≥ 3`; and
`LovelockReduction` said the two are jointly sufficient. -/
theorem classification_three
    {T : (Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ} (i : Fin 3)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ} (hR : IsAlgCurv R) (b c : Fin 3) :
    T R b c
      = T (ricciSeed (hIJ (0 : Fin 3) 1)) 0 0 * ricci R b c
        + (T (constCurv 3) i i / ((3 : ℝ) * ((3 : ℝ) - 1))
            - T (ricciSeed (hIJ (0 : Fin 3) 1)) 0 0 / (3 : ℝ)) * scal R * delta b c :=
  WeylVanishesThree.classification_three_of_ricciProportional i hadd hsmul hequiv
    (ricciProportional (by norm_num) hadd hsmul hequiv (by decide)) hR b c

/-! ## 4. The §3 standard: the hypotheses have a non-zero member

`AlgebraicCurvature` §15 exhibits `ricci` as a witness for the two-dimensional theorem, on the
ground that a classification satisfied only by the zero map is a theorem about nothing. The same
check at `n = 3`, and the same witness.
-/

/-- `ricci` is additive. -/
theorem ricci_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ricci (fun a b c d => R a b c d + S a b c d) = fun b c => ricci R b c + ricci S b c := by
  funext b c
  simp only [ricci]
  exact Finset.sum_add_distrib

/-- **A CONSISTENCY CHECK, LABELLED AS ONE.** The classification's constant `α` is
`T (ricciSeed (hIJ 0 1)) 0 0`; at `T = ricci` it must come out as `1`, since the seed inverts
`tracefreeRicci`. It does. Nothing downstream uses this — it is here because an index slip in the
five-file assembly would have shown up as any other number. -/
theorem ricci_ricciSeed_hIJ_three : ricci (ricciSeed (hIJ (0 : Fin 3) 1)) 0 0 = 1 := by
  rw [ricci_ricciSeed, hIJ_trace (by decide : (0 : Fin 3) ≠ 1), hIJ_at_i, delta_self]
  norm_num

/-- **AND THE SECOND CONSTANT MUST THEN VANISH AT `T = ricci`**, because `ricci R = 1 · ricci R`
leaves no room for a `scal R · δ` term. `ricci (constCurv 3) i i = 2` and `2/6 − 1/3 = 0`, so it
does. The second half of the same check. -/
theorem beta_ricci_three (i : Fin 3) :
    ricci (constCurv 3) i i / ((3 : ℝ) * ((3 : ℝ) - 1)) - (1 : ℝ) / (3 : ℝ) = 0 := by
  rw [ricci_constCurv, delta_self]
  norm_num

/-- **`ricci` MEETS ALL THREE HYPOTHESES AT `n = 3`, AND IS NOT THE ZERO MAP.** -/
theorem ricci_witness_three :
    (∀ R S : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ,
        ricci (fun a b c d => R a b c d + S a b c d) = fun b c => ricci R b c + ricci S b c)
      ∧ (∀ (lam : ℝ) (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ),
          ricci (fun a b c d => lam * R a b c d) = fun b c => lam * ricci R b c)
      ∧ (∀ Q, IsOrth Q → ∀ R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ, IsAlgCurv R →
          ∀ b c, ricci (act Q R) b c = act2 Q (ricci R) b c)
      ∧ ricci (constCurv 3) 0 0 ≠ 0 := by
  refine ⟨ricci_add, fun lam R => funext fun b => funext fun c => ricci_smul lam R b c,
    fun Q hQ R _ b c => ricci_act hQ R b c, ?_⟩
  rw [ricci_constCurv]
  norm_num [delta]

end LovelockDiagonalise
