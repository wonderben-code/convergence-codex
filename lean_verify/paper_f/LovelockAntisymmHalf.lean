import LovelockWitnessCount
import LovelockDiagonalReduction

/-!
# The antisymmetric half is the same statement again, and it is already zero on the witness

`LovelockDiagonalReduction` found a step nobody had counted: `KillsWeyl` constrains the
**antisymmetric** part of `T`'s output as much as the symmetric part, and the diagonalisation
argument reaches only the symmetric test tensors. It called the other half *"a different question —
what an equivariant `T` does into the antisymmetric 2-tensors, a representation this estate has
never looked at."*

**It is not a different question.** Splitting `T` itself into halves, rather than splitting the test
tensors, makes each half an equivariant map of the same kind — so every theorem in this group
applies to each half separately. **And on the explicit Weyl witness the antisymmetric half is
identically zero**, so the one free number `LovelockWitnessCount` left lives entirely in the
symmetric part.

## What is proved

* `act2_transpose` — transposing a 2-tensor commutes with the frame change. One `Finset.sum_comm`,
  and it is the only thing the rest of the file needs;
* **`antiHalf`** and `symHalf`, and **`antiHalf_hadd`, `antiHalf_hsmul`, `antiHalf_hequiv`** — the
  antisymmetric half of an additive, homogeneous, equivariant `T` **is itself additive, homogeneous
  and equivariant.** That is the whole point: the second half is an instance of the first problem;
* `antiHalf_antisymm`, `eq_symHalf_add_antiHalf`, and **`killsWeyl_iff_halves`** — `KillsWeyl T`
  is exactly the conjunction of `KillsWeyl` for the two halves;
* **`antiHalf_weyl_witness`** — and on `weylPart (knSquare (twoProj i j))` the antisymmetric half
  **vanishes at every entry**: `LovelockWeylTwoValues.T_weyl_twoProj_diagonal` applies to it, so it
  is diagonal, and a diagonal antisymmetric 2-tensor is zero.

## What this settles and what it does not

**It settles the antisymmetric half at the witness, completely — no free parameter at all.** So the
one number `LovelockWitnessCount` left over is a statement about the **symmetric** part of `T`
alone, and the antisymmetric part contributes nothing to it.

**It does not settle the antisymmetric half in general**, and the reason is the same one that stops
everything else in this group: the witness is one Weyl tensor, and `KillsWeyl` quantifies over all
of them. **What the file removes is the fear that the antisymmetric half was a second, harder
problem needing machinery nobody had.** It is the same problem, and it is at the same wall —
`WALLS` §W5.0 §5b's irreducibility question.

**`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockAntisymmHalf

open AlgebraicCurvature LovelockProjections LovelockEquivariance WeylNonzeroGeneral
  LovelockReduction LovelockWeylTwoValues LovelockDiagonalReduction Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The two halves of `T` -/

/-- The antisymmetric half of `T`. -/
noncomputable def antiHalf (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  (1/2 : ℝ) * (T R b c - T R c b)

noncomputable def symHalf (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  (1/2 : ℝ) * (T R b c + T R c b)

theorem act2_transpose (Q S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 Q (fun x y => S y x) b c = act2 Q S c b := by
  simp only [act2]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c' _ => by ring

/-! ## 2. The antisymmetric half satisfies the same three hypotheses -/

theorem antiHalf_hadd
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    antiHalf T (fun a b c d => R a b c d + S a b c d)
      = fun b c => antiHalf T R b c + antiHalf T S b c := by
  funext b c
  simp only [antiHalf]
  have h1 := congrFun (congrFun (hadd R S) b) c
  have h2 := congrFun (congrFun (hadd R S) c) b
  rw [h1, h2]
  ring

theorem antiHalf_hsmul
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    antiHalf T (fun a b c d => lam * R a b c d) = fun b c => lam * antiHalf T R b c := by
  funext b c
  simp only [antiHalf]
  have h1 := congrFun (congrFun (hsmul lam R) b) c
  have h2 := congrFun (congrFun (hsmul lam R) c) b
  rw [h1, h2]
  ring

theorem antiHalf_hequiv
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (Q : Fin n → Fin n → ℝ) (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hR : IsAlgCurv R) (b c : Fin n) :
    antiHalf T (act Q R) b c = act2 Q (antiHalf T R) b c := by
  have hR2 : act2 Q (antiHalf T R) b c
      = (1/2 : ℝ) * (act2 Q (T R) b c - act2 Q (T R) c b) := by
    have h1 : act2 Q (antiHalf T R) b c
        = (1/2 : ℝ) * (act2 Q (T R) b c - act2 Q (fun x y => T R y x) b c) := by
      simp only [antiHalf, act2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c' _ => by ring
    rw [h1, act2_transpose Q (T R) b c]
  rw [hR2]
  simp only [antiHalf]
  rw [hequiv Q hQ R hR b c, hequiv Q hQ R hR c b]

theorem antiHalf_antisymm (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    antiHalf T R b c = -antiHalf T R c b := by
  simp only [antiHalf]; ring

/-! ## 3. And it is zero on the witness -/

theorem antiHalf_weyl_witness (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c,
      T (act Q R) b c = act2 Q (T R) b c)
    (i j : Fin n) (b c : Fin n) :
    antiHalf T (weylPart (knSquare (twoProj i j))) b c = 0 := by
  by_cases hbc : b = c
  · subst hbc
    have := antiHalf_antisymm (T := T) (weylPart (knSquare (twoProj i j))) b b
    linarith
  · exact T_weyl_twoProj_diagonal
      (fun Q hQ R hR b' c' => antiHalf_hequiv hequiv Q hQ R hR b' c') i j hbc

theorem eq_symHalf_add_antiHalf (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    T R b c = symHalf T R b c + antiHalf T R b c := by
  simp only [symHalf, antiHalf]; ring

theorem killsWeyl_iff_halves :
    KillsWeyl T ↔
      (∀ R, IsAlgCurv R → ∀ b c, symHalf T (weylPart R) b c = 0)
      ∧ (∀ R, IsAlgCurv R → ∀ b c, antiHalf T (weylPart R) b c = 0) := by
  constructor
  · intro hW
    refine ⟨fun R hR b c => ?_, fun R hR b c => ?_⟩
    · simp only [symHalf, hW R hR b c, hW R hR c b]; ring
    · simp only [antiHalf, hW R hR b c, hW R hR c b]; ring
  · rintro ⟨hs, ha⟩ R hR b c
    rw [eq_symHalf_add_antiHalf (T := T) (weylPart R) b c, hs R hR b c, ha R hR b c]
    ring

end LovelockAntisymmHalf
