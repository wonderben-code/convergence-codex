import RealDivisionQuaternionCase
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# What Frobenius unlocks: finite-dimensional simple real algebras are `Mₙ(ℝ)`, `Mₙ(ℂ)` or `Mₙ(ℍ)`

`PROOF_STRATEGY` §6 question 1 asks, after every unit, *what did this just unlock*. The answer for
`RealDivisionQuaternionCase` is this file, and it is one step long.

**Mathlib already has Wedderburn–Artin** — `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`
says a finite-dimensional simple algebra is `Mₙ(D)` for **some** division algebra `D`, and
`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` says a semisimple one is a finite
product of such. **What it does not say is which `D`.** Over `ℝ` that is exactly Frobenius's
theorem, which this estate proved in the unit before this one, and the two compose without an
argument in between.

> **§1. Artinian, from finite-dimensional.** `isArtinianRing_of_finite` — `IsArtinianRing.of_finite`
> at `ℝ`, which is Artinian as a division ring. Mathlib does not make this an instance, so
> Wedderburn's hypothesis has to be supplied by hand and is supplied once here.
>
> **§2. The simple case.** `exists_matrix_over_three` — a finite-dimensional simple `ℝ`-algebra is
> `Mₙ(ℝ)`, `Mₙ(ℂ)` or `Mₙ(ℍ)`, with `n ≠ 0`. Wedderburn gives `Mₙ(D)`, `frobenius` identifies `D`,
> and `AlgEquiv.mapMatrix` carries the identification into the entries.
>
> **§3. The semisimple case.** `exists_pi_matrix_over_three` — a finite direct product of those.
> **It is stated with the division algebras still named** rather than through a three-valued
> dispatch type, and that is deliberate: building `Fin 3 → Type` and matching on it is the shape
> `ASSUMPTIONS 49` records as an **author's presentation decision**, and the standing orders say a
> decision belonging to the author is not made in passing. The statement here says the same thing
> without making it.

**WHAT THIS IS.** The structure theorem for finite-dimensional real algebras, in the shape the
`UNLOCK_WATCHLIST`'s Clifford item names its target — *`M_N(K)` or `M_N(K) × M_N(K)` with `K` one of
`ℝ`, `ℂ`, `ℍ`*. **Nothing in this estate used or implied Artin–Wedderburn before today**;
`CentralIdemInvariant`'s header says so in as many words, and `F1_6` and `F1_7` cite it in prose
without a statement.

**WHAT THIS IS NOT** (`ERRATUM 60`). **It does not classify Clifford algebras.** Getting
`Cl(p,q;ℝ)` from here needs that algebra to be shown simple or semisimple and its dimension pinned,
and **neither is done here, attempted here, or costed** (`ERRATUM 194`, `ERRATUM 246`). It does not
identify `n` or `K` for any particular algebra: it says the answer has that shape, not what the
answer is. And it is not an independent proof of Wedderburn–Artin — that half is Mathlib's, cited
and used, and only the identification of `D` is this estate's. **No published tag moves and nothing
in the earlier files is restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealSimpleAlgebra

open Quaternion

universe u

/-! ### §1. Finite-dimensional over `ℝ` implies Artinian -/

/-- Wedderburn's Artinian hypothesis, supplied from finite-dimensionality. Mathlib has the
implication as a theorem and not an instance, so it is named once here. -/
theorem isArtinianRing_of_finite (A : Type*) [Ring A] [Algebra ℝ A] [Module.Finite ℝ A] :
    IsArtinianRing A :=
  IsArtinianRing.of_finite ℝ A

/-! ### §2. The simple case -/

/-- **THE STRUCTURE THEOREM.** A finite-dimensional simple real algebra is a matrix algebra over
`ℝ`, over `ℂ`, or over `ℍ`. Wedderburn–Artin is Mathlib's; the identification of the division
algebra is `RealDivisionQuaternionCase.frobenius`. -/
theorem exists_matrix_over_three (A : Type*) [Ring A] [Algebra ℝ A] [IsSimpleRing A]
    [Module.Finite ℝ A] :
    ∃ n : ℕ, n ≠ 0 ∧
      (Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) ∨
        Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) ∨
        Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ])) := by
  haveI := isArtinianRing_of_finite A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite ℝ A
  refine ⟨n, hn.out, ?_⟩
  rcases RealDivisionQuaternionCase.frobenius (D := D) with f | f | f
  · exact Or.inl (f.map fun g => e.trans g.symm.mapMatrix)
  · exact Or.inr (Or.inl (f.map fun g => e.trans g.symm.mapMatrix))
  · exact Or.inr (Or.inr (f.map fun g => e.trans g.symm.mapMatrix))

/-! ### §3. The semisimple case -/

/-- **The semisimple form.** A finite direct product of matrix algebras, each over a division
algebra that is one of the three.

**The division algebras are left named rather than dispatched through a `Fin 3 → Type`**, because
building that dispatch is the presentation choice `ASSUMPTIONS 49` records as the author's, and the
standing orders say such a decision is not made in passing. -/
theorem exists_pi_matrix_over_three (A : Type u) [Ring A] [Algebra ℝ A] [IsSemisimpleRing A]
    [Module.Finite ℝ A] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra ℝ (D i)),
      (∀ i, Nonempty (ℝ ≃ₐ[ℝ] D i) ∨ Nonempty (ℂ ≃ₐ[ℝ] D i) ∨ Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D i)) ∧
      Nonempty (A ≃ₐ[ℝ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  obtain ⟨n, D, d, hD, hA, hfin, -, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℝ A
  exact ⟨n, D, d, hD, hA, fun i => RealDivisionQuaternionCase.frobenius (D := D i), ⟨e⟩⟩

end RealSimpleAlgebra
