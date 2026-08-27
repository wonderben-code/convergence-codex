import LovelockReflectionFour
import LovelockReduction

/-!
# The first statement this estate makes about `T` on a Weyl tensor

Every file in this group has ended with the same disclaimer — *"nothing here says what an
equivariant `T` does to the Weyl summand"* — and it has been true every time. **This one says
something.** It is small, and it is stated here rather than buried because the sentence it retires
has been repeated in nine headers.

## The two pieces, both already in the estate

`LovelockReflections.diagonal_of_reflection_invariant` says that if `R` is fixed by every
coordinate reflection then `T R` is **diagonal** — equivariance turns the reflection's sign into an
equation `x = −x` at every off-diagonal entry. That has been available since 15 August and had no
input to feed it: the tensors known to be reflection-invariant were `constCurv` and the diagonal
Kulkarni–Nomizu family, all of which have non-zero Ricci and say nothing about Weyl.

`LovelockReflectionFour.exists_ricciFlat_reflect_invariant` is the missing input, proved earlier the
same day: at every `n ≥ 4` there is a **non-zero, Ricci-flat — hence entirely Weyl —
reflection-invariant** algebraic curvature tensor.

## What is proved

**`exists_weyl_T_diagonal`** — for every additive, homogeneous, equivariant `T` and every `n ≥ 4`
there is a non-zero Ricci-flat algebraic curvature tensor `W` with **`T W` diagonal**.

## What it is not, and the arithmetic of how far it is from `KillsWeyl`

**It is not progress on `KillsWeyl` and the watchlist item does not move.** `KillsWeyl` asks `T W`
to be **zero**; this says it is **diagonal**. On `Fin n` that is `n` numbers instead of `n²`, and
`n` is not `0`.

**What would cut it further, and is not done.** The witness is invariant under the permutations
fixing `{i, j}` and changes sign under the transposition `(i j)`, so permutation equivariance —
`LovelockPermutations` — should force `T W = diag(p, p, q, …, q)` with `p` at `i` and `j`: **two
numbers.** And `∑_{i<j} knSquare (twoProj i j) = constCurv`, whose Weyl part is zero, should give
one linear relation between `p` and `q`: **one number.** Neither is proved here, both are hand
sketches, and by this project's vocabulary a hand sketch is a guess.

**⚠ SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`).** *"the watchlist item does not
move"* was true when written and is now false — `LovelockKillsWeyl.killsWeyl_of_equivariant`
proves `KillsWeyl` at every `n ≥ 3`, by a route that needs no witness at all. **What still
stands**: that THIS file is not that proof, that its two sketches were never carried out, and
that a hand sketch is a guess. The route that landed did not use either sketch, so neither was
tested (`ERRATUM 302`).

**And even at one number it would not be `KillsWeyl`**, which quantifies over every algebraic
curvature tensor, not over one witness. The orbit of a single Weyl tensor is not known to span the
Weyl summand — that is the irreducibility question `WALLS` §W5.0 §5b names, and nothing here
approaches it.

**It also settles the antisymmetric half of `LovelockDiagonalReduction.killsWeyl_iff_two_halves` at
this witness, and only there:** a diagonal 2-tensor is symmetric, so `T W`'s antisymmetric part is
zero. One witness is not the statement.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWeylWitness

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections
  LovelockReflectionFour LovelockReduction Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **THE FIRST STATEMENT THIS ESTATE MAKES ABOUT `T` ON A WEYL TENSOR.** -/
theorem exists_weyl_T_diagonal
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (hn : 4 ≤ n) :
    ∃ W : Fin n → Fin n → Fin n → Fin n → ℝ,
      IsAlgCurv W ∧ (∀ b c, ricci W b c = 0) ∧ W ≠ (fun _ _ _ _ => (0 : ℝ))
        ∧ ∀ b c, b ≠ c → T W b c = 0 := by
  obtain ⟨W, hW, hflat, hne, hfix⟩ :
      ∃ W : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv W
        ∧ (∀ b c, ricci W b c = 0) ∧ W ≠ (fun _ _ _ _ => (0 : ℝ))
        ∧ ∀ m a b c d, act (reflect m) W a b c d = W a b c d := by
    obtain ⟨W, h1, h2, h3, h4⟩ := exists_ricciFlat_reflect_invariant hn
    exact ⟨W, h1, h3, h4, h2⟩
  refine ⟨W, hW, hflat, hne, fun b c hbc => ?_⟩
  refine diagonal_of_reflection_invariant hequiv hW ?_ hbc
  intro k
  exact funext fun a => funext fun b' => funext fun c' => funext fun d' => hfix k a b' c' d'

end LovelockWeylWitness
