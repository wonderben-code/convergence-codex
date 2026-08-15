import WeylNonzeroGeneral

/-!
# `WeylVanishesThree`'s dimension hypothesis is not an artefact — it is sharp

`WeylVanishesThree` rests on one lemma:

> **`eq_zero_of_ricci_eq_zero`** — a curvature tensor on `Fin 3` with vanishing Ricci trace is
> zero.

Everything else in that file, and with it the three-dimensional Lovelock classification, follows
from it: the Weyl summand is Ricci-flat by `ricci_weylPart`, so at `n = 3` it is *zero*, so
`KillsWeyl` is free, so the classification holds.

**The `Fin 3` in that statement has been a `variable` line, and nothing said whether it was
load-bearing.** A dimension restriction can be an artefact of a proof — a case analysis that
happened to be written at one size — or it can be the mathematics. Nothing in the estate
distinguished the two here, and the difference decides whether looking for the `n ≥ 4` version is
worth an afternoon.

**It is the mathematics.** This file shows the lemma **fails at every `n ≥ 4`**, by exhibiting a
Ricci-flat algebraic curvature tensor that is not zero.

## What is proved

* **`exists_ricciFlat_ne_zero`** — for `4 ≤ n` there is an `R` with `IsAlgCurv R`, `ricci R = 0`
  and `R ≠ 0`;
* **`not_eq_zero_of_ricci_eq_zero`** — the same as an explicit refutation: the statement
  `eq_zero_of_ricci_eq_zero` makes at `n = 3` is **false** at every `n ≥ 4`.

The witness costs nothing new. `WeylNonzeroGeneral` already built `knSquare (twoProj i j)` and
computed one entry of its Weyl summand as `(n − 3)/(n − 1)`; the Weyl summand of *any* algebraic
curvature tensor is Ricci-flat (`ricci_weylPart`) and is itself an algebraic curvature tensor
(`isAlgCurv_weylPart`). So the witness is that Weyl summand, and the three facts are three
citations.

## What this changes, and what it does not

**It closes a question rather than opening one.** Nobody should now spend time looking for
`eq_zero_of_ricci_eq_zero` at `n ≥ 4`: it is false there, and the counterexample is explicit.

**It does not bear on `KillsWeyl`.** That statement is about what an equivariant `T` does to the
Weyl summand, not about whether the summand vanishes. This file says the summand does not vanish
and the three-dimensional shortcut therefore does not generalise — which `WeylNonzeroGeneral`
already said. What is new is the *contrapositive reading*: the shortcut fails because the lemma
under it fails, and now that is a theorem rather than an inference.

**And it is not a claim about the Lovelock classification at `n ≥ 4`.** The classification may
still be true there; what is false there is one lemma that would have proved it cheaply.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RicciFlatSharp

open AlgebraicCurvature LovelockProjections WeylNonzeroGeneral Finset

variable {n : ℕ}

/-- **A RICCI-FLAT ALGEBRAIC CURVATURE TENSOR THAT IS NOT ZERO**, in every dimension from four
up. The Weyl summand of the plane projector's square: an algebraic curvature tensor by
`isAlgCurv_weylPart`, Ricci-flat by `ricci_weylPart`, and non-zero by
`WeylNonzeroGeneral.weylPart_ne_zero_of_four_le`. -/
theorem exists_ricciFlat_ne_zero (hn : 4 ≤ n) :
    ∃ R : Fin n → Fin n → Fin n → Fin n → ℝ,
      IsAlgCurv R ∧ (∀ b c, ricci R b c = 0) ∧ R ≠ fun _ _ _ _ => (0 : ℝ) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (2 : ℕ) ≤ n := by omega
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  refine ⟨weylPart (knSquare (twoProj ⟨0, by omega⟩ ⟨1, by omega⟩)),
    isAlgCurv_weylPart (isAlgCurv_twoProjCurv _ _),
    fun b c => ricci_weylPart hn1 hn2 _ b c, weylPart_ne_zero_of_four_le hn hij⟩

/-- **SO `WeylVanishesThree.eq_zero_of_ricci_eq_zero` IS FALSE AT EVERY `n ≥ 4`.** The `Fin 3` in
its statement is the mathematics and not an artefact of how the proof was written. -/
theorem not_eq_zero_of_ricci_eq_zero (hn : 4 ≤ n) :
    ¬ ∀ R : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv R → (∀ b c, ricci R b c = 0) →
        ∀ a b c d : Fin n, R a b c d = 0 := by
  intro h
  obtain ⟨R, hR, hflat, hne⟩ := exists_ricciFlat_ne_zero hn
  exact hne (funext fun a => funext fun b => funext fun c => funext fun d => h R hR hflat a b c d)

end RicciFlatSharp
