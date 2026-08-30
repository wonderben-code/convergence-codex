import LovelockDiagonalise

/-!
# One `Prop` left, and it is not merely sufficient — it is the problem

`LovelockReduction` split the classification into two open statements, `KillsWeyl` and
`RicciProportional`, and proved them **jointly sufficient**. `LovelockDiagonalise` proved the
second. This file draws the two consequences.

**⚠ THE PARAGRAPH ABOVE, AND THIS FILE'S TITLE, DESCRIBE A STATE OF THE WORLD THAT ENDED THE NEXT
DAY. KEPT VERBATIM PER `ERRATUM 94`; `ERRATUM 351` RECORDS IT.** This file landed 2026-08-15;
**`LovelockKillsWeyl.killsWeyl_of_equivariant` (`171d474`, 2026-08-16) proves `KillsWeyl`** for
every additive, homogeneous, `O(n)`-equivariant `T` at every `n ≥ 3`. Four other files carry a
`⚠ SUPERSEDED` note saying so and this one did not, for a fortnight — the file whose *title* is a
claim about that `Prop`.

**NOTHING BELOW IS WRONG AS MATHEMATICS.** `classified_of_killsWeyl`, `killsWeyl_of_classified`
and `killsWeyl_iff` are exactly right and unchanged. What changed is that the `Prop` they are
about is no longer open, so *"one `Prop` left"* is now a statement about 15 August.

**AND THE COMPOSITION NOBODY WROTE IS NOW WRITTEN.** `classified_of_killsWeyl`'s `hW : KillsWeyl T`
follows from its own `hadd`, `hsmul`, `hequiv` together with `3 ≤ n`, so it is **derivable rather
than assumed**: `LovelockClassified.classified_of_equivariant` is the classification with no
`KillsWeyl` hypothesis at all.

## What is proved

* **`classified_of_killsWeyl`** — the classification follows from `KillsWeyl` **alone**, at every
  `n` with `(n:ℝ) − 2 ≠ 0` and two distinct indices to hand. One hypothesis where the reduction
  needed two;
* **`killsWeyl_of_classified`** — and conversely. If `T` is `α · ricci + β · scal · δ` then it
  kills the Weyl summand, because `ricci_weylPart` and `scal_weylPart` say both terms vanish
  there;
* **`killsWeyl_iff`** — so `KillsWeyl T` **is equivalent to** the classification holding for some
  pair of constants.

## Why the converse is the point

A sufficient condition can be a detour: one can imagine proving the classification some other way
and never touching `KillsWeyl`. **The equivalence says there is no other way.** Any route to the
classification proves `KillsWeyl` en route, and any failure of `KillsWeyl` is a failure of the
classification. The estate's remaining Lovelock gap is therefore **exactly one statement**, not a
convenient sufficient condition chosen because it looked tractable.

It also sharpens what `WeylNonzeroFour` bought — **and the sharpening is narrower than the first
draft of this paragraph said.** That file showed the Weyl summand is not identically zero at
`n = 4`, so the route by which `n = 3` came free — the subject of `KillsWeyl` vanishing — is
unavailable there, and by the equivalence the classification cannot be had that way either.
**Neither statement says the classification is false at `n = 4`, or hard**; both say only that the
three-dimensional argument does not reach it. A draft here wrote *"the classification is not
automatic there either"*, which reads as a claim about the classification's difficulty and is not
one that has been proved.

## What this is NOT

**It is not progress on `KillsWeyl`.** Nothing here attempts it, and the missing invariant theory
— that the Weyl summand contains no copy of the symmetric-2-tensor representation of `O(n)` — is
exactly as absent as before. **The watchlist item does not move.**

**And the equivalence is not a reduction of difficulty in either direction.** It is a statement
that two open problems are one problem. That is worth knowing precisely because it forecloses
looking for a way around, which is otherwise a natural thing to try.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockOneProp

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockDiagonalWitness
  LovelockDiagonalise LovelockReduction Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **THE CONCLUSION THE CLASSIFICATION ASKS FOR**, named so it can appear on both sides of an
`Iff`. `WALLS` §W5.0 item 4's *"spanned by `R ↦ ricci R` and `R ↦ scal R · δ`"*, with the
coefficients made explicit. -/
def Classified (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ) (α β : ℝ) : Prop :=
  ∀ R, IsAlgCurv R → ∀ b c, T R b c = α * ricci R b c + β * scal R * delta b c

/-! ## 1. One hypothesis where the reduction needed two -/

/-- **THE CLASSIFICATION FROM `KillsWeyl` ALONE.** -/
theorem classified_of_killsWeyl (hn2 : (n : ℝ) - 2 ≠ 0) (i : Fin n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) (hW : KillsWeyl T) :
    Classified T (T (ricciSeed (hIJ i₀ j₀)) i₀ i₀)
      (T (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
        - T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ / (n : ℝ)) := fun _ hR b c =>
  classification_of_killsWeyl_of_ricciProportional i hadd hsmul hequiv hW
    (ricciProportional hn2 hadd hsmul hequiv hij₀) hR b c

/-! ## 2. And the converse, which is what makes it the problem rather than a route to it -/

/-- **A CLASSIFIED `T` KILLS THE WEYL SUMMAND**, because both terms of the classification vanish
on it: `ricci_weylPart` and `scal_weylPart`. No equivariance and no additivity are used — this
direction is arithmetic. -/
theorem killsWeyl_of_classified (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {α β : ℝ} (hC : Classified T α β) : KillsWeyl T := by
  intro R hR b c
  rw [hC (weylPart R) (isAlgCurv_weylPart hR) b c, ricci_weylPart hn1 hn2 R b c,
    scal_weylPart hn1 hn2 R]
  ring

/-- **SO THE LAST OPEN `Prop` IS THE PROBLEM, NOT A ROUTE TO IT.** -/
theorem killsWeyl_iff (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0) (i : Fin n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) :
    KillsWeyl T ↔ ∃ α β : ℝ, Classified T α β :=
  ⟨fun hW => ⟨_, _, classified_of_killsWeyl hn2 i hadd hsmul hequiv hij₀ hW⟩,
    fun ⟨_, _, hC⟩ => killsWeyl_of_classified hn1 hn2 hC⟩

end LovelockOneProp
