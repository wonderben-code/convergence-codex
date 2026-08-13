import LovelockEquivariance

/-!
# What is left of Lovelock, written as two named statements

The `UNLOCK_WATCHLIST` item predicted two things from the hand route:

> LIKELY OUTCOME: **the projections and their orthogonality, plus a statement of the classification
> that is still open** — that is, the same split `n = 2` already went through, with the easy half
> landing and the exhaustion half remaining.

`LovelockProjections` and `LovelockEquivariance` delivered the first. **This is the second, and it
is the part that makes the remaining wall checkable instead of merely described.** Nothing here
closes anything; what it does is replace *"the exhaustion half is open"* — a sentence — with two
`Prop`s that a future unit can attempt one at a time, and a theorem saying they are jointly
sufficient.

## The reduction

`classification_of_killsWeyl_of_ricciProportional`: let `T` be additive and homogeneous on
four-index arrays and equivariant on algebraic curvature tensors. If

* **`KillsWeyl T`** — `T` vanishes on the Weyl part of every algebraic curvature tensor; and
* **`RicciProportional T α`** — `T` is `α` times the identity on the traceless-Ricci part,

then for every algebraic curvature tensor `R`,

    T R  =  α · ricci R  +  β · scal R · δ ,      β = T(constCurv)ᵢᵢ/(n(n−1)) − α/n

which is exactly *"`T` lies in the span of `R ↦ ricci R` and `R ↦ scal R · δ`"* — the conclusion
`WALLS` §W5.0 item 4 asks for, and the conclusion `AlgebraicCurvature.lovelock_two` reaches in
dimension two by a route that does not survive.

**The third piece needs no hypothesis at all**, and that is the one genuinely load-bearing thing
the previous two units bought: `scalPart_eq` computes `T` on the scalar piece outright, from
`AlgebraicCurvature.equivariant_constCurv` — which holds *at every `n`* — plus homogeneity. So of
the three summands, one is already pinned and two are the open questions.

## What this is and is not

**It is a reduction, not a proof.** `KillsWeyl` and `RicciProportional` are exactly as unproven as
the classification was; the content is that they are *two* statements rather than one, that they
concern disjoint pieces of the decomposition, and that the third piece needs neither of them.
Anyone tempted to read this as progress on Lovelock should note that a reduction to two open
statements is not a proof of either.

**Neither is stated as a theorem here, deliberately.** They are `def`s of `Prop`s, taken as
hypotheses. Writing them as `theorem … := sorry` would put a `sorry` in the estate for a statement
nobody is currently attempting, which this project does not do.

**And the reduction does not say the two statements are independent, or that either is true.** In
particular `KillsWeyl` is the harder of the two and is where the missing invariant theory lives: it
says the Weyl summand contains no copy of the symmetric-2-tensor representation, and proving that
is what needs the decomposition into irreducibles over `ℝ` that `UNLOCK_WATCHLIST` records as
blocked on compactness of `O(n)` with Haar averaging.

**AND THE REDUCTION DOES NOT NEED `n ≥ 3`, WHICH SURPRISED ME AND IS WORTH THE SENTENCE.** A draft
of this paragraph said `n ≥ 3` was inherited throughout, in the three forms `(n:ℝ) ≠ 0`,
`(n:ℝ) − 1 ≠ 0`, `(n:ℝ) − 2 ≠ 0`. **The file carries only the first.** The reason is structural
rather than lucky: `(n:ℝ) − 2 ≠ 0` is spent in `LovelockProjections` by `ricci_ricciPart`, which
computes the trace of the Ricci summand — and this file never computes it, because
`RicciProportional` supplies it as a hypothesis. `(n:ℝ) − 1 ≠ 0` never surfaces because the factor
`n(n−1)` appears identically on both sides of `scalPart_eq` and cancels. So the reduction is
stated at every dimension; it is the *projections it reduces to* that need three or more. Corrected
before commit by reading the signatures rather than the intention.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockReduction

open AlgebraicCurvature LovelockProjections LovelockEquivariance Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The two statements that remain -/

/-- **THE FIRST OPEN STATEMENT.** `T` annihilates the Weyl summand. This is the harder half and is
where the missing invariant theory sits. -/
def KillsWeyl (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ) : Prop :=
  ∀ R, IsAlgCurv R → ∀ b c, T (weylPart R) b c = 0

/-- **THE SECOND OPEN STATEMENT.** On the traceless-Ricci summand, `T` is a fixed multiple of the
identity. -/
def RicciProportional (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (α : ℝ) : Prop :=
  ∀ R, IsAlgCurv R → ∀ b c, T (ricciPart R) b c = α * tracefreeRicci R b c

/-! ## 2. The third summand needs neither, and this is what the previous two units bought

`equivariant_constCurv` pins an equivariant `T` to a multiple of `δ` on the constant-curvature
direction, **at every `n`** — `AlgebraicCurvature` §14 proves `act_constCurv` in every dimension,
and §15's own commentary names this as the one ingredient of `lovelock_two` that survives past
`n = 2`. Since `scalPart R` is a scalar multiple of that one tensor, homogeneity carries the
conclusion to every `R` at once.
-/

/-- **`T` ON THE SCALAR PIECE, COMPUTED.** No `KillsWeyl`, no `RicciProportional`, no `n ≥ 3`. -/
theorem scalPart_eq (i : Fin n)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    T (scalPart R) b c
      = scal R / ((n : ℝ) * ((n : ℝ) - 1)) * (T (constCurv n) i i * delta b c) := by
  have hfun : (scalPart R)
      = fun a b c d => (scal R / ((n : ℝ) * ((n : ℝ) - 1))) * constCurv n a b c d := by
    funext a b c d; simp only [scalPart, knSquare_delta]
  rw [hfun, hsmul]
  exact congrArg _ (equivariant_constCurv i hequiv b c)

/-! ## 3. The reduction -/

/-- **THE CLASSIFICATION FOLLOWS FROM THE TWO OPEN STATEMENTS.** -/
theorem classification_of_killsWeyl_of_ricciProportional
    (hn0 : (n : ℝ) ≠ 0) (i : Fin n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (hW : KillsWeyl T) {α : ℝ} (hRic : RicciProportional T α)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) (b c : Fin n) :
    T R b c
      = α * ricci R b c
        + (T (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1)) - α / (n : ℝ))
            * scal R * delta b c := by
  -- split `R` into its three pieces and push `T` across the two sums
  have hsplit : R = fun a b c d =>
      weylPart R a b c d + (ricciPart R a b c d + scalPart R a b c d) := by
    funext a b c d; rw [decomposition R a b c d]; ring
  have hstep : T R b c
      = T (weylPart R) b c + (T (ricciPart R) b c + T (scalPart R) b c) := by
    conv_lhs => rw [hsplit]
    rw [hadd (weylPart R) (fun a b c d => ricciPart R a b c d + scalPart R a b c d),
      hadd (ricciPart R) (scalPart R)]
  rw [hstep, hW R hR b c, hRic R hR b c, scalPart_eq i hsmul hequiv R b c, tracefreeRicci]
  field_simp
  ring

/-! ## 4. The two dimensions where this says nothing new, named so the scope is not overread -/

/-- At `n = 2` the second statement is **vacuous** —
`LovelockProjections.tracefreeRicci_eq_zero_two` says the traceless Ricci tensor is zero there —
so the reduction degenerates to `lovelock_two`'s situation and adds nothing to it. Recorded
because a reduction that is trivially satisfiable in a case is not evidence about the general
case. -/
theorem ricciProportional_two_of_zero
    {T : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ}
    (h : ∀ R, IsAlgCurv R → ∀ b c, T (ricciPart R) b c = 0) (α : ℝ) :
    RicciProportional T α := by
  intro R hR b c
  rw [h R hR b c, tracefreeRicci_eq_zero_two hR b c, mul_zero]

end LovelockReduction
