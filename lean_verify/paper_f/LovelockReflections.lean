import LovelockEquivariance

/-!
# The first rung of `RicciProportional`, which is a reflection and nothing more

`LovelockReduction` left the classification resting on two `Prop`s and named `KillsWeyl` the
harder. `WeylVanishesThree` made `KillsWeyl` free at `n = 3`. **The other one,
`RicciProportional`, was assessed and refused earlier in this campaign** — as *"needs Mathlib's
spectral theorem bridged to `IsOrth` plus a permutation-equivariance argument on diagonal traceless
tensors, substantial with uncertain plumbing"*. `PROOF_STRATEGY` §6's third question asks, of a
refused item, **what is B**. This file is B.

**Why this refusal and not one of the others.** The frontier holds several refused things, and the
most recent of them — tightness for the infinite-volume limit — is refused for a *structural*
reason: the finite-volume measures live on a different space for each volume, so there is nothing
for a tightness argument to be tight in. That refusal is not a sizing judgement and re-examining it
would not be answering §6's question. **`RicciProportional`'s refusal WAS a sizing judgement**, and
this campaign has had one of those turn out to be wrong within a day: `SL2Connected` did in an
afternoon what `LorentzConnectedReduction` had called a Mathlib contribution. That is the reason to
re-open this one and not the other.

## ERRATUM 168: the first draft of this file rebuilt a matrix the estate already had

**The first version defined its own reflection** — `sgnRefl`, `reflMat`, `isOrth_reflMat`,
`act2_reflMat` — and proved it orthogonal and computed its action on a 2-tensor. **All of that
already existed in `AlgebraicCurvature`**, in a file this one imports:

* `AlgebraicCurvature.reflect k a b = delta a b − 2·(delta a k · delta b k)` is **the same matrix**
  as the deleted `reflMat k` — diagonal, `−1` at `k`, `+1` elsewhere;
* `isOrth_reflect` is the same theorem as the deleted `isOrth_reflMat`;
* `act2_reflect` is the same theorem as the deleted `act2_reflMat`, written with the factor
  `1 − 2δ_{bk}` where the deleted version wrote `sgnRefl k b`.

**Nothing clashed and nothing warned.** The duplicates sat inside `namespace LovelockReflections`,
so the shadowing was silent; and `reflMat` was in addition a *third* use of that name in this
estate, `LorentzReflection.reflMat` being an unrelated Minkowski reflection on `Fin 4 → ℝ`. The
ledger already carries duplicated declaration names as an open decision; this file added to the
pile rather than reading it.

**What this file now is.** Everything below is stated on `reflect`, and what survives is the part
that was never in `AlgebraicCurvature`: not that the reflection is orthogonal, but **what a tensor
*fixed* by it forces on the image of an equivariant `T`**. Four declarations went; nothing that was
proved here is now unproved.

## What the elementary argument looks like, and which step this is

`RicciProportional T α` says an equivariant `T` is `α` times the identity on the traceless-Ricci
summand. The textbook proof is Schur's lemma: that summand is an irreducible real representation
of `O(n)`, so an equivariant endomorphism is a scalar. **Irreducibility is exactly what this
estate cannot reach** — `UNLOCK_WATCHLIST` records it as blocked on compactness of `O(n)` with
Haar averaging.

The elementary substitute has three steps, and only the third is representation theory in
disguise:

1. **reflections** force `T` to send a diagonal traceless tensor to a *diagonal* one;
2. **permutations** then force the diagonal to be a fixed multiple, using tracelessness;
3. **the spectral theorem** reduces the general symmetric traceless tensor to the diagonal case.

**This file is step 1, and it costs one sign.** Nothing here is representation theory, nothing
here needs `n ≥ 3`, and no compactness or Haar measure appears.

## The mechanism

`reflect k` is the diagonal orthogonal matrix that negates coordinate `k` and fixes the rest.
Acting on a 2-tensor it multiplies the `(b,c)` entry by `(1 − 2δ_{bk})(1 − 2δ_{ck})`, which is `−1`
exactly when one of `b`, `c` is `k` and the other is not (`reflect_factor_pair`). So if `R` is
*fixed* by the reflection, equivariance reads

    T R b c  =  T (act (reflect k) R) b c  =  act2 (reflect k) (T R) b c  =  (−1) · T R b c

at those entries, and a real number equal to its own negative is zero. That is
`eq_zero_of_reflection_invariant`; `diagonal_of_reflection_invariant` runs it at every `k` at once.

§3 supplies the input the classification actually needs:
`ricciPart_act_reflect` — **if the traceless Ricci tensor of `R` is diagonal then `ricciPart R` is
fixed by every coordinate reflection** — and `T_ricciPart_diagonal` is the conclusion, that `T`
takes it to a diagonal tensor.

## What this is not

**It is not `RicciProportional`, and it is not half of it.** Steps 2 and 3 above are untouched.

**Step 2** runs on permutation matrices. The first draft of this paragraph said they "are
orthogonal by the same kind of computation as §1, so it *looks* like the next unit and cheap",
recorded as a guess rather than a promise because this file exists thanks to a wrong sizing
judgement. **The guess was wrong in the direction nobody checks**: `AlgebraicCurvature.permMat`,
`isOrth_permMat` and `act2_permMat` already existed, so that part of step 2 was not cheap, it was
*already done*, and `LovelockPermutations` re-proved it before this erratum caught it. The part of
step 2 that is real work is the combinatorial one, and it is done in `LovelockDiagonalWitness`.

**Step 3 is where the refusal still stands**, and nothing here weakens it: reducing a general
symmetric traceless tensor to a diagonal one needs the spectral theorem carried across to
`AlgebraicCurvature.IsOrth`. The bridge `isOrth_of_mem_orthogonalGroup` exists; the
diagonalisation does not.

**And it says nothing about `KillsWeyl`**, which is the harder of the two `Prop`s and is where the
missing invariant theory lives. The watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockReflections

open AlgebraicCurvature LovelockProjections LovelockEquivariance Finset

variable {n : ℕ}

/-! ## 1. The sign the reflection puts on an entry

`AlgebraicCurvature.act2_reflect` already says `act2 (reflect k) S b c` is
`(1 − 2δ_{bk}) · ((1 − 2δ_{ck}) · S b c)`. The two facts this file needs about that factor are
that it squares to one, and that the *product* over a pair is `−1` exactly at an entry the
reflection moves.
-/

/-- The factor is `±1`, so a diagonal entry comes back unchanged. -/
theorem reflect_factor_self (k b : Fin n) :
    (1 - 2 * delta b k) * (1 - 2 * delta b k) = (1 : ℝ) := by
  by_cases h : b = k
  · norm_num [delta, h]
  · norm_num [delta, h]

/-- **THE SIGN IS `−1` AT EXACTLY THE ENTRIES THE REFLECTION MOVES**: one index equal to `k`, the
other not. -/
theorem reflect_factor_pair {k b c : Fin n} (hbc : (b = k) ≠ (c = k)) :
    (1 - 2 * delta b k) * (1 - 2 * delta c k) = (-1 : ℝ) := by
  by_cases hb : b = k
  · have hc : ¬ c = k := by rw [hb] at hbc; simpa using hbc
    norm_num [delta, hb, hc]
  · have hc : c = k := by
      by_contra hc
      exact hbc (by simp [hb, hc])
    norm_num [delta, hb, hc]

/-! ## 2. What a fixed tensor forces

The whole content is that a real number equal to minus itself is zero.
-/

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **THE RUNG.** If `R` is fixed by the reflection at `k`, then `T R` vanishes at every entry
that the reflection negates — that is, at `(k, c)` and `(b, k)` for `b, c ≠ k`. -/
theorem eq_zero_of_reflection_invariant
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) {k : Fin n}
    (hfix : act (reflect k) R = R) {b c : Fin n} (hbc : (b = k) ≠ (c = k)) :
    T R b c = 0 := by
  have hstep : T R b c = (1 - 2 * delta b k) * ((1 - 2 * delta c k) * T R b c) := by
    conv_lhs => rw [← hfix]
    rw [hequiv (reflect k) (isOrth_reflect k) R hR b c, act2_reflect]
  rw [← mul_assoc, reflect_factor_pair hbc] at hstep
  linarith

/-- **RUN AT EVERY `k` AT ONCE:** a tensor fixed by all coordinate reflections is sent to a
diagonal one. -/
theorem diagonal_of_reflection_invariant
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (hfix : ∀ k : Fin n, act (reflect k) R = R) {b c : Fin n} (hne : b ≠ c) :
    T R b c = 0 :=
  eq_zero_of_reflection_invariant hequiv hR (hfix b) (by simp [Ne.symm hne])

/-! ## 3. The input the classification supplies

`ricciPart R` is a multiple of `kn (tracefreeRicci R) δ`, and both factors transform by `act2`.
The reflection fixes `δ`, so `ricciPart R` is fixed exactly when the traceless Ricci tensor is —
which for a *diagonal* traceless Ricci tensor is the sign computation of §1.
-/

/-- A diagonal 2-tensor is fixed by every coordinate reflection. -/
theorem act2_reflect_of_diagonal {S : Fin n → Fin n → ℝ}
    (hS : ∀ b c, b ≠ c → S b c = 0) (k : Fin n) : act2 (reflect k) S = S := by
  funext b c
  rw [act2_reflect]
  by_cases hbc : b = c
  · subst hbc
    rw [← mul_assoc, reflect_factor_self, one_mul]
  · rw [hS b c hbc, mul_zero, mul_zero]

/-- **AND THEREFORE THE RICCI SUMMAND IS FIXED**, when the traceless Ricci tensor is diagonal. -/
theorem ricciPart_act_reflect {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0) (k : Fin n) :
    act (reflect k) (ricciPart R) = ricciPart R := by
  funext a b c d
  have hsplit : ricciPart R
      = fun a b c d => (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci R) delta a b c d := by
    funext a b c d; rfl
  rw [hsplit, act_smul, act_kn, act2_reflect_of_diagonal hdiag k,
    act2_delta_fun (isOrth_reflect k)]

/-- **THE PAYOFF, AND IT IS STEP 1 OF THREE.** For an equivariant `T` and an algebraic curvature
tensor whose traceless Ricci tensor is diagonal, `T` sends the Ricci summand to a diagonal
tensor. -/
theorem T_ricciPart_diagonal
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0) {b c : Fin n} (hne : b ≠ c) :
    T (ricciPart R) b c = 0 :=
  diagonal_of_reflection_invariant hequiv (isAlgCurv_ricciPart hR)
    (ricciPart_act_reflect hdiag) hne

end LovelockReflections
