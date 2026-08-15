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

`reflMat k` is the diagonal orthogonal matrix that negates coordinate `k` and fixes the rest.
Acting on a 2-tensor it multiplies the `(b,c)` entry by `sgnRefl k b * sgnRefl k c`, which is `−1`
exactly when one of `b`, `c` is `k` and the other is not. So if `R` is *fixed* by the reflection,
equivariance reads

    T R b c  =  T (act (reflMat k) R) b c  =  act2 (reflMat k) (T R) b c  =  (−1) · T R b c

at those entries, and a real number equal to its own negative is zero. That is
`eq_zero_of_reflection_invariant`; `diagonal_of_reflection_invariant` runs it at every `k` at once.

§3 supplies the input the classification actually needs:
`ricciPart_act_reflMat` — **if the traceless Ricci tensor of `R` is diagonal then `ricciPart R` is
fixed by every coordinate reflection** — and `T_ricciPart_diagonal` is the conclusion, that `T`
takes it to a diagonal tensor.

## What this is not

**It is not `RicciProportional`, and it is not half of it.** Steps 2 and 3 above are untouched.

**Step 2** runs on permutation matrices, which are orthogonal by the same kind of computation as
§1, so it *looks* like the next unit and cheap. **That is a sizing judgement, and this file exists
because a sizing judgement of mine was wrong**; it is recorded as a guess for the next unit to
test, not as a promise.

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

/-! ## 1. The reflection that negates one coordinate -/

/-- `−1` at `k`, `+1` elsewhere. -/
def sgnRefl (k : Fin n) (j : Fin n) : ℝ := if j = k then -1 else 1

/-- The diagonal orthogonal matrix negating coordinate `k`. -/
def reflMat (k : Fin n) (a b : Fin n) : ℝ := if a = b then sgnRefl k a else 0

theorem sgnRefl_mul_self (k j : Fin n) : sgnRefl k j * sgnRefl k j = 1 := by
  unfold sgnRefl; split <;> norm_num

/-- **THE REFLECTION IS ORTHOGONAL**, so it is a legitimate frame change for `hequiv`. -/
theorem isOrth_reflMat (k : Fin n) : IsOrth (reflMat k) where
  rows := by
    intro x y
    have h : ∀ a : Fin n, reflMat k x a * reflMat k y a
        = if x = a then (if y = a then (1 : ℝ) else 0) else 0 := by
      intro a
      by_cases hx : x = a <;> by_cases hy : y = a <;>
        simp [reflMat, hx, hy, sgnRefl_mul_self]
    simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true, delta]
    by_cases hxy : x = y <;> simp [hxy, eq_comm]
  cols := by
    intro x y
    have h : ∀ a : Fin n, reflMat k a x * reflMat k a y
        = if a = x then (if a = y then (1 : ℝ) else 0) else 0 := by
      intro a
      by_cases hx : a = x <;> by_cases hy : a = y <;>
        simp [reflMat, hx, hy, sgnRefl_mul_self]
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true, delta]

/-- **AND ITS ACTION ON A 2-TENSOR IS A SIGN**, entry by entry. -/
theorem act2_reflMat (k : Fin n) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (reflMat k) S b c = sgnRefl k b * sgnRefl k c * S b c := by
  simp only [act2, reflMat]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd; simp [Ne.symm hd]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro d _ hd
    refine Finset.sum_eq_zero fun e _ => ?_
    simp [Ne.symm hd]
  · intro h; exact absurd (Finset.mem_univ b) h

/-! ## 2. What a fixed tensor forces

The whole content is that a real number equal to minus itself is zero.
-/

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **THE RUNG.** If `R` is fixed by the reflection at `k`, then `T R` vanishes at every entry
that the reflection negates — that is, at `(k, c)` and `(b, k)` for `b, c ≠ k`. -/
theorem eq_zero_of_reflection_invariant
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) {k : Fin n}
    (hfix : act (reflMat k) R = R) {b c : Fin n} (hbc : (b = k) ≠ (c = k)) :
    T R b c = 0 := by
  have hstep : T R b c = sgnRefl k b * sgnRefl k c * T R b c := by
    conv_lhs => rw [← hfix]
    rw [hequiv (reflMat k) (isOrth_reflMat k) R hR b c, act2_reflMat]
  have hsign : sgnRefl k b * sgnRefl k c = -1 := by
    by_cases hb : b = k
    · have hc : ¬ c = k := by rw [hb] at hbc; simpa using hbc
      simp [sgnRefl, hb, hc]
    · have hc : c = k := by
        by_contra hc
        exact hbc (by simp [hb, hc])
      simp [sgnRefl, hb, hc]
  rw [hsign] at hstep
  linarith

/-- **RUN AT EVERY `k` AT ONCE:** a tensor fixed by all coordinate reflections is sent to a
diagonal one. -/
theorem diagonal_of_reflection_invariant
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (hfix : ∀ k : Fin n, act (reflMat k) R = R) {b c : Fin n} (hne : b ≠ c) :
    T R b c = 0 :=
  eq_zero_of_reflection_invariant hequiv hR (hfix b) (by simp [Ne.symm hne])

/-! ## 3. The input the classification supplies

`ricciPart R` is a multiple of `kn (tracefreeRicci R) δ`, and both factors transform by `act2`.
The reflection fixes `δ`, so `ricciPart R` is fixed exactly when the traceless Ricci tensor is —
which for a *diagonal* traceless Ricci tensor is the sign computation of §1.
-/

/-- A diagonal 2-tensor is fixed by every coordinate reflection. -/
theorem act2_reflMat_of_diagonal {S : Fin n → Fin n → ℝ}
    (hS : ∀ b c, b ≠ c → S b c = 0) (k : Fin n) : act2 (reflMat k) S = S := by
  funext b c
  rw [act2_reflMat]
  by_cases hbc : b = c
  · subst hbc
    rw [sgnRefl_mul_self, one_mul]
  · rw [hS b c hbc, mul_zero]

/-- **AND THEREFORE THE RICCI SUMMAND IS FIXED**, when the traceless Ricci tensor is diagonal. -/
theorem ricciPart_act_reflMat {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0) (k : Fin n) :
    act (reflMat k) (ricciPart R) = ricciPart R := by
  funext a b c d
  have hsplit : ricciPart R
      = fun a b c d => (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci R) delta a b c d := by
    funext a b c d; rfl
  rw [hsplit, act_smul, act_kn, act2_reflMat_of_diagonal hdiag k,
    act2_delta_fun (isOrth_reflMat k)]

/-- **THE PAYOFF, AND IT IS STEP 1 OF THREE.** For an equivariant `T` and an algebraic curvature
tensor whose traceless Ricci tensor is diagonal, `T` sends the Ricci summand to a diagonal
tensor. -/
theorem T_ricciPart_diagonal
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0) {b c : Fin n} (hne : b ≠ c) :
    T (ricciPart R) b c = 0 :=
  diagonal_of_reflection_invariant hequiv (isAlgCurv_ricciPart hR)
    (ricciPart_act_reflMat hdiag) hne

end LovelockReflections
