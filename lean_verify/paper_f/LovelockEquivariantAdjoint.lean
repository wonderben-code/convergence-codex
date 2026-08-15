import LovelockCurvProjection
import LovelockAdjoint
import LovelockActInverse
import LovelockReflectionFour

/-!
# The equivariant adjoint: `WALLS` §W5.0 §5d's two gaps, closed

§5d's route to `KillsWeyl` was open at two places, and both were the same mismatch:
`LovelockReduction`'s equivariance hypothesis holds only at algebraic curvature tensors, while
`LovelockAdjoint.adjoint` is assembled from a standard basis whose members are not. `WALLS` named
the object that would close both — an explicit projection onto the algebraic curvature tensors —
and `LovelockCurvProjection` built it. **This file forms the composite and proves the two
statements the gaps were about.**

## What is proved

* `ip2_act2_transp` — the 2-tensor twin of `LovelockActInverse.ip_act_transp`, and **it needs no
  orthogonality at all**: it is Fubini on the doubled index;
* `ip_sub_left` — two lines, and named here because §5d listed it as one of the two things standing
  in the way. **§5d listed the other as `isAlgCurv_sub`, and that one was already in the estate**
  (`LovelockProjections`, since the file was written). A first version of this file proved it again;
  `ERRATUM 173` records the miss and the duplicate is gone;
* **`eqAdjoint T S := curvProj (adjoint T S)`**, with
  * **`isAlgCurv_eqAdjoint`** — **it is an algebraic curvature tensor, for every `T` and every
    `S`, with no hypothesis at all.** *This is gap (ii);*
  * `ip_eqAdjoint` — `⟨eqAdjoint T S, R⟩ = ⟨S, T R⟩` for every algebraic curvature `R`, so the
    projection costs nothing where it is used;
  * **`act_eqAdjoint`** — **`act Q (eqAdjoint T S) = eqAdjoint T (act2 Q S)` for every orthogonal
    `Q`.** *This is gap (i).* The proof is the reason the projection was worth building: the two
    sides are both algebraic curvature tensors, their difference is `ip`-orthogonal to every
    algebraic curvature tensor by four rewrites, and `LovelockInnerPositive`'s positive
    definiteness turns that into equality — **the equivariance hypothesis is used only at
    algebraic curvature tensors throughout**;
* **`killsWeyl_iff_eqAdjoint`** — `KillsWeyl T` iff `eqAdjoint T S` is `ip`-orthogonal to every
  Weyl part;
* **`reflect_eqAdjoint`** — and for **diagonal** `S`, `eqAdjoint T S` is fixed by every coordinate
  reflection, because a diagonal 2-tensor is (`LovelockReflections.act2_reflect_of_diagonal`);
* **`eqAdjoint_eq_zero_of_ne_pattern`** — so `LovelockReflectionFour` applies to it: for diagonal
  `S`, **`eqAdjoint T S` vanishes unless `(c,d)` is `(a,b)` or `(b,a)`**, and by `eq_of_diag_eq` it
  is determined by the numbers `eqAdjoint T S a b a b`.

## What is still open, which is now one thing rather than three

**`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.** What has changed is
where the route is open. §5d's rungs 1, 2, 3 were built earlier today and gaps (i) and (ii) are
closed here, so **the whole of what remains is rung 6**, and it is three named steps, none of them
done:

1. reduce a general symmetric `S` to a diagonal one — `LovelockDiagonalise.diagonalisable` exists
   and `act_eqAdjoint` is the transport, but the reduction is not written;
2. the permutation argument that pins the surviving numbers `eqAdjoint T S a b a b` to a
   one-parameter family;
3. the computation that the family lies in the Ricci part, so its Weyl component vanishes.

**Step 3 has been checked by hand and is not a theorem**, and that is said here in the same words
§5d uses, because a hand check is what this project calls a guess.

**And nothing here says any equivariant `T` is a multiple of the Ricci trace.** Every theorem in
this file is conditional on `hadd`, `hsmul` and `hequiv` and says something about `eqAdjoint`; none
of them evaluates `T` anywhere.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockEquivariantAdjoint

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality
  LovelockReduction LovelockInnerPositive LovelockActInverse LovelockFrameInverse
  LovelockAdjoint LovelockCurvProjection LovelockReflections LovelockReflectionFour Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The two small lemmas §5d named -/

theorem ip2_act2_transp (Q : Fin n → Fin n → ℝ) (S U : Fin n → Fin n → ℝ) :
    ip2 (act2 Q S) U = ip2 S (act2 (transp Q) U) := by
  have hL : ip2 (act2 Q S) U
      = ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
          Q p.1.1 p.2.1 * Q p.1.2 p.2.2 * S p.2.1 p.2.2 * U p.1.1 p.1.2 := by
    simp only [ip2, act2, Fintype.sum_prod_type, Finset.sum_mul]
  have hR : ip2 S (act2 (transp Q) U)
      = ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
          Q p.2.1 p.1.1 * Q p.2.2 p.1.2 * S p.1.1 p.1.2 * U p.2.1 p.2.2 := by
    simp only [ip2, act2, transp, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c' _ => by ring
  rw [hL, hR]
  exact Fintype.sum_equiv
    ⟨fun p => (p.2, p.1), fun p => (p.2, p.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

theorem ip_sub_left (A B C : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (fun a b c d => A a b c d - B a b c d) C = ip A C - ip B C := by
  simp only [ip, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-! ## 2. The equivariant adjoint -/

/-- **THE EQUIVARIANT ADJOINT.** -/
noncomputable def eqAdjoint (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → ℝ) : Fin n → Fin n → Fin n → Fin n → ℝ := curvProj (adjoint T S)

theorem isAlgCurv_eqAdjoint (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → ℝ) : IsAlgCurv (eqAdjoint T S) := isAlgCurv_curvProj _

theorem ip_eqAdjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (S : Fin n → Fin n → ℝ) {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    ip (eqAdjoint T S) R = ip2 S (T R) := by
  rw [eqAdjoint, ip_curvProj hR, ip_adjoint hadd hsmul]

theorem act_eqAdjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrth Q) (S : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (eqAdjoint T S) a b c d = eqAdjoint T (act2 Q S) a b c d := by
  set D : Fin n → Fin n → Fin n → Fin n → ℝ :=
    fun x y z w => eqAdjoint T (act2 Q S) x y z w - act Q (eqAdjoint T S) x y z w with hD
  have hDcurv : IsAlgCurv D :=
    isAlgCurv_sub (isAlgCurv_eqAdjoint T _) (isAlgCurv_act Q (isAlgCurv_eqAdjoint T S))
  have hzero : ∀ R : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv R → ip D R = 0 := by
    intro R hR
    rw [hD, ip_sub_left, ip_eqAdjoint hadd hsmul _ hR, ip2_act2_transp,
      ip_act_transp hQ, ip_eqAdjoint hadd hsmul S (isAlgCurv_act (transp Q) hR)]
    have hT : ∀ x y : Fin n,
        T (act (transp Q) R) x y = act2 (transp Q) (T R) x y :=
      fun x y => hequiv (transp Q) (isOrth_transp hQ) R hR x y
    have hfun : T (act (transp Q) R) = act2 (transp Q) (T R) :=
      funext fun x => funext fun y => hT x y
    rw [hfun]
    ring
  have hDD := hzero D hDcurv
  have hz := eq_zero_of_ip_self_eq_zero hDD
  have := congrFun (congrFun (congrFun (congrFun hz a) b) c) d
  rw [hD] at this
  linarith

/-! ## 3. What it buys -/

theorem killsWeyl_iff_eqAdjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c) :
    KillsWeyl T ↔ ∀ (S : Fin n → Fin n → ℝ) R, IsAlgCurv R →
      ip (eqAdjoint T S) (weylPart R) = 0 := by
  constructor
  · intro hW S R hR
    rw [ip_eqAdjoint hadd hsmul S (isAlgCurv_weylPart hR)]
    simp only [ip2]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [hW R hR p q, mul_zero]
  · intro h R hR b c
    have hb := h (fun x y => delta b x * delta c y) R hR
    rw [ip_eqAdjoint hadd hsmul _ (isAlgCurv_weylPart hR), ip2_unit] at hb
    exact hb

theorem reflect_eqAdjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {S : Fin n → Fin n → ℝ} (hS : ∀ b c, b ≠ c → S b c = 0) (k a b c d : Fin n) :
    act (reflect k) (eqAdjoint T S) a b c d = eqAdjoint T S a b c d := by
  rw [act_eqAdjoint hadd hsmul hequiv (isOrth_reflect k) S, act2_reflect_of_diagonal hS]

theorem eqAdjoint_eq_zero_of_ne_pattern
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {S : Fin n → Fin n → ℝ} (hS : ∀ b c, b ≠ c → S b c = 0) {a b c d : Fin n}
    (hne : ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))) : eqAdjoint T S a b c d = 0 :=
  LovelockReflectionFour.eq_zero_of_ne_pattern (isAlgCurv_eqAdjoint T S)
    (fun k x y z w => reflect_eqAdjoint hadd hsmul hequiv hS k x y z w) hne

end LovelockEquivariantAdjoint
