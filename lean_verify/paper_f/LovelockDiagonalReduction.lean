import LovelockEquivariantAdjoint
import LovelockDiagonalise

/-!
# Rung 6, step 1 — and the half of `KillsWeyl` the diagonalisation does not reach

`LovelockEquivariantAdjoint` closed `WALLS` §W5.0 §5d's two gaps and left the route open at rung 6,
whose first step was *"reduce a general symmetric `S` to a diagonal one — `diagonalisable` exists
and `act_eqAdjoint` is the transport, but the reduction is not written"*. **It is written here, and
writing it turned up a step 0 that §5d had not noticed.**

## What is proved

* **`ip_eqAdjoint_weylPart_of_symm`** — if `eqAdjoint T S` is `ip`-orthogonal to every Weyl part for
  every **diagonal** `S`, then it is for every **symmetric** `S`. Four rewrites:
  `LovelockDiagonalise.diagonalisable` supplies the frame, `act_eqAdjoint` and `act_weylPart` move
  both arguments into it, and `LovelockInnerInvariant.ip_act` says the pairing did not notice;
* `symmPart`, `antisymmPart` and `ip2_split` — every 2-tensor is the sum of a symmetric and an
  antisymmetric one, and the pairing splits with it;
* **`killsWeyl_iff_two_halves`** — **`KillsWeyl T` is exactly the conjunction of two independent
  statements**, one tested by symmetric 2-tensors and one by antisymmetric ones.

## The step 0 this turned up, stated plainly

`LovelockReduction.KillsWeyl` asks `T (weylPart R) b c = 0` at **every** `b, c`. It therefore
constrains the **antisymmetric** part of `T`'s output as much as the symmetric part — and
**`diagonalisable` reaches only the symmetric test tensors**, because an antisymmetric real matrix
is not orthogonally diagonalisable. So the route's rung 6 addresses one of the two halves that
`killsWeyl_iff_two_halves` names, and **the other half is a different question**: what an
equivariant `T` does into the antisymmetric 2-tensors, which is a representation the estate has
never looked at.

**And it cannot be assumed away.** `LovelockOneProp.killsWeyl_iff` says `KillsWeyl T` holds exactly
when `T` is `α·ricci + β·scal·δ`, whose values are symmetric — so **`KillsWeyl` *implies* `T`'s
output is symmetric on curvature tensors.** Adding that symmetry as a hypothesis would be assuming
a consequence of what is being proved. If the antisymmetric half is to be disposed of, it has to be
disposed of, not hypothesised.

**`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.** What this file does is
make the remaining work two named halves instead of one unnamed one.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockDiagonalReduction

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality
  LovelockReduction LovelockInnerInvariant LovelockActInverse LovelockFrameInverse
  LovelockDiagonalise LovelockEquivariantAdjoint LovelockAdjoint Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The diagonal case reaches every symmetric one -/

theorem ip_eqAdjoint_weylPart_of_symm
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (hdiag : ∀ S : Fin n → Fin n → ℝ, (∀ b c, b ≠ c → S b c = 0) →
      ∀ R, IsAlgCurv R → ip (eqAdjoint T S) (weylPart R) = 0)
    {S : Fin n → Fin n → ℝ} (hS : ∀ x y, S x y = S y x)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    ip (eqAdjoint T S) (weylPart R) = 0 := by
  obtain ⟨Q, hQ, hQd⟩ := diagonalisable n S hS
  have hkey := hdiag (act2 Q S) hQd (act Q R) (isAlgCurv_act Q hR)
  have h1 : eqAdjoint T (act2 Q S) = act Q (eqAdjoint T S) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      (act_eqAdjoint hadd hsmul hequiv hQ S a b c d).symm
  have h2 : weylPart (act Q R) = act Q (weylPart R) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      (act_weylPart hQ R a b c d).symm
  rw [h1, h2, ip_act hQ] at hkey
  exact hkey

/-! ## 2. And the symmetric ones are only half of `KillsWeyl` -/

noncomputable def symmPart (S : Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  (1/2 : ℝ) * (S b c + S c b)

noncomputable def antisymmPart (S : Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  (1/2 : ℝ) * (S b c - S c b)

theorem symm_symmPart (S : Fin n → Fin n → ℝ) (x y : Fin n) :
    symmPart S x y = symmPart S y x := by simp only [symmPart]; ring

theorem antisymm_antisymmPart (S : Fin n → Fin n → ℝ) (x y : Fin n) :
    antisymmPart S x y = -antisymmPart S y x := by simp only [antisymmPart]; ring

theorem ip2_split (S U : Fin n → Fin n → ℝ) :
    ip2 S U = ip2 (symmPart S) U + ip2 (antisymmPart S) U := by
  simp only [ip2, symmPart, antisymmPart, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

theorem killsWeyl_iff_two_halves :
    KillsWeyl T ↔
      (∀ S : Fin n → Fin n → ℝ, (∀ x y, S x y = S y x) →
        ∀ R, IsAlgCurv R → ip2 S (T (weylPart R)) = 0)
      ∧ (∀ S : Fin n → Fin n → ℝ, (∀ x y, S x y = -S y x) →
        ∀ R, IsAlgCurv R → ip2 S (T (weylPart R)) = 0) := by
  constructor
  · intro hW
    have hz : ∀ (S : Fin n → Fin n → ℝ) R, IsAlgCurv R → ip2 S (T (weylPart R)) = 0 := by
      intro S R hR
      simp only [ip2]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      rw [hW R hR p q, mul_zero]
    exact ⟨fun S _ R hR => hz S R hR, fun S _ R hR => hz S R hR⟩
  · rintro ⟨hs, ha⟩ R hR b c
    have h1 := hs (symmPart (fun x y => delta b x * delta c y)) (symm_symmPart _) R hR
    have h2 := ha (antisymmPart (fun x y => delta b x * delta c y))
      (antisymm_antisymmPart _) R hR
    have h3 := ip2_split (fun x y => delta b x * delta c y) (T (weylPart R))
    rw [ip2_unit] at h3
    linarith

end LovelockDiagonalReduction
