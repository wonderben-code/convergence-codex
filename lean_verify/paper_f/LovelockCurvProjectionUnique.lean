import LovelockEquivariantAdjoint

/-!
# The projection is the only one, and the adjoint does not depend on the basis

`LovelockCurvProjection` built `curvProj` and then named what it was not:

> Nor is it the `ip`-orthogonal projection in the bundled sense. No submodule, no
> `orthogonalProjection` instance, **no uniqueness statement.**

**The uniqueness statement is here**, and it costs one lemma. Bundling — a submodule, a Mathlib
instance — is still a decision nobody has taken, and `LovelockReduction` §1's reason for not taking
it stands. **What was missing mathematically was not the bundling; it was this.**

## What is proved

* **`eq_of_ip_eq_on_curv`** — **the pairing separates algebraic curvature tensors**: two of them
  agreeing against every algebraic curvature tensor are equal. The difference is one
  (`LovelockProjections.isAlgCurv_sub`), it pairs to zero with itself, and
  `LovelockInnerPositive.eq_zero_of_ip_self_eq_zero` finishes;
* **`curvProj_eq_self`** — the projection is the identity on its target, and **`curvProj_idem`** —
  so it is idempotent. `LovelockCurvProjection` proved idempotence *on the image* of each of its two
  factors; this is the statement for the composite, and it follows from the characterisation rather
  than from re-running the algebra;
* **`curvProj_unique`** — and it is the **only** algebraic curvature tensor pairing with `Curv` the
  way `A` does;
* **`eqAdjoint_unique`** — the same for `LovelockEquivariantAdjoint.eqAdjoint`: it is the unique
  algebraic curvature tensor `X` with `⟨X, R⟩ = ⟨S, T R⟩` at every algebraic curvature `R`. **So the
  adjoint does not depend on the standard basis it was built from**, which nothing said before and
  which a reader was entitled to worry about.

## What this does not do

**It does not bear on `KillsWeyl`**, which is untouched, and **the watchlist item does not move.**
Every theorem here is about the construction being canonical, not about what `T` does.

**And it is still not a bundled projection.** No `Submodule`, no `orthogonalProjection`, no
`LinearMap`. What `curvProj` now has is the characterisation those instances would carry; what it
does not have is the instance, and that remains a decision rather than a gap.

**⚠ SUPERSEDED — IT IS ONE NOW.** Kept per `ERRATUM 94`.
`LovelockCurvProjectionOrthogonal.algCurv` is the `Submodule`, and `starProjection_arrEquiv`
proves `curvProj` **equal** to Mathlib's orthogonal projection onto it — using this file's own
`curvProj_unique` route in Mathlib's vocabulary: membership plus orthogonality of the difference.
**The sentence was right that it was a decision rather than a gap, and wrong about what the
decision cost**: taking it produced `curvProj_minimal`, that `curvProj A` is the **closest**
algebraic curvature tensor to `A`, which no theorem here could state because "closest" needs a
metric. What still stands: **no instance on the array type**, and this file's theorems are still
about the bare form. `ERRATUM 228`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockCurvProjectionUnique

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerPositive
  LovelockCurvProjection LovelockAdjoint LovelockEquivariantAdjoint Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The pairing separates -/

/-- **THE PAIRING SEPARATES ALGEBRAIC CURVATURE TENSORS.** -/
theorem eq_of_ip_eq_on_curv {X Y : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hX : IsAlgCurv X) (hY : IsAlgCurv Y)
    (h : ∀ B, IsAlgCurv B → ip X B = ip Y B) (a b c d : Fin n) :
    X a b c d = Y a b c d := by
  set D : Fin n → Fin n → Fin n → Fin n → ℝ :=
    fun x y z w => X x y z w - Y x y z w with hD
  have hDcurv : IsAlgCurv D := LovelockProjections.isAlgCurv_sub hX hY
  have hDD : ip D D = 0 := by
    rw [hD, ip_sub_left, h D hDcurv]
    ring
  have hz := eq_zero_of_ip_self_eq_zero hDD
  have := congrFun (congrFun (congrFun (congrFun hz a) b) c) d
  rw [hD] at this
  linarith

/-! ## 2. And therefore the projection is characterised -/

/-- **THE PROJECTION IS THE IDENTITY ON ITS TARGET.** -/
theorem curvProj_eq_self {A : Fin n → Fin n → Fin n → Fin n → ℝ} (hA : IsAlgCurv A)
    (a b c d : Fin n) : curvProj A a b c d = A a b c d :=
  eq_of_ip_eq_on_curv (isAlgCurv_curvProj A) hA (fun _ hB => ip_curvProj hB A) a b c d

/-- **AND THEREFORE IDEMPOTENT.** -/
theorem curvProj_idem (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    curvProj (curvProj A) a b c d = curvProj A a b c d :=
  curvProj_eq_self (isAlgCurv_curvProj A) a b c d

/-- **AND IT IS THE ONLY ONE.** -/
theorem curvProj_unique {A X : Fin n → Fin n → Fin n → Fin n → ℝ} (hX : IsAlgCurv X)
    (h : ∀ B, IsAlgCurv B → ip X B = ip A B) (a b c d : Fin n) :
    X a b c d = curvProj A a b c d :=
  eq_of_ip_eq_on_curv hX (isAlgCurv_curvProj A)
    (fun B hB => (h B hB).trans (ip_curvProj hB A).symm) a b c d

/-- **THE EQUIVARIANT ADJOINT DOES NOT DEPEND ON THE BASIS IT WAS BUILT FROM.** -/
theorem eqAdjoint_unique
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (S : Fin n → Fin n → ℝ) {X : Fin n → Fin n → Fin n → Fin n → ℝ} (hX : IsAlgCurv X)
    (h : ∀ R, IsAlgCurv R → ip X R = ip2 S (T R)) (a b c d : Fin n) :
    X a b c d = eqAdjoint T S a b c d :=
  eq_of_ip_eq_on_curv hX (isAlgCurv_eqAdjoint T S)
    (fun B hB => (h B hB).trans (ip_eqAdjoint hadd hsmul S hB).symm) a b c d

end LovelockCurvProjectionUnique
