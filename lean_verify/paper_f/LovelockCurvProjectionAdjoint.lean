import LovelockCurvProjectionUnique

/-!
# The projection is self-adjoint, and it shortens

`LovelockCurvProjection.ip_curvProj` says `⟨curvProj A, B⟩ = ⟨A, B⟩` **for `B` an algebraic
curvature tensor**. That hypothesis is not needed for the statement the estate actually wants, and
`PROOF_STRATEGY` §7 item 3 is to notice such a fence and take it off.

**The right statement is self-adjointness**, `⟨curvProj A, B⟩ = ⟨A, curvProj B⟩`, **with no
hypothesis on either argument** — and the hypothesis-carrying form is its corollary, by
`LovelockCurvProjectionUnique.curvProj_eq_self`. Together with idempotence and the image lying in
`Curv`, that is the textbook characterisation of an orthogonal projection, now held in full.

## What is proved

* `ip_sub_right` — the mirror of `LovelockEquivariantAdjoint.ip_sub_left`, one line, and absent
  because nothing had needed it;
* **`ip_residue`** — `B − curvProj B` is `ip`-orthogonal to **every** algebraic curvature tensor.
  This is `ip_curvProj` read as a statement about the residue rather than about the image, and it
  is the only step with content;
* **`ip_curvProj_comm`** — **the projection is self-adjoint.** Both `⟨curvProj A, B⟩` and
  `⟨A, curvProj B⟩` equal `⟨curvProj A, curvProj B⟩`, each by one application of `ip_residue`;
* `ip_curvProj'` — and so `ip_curvProj`'s hypothesis-carrying form falls out. **The fence is off:
  nothing about `B` is assumed**;
* **`ip_self_split`** — Pythagoras: `⟨B,B⟩` splits as image plus residue, the cross term vanishing;
* **`ip_curvProj_le`** — **the projection does not increase length**, by `ip_self_nonneg` on the
  residue.

## What this does not do

**It does not bear on `KillsWeyl`**, which is untouched, and **the watchlist item does not move.**
Everything here is a property of the projection.

**And it is still not a bundled `orthogonalProjection`.** No `Submodule`, no instance, no
`LinearMap`. What `curvProj` now carries is the full mathematical characterisation those would
package — idempotent, self-adjoint, image in `Curv`, unique, length-non-increasing — and the
packaging remains a decision nobody has taken rather than a gap. `LovelockReduction` §1's reason
stands.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockCurvProjectionAdjoint

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerPositive
  LovelockCurvProjection LovelockEquivariantAdjoint LovelockCurvProjectionUnique Finset

variable {n : ℕ}

/-! ## 1. The residue -/

theorem ip_sub_right (A B C : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip A (fun a b c d => B a b c d - C a b c d) = ip A B - ip A C := by
  simp only [ip, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- **THE RESIDUE OF THE PROJECTION IS ORTHOGONAL TO EVERY CURVATURE TENSOR.** -/
theorem ip_residue (B : Fin n → Fin n → Fin n → Fin n → ℝ)
    {X : Fin n → Fin n → Fin n → Fin n → ℝ} (hX : IsAlgCurv X) :
    ip (fun x y z w => B x y z w - curvProj B x y z w) X = 0 := by
  rw [ip_sub_left, ip_curvProj hX B]
  ring

/-! ## 2. Self-adjointness, and the fence coming off -/

/-- **THE PROJECTION IS SELF-ADJOINT**, with no hypothesis on either argument. -/
theorem ip_curvProj_comm (A B : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (curvProj A) B = ip A (curvProj B) := by
  have h1 : ip (curvProj A) B = ip (curvProj A) (curvProj B) := by
    have hz := ip_residue B (isAlgCurv_curvProj A)
    rw [ip_sub_left] at hz
    rw [ip_comm (curvProj A) B, ip_comm (curvProj A) (curvProj B)]
    linarith
  have h2 : ip A (curvProj B) = ip (curvProj A) (curvProj B) := by
    have hz := ip_residue A (isAlgCurv_curvProj B)
    rw [ip_sub_left] at hz
    linarith
  rw [h1, h2]

/-- And the hypothesis-carrying form is the corollary. -/
theorem ip_curvProj' {B : Fin n → Fin n → Fin n → Fin n → ℝ} (hB : IsAlgCurv B)
    (A : Fin n → Fin n → Fin n → Fin n → ℝ) : ip (curvProj A) B = ip A B := by
  rw [ip_curvProj_comm]
  have : curvProj B = B := funext fun a => funext fun b => funext fun c => funext fun d =>
    curvProj_eq_self hB a b c d
  rw [this]

/-! ## 3. Pythagoras -/

/-- **PYTHAGORAS FOR THE PROJECTION.** -/
theorem ip_self_split (B : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip B B = ip (curvProj B) (curvProj B)
      + ip (fun x y z w => B x y z w - curvProj B x y z w)
          (fun x y z w => B x y z w - curvProj B x y z w) := by
  have h0 : ip (fun x y z w => B x y z w - curvProj B x y z w) (curvProj B) = 0 :=
    ip_residue B (isAlgCurv_curvProj B)
  have h1 : ip (fun x y z w => B x y z w - curvProj B x y z w)
      (fun x y z w => B x y z w - curvProj B x y z w)
      = ip (fun x y z w => B x y z w - curvProj B x y z w) B := by
    rw [ip_sub_right, h0]
    ring
  have h2 : ip (fun x y z w => B x y z w - curvProj B x y z w) B
      = ip B B - ip (curvProj B) B := by
    rw [ip_sub_left]
  have h3 : ip (curvProj B) B = ip (curvProj B) (curvProj B) := by
    have hz := ip_residue B (isAlgCurv_curvProj B)
    rw [ip_sub_left] at hz
    rw [ip_comm (curvProj B) B, ip_comm (curvProj B) (curvProj B)]
    linarith
  rw [h1, h2, h3]
  ring

/-- **AND THEREFORE THE PROJECTION DOES NOT INCREASE LENGTH.** -/
theorem ip_curvProj_le (B : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (curvProj B) (curvProj B) ≤ ip B B := by
  have hs := ip_self_split B
  have hn := ip_self_nonneg (fun x y z w => B x y z w - curvProj B x y z w)
  linarith

end LovelockCurvProjectionAdjoint
