import QuaternionTensor
import Mathlib.RingTheory.MatrixAlgebra

/-!
# `Cl(Q ⊥ ⟨c₁,c₂⟩) ≅ Cl((−c₁c₂)·Q) ⊗ Cl⟨c₁,c₂⟩` whenever `c₁c₂ ≠ 0`

**The ungraded decomposition**, and the second of the two ingredients the eight-fold periodicity
needs. The watchlist recorded it absent from Mathlib and it is: the library's only Clifford
decomposition, `CliffordAlgebra.prodEquiv`, lands in the **graded** tensor product
`evenOdd Q₁ ᵍ⊗ evenOdd Q₂`, and `GradedTensorProduct.of` is `LinearEquiv.refl` — same carrier,
different multiplication — so there is no free conversion to the ordinary one.

> **`equivTensor`** — `Cl(Q ⊥ ⟨c₁,c₂⟩) ≃ₐ[ℝ] Cl((−c₁c₂) • Q) ⊗[ℝ] Cl⟨c₁,c₂⟩`, for every real
> quadratic form `Q` on every finite-dimensional real space, whenever `c₁ * c₂ ≠ 0`.

## Why the hypothesis is `c₁c₂ ≠ 0` and not `c₁ = c₂ = 1`

`ω² = −c₁c₂` with **no** hypothesis (`vol_sq`); the nonvanishing is used in exactly one place, to
invert it and recover the first-factor generators (`ι_inl_mem_range`). Weakening the hypothesis from
`c₁c₂ = 1` — which is where this file started — to `c₁c₂ ≠ 0` buys the whole move set:

* `(1,1)`: `Cl(p+2,q) ≅ Cl(q,p) ⊗ M₂(ℝ)`  — `equivTensorPos`, `equivMatrixTwo`;
* `(−1,−1)`: `Cl(p,q+2) ≅ Cl(q,p) ⊗ ℍ`  — `equivTensorNeg`, `equivQuatTwo`;
* `(1,−1)`: `Cl(Q ⊥ ⟨1,−1⟩) ≅ M₂(Cl Q)`  — `equivHyperbolic`, **which is
  `CliffordPeriodicityHyperbolic.periodicityEquivHyp`**, and at this point the first factor is
  `1 • Q = Q` with no negation at all.

**Three of the reach analysis's five moves are now instances of one theorem**, and the fourth and
fifth — the eight-fold periodicity — were already built by composing the first two. At `c₁c₂ = 1`
they were two theorems and an import.

## The substitution

Write `a₁, a₂` for the two extra generators and `ω = a₁a₂`. Then

* `ω² = −c₁c₂ = −1`  (`vol_sq`),
* `ω` **commutes** with every `ι (v, 0)` — two anticommutations cancel (`vol_comm_inl`),
* `ω` **anticommutes** with every `ι (0, w)` (`vol_anticomm_inr`).

So `v ↦ ι (v,0) · ω` squares to `−Q v` (`fMap_sq`): it generates `Cl(−Q)`, and it commutes with the
second factor because the sign from `ω` and the sign from orthogonality cancel (`commute_gen`).
That commuting pair is exactly what `Algebra.TensorProduct.lift` consumes — the same lemma that
built `QuaternionTensor`, and the reason this file is short.

## Surjectivity

`ω` is in the range because it is a product of two second-factor generators, and
`ι (v,0) = −(ι (v,0) · ω) · ω` recovers the first-factor generators from it. Every generator of
`Cl(Q ⊥ ⟨c₁,c₂⟩)` is a sum of the two kinds, so `CliffordAlgebra.adjoin_range_ι` closes it.
Injectivity is then free: both sides have dimension `2 ^ (finrank V + 2)`.
-/

namespace CliffordTensorTwo

open CliffordAlgebra QuadraticMap
open scoped TensorProduct Quaternion

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The two-dimensional factor `⟨c₁, c₂⟩`. -/
abbrev N (c₁ c₂ : ℝ) : QuadraticForm ℝ (ℝ × ℝ) := CliffordAlgebraQuaternion.Q c₁ c₂

/-- `Q ⊥ ⟨c₁,c₂⟩`, the form whose Clifford algebra is being decomposed. -/
abbrev Qext (Q : QuadraticForm ℝ V) (c₁ c₂ : ℝ) : QuadraticForm ℝ (V × (ℝ × ℝ)) :=
  Q.prod (N c₁ c₂)

variable (Q : QuadraticForm ℝ V) (c₁ c₂ : ℝ)

/-- The first extra generator. -/
def a₁ : CliffordAlgebra (Qext Q c₁ c₂) := ι (Qext Q c₁ c₂) (0, (1, 0))

/-- The second extra generator. -/
def a₂ : CliffordAlgebra (Qext Q c₁ c₂) := ι (Qext Q c₁ c₂) (0, (0, 1))

/-- The volume element of the two extra directions. -/
def vol : CliffordAlgebra (Qext Q c₁ c₂) := a₁ Q c₁ c₂ * a₂ Q c₁ c₂

variable {Q c₁ c₂}

theorem a₁_def : a₁ Q c₁ c₂ = ι (Qext Q c₁ c₂) (0, ((1 : ℝ), (0 : ℝ))) := rfl

theorem a₂_def : a₂ Q c₁ c₂ = ι (Qext Q c₁ c₂) (0, ((0 : ℝ), (1 : ℝ))) := rfl

/-- Orthogonal vectors anticommute; this is the only sign rule the file uses. -/
theorem anticomm {x y : V × (ℝ × ℝ)} (h : polar (Qext Q c₁ c₂) x y = 0) :
    ι (Qext Q c₁ c₂) x * ι (Qext Q c₁ c₂) y = -(ι (Qext Q c₁ c₂) y * ι (Qext Q c₁ c₂) x) := by
  have hc := ι_mul_ι_comm (Q := Qext Q c₁ c₂) x y
  rw [h] at hc
  simpa using hc

theorem polar_inl_inr (v : V) (w : ℝ × ℝ) : polar (Qext Q c₁ c₂) (v, 0) (0, w) = 0 := by
  simp [Qext, polar_prod]

theorem anticomm_inl_inr (v : V) (w : ℝ × ℝ) :
    ι (Qext Q c₁ c₂) (v, 0) * ι (Qext Q c₁ c₂) (0, w)
      = -(ι (Qext Q c₁ c₂) (0, w) * ι (Qext Q c₁ c₂) (v, 0)) :=
  anticomm (polar_inl_inr v w)

theorem anticomm_a₁_a₂ : a₁ Q c₁ c₂ * a₂ Q c₁ c₂ = -(a₂ Q c₁ c₂ * a₁ Q c₁ c₂) := by
  refine anticomm ?_
  simp [Qext, polar, CliffordAlgebraQuaternion.Q_apply]

theorem swap_a₂_a₁ : a₂ Q c₁ c₂ * a₁ Q c₁ c₂ = -(a₁ Q c₁ c₂ * a₂ Q c₁ c₂) := by
  rw [anticomm_a₁_a₂, neg_neg]

theorem a₁_sq : a₁ Q c₁ c₂ * a₁ Q c₁ c₂ = algebraMap ℝ (CliffordAlgebra (Qext Q c₁ c₂)) c₁ := by
  rw [a₁_def, ι_sq_scalar]
  simp [Qext, CliffordAlgebraQuaternion.Q_apply]

theorem a₂_sq : a₂ Q c₁ c₂ * a₂ Q c₁ c₂ = algebraMap ℝ (CliffordAlgebra (Qext Q c₁ c₂)) c₂ := by
  rw [a₂_def, ι_sq_scalar]
  simp [Qext, CliffordAlgebraQuaternion.Q_apply]

/-- **`ω² = −c₁c₂`, with no hypothesis at all.** The `c₁ * c₂ ≠ 0` below is needed only to
invert it. -/
theorem vol_sq : vol Q c₁ c₂ * vol Q c₁ c₂
    = algebraMap ℝ (CliffordAlgebra (Qext Q c₁ c₂)) (-(c₁ * c₂)) := by
  calc vol Q c₁ c₂ * vol Q c₁ c₂
      = a₁ Q c₁ c₂ * ((a₂ Q c₁ c₂ * a₁ Q c₁ c₂) * a₂ Q c₁ c₂) := by simp only [vol, mul_assoc]
    _ = a₁ Q c₁ c₂ * ((-(a₁ Q c₁ c₂ * a₂ Q c₁ c₂)) * a₂ Q c₁ c₂) := by rw [swap_a₂_a₁]
    _ = -(a₁ Q c₁ c₂ * (a₁ Q c₁ c₂ * (a₂ Q c₁ c₂ * a₂ Q c₁ c₂))) := by
        simp only [neg_mul, mul_neg, mul_assoc]
    _ = algebraMap ℝ (CliffordAlgebra (Qext Q c₁ c₂)) (-(c₁ * c₂)) := by
        rw [a₂_sq, ← mul_assoc, a₁_sq, ← map_mul, map_neg]

/-- `ω` commutes with the first factor: two anticommutations cancel. -/
theorem vol_comm_inl (v : V) :
    ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ = vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0) := by
  have h₁ : ι (Qext Q c₁ c₂) (v, 0) * a₁ Q c₁ c₂ = -(a₁ Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0)) :=
    anticomm_inl_inr v (1, 0)
  have h₂ : ι (Qext Q c₁ c₂) (v, 0) * a₂ Q c₁ c₂ = -(a₂ Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0)) :=
    anticomm_inl_inr v (0, 1)
  calc ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂
      = (ι (Qext Q c₁ c₂) (v, 0) * a₁ Q c₁ c₂) * a₂ Q c₁ c₂ := by simp only [vol, mul_assoc]
    _ = (-(a₁ Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0))) * a₂ Q c₁ c₂ := by rw [h₁]
    _ = -(a₁ Q c₁ c₂ * (ι (Qext Q c₁ c₂) (v, 0) * a₂ Q c₁ c₂)) := by
        simp only [neg_mul, mul_assoc]
    _ = -(a₁ Q c₁ c₂ * (-(a₂ Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0)))) := by rw [h₂]
    _ = vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0) := by
        simp only [vol, mul_neg, neg_neg, mul_assoc]

theorem vol_mul_a₁ : vol Q c₁ c₂ * a₁ Q c₁ c₂ = -(a₁ Q c₁ c₂ * vol Q c₁ c₂) := by
  calc vol Q c₁ c₂ * a₁ Q c₁ c₂ = a₁ Q c₁ c₂ * (a₂ Q c₁ c₂ * a₁ Q c₁ c₂) := by
        simp only [vol, mul_assoc]
    _ = a₁ Q c₁ c₂ * (-(a₁ Q c₁ c₂ * a₂ Q c₁ c₂)) := by rw [swap_a₂_a₁]
    _ = -(a₁ Q c₁ c₂ * vol Q c₁ c₂) := by simp only [vol, mul_neg]

theorem vol_mul_a₂ : vol Q c₁ c₂ * a₂ Q c₁ c₂ = -(a₂ Q c₁ c₂ * vol Q c₁ c₂) := by
  have e1 : vol Q c₁ c₂ * a₂ Q c₁ c₂ = a₁ Q c₁ c₂ * algebraMap ℝ _ c₂ := by
    calc vol Q c₁ c₂ * a₂ Q c₁ c₂ = a₁ Q c₁ c₂ * (a₂ Q c₁ c₂ * a₂ Q c₁ c₂) := by
          simp only [vol, mul_assoc]
      _ = a₁ Q c₁ c₂ * algebraMap ℝ _ c₂ := by rw [a₂_sq]
  have e2 : a₂ Q c₁ c₂ * vol Q c₁ c₂ = -(a₁ Q c₁ c₂ * algebraMap ℝ _ c₂) := by
    calc a₂ Q c₁ c₂ * vol Q c₁ c₂ = (a₂ Q c₁ c₂ * a₁ Q c₁ c₂) * a₂ Q c₁ c₂ := by
          simp only [vol, mul_assoc]
      _ = (-(a₁ Q c₁ c₂ * a₂ Q c₁ c₂)) * a₂ Q c₁ c₂ := by rw [swap_a₂_a₁]
      _ = -(a₁ Q c₁ c₂ * (a₂ Q c₁ c₂ * a₂ Q c₁ c₂)) := by simp only [neg_mul, mul_assoc]
      _ = -(a₁ Q c₁ c₂ * algebraMap ℝ _ c₂) := by rw [a₂_sq]
  rw [e1, e2, neg_neg]

/-- `ω` anticommutes with the second factor. -/
theorem vol_anticomm_inr (w : ℝ × ℝ) :
    vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (0, w) = -(ι (Qext Q c₁ c₂) (0, w) * vol Q c₁ c₂) := by
  have hw : ((0 : V), w)
      = w.1 • ((0 : V), ((1 : ℝ), (0 : ℝ))) + w.2 • ((0 : V), ((0 : ℝ), (1 : ℝ))) := by
    ext <;> simp
  rw [hw, map_add, map_smul, map_smul]
  simp only [← a₁_def, ← a₂_def, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    vol_mul_a₁, vol_mul_a₂, smul_neg]
  abel

variable (Q c₁ c₂)

/-- `v ↦ ι (v,0) · ω`. -/
def fMap : V →ₗ[ℝ] CliffordAlgebra (Qext Q c₁ c₂) :=
  (LinearMap.mulRight ℝ (vol Q c₁ c₂)).comp
    ((ι (Qext Q c₁ c₂)).comp (LinearMap.inl ℝ V (ℝ × ℝ)))

theorem fMap_apply (v : V) : fMap Q c₁ c₂ v = ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ := rfl

/-- The whole point of the substitution: the sign of the square flips. -/
theorem fMap_sq (v : V) :
    fMap Q c₁ c₂ v * fMap Q c₁ c₂ v = algebraMap ℝ _ (((-(c₁ * c₂)) • Q) v) := by
  simp only [fMap_apply]
  calc ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ * (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂)
      = ι (Qext Q c₁ c₂) (v, 0) * (vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (v, 0)) * vol Q c₁ c₂ := by
        simp only [mul_assoc]
    _ = ι (Qext Q c₁ c₂) (v, 0) * (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂) * vol Q c₁ c₂ := by
        rw [← vol_comm_inl]
    _ = (ι (Qext Q c₁ c₂) (v, 0) * ι (Qext Q c₁ c₂) (v, 0)) * (vol Q c₁ c₂ * vol Q c₁ c₂) := by
        simp only [mul_assoc]
    _ = algebraMap ℝ _ (Qext Q c₁ c₂ (v, 0))
          * algebraMap ℝ _ (-(c₁ * c₂)) := by rw [ι_sq_scalar, vol_sq]
    _ = algebraMap ℝ _ (((-(c₁ * c₂)) • Q) v) := by
        rw [← map_mul]
        congr 1
        simp [Qext, mul_comm]

/-- The second factor's generators, unchanged. -/
def gMap : (ℝ × ℝ) →ₗ[ℝ] CliffordAlgebra (Qext Q c₁ c₂) :=
  (ι (Qext Q c₁ c₂)).comp (LinearMap.inr ℝ V (ℝ × ℝ))

theorem gMap_apply (w : ℝ × ℝ) : gMap Q c₁ c₂ w = ι (Qext Q c₁ c₂) (0, w) := rfl

theorem gMap_sq (w : ℝ × ℝ) :
    gMap Q c₁ c₂ w * gMap Q c₁ c₂ w = algebraMap ℝ _ (N c₁ c₂ w) := by
  rw [gMap_apply, ι_sq_scalar]
  simp [Qext]


/-- `Cl(−Q) → Cl(Q ⊥ ⟨c₁,c₂⟩)`. -/
def L : CliffordAlgebra ((-(c₁ * c₂)) • Q) →ₐ[ℝ] CliffordAlgebra (Qext Q c₁ c₂) :=
  CliffordAlgebra.lift _ ⟨fMap Q c₁ c₂, fMap_sq Q c₁ c₂⟩

/-- `Cl⟨c₁,c₂⟩ → Cl(Q ⊥ ⟨c₁,c₂⟩)`. -/
def R : CliffordAlgebra (N c₁ c₂) →ₐ[ℝ] CliffordAlgebra (Qext Q c₁ c₂) :=
  CliffordAlgebra.lift (N c₁ c₂) ⟨gMap Q c₁ c₂, gMap_sq Q c₁ c₂⟩

@[simp] theorem L_ι (v : V) :
    L Q c₁ c₂ (ι ((-(c₁ * c₂)) • Q) v) = ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ := by
  rw [L, CliffordAlgebra.lift_ι_apply, fMap_apply]

@[simp] theorem R_ι (w : ℝ × ℝ) :
    R Q c₁ c₂ (ι (N c₁ c₂) w) = ι (Qext Q c₁ c₂) (0, w) := by
  rw [R, CliffordAlgebra.lift_ι_apply, gMap_apply]

/-- **The two signs cancel.** `ω` anticommutes with the second factor, and orthogonality
anticommutes `ι (v,0)` past it; the product of the two signs is `+1`. -/
theorem commute_gen (v : V) (w : ℝ × ℝ) :
    Commute (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂) (ι (Qext Q c₁ c₂) (0, w)) := by
  change ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (0, w)
      = ι (Qext Q c₁ c₂) (0, w) * (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂)
  calc ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (0, w)
      = ι (Qext Q c₁ c₂) (v, 0) * (vol Q c₁ c₂ * ι (Qext Q c₁ c₂) (0, w)) := by rw [mul_assoc]
    _ = ι (Qext Q c₁ c₂) (v, 0) * -(ι (Qext Q c₁ c₂) (0, w) * vol Q c₁ c₂) := by
        rw [vol_anticomm_inr]
    _ = -(ι (Qext Q c₁ c₂) (v, 0) * ι (Qext Q c₁ c₂) (0, w) * vol Q c₁ c₂) := by
        simp only [mul_neg, mul_assoc]
    _ = -(-(ι (Qext Q c₁ c₂) (0, w) * ι (Qext Q c₁ c₂) (v, 0)) * vol Q c₁ c₂) := by
        rw [anticomm_inl_inr]
    _ = ι (Qext Q c₁ c₂) (0, w) * (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂) := by
        simp only [neg_mul, neg_neg, mul_assoc]

theorem commute_L_ι_R (v : V) (y : CliffordAlgebra (N c₁ c₂)) :
    Commute (L Q c₁ c₂ (ι ((-(c₁ * c₂)) • Q) v)) (R Q c₁ c₂ y) := by
  induction y using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact (Algebra.commutes r _).symm
  | ι w => rw [L_ι, R_ι]; exact commute_gen Q c₁ c₂ v w
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

theorem commute_L_R (x : CliffordAlgebra ((-(c₁ * c₂)) • Q))
    (y : CliffordAlgebra (N c₁ c₂)) : Commute (L Q c₁ c₂ x) (R Q c₁ c₂ y) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r _
  | ι v => exact commute_L_ι_R Q c₁ c₂ v y
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb

/-- `Cl(−Q) ⊗ Cl⟨c₁,c₂⟩ → Cl(Q ⊥ ⟨c₁,c₂⟩)`, out of the ORDINARY tensor product. -/
def T : CliffordAlgebra ((-(c₁ * c₂)) • Q) ⊗[ℝ] CliffordAlgebra (N c₁ c₂) →ₐ[ℝ]
      CliffordAlgebra (Qext Q c₁ c₂) :=
  Algebra.TensorProduct.lift (L Q c₁ c₂) (R Q c₁ c₂) (commute_L_R Q c₁ c₂)

@[simp] theorem T_tmul (x : CliffordAlgebra ((-(c₁ * c₂)) • Q))
    (y : CliffordAlgebra (N c₁ c₂)) :
    T Q c₁ c₂ (x ⊗ₜ[ℝ] y) = L Q c₁ c₂ x * R Q c₁ c₂ y :=
  Algebra.TensorProduct.lift_tmul (L Q c₁ c₂) (R Q c₁ c₂) (commute_L_R Q c₁ c₂) x y

/-- `ω` itself is in the range: it is a product of two second-factor generators. -/
theorem vol_mem_range : vol Q c₁ c₂ ∈ (T Q c₁ c₂).range :=
  ⟨1 ⊗ₜ[ℝ] (ι (N c₁ c₂) (1, 0) * ι (N c₁ c₂) (0, 1)), by simp [vol, a₁, a₂]⟩

theorem ι_inr_mem_range (w : ℝ × ℝ) :
    ι (Qext Q c₁ c₂) (0, w) ∈ (T Q c₁ c₂).range :=
  ⟨1 ⊗ₜ[ℝ] ι (N c₁ c₂) w, by simp⟩

/-- And the first-factor generators come back out, because `ω² = −c₁c₂` is **invertible**. This is
the only place the nonvanishing hypothesis is used. -/
theorem ι_inl_mem_range (hc : c₁ * c₂ ≠ 0) (v : V) :
    ι (Qext Q c₁ c₂) (v, 0) ∈ (T Q c₁ c₂).range := by
  have h : T Q c₁ c₂ ((ι ((-(c₁ * c₂)) • Q) v)
        ⊗ₜ[ℝ] (ι (N c₁ c₂) (1, 0) * ι (N c₁ c₂) (0, 1)))
      = algebraMap ℝ _ (-(c₁ * c₂)) * ι (Qext Q c₁ c₂) (v, 0) := by
    calc T Q c₁ c₂ ((ι ((-(c₁ * c₂)) • Q) v)
            ⊗ₜ[ℝ] (ι (N c₁ c₂) (1, 0) * ι (N c₁ c₂) (0, 1)))
        = (ι (Qext Q c₁ c₂) (v, 0) * vol Q c₁ c₂) * vol Q c₁ c₂ := by simp [vol, a₁, a₂]
      _ = ι (Qext Q c₁ c₂) (v, 0) * (vol Q c₁ c₂ * vol Q c₁ c₂) := by rw [mul_assoc]
      _ = algebraMap ℝ _ (-(c₁ * c₂)) * ι (Qext Q c₁ c₂) (v, 0) := by
          rw [vol_sq, Algebra.commutes]
  have hne : (-(c₁ * c₂)) ≠ 0 := neg_ne_zero.mpr hc
  have hmem : algebraMap ℝ (CliffordAlgebra (Qext Q c₁ c₂)) (-(c₁ * c₂))
      * ι (Qext Q c₁ c₂) (v, 0) ∈ (T Q c₁ c₂).range := ⟨_, h⟩
  have := Subalgebra.smul_mem (T Q c₁ c₂).range hmem (-(c₁ * c₂))⁻¹
  rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul] at this

theorem T_surjective (hc : c₁ * c₂ ≠ 0) : Function.Surjective (T Q c₁ c₂) := by
  have hgen : Set.range (ι (Qext Q c₁ c₂))
      ⊆ (((T Q c₁ c₂).range : Subalgebra ℝ _) : Set (CliffordAlgebra (Qext Q c₁ c₂))) := by
    rintro _ ⟨⟨v, w⟩, rfl⟩
    have hsplit : ((v, w) : V × (ℝ × ℝ)) = (v, 0) + (0, w) := by ext <;> simp
    rw [hsplit, map_add]
    exact add_mem (ι_inl_mem_range Q c₁ c₂ hc v) (ι_inr_mem_range Q c₁ c₂ w)
  have htop : (⊤ : Subalgebra ℝ (CliffordAlgebra (Qext Q c₁ c₂))) ≤ (T Q c₁ c₂).range := by
    rw [← CliffordAlgebra.adjoin_range_ι (Q := Qext Q c₁ c₂)]
    exact Algebra.adjoin_le hgen
  rw [← AlgHom.range_eq_top]
  exact top_le_iff.mp htop

variable [FiniteDimensional ℝ V]

theorem finrank_tensor :
    Module.finrank ℝ (CliffordAlgebra ((-(c₁ * c₂)) • Q) ⊗[ℝ] CliffordAlgebra (N c₁ c₂))
      = 2 ^ (Module.finrank ℝ V + 2) := by
  rw [Module.finrank_tensorProduct,
    CliffordDimension.finrank_cliffordAlgebra ℝ V ((-(c₁ * c₂)) • Q),
    CliffordDimension.finrank_cliffordAlgebra ℝ (ℝ × ℝ) (N c₁ c₂)]
  simp [pow_add]

theorem finrank_ext :
    Module.finrank ℝ (CliffordAlgebra (Qext Q c₁ c₂)) = 2 ^ (Module.finrank ℝ V + 2) := by
  rw [CliffordDimension.finrank_cliffordAlgebra ℝ (V × (ℝ × ℝ)) (Qext Q c₁ c₂),
    Module.finrank_prod]
  simp

theorem T_injective (hc : c₁ * c₂ ≠ 0) : Function.Injective (T Q c₁ c₂) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := CliffordAlgebra ((-(c₁ * c₂)) • Q) ⊗[ℝ] CliffordAlgebra (N c₁ c₂))
    (V₂ := CliffordAlgebra (Qext Q c₁ c₂))
    (by rw [finrank_tensor Q c₁ c₂, finrank_ext Q c₁ c₂])
    (f := (T Q c₁ c₂).toLinearMap)).2 (T_surjective Q c₁ c₂ hc)

/-- **The ungraded decomposition.** -/
def equivTensor (hc : c₁ * c₂ ≠ 0) :
    CliffordAlgebra (Qext Q c₁ c₂) ≃ₐ[ℝ]
      CliffordAlgebra ((-(c₁ * c₂)) • Q) ⊗[ℝ] CliffordAlgebra (N c₁ c₂) :=
  (AlgEquiv.ofBijective (T Q c₁ c₂)
    ⟨T_injective Q c₁ c₂ hc, T_surjective Q c₁ c₂ hc⟩).symm

/-- Transport a Clifford algebra along an equality of forms. -/
def congrQ {W : Type*} [AddCommGroup W] [Module ℝ W] {Q₁ Q₂ : QuadraticForm ℝ W}
    (h : Q₁ = Q₂) : CliffordAlgebra Q₁ ≃ₐ[ℝ] CliffordAlgebra Q₂ := h ▸ AlgEquiv.refl

omit [FiniteDimensional ℝ V] in
theorem smul_pos_case : (-((1 : ℝ) * 1)) • Q = -Q := by ext x; simp

omit [FiniteDimensional ℝ V] in
theorem smul_neg_case : (-((-1 : ℝ) * (-1))) • Q = -Q := by ext x; simp

/-- `Cl(Q ⊥ ⟨1,1⟩) ≅ Cl(−Q) ⊗ Cl(2,0)`: the step that adds `(2,0)` to the signature. -/
def equivTensorPos :
    CliffordAlgebra (Qext Q 1 1) ≃ₐ[ℝ] CliffordAlgebra (-Q) ⊗[ℝ] CliffordAlgebra (N 1 1) :=
  (equivTensor Q 1 1 (by norm_num)).trans
    (Algebra.TensorProduct.congr (congrQ (smul_pos_case Q)) AlgEquiv.refl)

/-- `Cl(Q ⊥ ⟨−1,−1⟩) ≅ Cl(−Q) ⊗ Cl(0,2)`: the step that adds `(0,2)`. Same construction, and
the reason the hypothesis is `c₁c₂ = 1` rather than `c₁ = c₂ = 1`. -/
def equivTensorNeg :
    CliffordAlgebra (Qext Q (-1) (-1)) ≃ₐ[ℝ]
      CliffordAlgebra (-Q) ⊗[ℝ] CliffordAlgebra (N (-1) (-1)) :=
  (equivTensor Q (-1) (-1) (by norm_num)).trans
    (Algebra.TensorProduct.congr (congrQ (smul_neg_case Q)) AlgEquiv.refl)

/-- `Cl⟨1,1⟩` is **literally** `CliffordRealTwoZero.Q₂₀` — the same term, not a transported one —
so this estate's `equivM2Real` applies with no work. -/
def rightM2 : CliffordAlgebra (N (1 : ℝ) 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordRealTwoZero.equivM2Real

/-- ...and `Cl⟨−1,−1⟩` is Mathlib's quaternion form. -/
def rightQuat : CliffordAlgebra (N (-1 : ℝ) (-1)) ≃ₐ[ℝ] ℍ[ℝ] :=
  CliffordAlgebraQuaternion.equiv (c₁ := (-1 : ℝ)) (c₂ := (-1 : ℝ))


/-- Replacing the second factor by `M₂(ℝ)`. -/
def congrM2 :
    CliffordAlgebra (-Q) ⊗[ℝ] CliffordAlgebra (N (1 : ℝ) 1) ≃ₐ[ℝ]
      CliffordAlgebra (-Q) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  Algebra.TensorProduct.congr AlgEquiv.refl rightM2

/-- Replacing the second factor by `ℍ`. -/
def congrQuat :
    CliffordAlgebra (-Q) ⊗[ℝ] CliffordAlgebra (N (-1 : ℝ) (-1)) ≃ₐ[ℝ]
      CliffordAlgebra (-Q) ⊗[ℝ] ℍ[ℝ] :=
  Algebra.TensorProduct.congr AlgEquiv.refl rightQuat

/-- **The matrix form of the positive step**: `Cl(Q ⊥ ⟨1,1⟩) ≅ M₂(Cl(−Q))`, with the matrix
factor absorbed by `matrixEquivTensor`. -/
def equivMatrixTwo :
    CliffordAlgebra (Qext Q 1 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra (-Q)) :=
  ((equivTensorPos Q).trans (congrM2 Q)).trans
    (matrixEquivTensor (Fin 2) ℝ (CliffordAlgebra (-Q))).symm

/-- **The quaternionic form of the negative step**: `Cl(Q ⊥ ⟨−1,−1⟩) ≅ Cl(−Q) ⊗ ℍ`. The asymmetry
is real rather than an artefact — `ℍ` is not a matrix algebra over `ℝ`, so this factor cannot be
absorbed the way the other one can, and that is exactly why the classical periodicity argument
needs `ℍ ⊗ ℍ ≅ M₄(ℝ)` (`QuaternionTensor.equivM4`) to close the cycle. -/
def equivQuatTwo :
    CliffordAlgebra (Qext Q (-1) (-1)) ≃ₐ[ℝ] CliffordAlgebra (-Q) ⊗[ℝ] ℍ[ℝ] :=
  (equivTensorNeg Q).trans (congrQuat Q)

/-! ### The hyperbolic step, as an instance of the same theorem

`c₁ = 1`, `c₂ = −1` gives `c₁c₂ = −1 ≠ 0`, so `ω² = +1` and the first factor is `1 • Q = Q` — **no
negation at all**. The second factor `⟨1,−1⟩` is the hyperbolic plane, whose Clifford algebra is
`M₂(ℝ)`. So `equivTensor` at that point reads `Cl(Q ⊥ ⟨1,−1⟩) ≅ M₂(Cl Q)`, which is
`CliffordPeriodicityHyperbolic.periodicityEquivHyp`.

**This is the whole reason the hypothesis was weakened from `c₁c₂ = 1` to `c₁c₂ ≠ 0`**: at
`c₁c₂ = 1` the three moves the reach analysis uses were two theorems and an import; at `c₁c₂ ≠ 0`
they are three instances of one. -/

omit [FiniteDimensional ℝ V] in
theorem one_smul_case : ((-((1 : ℝ) * (-1))) • Q) = Q := by ext x; simp

theorem sep_hyp : (QuadraticMap.associated (R := ℝ) (N 1 (-1))).SeparatingLeft := by
  refine CliffordRealSignatures.separatingLeft_of_sig ?_
  simp [N]
  norm_num

/-- **`Cl(Q ⊥ ⟨1,−1⟩) ≅ M₂(Cl Q)`, from `equivTensor` alone.** -/
theorem equivHyperbolic :
    Nonempty (CliffordAlgebra (Qext Q 1 (-1)) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) := by
  obtain ⟨e⟩ := CliffordRealSignatures.clifford_iso_M2R_of_sig (N 1 (-1)) sep_hyp
    (by simp) (by simp [N])
  refine ⟨((equivTensor Q 1 (-1) (by norm_num)).trans
    (Algebra.TensorProduct.congr (congrQ (one_smul_case Q)) e)).trans
      (matrixEquivTensor (Fin 2) ℝ (CliffordAlgebra Q)).symm⟩

end

end CliffordTensorTwo
