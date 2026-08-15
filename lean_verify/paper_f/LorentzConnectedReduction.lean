import LorentzIdentityComponent
import LorentzSurjectivity

/-!
# The Lorentz group is eliminated from its own last open statement

`LorentzIdentityComponent` proved one of the two inclusions of the identity-component
identification and left the other as a hypothesis on O(1,3) itself:

> `eq_of_isPreconnected (h : IsPreconnected (Splus : Set O13)) :
>    Subgroup.connectedComponentOfOne O13 = Splus`

**That hypothesis is nearly a restatement of the conclusion**, and saying so was the honest
reading of it. This file replaces it with a hypothesis about SL₂(ℂ) and nothing else:

> `identityComponent_eq (h : IsPreconnected (univ : Set SL2C)) :
>    Subgroup.connectedComponentOfOne O13 = Splus`

After this, **nothing in that watchlist item rests on an unproved fact about the Lorentz group.**
What it rests on is a standard fact about a standard Mathlib object, which Mathlib does not have.

## What makes the substitution legal

`LorentzSurjectivity.SOplus13_surjective` says every proper orthochronous Lorentz transformation
is `Λ(A)` for some `A ∈ SL₂(ℂ)`, and `LorentzGroup.lorentzUnit_mem_SOplus13` says every `Λ(A)` is
one. So SO⁺(1,3) is exactly the **range** of `toO13 : SL₂(ℂ) →* O(1,3)` (`range_toO13`), and a
preconnected space has preconnected continuous image.

The one thing that had to be proved rather than cited is **continuity of `Λ`**
(`continuous_lorentzMat`). It is not deep: `Λ(A)`'s entries are the Pauli coordinates of
`A · σ · Aᴴ` for the four constant Pauli matrices `σ`, so each entry is a real *quadratic*
polynomial in the real and imaginary parts of `A`'s entries.

**And it is not enough on its own.** Mathlib topologises a unit group by the embedding
`u ↦ (u, u⁻¹)`, so `Units.continuous_iff` asks for two things, and a map into GL₄(ℝ) needs the
matrix **and the inverse** to move continuously. The inverse half is `coe_inv_eq`: inverting
inside SL₂(ℂ) is taking the adjugate, because the determinant is `1`, so it is polynomial as
well. For GL₄(ℝ) that topology does in fact agree with the subspace topology from matrices —
inversion is continuous where the determinant does not vanish — but **that agreement is a theorem
this file neither proves nor uses**; it proves the second half directly instead, which is cheap
here and would not have been had `Λ` been defined on a group where inversion is not polynomial.

## What is still open, and it is now entirely outside this estate

**SL₂(ℂ) is connected.** Not proved here, and **not in this Mathlib**: probed 15 Aug 2026 by
`grep -rn` over `.lake/packages/mathlib/Mathlib/ --include=*.lean` for the three patterns
`ConnectedSpace.*SpecialLinearGroup`, `SpecialLinearGroup.*Connected` and
`PathConnected.*SpecialLinear`, zero matches between them.

The route, named so the leg is written down rather than gestured at:

1. every `A ∈ SL₂(ℂ)` is `(transvections) · diagonal · (transvections)` — Mathlib has this for
   any matrix over a field as
   `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`;
2. each transvection is joined to `1` by the path `t ↦ transvection i j (t·c)`, which stays in
   SL₂ because `Matrix.det_transvection_of_ne` gives every transvection determinant `1`;
3. a diagonal matrix of determinant one is `diag(λ, λ⁻¹)` with `λ ≠ 0`, and `ℂ \ {0}` is
   path-connected, so it too is joined to `1`;
4. `Subgroup.connectedComponentOfOne` is a subgroup — which is the whole reason steps 2 and 3
   suffice — so it contains every product of the above, hence all of SL₂(ℂ).

**Steps 2–4 are routine; step 1 is where the work is**, and the whole thing is a Mathlib
contribution about SL₂ over a field, not a fact about Lorentz transformations. It is recorded in
`UNLOCK_WATCHLIST` that way.

## What this file does NOT do

**It does not close the watchlist item.** `identityComponent_eq` carries a hypothesis and nothing
in this estate discharges it. **It does not give the item a consumer either** — nothing downstream
wanted the identification before and nothing wants it now; the item is being finished because it
was down to one statement, not because anything is waiting on it, and the two units together
should be read as *making a wall checkable*, in the sense `LovelockReduction` uses, rather than as
progress against a queue.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LorentzConnectedReduction

open Matrix LorentzGroup MinkowskiSignature MinkowskiHerm2 LorentzIdentityComponent Set

/-! ## 1. Λ is continuous

`lorentzMat_apply` reads off the `(i,j)` entry as the `i`-th Pauli coordinate of
`A · pauliHerm(eⱼ) · Aᴴ`. The middle factor is constant in `A`, and `pauliCoord` is a real-linear
combination of real and imaginary parts of four entries, so the composite is continuous.
-/

theorem continuous_lorentzMat_entry (i j : Fin 4) :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => lorentzMat A i j := by
  simp only [lorentzMat_apply, lorentzMap, pauliCoord]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    fun_prop

theorem continuous_lorentzMat :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => lorentzMat A :=
  continuous_matrix fun i j => continuous_lorentzMat_entry i j

/-! ## 2. Inverting inside SL₂(ℂ) is polynomial

Needed because the topology on GL₄(ℝ) is the one induced from `M ↦ (M, M⁻¹)`: a continuous map
into a unit group must move the inverse continuously too, and `Λ(A)⁻¹` is `Λ(A⁻¹)`.
-/

theorem coe_inv_eq (A : SL2C) :
    ((A⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = ((A : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ := by
  rw [Matrix.inv_def, Matrix.SpecialLinearGroup.det_coe, Ring.inverse_one, one_smul]
  exact Matrix.SpecialLinearGroup.coe_inv A

theorem continuous_coe_inv :
    Continuous fun A : SL2C => ((A : Matrix (Fin 2) (Fin 2) ℂ))⁻¹ := by
  simp only [← coe_inv_eq]
  fun_prop

/-! ## 3. The bundled map SL₂(ℂ) → O(1,3), and its continuity -/

/-- `Λ`, landing in the group O(1,3) rather than in GL₄(ℝ). Built from the estate's existing
`lorentzSOplusHom` rather than rebuilt. -/
noncomputable def toO13 : SL2C →* O13 :=
  (Subgroup.inclusion SOplus_le_O13).comp lorentzSOplusHom

theorem mat_toO13 (A : SL2C) :
    mat (toO13 A) = lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem continuous_toO13 : Continuous (toO13 : SL2C → O13) := by
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact continuous_lorentzMat.comp (by fun_prop)
  · exact continuous_lorentzMat.comp continuous_coe_inv

/-! ## 4. The image is exactly SO⁺(1,3)

Both inclusions are already theorems; this only packages them as an equality of sets, which is
the form the topology needs.
-/

theorem range_toO13 : Set.range (toO13 : SL2C → O13) = (Splus : Set O13) := by
  ext M
  constructor
  · rintro ⟨A, rfl⟩
    exact SetLike.mem_coe.2 (mem_Splus_iff.2 (lorentzUnit_mem_SOplus13 A.1 A.2))
  · intro hM
    obtain ⟨A, hA, heq⟩ := LorentzSurjectivity.SOplus13_surjective
      (M : Matrix.GeneralLinearGroup (Fin 4) ℝ) (mem_Splus_iff.1 (SetLike.mem_coe.1 hM))
    exact ⟨⟨A, hA⟩, Subtype.ext heq⟩

/-! ## 5. The reduction -/

theorem isPreconnected_Splus (h : IsPreconnected (univ : Set SL2C)) :
    IsPreconnected (Splus : Set O13) := by
  rw [← range_toO13, ← Set.image_univ]
  exact h.image _ continuous_toO13.continuousOn

/-- **THE IDENTIFICATION, REDUCED TO A STATEMENT ABOUT SL₂(ℂ).** No Lorentz group appears in the
hypothesis. -/
theorem identityComponent_eq (h : IsPreconnected (univ : Set SL2C)) :
    Subgroup.connectedComponentOfOne O13 = Splus :=
  eq_of_isPreconnected (isPreconnected_Splus h)

/-- The same statement in Mathlib's idiom, for whoever eventually supplies the instance. -/
theorem identityComponent_eq_of_preconnectedSpace [PreconnectedSpace SL2C] :
    Subgroup.connectedComponentOfOne O13 = Splus :=
  identityComponent_eq isPreconnected_univ

end LorentzConnectedReduction
