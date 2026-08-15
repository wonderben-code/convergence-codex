import LorentzConnectedReduction
import Mathlib.Tactic.LinearCombination

/-!
# SL₂(ℂ) is connected, and the identity component of O(1,3) is SO⁺(1,3)

`LorentzConnectedReduction` reduced the identity-component identification to one statement,
recorded it as *"a Mathlib contribution, not an estate task"*, and named a four-step route to it.
**That sizing was wrong, and this file is the correction.**

## Why the route was named badly, which is the finding

The route I wrote down went through Mathlib's general transvection machinery: any matrix over a
field is `(transvections) · diagonal · (transvections)`
(`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`), then connect the pieces to
`1`. I called step 1 *"where the work is"* — **and step 1 is a citation, not work.** What is
actually expensive in that route is everything around it: lifting a `List`-of-`TransvectionStruct`
decomposition into the subtype `SL₂(ℂ)`, proving the diagonal factor has determinant one, and
handling `diag(λ, λ⁻¹)` separately.

**At `n = 2` none of that is needed, because the decomposition is a three-term formula.** For
`A = !![a,b;c,d]` with `c ≠ 0`,

    A  =  upper ((a−1)/c) · lower c · upper ((d−1)/c)

and the only place `det A = 1` is spent is the `(0,1)` entry, where `ad − 1 = bc`. When `c = 0`
one right multiplication by `lower 1` makes it nonzero, because `ad = 1` forces `d ≠ 0`. No
transvection API, no diagonal case, no `ℂ \ {0}` path-connectedness. **`PROOF_STRATEGY` §6's
second question asks which wall is one hard step wearing easy ones as a disguise; this was the
reverse — an easy step I had dressed as a hard one by planning it in the wrong generality.**

## What is proved

* `upper_mem`, `lower_mem` — each elementary matrix lies in the identity component, because
  `t ↦ upper (t·x)` is a continuous map from `ℝ` (preconnected) whose image contains `1` and it.
* `mem_component` — **every** element of SL₂(ℂ) lies in the identity component, by the
  decomposition above and the fact that `Subgroup.connectedComponentOfOne` is a subgroup.
* `isPreconnected_univ`, and the `PreconnectedSpace` instance.
* `identityComponent_eq` — **and therefore, unconditionally, the identity component of O(1,3) is
  SO⁺(1,3).** `LorentzConnectedReduction.identityComponent_eq` had this waiting on exactly the
  hypothesis §1–§4 now discharge.

## What this closes and what it does not

**It closes the `UNLOCK_WATCHLIST` item "the O(1,3)/SO⁺(1,3) groups as MATHLIB-STYLE objects"**,
whose `BLOCKED ON` line names three things — a `MonoidHom SL₂(ℂ) →* SOplus13`, a `MulAction` on
`Herm₂`, and this identification — of which the first two closed on 1 Aug 2026 and the third was
the sole residue from that day on. It fires the trigger written for that item **hours earlier the
same day** — *"Mathlib gains connectedness of `SpecialLinearGroup (Fin 2) ℂ`, **or someone proves
it here**"* — by its second clause. **That interval is the point of this header**: the sentence
declaring the work out of scope and the file doing it are the same afternoon's output.

**It does not generalise.** The argument is `2 × 2` throughout: the three-term formula, the
`c = 0` repair and the determinant bookkeeping all use the shape of a `2 × 2` matrix. Nothing here
says anything about `SLₙ(ℂ)` for `n ≥ 3`, and the transvection route is what that would need —
stated as what is missing rather than as what is true elsewhere, since this estate has not
checked it.

**And the identification still has no consumer.** Nothing downstream of `O13` asks which of its
elements are connected to the identity; the item is finished because it was down to one statement,
not because anything was waiting. Said again here because three units in a row have now been spent
on it and that is exactly the situation in which a project talks itself into believing otherwise.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SL2Connected

open Matrix LorentzGroup

/-! ## 1. The two elementary matrices -/

/-- `!![1, x; 0, 1]`, as an element of SL₂(ℂ). -/
noncomputable def upper (x : ℂ) : SL2C := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- `!![1, 0; x, 1]`, as an element of SL₂(ℂ). -/
noncomputable def lower (x : ℂ) : SL2C := ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem upper_zero : upper 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

@[simp] theorem lower_zero : lower 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower]

/-! ## 2. Each elementary matrix is connected to the identity

The path is the obvious one and the argument is the estate's usual shape: a continuous map out of
a preconnected space lands inside a single connected component, so both endpoints share one.
-/

theorem continuous_upper (x : ℂ) : Continuous fun t : ℝ => upper ((t : ℂ) * x) := by
  refine continuous_induced_rng.2 (continuous_matrix fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp only [upper, Fin.zero_eta, Fin.isValue, Fin.mk_one, Function.comp_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;>
    fun_prop

theorem continuous_lower (x : ℂ) : Continuous fun t : ℝ => lower ((t : ℂ) * x) := by
  refine continuous_induced_rng.2 (continuous_matrix fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp only [lower, Fin.zero_eta, Fin.isValue, Fin.mk_one, Function.comp_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;>
    fun_prop

theorem upper_mem (x : ℂ) : upper x ∈ Subgroup.connectedComponentOfOne SL2C := by
  have hpre : IsPreconnected ((fun t : ℝ => upper ((t : ℂ) * x)) '' Set.univ) :=
    isPreconnected_univ.image _ (continuous_upper x).continuousOn
  have h1 : (1 : SL2C) ∈ (fun t : ℝ => upper ((t : ℂ) * x)) '' Set.univ :=
    ⟨0, Set.mem_univ _, by simp⟩
  exact hpre.subset_connectedComponent h1 ⟨1, Set.mem_univ _, by simp⟩

theorem lower_mem (x : ℂ) : lower x ∈ Subgroup.connectedComponentOfOne SL2C := by
  have hpre : IsPreconnected ((fun t : ℝ => lower ((t : ℂ) * x)) '' Set.univ) :=
    isPreconnected_univ.image _ (continuous_lower x).continuousOn
  have h1 : (1 : SL2C) ∈ (fun t : ℝ => lower ((t : ℂ) * x)) '' Set.univ :=
    ⟨0, Set.mem_univ _, by simp⟩
  exact hpre.subset_connectedComponent h1 ⟨1, Set.mem_univ _, by simp⟩

/-! ## 3. The three-term decomposition

The one place `det A = 1` is spent is the `(0,1)` entry: there the computation produces
`(a·d − 1)/c`, and `a·d − 1 = b·c` is exactly the determinant relation.
-/

/-- The product of the three elementary matrices, computed once for arbitrary entries. Keeping
this separate from the determinant bookkeeping is what makes the next proof one line per entry. -/
theorem upper_mul_lower_mul_upper (x c y : ℂ) :
    ((upper x * lower c * upper y : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
      = !![1 + x * c, (1 + x * c) * y + x; c, c * y + 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_prod_of_ne_zero (A : SL2C) (hc : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0) :
    A = upper (((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - 1) / (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
        * lower ((A : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
        * upper (((A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - 1)
            / (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [upper_mul_lower_mul_upper]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp
  · -- (0,0): `1 + ((a−1)/c)·c = a`, and the division cancels because `c ≠ 0`
    field_simp
    ring
  · -- (0,1): the only entry that spends the determinant, as `a·d − 1 = b·c`
    field_simp
    linear_combination -hdet
  · -- (1,1): `c·((d−1)/c) + 1 = d`
    field_simp
    ring

/-! ## 4. Every element is in the identity component -/

theorem mem_component (A : SL2C) : A ∈ Subgroup.connectedComponentOfOne SL2C := by
  -- the case that does the work
  have key : ∀ B : SL2C, (B : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 →
      B ∈ Subgroup.connectedComponentOfOne SL2C := by
    intro B hB
    rw [eq_prod_of_ne_zero B hB]
    exact mul_mem (mul_mem (upper_mem _) (lower_mem _)) (upper_mem _)
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · -- `a·d = 1` forces `d ≠ 0`, and right multiplication by `lower 1` moves `d` into the corner
    have hdet : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        - (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
      have := A.2
      rwa [Matrix.det_fin_two] at this
    have hd : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      intro h
      rw [h, hc] at hdet
      simp at hdet
    have hcorner : ((A * lower 1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simpa [lower, Matrix.mul_apply, Fin.sum_univ_two, hc] using hd
    have hsplit : A = (A * lower 1) * (lower 1)⁻¹ := by group
    rw [hsplit]
    exact mul_mem (key _ hcorner) (inv_mem (lower_mem 1))
  · exact key A hc

/-! ## 5. Therefore SL₂(ℂ) is connected -/

theorem connectedComponentOfOne_eq_top :
    Subgroup.connectedComponentOfOne SL2C = ⊤ :=
  eq_top_iff.mpr fun A _ => mem_component A

theorem isPreconnected_univ_SL2C : IsPreconnected (Set.univ : Set SL2C) := by
  have h : connectedComponent (1 : SL2C) = Set.univ :=
    Set.eq_univ_of_forall mem_component
  rw [← h]
  exact isPreconnected_connectedComponent

instance : PreconnectedSpace SL2C :=
  ⟨isPreconnected_univ_SL2C⟩

/-! ## 6. The payoff, unconditional

`LorentzConnectedReduction.identityComponent_eq` had been waiting on exactly this.
-/

/-- **THE IDENTITY COMPONENT OF O(1,3) IS SO⁺(1,3).** No hypothesis. -/
theorem identityComponent_eq :
    Subgroup.connectedComponentOfOne O13 = LorentzIdentityComponent.Splus :=
  LorentzConnectedReduction.identityComponent_eq isPreconnected_univ_SL2C

end SL2Connected
