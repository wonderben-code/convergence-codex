import FieldCommutant
import FieldSignFlip
import GreenExpansion
import AdjSqForcesRegular

/-!
# A symmetry of the field on EVERY graph, connected ones included, and it is a reflection

The last three units chased an invariant isometry outside the permutations, the signs and their
composites. `FieldSignFlip` found one on **disconnected** graphs; `FieldSignFlipSharp` proved that
route reaches no further; `FieldCommutant` restated the hypothesis as *commutes with the propagator*
and named one route to the connected case — a rotation inside a degenerate eigenspace.

**A route was never needed, and neither was a degenerate eigenspace.** The all-ones vector is an
eigenvector of `green` at `m⁻²` **on every finite graph** — `GreenExpansion.green_mulVec_one`, which
this estate has had since 12 August and which `GreenNormExact`, `GreenQuadFormSharp` and
`LatticeRegularitySharp` have each used today. A symmetric operator therefore preserves both that
line and its orthogonal complement, so **the Householder reflection through the all-ones line
commutes with `green`** — at every graph, connected or not.

`ERRATUM 454` records that this is the **third** unit in a row whose fence named a route the answer
did not take.

## What is proved

**`house V = (2/|V|) · J − 1`** — reflection through the all-ones line: it fixes `1` and negates
everything orthogonal to it. **`house_isSymm`**, **`house_mul_house`** (`= 1`, so it is an
involution and an isometry), and **`house_mul_green_comm`** — it commutes with the propagator,
straight out of `GreenExpansion.green_mul_allOnes` and the propagator's symmetry.

**`houseIsometry`** — packaged as a `LinearIsometryEquiv` through the general
**`reflIsometry`**: *any* symmetric matrix squaring to `1` is one, with the norm coming from
`RayleighMatrix.mv_adjoint`.

**`gaussianField_map_house`** — **the Gaussian field is invariant under it**, at every finite
nonempty graph and every `m ≠ 0`, by `FieldCommutant.gaussianField_map_of_commutes`.

**`houseIsometry_ne_permField`**, **`houseIsometry_ne_negPermField`** and
**`houseIsometry_ne_signFlip`** — and at `3 ≤ |V|` it is in **none** of the three families, because
its off-diagonal entries are `2/|V| ∈ (0,1)` while every member of those families has entries in
`{0, 1, −1}`.

## What is NOT here

**No claim to have found the commutant.** One isometry outside the known families is exhibited;
nothing here describes all of them, and the rotations inside degenerate eigenspaces that
`FieldCommutant` named are still not built. **Not attempted, no cost claimed** (`ERRATUM 246`).

**Nothing about `|V| ≤ 2`.** At `|V| = 2` the matrix **is** the swap permutation and at `|V| = 1`
it is the identity, so the three separation theorems genuinely need `3 ≤ |V|` and say so.

**Not OS3 and not any OS axiom.** `FieldAutInvariance`'s disclaimer stands for this wider class too:
a wider shadow is not a smaller gap.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldHouseholder

open Matrix GraphLaplacian FieldAutInvariance FieldIsometryInvariance FieldCommutant
open RayleighMatrix GreenExpansion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Two bridges for the matrix action -/

theorem mv_one (x : EuclideanSpace ℝ V) : mv (1 : Matrix V V ℝ) x = x := by
  ext i
  rw [mv_row]
  simp [Matrix.one_apply]

omit [DecidableEq V] in
theorem mv_mul (A B : Matrix V V ℝ) (x : EuclideanSpace ℝ V) :
    mv (A * B) x = mv A (mv B x) := by
  ext i
  rw [mv_row, mv_row]
  simp only [mv_row, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-! ## 2. A symmetric involution is an isometry -/

/-- **ANY SYMMETRIC MATRIX SQUARING TO `1` IS A LINEAR ISOMETRY OF `EuclideanSpace`.** The norm
comes from `RayleighMatrix.mv_adjoint`: `⟪Mx, Mx⟫ = ⟪x, M²x⟫ = ⟪x, x⟫`. -/
noncomputable def reflIsometry {M : Matrix V V ℝ} (hsymm : M.IsSymm) (hinv : M * M = 1) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V where
  toFun := mv M
  invFun := mv M
  left_inv x := by rw [← mv_mul, hinv, mv_one]
  right_inv x := by rw [← mv_mul, hinv, mv_one]
  map_add' := mv_add (A := M)
  map_smul' c x := mv_smul (A := M) c x
  norm_map' x := by
    have hher : M.IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hsymm
    have h : inner ℝ (mv M x) (mv M x) = inner ℝ x x := by
      rw [← mv_adjoint hher, ← mv_mul, hinv, mv_one]
    have h1 : ‖mv M x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact h
    have := abs_eq_abs.mpr (Or.inl (by
      nlinarith [h1, norm_nonneg (mv M x), norm_nonneg x] : ‖mv M x‖ = ‖x‖))
    simpa using this

@[simp] theorem reflIsometry_apply {M : Matrix V V ℝ} (hsymm : M.IsSymm) (hinv : M * M = 1)
    (x : EuclideanSpace ℝ V) : reflIsometry hsymm hinv x = mv M x := by
  rfl

/-- **AND IF IT COMMUTES WITH THE PROPAGATOR IT IS A SYMMETRY OF THE FIELD.** -/
theorem gaussianField_map_reflIsometry (hm : m ≠ 0) {M : Matrix V V ℝ} (hsymm : M.IsSymm)
    (hinv : M * M = 1) (hcomm : M * green G m = green G m * M) :
    MeasureTheory.Measure.map (reflIsometry hsymm hinv) (gaussianField G m)
      = gaussianField G m := by
  refine gaussianField_map_of_commutes hm fun x => ?_
  rw [reflIsometry_apply, reflIsometry_apply, ← mv_mul, ← mv_mul, hcomm]

/-! ## 3. The reflection through the all-ones line -/

/-- **REFLECTION THROUGH THE ALL-ONES LINE**: it fixes `1` and negates its orthogonal complement. -/
noncomputable def house (V : Type*) [Fintype V] [DecidableEq V] : Matrix V V ℝ :=
  (2 / (Fintype.card V : ℝ)) • allOnes V - 1

theorem house_isSymm : (house V).IsSymm := by
  rw [house]
  refine Matrix.IsSymm.sub ?_ (Matrix.isSymm_one)
  refine Matrix.IsSymm.smul ?_ _
  ext p q
  simp [allOnes, Matrix.transpose_apply]

theorem house_mul_house [Nonempty V] : house V * house V = 1 := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hkey : (2 / (Fintype.card V : ℝ)) * (2 / (Fintype.card V : ℝ)) * (Fintype.card V : ℝ)
      = 2 * (2 / (Fintype.card V : ℝ)) := by
    field_simp
  rw [house, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    AdjSqForcesRegular.allOnes_mul_allOnes, Matrix.one_mul, Matrix.mul_one, smul_smul,
    smul_smul, hkey]
  simp only [Matrix.one_mul]
  module

/-! ## 4. It commutes with the propagator, at every graph -/

theorem allOnes_mul_green (hm : m ≠ 0) :
    allOnes V * green G m = (m ^ 2)⁻¹ • allOnes V := by
  have h := green_mul_allOnes (G := G) (m := m) hm
  have hg : (green G m).IsSymm := green_isSymm G hm
  have hJ : (allOnes V).IsSymm := by ext p q; simp [allOnes, Matrix.transpose_apply]
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, hJ, hg, Matrix.transpose_smul, hJ] at this

/-- **THE REFLECTION COMMUTES WITH THE PROPAGATOR, ON EVERY FINITE GRAPH.** The all-ones vector is
an eigenvector of `green` at `m⁻²` (`GreenExpansion.green_mulVec_one`), so a symmetric operator
preserves both its line and its complement. -/
theorem house_mul_green_comm (hm : m ≠ 0) :
    house V * green G m = green G m * house V := by
  rw [house, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    green_mul_allOnes hm, allOnes_mul_green hm, Matrix.one_mul, Matrix.mul_one]

/-- **THE GAUSSIAN FIELD IS INVARIANT UNDER IT**, at every finite nonempty graph and `m ≠ 0`. -/
theorem gaussianField_map_house [Nonempty V] (hm : m ≠ 0) :
    MeasureTheory.Measure.map (reflIsometry (house_isSymm (V := V)) house_mul_house)
        (gaussianField G m)
      = gaussianField G m :=
  gaussianField_map_reflIsometry hm _ _ (house_mul_green_comm hm)

/-! ## 5. And it is in none of the three known families -/

theorem house_apply (p q : V) :
    house V p q = 2 / (Fintype.card V : ℝ) - (if p = q then 1 else 0) := by
  simp [house, allOnes, Matrix.one_apply]

/-- The reflection as a named isometry. -/
noncomputable def houseIsometry (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
  reflIsometry (house_isSymm (V := V)) house_mul_house

/-- Its action on a basis vector reads off a column of the matrix. -/
theorem houseIsometry_single [Nonempty V] (p q : V) :
    houseIsometry V (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q = house V q p := by
  rw [houseIsometry, reflIsometry_apply, mv_row]
  rw [Finset.sum_eq_single p (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

/-- Off the diagonal the entry is `2/|V|`, which at `3 ≤ |V|` lies strictly between `0` and `1`. -/
theorem houseIsometry_single_ne [Nonempty V] {p q : V} (hpq : q ≠ p) :
    houseIsometry V (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q = 2 / (Fintype.card V : ℝ) := by
  rw [houseIsometry_single, house_apply, if_neg hpq, sub_zero]

omit [DecidableEq V] in
private theorem two_div_card_mem [Nonempty V] (h3 : 3 ≤ Fintype.card V) :
    0 < 2 / (Fintype.card V : ℝ) ∧ 2 / (Fintype.card V : ℝ) < 1 := by
  have hc : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- **NOT A RELABELLING.** -/
theorem houseIsometry_ne_permField [Nonempty V] (h3 : 3 ≤ Fintype.card V) (ψ : V ≃ V) :
    houseIsometry V ≠ permField ψ := by
  obtain ⟨hpos, hlt⟩ := two_div_card_mem (V := V) h3
  obtain ⟨p⟩ := ‹Nonempty V›
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  intro hcontra
  have h := DFunLike.congr_fun hcontra (WithLp.toLp 2 (Pi.single p (1 : ℝ)))
  have hval : houseIsometry V (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q
      = permField ψ (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q := by rw [h]
  rw [houseIsometry_single_ne hq, permField_apply] at hval
  simp only [Pi.single_apply] at hval
  split_ifs at hval <;> linarith

/-- **AND NOT A RELABELLING COMPOSED WITH THE GLOBAL SIGN FLIP.** -/
theorem houseIsometry_ne_negPermField [Nonempty V] (h3 : 3 ≤ Fintype.card V) (ψ : V ≃ V) :
    houseIsometry V ≠ (permField ψ).trans (LinearIsometryEquiv.neg ℝ) := by
  obtain ⟨hpos, hlt⟩ := two_div_card_mem (V := V) h3
  obtain ⟨p⟩ := ‹Nonempty V›
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  intro hcontra
  have h := DFunLike.congr_fun hcontra (WithLp.toLp 2 (Pi.single p (1 : ℝ)))
  have hright : ((permField ψ).trans (LinearIsometryEquiv.neg ℝ))
      (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q
      = -(permField ψ (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q) := rfl
  have hval : houseIsometry V (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q
      = ((permField ψ).trans (LinearIsometryEquiv.neg ℝ))
        (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q := by rw [h]
  rw [houseIsometry_single_ne hq, hright, permField_apply] at hval
  simp only [Pi.single_apply] at hval
  split_ifs at hval <;> linarith

/-- **AND NOT A SIGN FLIP.** -/
theorem houseIsometry_ne_signFlip [Nonempty V] (h3 : 3 ≤ Fintype.card V) (s : Finset V) :
    houseIsometry V ≠ FieldSignFlip.signFlip s := by
  obtain ⟨hpos, hlt⟩ := two_div_card_mem (V := V) h3
  obtain ⟨p⟩ := ‹Nonempty V›
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card (by omega) p
  intro hcontra
  have h := DFunLike.congr_fun hcontra (WithLp.toLp 2 (Pi.single p (1 : ℝ)))
  have hval : houseIsometry V (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q
      = FieldSignFlip.signFlip s (WithLp.toLp 2 (Pi.single p (1 : ℝ))) q := by rw [h]
  rw [houseIsometry_single_ne hq, FieldSignFlip.signFlip_apply] at hval
  simp only [Pi.single_apply, if_neg hq] at hval
  split_ifs at hval <;> linarith

end FieldHouseholder
