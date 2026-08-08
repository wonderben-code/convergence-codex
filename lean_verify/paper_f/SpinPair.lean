/-
  SpinPair.lean — every suitably normalised pair of vectors gives a spin
  element, and its action is the composite of two reflections.

  WHY: PROOF_STRATEGY §7.3, deepen rather than broaden — take a result
  proved under restrictive hypotheses and remove one. The estate's spin
  chain contains exactly TWO spin elements, and both were written down
  in hand-picked coordinates: `R₁₂ = ι(e₁)·ι(e₂)` in `SpinVectorRep`
  and `B = ι(e₀)·ι(w)` with `w = (5/4,3/4,0,0)` in `SpinBoost`. Each was
  built to answer a specific question — is the representation
  non-trivial, is the group Lorentzian — and each carried its own
  membership proof, its own conjugation computation, and its own
  literal arithmetic.

  That is a fence. Both are instances of one construction: a product of
  two vectors whose quadratic forms multiply to 1. This file proves the
  general case, so the estate has a family instead of two examples, and
  the two examples become one-line corollaries.

  WHAT THIS FILE PROVES:
  1. `vecUnit` — a vector with `Q₁₃ v ≠ 0` gives a unit of the Clifford
     algebra, with `(Q₁₃ v)⁻¹ • ι v` as its inverse.
  2. **`pair_mem`** — for ANY `v, w` with `Q₁₃ v · Q₁₃ w = 1`, the
     product `ι(v)·ι(w)` is a spin element. The hypothesis is exactly
     the one that makes the unitarity check work, and it is satisfied
     by two spacelike unit vectors (`(−1)(−1)`) and by two timelike
     ones (`(+1)(+1)` — the boost case) and by no mixed pair.
  3. **`vreflect`** — the conjugation action of a single vector, as the
     reflection `u ↦ (polar(v,u)/Q₁₃ v)·v − u`, with `conj_vecUnit`.
  4. **`spinToEndo_pair`** — the action of `pair v w` on ℝ⁴ is
     `vreflect v ∘ vreflect w`, for every admissible pair. The two
     existing computations in `SpinVectorRep` and `SpinBoost` are
     instances.
  5. `vreflect_preserves` — each reflection is an isometry, so the
     general statement carries the property the special cases had.
  6. `R₁₂_eq_pair` and `B_eq_pair` — the two hand-built elements really
     are instances, so this genuinely subsumes them rather than sitting
     alongside them.
  7. **`vreflect_comp_rotXY` and `vreflect_comp_boostTX`** — added by
     review round 23, and they are the point. Items 6 say the GROUP
     ELEMENTS coincide; that is not the same as the ACTIONS coinciding,
     since `spinToEndo_pair` computes through `vreflect ∘ vreflect`
     while `SpinVectorRep` and `SpinBoost` computed `rotXY` and
     `boostTX` by entirely different routes. These two say the actions
     agree, so the generalisation is the same map and not a different
     one wearing the same name.

  WHAT THIS DOES NOT DO. It adds no new information about the IMAGE of
  the representation. A family of elements is still not a
  determination of the group they generate, and W7 step (d)'s two
  remaining parts — image inside SO⁺(1,3), surjectivity onto it — are
  untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import SpinVectorRep
import SpinBoost

open CliffordAlgebra CliffordRealMinkowski SpinVectorRep

noncomputable section

namespace SpinPair

/-! ## 1. A non-null vector is a unit -/

/-- A vector with `Q₁₃ v ≠ 0` is invertible in the Clifford algebra,
    with inverse `v / Q₁₃ v`. -/
def vecUnit (v : V) (hv : Q₁₃ v ≠ 0) : Clˣ where
  val := ι Q₁₃ v
  inv := (Q₁₃ v)⁻¹ • ι Q₁₃ v
  val_inv := by
    rw [mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ hv, one_smul]
  inv_val := by
    rw [smul_mul_assoc, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ hv, one_smul]

@[simp] theorem vecUnit_val (v : V) (hv : Q₁₃ v ≠ 0) :
    ((vecUnit v hv : Clˣ) : Cl) = ι Q₁₃ v := rfl

@[simp] theorem vecUnit_inv (v : V) (hv : Q₁₃ v ≠ 0) :
    (((vecUnit v hv)⁻¹ : Clˣ) : Cl) = (Q₁₃ v)⁻¹ • ι Q₁₃ v := rfl

theorem vecUnit_mem (v : V) (hv : Q₁₃ v ≠ 0) : vecUnit v hv ∈ lipschitzGroup Q₁₃ :=
  Subgroup.subset_closure ⟨v, rfl⟩

/-! ## 2. The pair, and when it is a spin element -/

/-- The product of two non-null vectors, as a unit. -/
def pair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0) : Clˣ :=
  vecUnit v hv * vecUnit w hw

theorem pair_val {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0) :
    ((pair hv hw : Clˣ) : Cl) = ι Q₁₃ v * ι Q₁₃ w := rfl

theorem pair_inv {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0) :
    (((pair hv hw)⁻¹ : Clˣ) : Cl)
      = (((vecUnit w hw)⁻¹ : Clˣ) : Cl) * (((vecUnit v hv)⁻¹ : Clˣ) : Cl) := rfl

/-- **The general membership.** `Q₁₃ v · Q₁₃ w = 1` is exactly what the
    unitarity check needs. Two spacelike unit vectors give `(−1)(−1)`,
    two timelike ones give `(+1)(+1)`, and a mixed pair gives `−1` and
    fails — which is `SpinBoost.mixed_pair_not_mem`. -/
theorem pair_mem {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) : ((pair hv hw : Clˣ) : Cl) ∈ spinGroup Q₁₃ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact lipschitzGroup.coe_mem_iff_mem.2
      (mul_mem (vecUnit_mem v hv) (vecUnit_mem w hw))
  · change star (ι Q₁₃ v * ι Q₁₃ w) * (ι Q₁₃ v * ι Q₁₃ w) = 1
    rw [star_mul, star_ι, star_ι]
    calc -ι Q₁₃ w * -ι Q₁₃ v * (ι Q₁₃ v * ι Q₁₃ w)
        = ι Q₁₃ w * ((ι Q₁₃ v * ι Q₁₃ v) * ι Q₁₃ w) := by
          simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = 1 := by
          rw [ι_sq_scalar, Algebra.commutes, ← mul_assoc, ι_sq_scalar, ← map_mul,
            mul_comm (Q₁₃ w), hprod, map_one]
  · change (ι Q₁₃ v * ι Q₁₃ w) * star (ι Q₁₃ v * ι Q₁₃ w) = 1
    rw [star_mul, star_ι, star_ι]
    calc ι Q₁₃ v * ι Q₁₃ w * (-ι Q₁₃ w * -ι Q₁₃ v)
        = ι Q₁₃ v * ((ι Q₁₃ w * ι Q₁₃ w) * ι Q₁₃ v) := by
          simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = 1 := by
          rw [ι_sq_scalar, Algebra.commutes, ← mul_assoc, ι_sq_scalar, ← map_mul,
            hprod, map_one]
  · exact ι_mul_ι_mem_evenOdd_zero Q₁₃ v w

/-! ## 3. The action is a composite of two reflections -/

/-- The conjugation action of a single non-null vector: the reflection
    `u ↦ (polar(v,u)/Q₁₃ v)·v − u`. -/
def vreflect (v : V) (u : V) : V :=
  (Q₁₃ v)⁻¹ • (QuadraticMap.polar Q₁₃ v u • v - Q₁₃ v • u)

theorem conj_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) (u : V) :
    ι Q₁₃ v * ι Q₁₃ u * (((vecUnit v hv)⁻¹ : Clˣ) : Cl) = ι Q₁₃ (vreflect v u) := by
  change ι Q₁₃ v * ι Q₁₃ u * ((Q₁₃ v)⁻¹ • ι Q₁₃ v) = _
  rw [mul_smul_comm, ι_mul_ι_mul_ι, ← map_smul]
  rfl

/-- **The action of an admissible pair, in general.** Both hand-built
    computations in `SpinVectorRep` and `SpinBoost` are instances. -/
theorem conj_pair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0) (u : V) :
    ((pair hv hw : Clˣ) : Cl) * ι Q₁₃ u * (((pair hv hw)⁻¹ : Clˣ) : Cl)
      = ι Q₁₃ (vreflect v (vreflect w u)) := by
  rw [pair_val, pair_inv]
  calc ι Q₁₃ v * ι Q₁₃ w * ι Q₁₃ u
        * ((((vecUnit w hw)⁻¹ : Clˣ) : Cl) * (((vecUnit v hv)⁻¹ : Clˣ) : Cl))
      = ι Q₁₃ v * (ι Q₁₃ w * ι Q₁₃ u * (((vecUnit w hw)⁻¹ : Clˣ) : Cl))
          * (((vecUnit v hv)⁻¹ : Clˣ) : Cl) := by
        simp only [mul_assoc]
    _ = ι Q₁₃ v * ι Q₁₃ (vreflect w u) * (((vecUnit v hv)⁻¹ : Clˣ) : Cl) := by
        rw [conj_vecUnit hw u]
    _ = ι Q₁₃ (vreflect v (vreflect w u)) := conj_vecUnit hv _

theorem spinToEndo_pair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) (u : V) :
    spinToEndo (pair_mem hv hw hprod) u = vreflect v (vreflect w u) := by
  apply ι_injective
  rw [ι_spinToEndo, conj_pair]

/-- Each reflection is an isometry. -/
theorem vreflect_preserves {v : V} (hv : Q₁₃ v ≠ 0) (u : V) :
    Q₁₃ (vreflect v u) = Q₁₃ u := by
  apply FaithfulSMul.algebraMap_injective ℝ Cl
  have key : ι Q₁₃ (vreflect v u) * ι Q₁₃ (vreflect v u)
      = algebraMap ℝ Cl (Q₁₃ u) := by
    rw [← conj_vecUnit hv u]
    change ((vecUnit v hv : Clˣ) : Cl) * ι Q₁₃ u * (((vecUnit v hv)⁻¹ : Clˣ) : Cl)
        * (((vecUnit v hv : Clˣ) : Cl) * ι Q₁₃ u * (((vecUnit v hv)⁻¹ : Clˣ) : Cl))
      = algebraMap ℝ Cl (Q₁₃ u)
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, ← mul_assoc (ι Q₁₃ u), ι_sq_scalar,
      Algebra.commutes, Units.mul_inv_cancel_left]
  rw [← ι_sq_scalar, key]

/-! ## 4. The two hand-built elements are instances -/

theorem Q₁₃_e₁_ne : Q₁₃ e₁ ≠ 0 := by rw [Q₁₃_e₁]; norm_num
theorem Q₁₃_e₂_ne : Q₁₃ e₂ ≠ 0 := by rw [Q₁₃_e₂]; norm_num
theorem Q₁₃_e₀_ne : Q₁₃ e₀ ≠ 0 := by rw [Q₁₃_e₀]; norm_num
theorem Q₁₃_w_ne : Q₁₃ SpinBoost.w ≠ 0 := by rw [SpinBoost.Q₁₃_w]; norm_num

theorem prod_e₁_e₂ : Q₁₃ e₁ * Q₁₃ e₂ = 1 := by rw [Q₁₃_e₁, Q₁₃_e₂]; norm_num
theorem prod_e₀_w : Q₁₃ e₀ * Q₁₃ SpinBoost.w = 1 := by
  rw [Q₁₃_e₀, SpinBoost.Q₁₃_w]; norm_num

/-- The π-rotation is an instance. -/
theorem R₁₂_eq_pair : pair Q₁₃_e₁_ne Q₁₃_e₂_ne = R₁₂ := Units.ext rfl

/-- And so is the boost. -/
theorem B_eq_pair : pair Q₁₃_e₀_ne Q₁₃_w_ne = SpinBoost.B := Units.ext rfl

/-! ## 5. The reflections in coordinates, and the two cross-checks

Review round 23's fold. §4 shows the group elements coincide with the
two hand-built ones; that leaves open whether the ACTIONS do, because
they are computed by different routes. §5 closes that, and the
coordinate readouts are the reusable part. -/

theorem polar_e₁ (u : V) : QuadraticMap.polar Q₁₃ e₁ u = -(2 * u.1.2) := by
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [QuadraticMap.polar, Q₁₃_apply, e₁, Prod.fst_add, Prod.snd_add]
  ring

theorem polar_e₂ (u : V) : QuadraticMap.polar Q₁₃ e₂ u = -(2 * u.2.1) := by
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [QuadraticMap.polar, Q₁₃_apply, e₂, Prod.fst_add, Prod.snd_add]
  ring

theorem polar_e₃ (u : V) : QuadraticMap.polar Q₁₃ e₃ u = -(2 * u.2.2) := by
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [QuadraticMap.polar, Q₁₃_apply, e₃, Prod.fst_add, Prod.snd_add]
  ring

theorem vreflect_e₀ (u : V) :
    vreflect e₀ u = ((u.1.1, -u.1.2), (-u.2.1, -u.2.2)) := by
  rw [vreflect, SpinBoost.polar_e₀, Q₁₃_e₀]
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [e₀, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  norm_num
  ring

theorem vreflect_e₁ (u : V) :
    vreflect e₁ u = ((-u.1.1, u.1.2), (-u.2.1, -u.2.2)) := by
  rw [vreflect, polar_e₁, Q₁₃_e₁]
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [e₁, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  norm_num
  ring

theorem vreflect_e₂ (u : V) :
    vreflect e₂ u = ((-u.1.1, -u.1.2), (u.2.1, -u.2.2)) := by
  rw [vreflect, polar_e₂, Q₁₃_e₂]
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [e₂, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  norm_num
  ring

theorem vreflect_e₃ (u : V) :
    vreflect e₃ u = ((-u.1.1, -u.1.2), (-u.2.1, u.2.2)) := by
  rw [vreflect, polar_e₃, Q₁₃_e₃]
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [e₃, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
  norm_num
  ring

theorem vreflect_w (u : V) :
    vreflect SpinBoost.w u
      = ((17/8 * u.1.1 - 15/8 * u.1.2, 15/8 * u.1.1 - 17/8 * u.1.2),
          (-u.2.1, -u.2.2)) := by
  rw [vreflect, SpinBoost.polar_w, SpinBoost.Q₁₃_w]
  obtain ⟨⟨t, x⟩, ⟨y, z⟩⟩ := u
  simp only [SpinBoost.w, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul,
    Prod.mk.injEq]
  norm_num
  constructor <;> ring

/-- **The π-rotation, recomputed through the general formula.** -/
theorem vreflect_comp_rotXY (u : V) : vreflect e₁ (vreflect e₂ u) = rotXY u := by
  rw [vreflect_e₂, vreflect_e₁]
  simp [rotXY]

/-- **The boost, recomputed through the general formula.** -/
theorem vreflect_comp_boostTX (u : V) :
    vreflect e₀ (vreflect SpinBoost.w u) = SpinBoost.boostTX u := by
  rw [vreflect_w, vreflect_e₀]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp [SpinBoost.boostTX]

/-! ## 6. The family is bigger than the two examples -/

theorem Q₁₃_e₃_ne : Q₁₃ e₃ ≠ 0 := by rw [Q₁₃_e₃]; norm_num

/-- A THIRD spin element, neither of the two that existed before. -/
theorem pair_e₁_e₃_mem :
    ((pair Q₁₃_e₁_ne Q₁₃_e₃_ne : Clˣ) : Cl) ∈ spinGroup Q₁₃ :=
  pair_mem _ _ (by rw [Q₁₃_e₁, Q₁₃_e₃]; norm_num)

/-- And it acts differently: the e₁e₃ rotation FIXES e₂, where the e₁e₂
    rotation negates it. So the family is not the two old elements in
    disguise. -/
theorem vreflect_e₁_e₃_fixes_e₂ : vreflect e₁ (vreflect e₃ e₂) = e₂ := by
  rw [vreflect_e₃, vreflect_e₁]
  simp [e₂]

theorem vreflect_e₁_e₃_ne_rotXY : vreflect e₁ (vreflect e₃ e₂) ≠ rotXY e₂ := by
  rw [vreflect_e₃, vreflect_e₁]
  intro h
  have h1 := congrArg (fun v : V => v.2.1) h
  norm_num [rotXY, e₂] at h1

/-! ## 7. The reflections are involutions, and the family is closed
under inversion

Review round 23 recorded `vreflect v ∘ vreflect v = id` as NOT CHECKED —
true, but needing plumbing that round did not write. PROOF_STRATEGY §7.2
says a chain reported incomplete is still open, so here it is, by a
route that avoids the plumbing entirely: work in the vector space rather
than the algebra, where the whole thing is bilinearity of `polar`. -/

/-- The reflection does not change the component being reflected: the
    polar form of `v` against `vreflect v u` is the polar form of `v`
    against `u`. This is the only computation the involution needs. -/
theorem polar_vreflect {v : V} (hv : Q₁₃ v ≠ 0) (u : V) :
    QuadraticMap.polar Q₁₃ v (vreflect v u) = QuadraticMap.polar Q₁₃ v u := by
  rw [vreflect]
  simp only [QuadraticMap.polar_smul_right, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_self, smul_eq_mul]
  apply mul_left_cancel₀ hv
  rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
  ring

/-- **Each reflection is an involution.** -/
theorem vreflect_involutive {v : V} (hv : Q₁₃ v ≠ 0) (u : V) :
    vreflect v (vreflect v u) = u := by
  conv_lhs => rw [vreflect, polar_vreflect hv, vreflect]
  rw [smul_smul, mul_inv_cancel₀ hv, one_smul, sub_sub_cancel, smul_smul,
    inv_mul_cancel₀ hv, one_smul]

/-- The normalisation condition is symmetric. -/
theorem prod_symm {v w : V} (hprod : Q₁₃ v * Q₁₃ w = 1) : Q₁₃ w * Q₁₃ v = 1 := by
  rw [mul_comm]; exact hprod

/-- **The family is closed under inversion, and explicitly so:** the
    inverse of `pair v w` is `pair w v`. Not obvious from the
    definition, where the inverse carries two scalar factors — they
    cancel exactly because `Q₁₃ v · Q₁₃ w = 1`. -/
theorem pair_inv_eq_pair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) : (pair hv hw)⁻¹ = pair hw hv := by
  refine Units.ext ?_
  have hs : (Q₁₃ w)⁻¹ * (Q₁₃ v)⁻¹ = 1 := by
    rw [← mul_inv, mul_comm (Q₁₃ w), hprod, inv_one]
  rw [pair_inv, pair_val, vecUnit_inv, vecUnit_inv, smul_mul_assoc,
    mul_smul_comm, smul_smul, hs, one_smul]

/-- So the swapped pair is a spin element too. -/
theorem pair_swap_mem {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) : ((pair hw hv : Clˣ) : Cl) ∈ spinGroup Q₁₃ :=
  pair_mem hw hv (prod_symm hprod)

/-- **And the two actions undo each other**, which is what "closed under
    inversion" is worth at the level of ℝ⁴. -/
theorem vreflect_pair_symm {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0) (u : V) :
    vreflect w (vreflect v (vreflect v (vreflect w u))) = u := by
  rw [vreflect_involutive hv, vreflect_involutive hw]

end SpinPair
