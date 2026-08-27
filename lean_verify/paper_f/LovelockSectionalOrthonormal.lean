import LovelockSectional

/-!
# Orthonormal pairs are enough, and the Mathlib bridge that was named is not needed

`LovelockSectional.eq_zero_of_sec` says an algebraic curvature tensor whose sectional entries all
vanish is zero — **at every pair `x, y`**. Its header names the gap between that and what an
orthogonality condition against the witness orbit would actually supply:

> This is a hypothesis about ALL pairs `x, y`. What an orthogonality condition against the orbit of
> the witness would supply is the same vanishing **only for orthonormal pairs** — one pair of rows
> of an orthogonal matrix at a time. Getting from there to here is elementary (scale, and use the
> antisymmetry when the pair is dependent) but it is **not proved here**, and the Lean form of it
> needs *extend an orthonormal pair to an orthogonal matrix*, which is a Mathlib bridge this estate
> has not built.

**The first half is right and the second is not.** The step is elementary, and it needs **no such
bridge**: extending a pair to a whole orthogonal matrix is far more than the argument uses. Two
vectors are enough, and Gram–Schmidt on two vectors is three lines of algebra in `Fin n → ℝ`.
`sec_eq_zero_of_orthonormal` below closes the gap outright.

## The argument, in the order the file proves it

* **`sec` does not see a multiple of the first slot added to the second.**
  `sec Z x (y + t·x) = sec Z x y`, because the added `t·x` sits against `x` in slots 1–2 on one
  side and in slots 3–4 on the other, and both die by antisymmetry. **This is what replaces
  "extend to an orthogonal matrix": it produces the orthogonal partner directly.**
* **`sec` scales by the square in each slot**, `sec Z (a·x) (b·y) = a²b² · sec Z x y`, which turns
  an orthogonal pair into an orthonormal one.
* **A dependent pair contributes nothing**, `sec Z x (c·x) = 0`, so the degenerate case needs no
  hypothesis at all.

Given `x, y`: if `x = 0` the entry vanishes; otherwise `w = y − (⟪y,x⟫/⟪x,x⟫)·x` is orthogonal to
`x` with `sec Z x w = sec Z x y`, and either `w = 0` — the dependent case — or both normalise, and
the hypothesis applies to the normalised pair.

## What is proved

* `multZeroOne` and the four scaling lemmas — `mult` is multilinear, which the previous file needed
  only additively;
* **`mult_left_self`, `mult_right_self`** — `mult Z x x z w = 0` and `mult Z x y z z = 0`, the
  antisymmetries carried from indices to vectors by re-indexing the sum;
* `sec_add_smul`, `sec_smul_left`, `sec_smul_right`, `sec_dependent`;
* **`sec_eq_zero_of_orthonormal`** — vanishing on orthonormal pairs gives vanishing on all pairs;
* **`eq_zero_of_sec_orthonormal`** — hence the tensor is zero, which is
  `LovelockSectional.eq_zero_of_sec` with its hypothesis weakened to the one an orthogonality
  condition can supply.

## What this does NOT do

**It does not supply the orthogonality condition.** `LovelockSectional`'s header names two missing
things and this is the first; the second — that `ip Z (act Q W) = 0` for every orthogonal `Q` is
equivalent to the sectional entries of every frame-change of `Z` vanishing — is a computation about
`ip Y (knSquare (twoProj i j))` and is untouched here. **`KillsWeyl` does not move**, no wall moves,
and no published tag moves.
-/

namespace LovelockSectionalOrthonormal

open AlgebraicCurvature Finset LovelockSectional

variable {n : ℕ}

/-! ## 1. `mult` is multilinear, and vanishes on a repeated slot -/

theorem mult_zero_one (Z : Fin n → Fin n → Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, x i = 0) (y z w : Fin n → ℝ) : mult Z x y z w = 0 := by
  simp [mult, hx]

theorem mult_smul_one (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ) (x y z w : Fin n → ℝ) :
    mult Z (fun t => c * x t) y z w = c * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_smul_two (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x (fun t => c * y t) z w = c * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_smul_three (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x y (fun t => c * z t) w = c * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_smul_four (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (c : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x y z (fun t => c * w t) = c * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The index swap that carries `antisymm_left` from indices to vectors. -/
private def swap12 : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun p := (p.2.1, p.1, p.2.2.1, p.2.2.2)
  invFun p := (p.2.1, p.1, p.2.2.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same for `antisymm_right`. -/
private def swap34 : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun p := (p.1, p.2.1, p.2.2.2, p.2.2.1)
  invFun p := (p.1, p.2.1, p.2.2.2, p.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A REPEATED FIRST-PAIR ARGUMENT KILLS `mult`.** `antisymm_left` is a statement about indices;
this is the same statement about vectors, and the whole of the proof is re-indexing the sum by the
swap that realises it. -/
theorem mult_left_self {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x z w : Fin n → ℝ) : mult Z x x z w = 0 := by
  have h : mult Z x x z w = - mult Z x x z w := by
    simp only [mult, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv swap12 _ _ fun p => ?_
    -- `dsimp only` rather than `show`: the goal needs the equiv applied, which is a
    -- definitional unfold, and the style linter reserves `show` for readability
    dsimp only [swap12, Equiv.coe_fn_mk]
    rw [hZ.antisymm_left p.2.1 p.1]
    ring
  linarith

/-- **AND A REPEATED SECOND-PAIR ARGUMENT DOES TOO**, by `antisymm_right` and `swap34`. -/
theorem mult_right_self {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y z : Fin n → ℝ) : mult Z x y z z = 0 := by
  have h : mult Z x y z z = - mult Z x y z z := by
    simp only [mult, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv swap34 _ _ fun p => ?_
    dsimp only [swap34, Equiv.coe_fn_mk]
    rw [hZ.antisymm_right p.1 p.2.1 p.2.2.2 p.2.2.1]
    ring
  linarith

/-! ## 2. What `sec` does under the two moves Gram–Schmidt needs -/

/-- **ADDING A MULTIPLE OF THE FIRST SLOT TO THE SECOND CHANGES NOTHING.** This is the whole of the
"extend to an orthogonal matrix" step, done with two vectors instead of a matrix: it manufactures
the orthogonal partner of `x` inside the plane and leaves the sectional entry alone. -/
theorem sec_add_smul {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y : Fin n → ℝ) (t : ℝ) :
    sec Z x (fun i => y i + t * x i) = sec Z x y := by
  simp only [sec, mult_add_two, mult_add_three, mult_smul_two, mult_smul_three]
  rw [mult_right_self hZ x y x, mult_left_self hZ x y x, mult_left_self hZ x x x]
  ring

theorem sec_smul_left (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (a : ℝ) (x y : Fin n → ℝ) :
    sec Z (fun i => a * x i) y = a ^ 2 * sec Z x y := by
  simp only [sec]
  rw [mult_smul_one, mult_smul_four]
  ring

theorem sec_smul_right (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (b : ℝ) (x y : Fin n → ℝ) :
    sec Z x (fun i => b * y i) = b ^ 2 * sec Z x y := by
  simp only [sec]
  rw [mult_smul_two, mult_smul_three]
  ring

/-- **A DEPENDENT PAIR SPANS NO PLANE AND CONTRIBUTES NOTHING**, with no hypothesis on `Z` beyond
being an algebraic curvature tensor. -/
theorem sec_dependent {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x : Fin n → ℝ) (c : ℝ) : sec Z x (fun i => c * x i) = 0 := by
  rw [sec_smul_right, sec, mult_left_self hZ, mul_zero]

/-! ## 3. Orthonormal pairs are enough -/

/-- The Euclidean form on `Fin n → ℝ`, written out rather than imported so that nothing here
depends on a bundled inner-product space. -/
def dotv (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

theorem dotv_comm (x y : Fin n → ℝ) : dotv x y = dotv y x :=
  Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

theorem dotv_smul_smul (c d : ℝ) (x y : Fin n → ℝ) :
    dotv (fun i => c * x i) (fun i => d * y i) = c * d * dotv x y := by
  simp only [dotv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotv_self_nonneg (x : Fin n → ℝ) : 0 ≤ dotv x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem eq_zero_of_dotv_self_eq_zero {x : Fin n → ℝ} (h : dotv x x = 0) (i : Fin n) : x i = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp h i
    (Finset.mem_univ i)
  exact mul_self_eq_zero.mp this

/-- **VANISHING ON ORTHONORMAL PAIRS IS VANISHING ON ALL PAIRS.** The bridge
`LovelockSectional`'s header said was missing, built from `sec_add_smul` and the scaling lemmas
and needing no statement about orthogonal matrices at all. -/
theorem sec_eq_zero_of_orthonormal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ u v : Fin n → ℝ, dotv u u = 1 → dotv v v = 1 → dotv u v = 0 → sec Z u v = 0)
    (x y : Fin n → ℝ) : sec Z x y = 0 := by
  by_cases hx : dotv x x = 0
  · exact mult_zero_one Z (eq_zero_of_dotv_self_eq_zero hx) y y x
  have hxpos : 0 < dotv x x := lt_of_le_of_ne (dotv_self_nonneg x) (Ne.symm hx)
  set t : ℝ := -(dotv y x) / dotv x x with ht
  set w : Fin n → ℝ := fun i => y i + t * x i with hw
  have hexp : dotv w x = dotv y x + t * dotv x x := by
    simp only [hw, dotv, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwx : dotv w x = 0 := by
    rw [hexp, ht]
    field_simp
    ring
  have hsec : sec Z x y = sec Z x w := (sec_add_smul hZ x y t).symm
  by_cases hq : dotv w w = 0
  · -- `w = 0`: the pair was dependent, and `sec` is linear in the second slot
    rw [hsec, sec]
    have h0 : ∀ i, w i = 0 := eq_zero_of_dotv_self_eq_zero hq
    simp [mult, h0]
  have hqpos : 0 < dotv w w := lt_of_le_of_ne (dotv_self_nonneg w) (Ne.symm hq)
  have hsx : Real.sqrt (dotv x x) * Real.sqrt (dotv x x) = dotv x x :=
    Real.mul_self_sqrt (le_of_lt hxpos)
  have hsw : Real.sqrt (dotv w w) * Real.sqrt (dotv w w) = dotv w w :=
    Real.mul_self_sqrt (le_of_lt hqpos)
  have hax : Real.sqrt (dotv x x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxpos)
  have hbw : Real.sqrt (dotv w w) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hqpos)
  -- the two normalisers, packaged with exactly the two facts the argument uses
  obtain ⟨a, hane, ha⟩ : ∃ a : ℝ, a ≠ 0 ∧ a * a * dotv x x = 1 := by
    refine ⟨(Real.sqrt (dotv x x))⁻¹, inv_ne_zero hax, ?_⟩
    -- forwards, not `rw [← hsx]`: that rewrites `dotv x x` inside the square roots as well
    calc (Real.sqrt (dotv x x))⁻¹ * (Real.sqrt (dotv x x))⁻¹ * dotv x x
        = (Real.sqrt (dotv x x))⁻¹ * (Real.sqrt (dotv x x))⁻¹
            * (Real.sqrt (dotv x x) * Real.sqrt (dotv x x)) := by rw [hsx]
      _ = ((Real.sqrt (dotv x x))⁻¹ * Real.sqrt (dotv x x))
            * ((Real.sqrt (dotv x x))⁻¹ * Real.sqrt (dotv x x)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hax, one_mul]
  obtain ⟨b, hbne, hbb⟩ : ∃ b : ℝ, b ≠ 0 ∧ b * b * dotv w w = 1 := by
    refine ⟨(Real.sqrt (dotv w w))⁻¹, inv_ne_zero hbw, ?_⟩
    calc (Real.sqrt (dotv w w))⁻¹ * (Real.sqrt (dotv w w))⁻¹ * dotv w w
        = (Real.sqrt (dotv w w))⁻¹ * (Real.sqrt (dotv w w))⁻¹
            * (Real.sqrt (dotv w w) * Real.sqrt (dotv w w)) := by rw [hsw]
      _ = ((Real.sqrt (dotv w w))⁻¹ * Real.sqrt (dotv w w))
            * ((Real.sqrt (dotv w w))⁻¹ * Real.sqrt (dotv w w)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hbw, one_mul]
  have hu : dotv (fun i => a * x i) (fun i => a * x i) = 1 := by
    rw [dotv_smul_smul]; exact ha
  have hv : dotv (fun i => b * w i) (fun i => b * w i) = 1 := by
    rw [dotv_smul_smul]; exact hbb
  have huv : dotv (fun i => a * x i) (fun i => b * w i) = 0 := by
    rw [dotv_smul_smul, dotv_comm, hwx, mul_zero]
  have hzero := h _ _ hu hv huv
  rw [sec_smul_left, sec_smul_right] at hzero
  have h2 : a ^ 2 ≠ 0 := pow_ne_zero 2 hane
  have h3 : b ^ 2 ≠ 0 := pow_ne_zero 2 hbne
  have hfin : sec Z x w = 0 := by
    have hprod : a ^ 2 * b ^ 2 ≠ 0 := mul_ne_zero h2 h3
    have hz : a ^ 2 * b ^ 2 * sec Z x w = 0 := by rw [← hzero]; ring
    exact (mul_eq_zero.mp hz).resolve_left hprod
  rw [hsec, hfin]

/-- **AND HENCE THE TENSOR IS ZERO.** `LovelockSectional.eq_zero_of_sec` with its hypothesis
weakened from all pairs to orthonormal pairs — the form an orthogonality condition against the
witness orbit could actually supply. -/
theorem eq_zero_of_sec_orthonormal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ u v : Fin n → ℝ, dotv u u = 1 → dotv v v = 1 → dotv u v = 0 → sec Z u v = 0)
    (a b c d : Fin n) : Z a b c d = 0 :=
  eq_zero_of_sec hZ (sec_eq_zero_of_orthonormal hZ h) a b c d

end LovelockSectionalOrthonormal
