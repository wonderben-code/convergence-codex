/-
  LorentzSurjectivity: SL₂(ℂ) → SO⁺(1,3) IS Surjective — Old Gap #7 Closes
  ========================================================================

  The last leg of the chain built in `MinkowskiHerm2` → `MinkowskiSignature` →
  `LorentzGroup`. Those files left exactly one thing standing between the
  estate and the double-cover statement: surjectivity, reduced by
  `LorentzGroup.surjective_of_stabiliser_surjective` to the classical
  SU(2) ↠ SO(3) — every rotation of the spatial slice has an SL₂(ℂ)
  preimage. Mathlib does not have that theorem. This file proves it, and
  with it the full surjectivity.

  THE ROUTE — everything algebraic, no topology, no transcendental functions.
  "Angles" never appear: a rotation is parametrised by a point (a, b) on the
  circle a² + b² = 1, and the only analytic ingredient anywhere is the real
  square root, used twice:

  1. §1 `su2Z`, `su2Y` — the two one-parameter families
     U_z(c,s) = diag(c − is, c + is) and U_y(c,s) = [[c, −s],[s, c]], with
     `su2Z_conj`/`su2Y_conj`: conjugating the Pauli parametrisation by them
     rotates (x,y) resp. (x,z) by the DOUBLED angle (c² − s², 2cs). Proved
     entrywise; the only fact about ℂ used is I² = −1.
  2. §2 `rotZ`, `rotY` — the corresponding 4×4 rotations, and
     `lorentzMat_su2Z`/`lorentzMat_su2Y`: Λ(U_z(c,s)) = rotZ(c²−s², 2cs),
     Λ(U_y(c,s)) = rotY(c²−s², 2cs), computed through the Pauli round trip.
  3. §3 `half_angle` — for every (a,b) on the circle there is (c,s) on the
     circle with c² − s² = a, 2cs = b. Purely algebraic: c = √((1+a)/2),
     s = b/(2c), with the case a = −1 handled by (c,s) = (0,1). Hence
     `exists_su2_rotZ`/`exists_su2_rotY`: EVERY rotZ/rotY is hit, and is
     therefore Lorentz with det 1 for free (`rotZ_facts`, `rotY_facts`).
  4. §4 `det_inner_block` — Laplace expansion for the 4×4 shape with time
     and z-axis pinned.
  5. §5 **`stabiliser_surjective`** — the Euler decomposition: a Lorentz R
     fixing the time axis satisfies R = rotZ(cα,sα)·rotY(w₃,r)·rotZ(p,q),
     where (0,w₁,w₂,w₃) is its z-column, r = √(w₁²+w₂²), (cα,sα) points
     along (w₁,w₂), and (p,q) is read off the residual matrix, which is
     proven to BE a rotZ by orthonormality + determinant — the determinant
     pins the reflection sign LINEARLY, no case split. Composing the three
     preimages: every time-axis-fixing Lorentz rotation is Λ(A).
  6. §6 **`lorentz_surjective`** — combining with the boost factorisation:
     for EVERY L with ΛᵀGΛ = G, det L = 1, L⁰₀ > 0 there is A ∈ SL₂(ℂ) with
     Λ(A) = L. Bundled: `SOplus13_surjective`. With
     `MinkowskiHerm2.kernel_of_conj_action` (kernel exactly {±1}) this is
     **the 2-to-1 covering SL₂(ℂ) → SO⁺(1,3): old gap #7, closed.**

  NOT proven here:

  * That SO⁺(1,3) is the identity component / anything topological — the
    covering is algebraic (a surjection with kernel {±1}), and the words
    "continuous", "connected", "Lie group" appear nowhere.
  * Any identification with Mathlib's `spinGroup`, and any statement that
    the cascade FORCES this structure (`MinkowskiSignature`'s disclaimers
    unchanged).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import LorentzGroup

open Matrix Complex MinkowskiHerm2 MinkowskiSignature LorentzGroup

noncomputable section

namespace LorentzSurjectivity

/-! ## 1. The two SU(2) one-parameter families -/

/-- U_z(c,s) = c·1 − i s σ₃: the diagonal family. -/
def su2Z (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ) - s * I, 0; 0, (c : ℂ) + s * I]

/-- U_y(c,s) = c·1 − i s σ₂ = [[c, −s],[s, c]]: the real family. -/
def su2Y (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)]

theorem det_su2Z (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (su2Z c s).det = 1 := by
  have hc : ((c : ℂ)) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  rw [su2Z, Matrix.det_fin_two_of]
  linear_combination hc - (s : ℂ) ^ 2 * Complex.I_sq

theorem det_su2Y (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : (su2Y c s).det = 1 := by
  have hc : ((c : ℂ)) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  rw [su2Y, Matrix.det_fin_two_of]
  linear_combination hc

/-- **Conjugation by U_z rotates the (x,y)-plane by the doubled angle.** -/
theorem su2Z_conj (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (t x y z : ℝ) :
    su2Z c s * pauliHerm t x y z * (su2Z c s)ᴴ
      = pauliHerm t ((c ^ 2 - s ^ 2) * x - 2 * c * s * y)
          (2 * c * s * x + (c ^ 2 - s ^ 2) * y) z := by
  have hc : ((c : ℂ)) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [su2Z, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf)
      (((t : ℂ) + z)) * hc - (s : ℂ) ^ 2 * ((t : ℂ) + z) * Complex.I_sq
  · simp [su2Z, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf)
      (2 * (c : ℂ) * s * y + (s : ℂ) ^ 2 * x - (s : ℂ) ^ 2 * I * y) * Complex.I_sq
  · simp [su2Z, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf)
      (2 * (c : ℂ) * s * y + (s : ℂ) ^ 2 * x + (s : ℂ) ^ 2 * I * y) * Complex.I_sq
  · simp [su2Z, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf)
      (((t : ℂ) - z)) * hc - (s : ℂ) ^ 2 * ((t : ℂ) - z) * Complex.I_sq

/-- **Conjugation by U_y rotates the (x,z)-plane by the doubled angle.** -/
theorem su2Y_conj (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (t x y z : ℝ) :
    su2Y c s * pauliHerm t x y z * (su2Y c s)ᴴ
      = pauliHerm t ((c ^ 2 - s ^ 2) * x + 2 * c * s * z) y
          ((c ^ 2 - s ^ 2) * z - 2 * c * s * x) := by
  have hc : ((c : ℂ)) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [su2Y, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf) ((t : ℂ)) * hc
  · simp [su2Y, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf) (-(y : ℂ) * I) * hc
  · simp [su2Y, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf) ((y : ℂ) * I) * hc
  · simp [su2Y, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    linear_combination (norm := ring_nf) ((t : ℂ)) * hc

/-! ## 2. The corresponding 4×4 rotations, and Λ of the families -/

/-- Rotation of the (x,y)-plane: the image of U_z under Λ. -/
def rotZ (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, a, -b, 0; 0, b, a, 0; 0, 0, 0, 1]

/-- Rotation of the (x,z)-plane: the image of U_y under Λ. -/
def rotY (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, a, 0, b; 0, 0, 1, 0; 0, -b, 0, a]

/-- **Λ(U_z(c,s)) = rotZ(c²−s², 2cs).** -/
theorem lorentzMat_su2Z (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    lorentzMat (su2Z c s) = rotZ (c ^ 2 - s ^ 2) (2 * c * s) := by
  ext i j
  rw [lorentzMat_apply]
  fin_cases j <;>
    · simp only [lorentzMap]
      norm_num [Pi.single_apply]
      rw [su2Z_conj c s h, pauliCoord_pauliHerm]
      fin_cases i <;> simp [rotZ]

/-- **Λ(U_y(c,s)) = rotY(c²−s², 2cs).** -/
theorem lorentzMat_su2Y (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    lorentzMat (su2Y c s) = rotY (c ^ 2 - s ^ 2) (2 * c * s) := by
  ext i j
  rw [lorentzMat_apply]
  fin_cases j <;>
    · simp only [lorentzMap]
      norm_num [Pi.single_apply]
      rw [su2Y_conj c s h, pauliCoord_pauliHerm]
      fin_cases i <;> simp [rotY]

/-- rotZ(a,−b) inverts rotZ(a,b). -/
theorem rotZ_mul_neg (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    rotZ a b * rotZ a (-b) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_four] <;>
    linarith [h]

/-- rotY(a,−b) inverts rotY(a,b). -/
theorem rotY_mul_neg (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    rotY a b * rotY a (-b) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_four] <;>
    linarith [h]

/-! ## 3. The half-angle: every point of the circle is a doubled point -/

/-- **The algebraic half-angle**: every (a,b) with a² + b² = 1 is
    (c² − s², 2cs) for some (c,s) with c² + s² = 1. The whole trigonometric
    content of the covering map, done with one square root. -/
theorem half_angle (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 - s ^ 2 = a ∧ 2 * c * s = b := by
  by_cases ha : a = -1
  · have hb : b = 0 := by
      have : b ^ 2 = 0 := by rw [ha] at h; nlinarith
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨0, 1, by norm_num, by rw [ha]; norm_num, by rw [hb]; ring⟩
  · have hle : -1 ≤ a := by nlinarith [sq_nonneg b]
    have hlt : -1 < a := lt_of_le_of_ne hle (fun hc => ha hc.symm)
    have hpos : 0 < 1 + a := by linarith
    set c := Real.sqrt ((1 + a) / 2) with hc
    have hc2 : c ^ 2 = (1 + a) / 2 := Real.sq_sqrt (by positivity)
    have hcpos : 0 < c := Real.sqrt_pos.mpr (by positivity)
    refine ⟨c, b / (2 * c), ?_, ?_, ?_⟩
    · have hs2 : (b / (2 * c)) ^ 2 = (1 - a) / 2 := by
        rw [div_pow, mul_pow, hc2]
        rw [show b ^ 2 = (1 - a) * (1 + a) by nlinarith]
        field_simp
      rw [hs2, hc2]; ring
    · have hs2 : (b / (2 * c)) ^ 2 = (1 - a) / 2 := by
        rw [div_pow, mul_pow, hc2]
        rw [show b ^ 2 = (1 - a) * (1 + a) by nlinarith]
        field_simp
      rw [hs2, hc2]; ring
    · field_simp

/-- **Every rotZ is hit** by an element of SL₂(ℂ). -/
theorem exists_su2_rotZ (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, U.det = 1 ∧ lorentzMat U = rotZ a b := by
  obtain ⟨c, s, hcs, hca, hcb⟩ := half_angle a b h
  exact ⟨su2Z c s, det_su2Z c s hcs, by rw [lorentzMat_su2Z c s hcs, hca, hcb]⟩

/-- **Every rotY is hit** by an element of SL₂(ℂ). -/
theorem exists_su2_rotY (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, U.det = 1 ∧ lorentzMat U = rotY a b := by
  obtain ⟨c, s, hcs, hca, hcb⟩ := half_angle a b h
  exact ⟨su2Y c s, det_su2Y c s hcs, by rw [lorentzMat_su2Y c s hcs, hca, hcb]⟩

/-- rotZ is Lorentz with det 1 — free, because it is in the image. -/
theorem rotZ_facts (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    IsLorentzMat (rotZ a b) ∧ (rotZ a b).det = 1 := by
  obtain ⟨U, hU, hUeq⟩ := exists_su2_rotZ a b h
  exact ⟨hUeq ▸ lorentzMat_gram U hU, hUeq ▸ det_lorentzMat U hU⟩

/-- rotY is Lorentz with det 1 — free, because it is in the image. -/
theorem rotY_facts (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    IsLorentzMat (rotY a b) ∧ (rotY a b).det = 1 := by
  obtain ⟨U, hU, hUeq⟩ := exists_su2_rotY a b h
  exact ⟨hUeq ▸ lorentzMat_gram U hU, hUeq ▸ det_lorentzMat U hU⟩

/-! ## 4. Laplace expansion for the pinned shape -/

/-- The determinant of a 4×4 matrix with the time row/column and the z
    row/column pinned is the determinant of its middle 2×2 block. -/
theorem det_inner_block (M : Matrix (Fin 4) (Fin 4) ℝ)
    (h00 : M 0 0 = 1) (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h30 : M 3 0 = 0)
    (h13 : M 1 3 = 0) (h23 : M 2 3 = 0) (h31 : M 3 1 = 0) (h32 : M 3 2 = 0)
    (h33 : M 3 3 = 1) :
    M.det = M 1 1 * M 2 2 - M 1 2 * M 2 1 := by
  have hM : M = !![1, 0, 0, 0; 0, M 1 1, M 1 2, 0; 0, M 2 1, M 2 2, 0;
      0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h00, h01, h02, h03, h10, h20, h30, h13, h23, h31, h32, h33]
  rw [hM, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [Matrix.det_fin_three]

/-! ## 5. The Euler decomposition: the stabiliser of the time axis is hit -/

/-- **SU(2) ↠ SO(3), in the coordinates of this estate**: every Lorentz
    matrix fixing the time axis is Λ(A) for some A ∈ SL₂(ℂ). The proof is
    the Euler decomposition R = rotZ(cα,sα)·rotY(w₃,r)·rotZ(p,q), assembled
    from the z-column of R, with all three factors hit by §3. -/
theorem stabiliser_surjective :
    ∀ R : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat R → R.det = 1 →
      (∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) →
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ lorentzMat A = R := by
  intro R hR hdet hcol
  obtain ⟨hrow, horth⟩ := stabiliser_is_rotation hR hcol
  have hcol' : ∀ i, R i 0 = if i = 0 then 1 else 0 := by
    intro i; rw [hcol i, Pi.single_apply]
  have hrow' : ∀ j, R 0 j = if j = 0 then 1 else 0 := by
    intro j; rw [hrow j, Pi.single_apply]
  have hw : R 1 3 ^ 2 + R 2 3 ^ 2 + R 3 3 ^ 2 = 1 := by
    have h := horth 3 3 (by decide) (by decide)
    simp at h
    linear_combination h
  set r := Real.sqrt (R 1 3 ^ 2 + R 2 3 ^ 2) with hrdef
  have hr2 : r ^ 2 = R 1 3 ^ 2 + R 2 3 ^ 2 := Real.sq_sqrt (by positivity)
  have hyz : R 3 3 ^ 2 + r ^ 2 = 1 := by rw [hr2]; linarith [hw]
  obtain ⟨ca, sa, hα, hk1, hk2⟩ :
      ∃ ca sa : ℝ, ca ^ 2 + sa ^ 2 = 1 ∧ ca * r = R 1 3 ∧ sa * r = R 2 3 := by
    by_cases hr : r = 0
    · have h12 : R 1 3 ^ 2 + R 2 3 ^ 2 = 0 := by rw [← hr2, hr]; ring
      have h1 : R 1 3 = 0 := by nlinarith [sq_nonneg (R 1 3), sq_nonneg (R 2 3)]
      have h2 : R 2 3 = 0 := by nlinarith [sq_nonneg (R 1 3), sq_nonneg (R 2 3)]
      exact ⟨1, 0, by norm_num, by rw [hr, h1]; ring, by rw [hr, h2]; ring⟩
    · refine ⟨R 1 3 / r, R 2 3 / r, ?_, by field_simp, by field_simp⟩
      have hsplit : (R 1 3 / r) ^ 2 + (R 2 3 / r) ^ 2
          = (R 1 3 ^ 2 + R 2 3 ^ 2) / r ^ 2 := by ring
      rw [hsplit, ← hr2]
      field_simp
  have hα' : ca ^ 2 + (-sa) ^ 2 = 1 := by linear_combination hα
  have hyz' : R 3 3 ^ 2 + (-r) ^ 2 = 1 := by linear_combination hyz
  have hC1f := rotZ_facts ca (-sa) hα'
  have hC2f := rotY_facts (R 3 3) (-r) hyz'
  set D := rotY (R 3 3) (-r) * (rotZ ca (-sa) * R) with hD
  have hDlor : IsLorentzMat D := hC2f.1.mul (hC1f.1.mul hR)
  have hDdet : D.det = 1 := by
    rw [hD, Matrix.det_mul, Matrix.det_mul, hC2f.2, hC1f.2, hdet]; ring
  -- column 0 of D is the time axis
  have hC1R_col0 : ∀ i, (rotZ ca (-sa) * R) i 0 = if i = 0 then 1 else 0 := by
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_four, hcol' 0, hcol' 1, hcol' 2, hcol' 3]
    fin_cases i <;> simp [rotZ]
  have hDcol0 : ∀ i, D i 0 = if i = 0 then 1 else 0 := by
    intro i
    rw [hD, Matrix.mul_apply, Fin.sum_univ_four,
      hC1R_col0 0, hC1R_col0 1, hC1R_col0 2, hC1R_col0 3]
    fin_cases i <;> simp [rotY]
  -- column 3 of D is the z axis
  have hR03 : R 0 3 = 0 := by rw [hrow' 3]; simp
  have hc13a : (rotZ ca (-sa) * R) 0 3 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [rotZ, hR03]
  have hc13b : (rotZ ca (-sa) * R) 1 3 = r := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [rotZ, hR03]
    linear_combination (-ca) * hk1 + (-sa) * hk2 + r * hα
  have hc13c : (rotZ ca (-sa) * R) 2 3 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [rotZ, hR03]
    linear_combination sa * hk1 + (-ca) * hk2
  have hc13d : (rotZ ca (-sa) * R) 3 3 = R 3 3 := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [rotZ, hR03]
  have hDcol3 : ∀ i, D i 3 = if i = 3 then 1 else 0 := by
    intro i
    rw [hD, Matrix.mul_apply, Fin.sum_univ_four, hc13a, hc13b, hc13c, hc13d]
    fin_cases i
    · simp [rotY]
    · simp [rotY]
      ring
    · simp [rotY]
    · simp [rotY]
      linear_combination hyz
  -- the residual matrix is a rotZ
  have hDcolS : ∀ i, D i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i := by
    intro i; rw [hDcol0 i, Pi.single_apply]
  obtain ⟨hDrow, hDorth⟩ := stabiliser_is_rotation hDlor hDcolS
  have hDrow' : ∀ j, D 0 j = if j = 0 then 1 else 0 := by
    intro j; rw [hDrow j, Pi.single_apply]
  have hD13 : D 1 3 = 0 := by rw [hDcol3 1]; simp
  have hD23 : D 2 3 = 0 := by rw [hDcol3 2]; simp
  have hD33 : D 3 3 = 1 := by rw [hDcol3 3]; simp
  have hD31 : D 3 1 = 0 := by
    have h := hDorth 1 3 (by decide) (by decide)
    rw [hD13, hD23, hD33] at h
    simpa using h
  have hD32 : D 3 2 = 0 := by
    have h := hDorth 2 3 (by decide) (by decide)
    rw [hD13, hD23, hD33] at h
    simpa using h
  have hpq : D 1 1 ^ 2 + D 2 1 ^ 2 = 1 := by
    have h := hDorth 1 1 (by decide) (by decide)
    rw [hD31] at h
    simp at h
    linear_combination h
  have hperp : D 1 1 * D 1 2 + D 2 1 * D 2 2 = 0 := by
    have h := hDorth 1 2 (by decide) (by decide)
    rw [hD31, hD32] at h
    simpa using h
  have hdetD' : D 1 1 * D 2 2 - D 1 2 * D 2 1 = 1 := by
    have hexp := det_inner_block D
      (by rw [hDrow' 0]; simp) (by rw [hDrow' 1]; simp)
      (by rw [hDrow' 2]; simp) (by rw [hDrow' 3]; simp)
      (by rw [hDcol0 1]; simp) (by rw [hDcol0 2]; simp)
      (by rw [hDcol0 3]; simp) hD13 hD23 hD31 hD32 hD33
    rw [← hexp]
    exact hDdet
  -- the determinant pins the residual block LINEARLY: no reflection case
  have hD22 : D 2 2 = D 1 1 := by
    linear_combination D 1 1 * hdetD' + D 2 1 * hperp - D 2 2 * hpq
  have hD12 : D 1 2 = -(D 2 1) := by
    linear_combination (-(D 2 1)) * hdetD' + D 1 1 * hperp - D 1 2 * hpq
  have hDeq : D = rotZ (D 1 1) (D 2 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, hDrow' 1, hDrow' 2, hDrow' 3,
        (by rw [hDrow' 0]; simp : D 0 0 = 1),
        (by rw [hDcol0 1]; simp : D 1 0 = 0),
        (by rw [hDcol0 2]; simp : D 2 0 = 0),
        (by rw [hDcol0 3]; simp : D 3 0 = 0),
        hD13, hD23, hD31, hD32, hD33, hD12, hD22]
  -- assemble R back out of the three rotations
  have h1 : rotY (R 3 3) r * rotY (R 3 3) (-r) = 1 := rotY_mul_neg (R 3 3) r hyz
  have h2 : rotZ ca sa * rotZ ca (-sa) = 1 := rotZ_mul_neg ca sa hα
  have hass : R = rotZ ca sa * (rotY (R 3 3) r * D) := by
    rw [hD]
    calc R = 1 * R := (Matrix.one_mul R).symm
      _ = (rotZ ca sa * rotZ ca (-sa)) * R := by rw [h2]
      _ = rotZ ca sa * (rotZ ca (-sa) * R) := by rw [Matrix.mul_assoc]
      _ = rotZ ca sa * (1 * (rotZ ca (-sa) * R)) := by rw [Matrix.one_mul]
      _ = rotZ ca sa * ((rotY (R 3 3) r * rotY (R 3 3) (-r))
            * (rotZ ca (-sa) * R)) := by rw [h1]
      _ = rotZ ca sa * (rotY (R 3 3) r
            * (rotY (R 3 3) (-r) * (rotZ ca (-sa) * R))) := by
          rw [Matrix.mul_assoc]
  obtain ⟨U1, hU1det, hU1⟩ := exists_su2_rotZ ca sa hα
  obtain ⟨U2, hU2det, hU2⟩ := exists_su2_rotY (R 3 3) r hyz
  obtain ⟨U3, hU3det, hU3⟩ := exists_su2_rotZ (D 1 1) (D 2 1) hpq
  refine ⟨U1 * (U2 * U3), ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hU1det, hU2det, hU3det]; ring
  · rw [lorentzMat_mul, lorentzMat_mul, hU1, hU2, hU3, ← hDeq]
    exact hass.symm

/-! ## 6. The covering: old gap #7 -/

/-- **SURJECTIVITY OF SL₂(ℂ) → SO⁺(1,3)**: every real 4×4 matrix preserving
    the Minkowski form, with determinant 1, preserving the direction of
    time, is Λ(A) for some A of determinant 1. The last open leg of old
    gap #7. -/
theorem lorentz_surjective (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsLorentzMat L)
    (hdet : L.det = 1) (h0 : 0 < L 0 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ lorentzMat A = L :=
  surjective_of_stabiliser_surjective stabiliser_surjective L hL hdet h0

/-- The bundled form: the homomorphism hits every element of the subgroup
    `SOplus13`. -/
theorem SOplus13_surjective (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)
    (hM : M ∈ SOplus13) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1), lorentzUnit A hA = M := by
  obtain ⟨hlor, hdetM, h0⟩ := hM
  obtain ⟨A, hAdet, hAeq⟩ := lorentz_surjective M hlor hdetM h0
  exact ⟨A, hAdet, Units.ext (by rw [lorentzUnit_val, hAeq])⟩

/-- The kernel, stated in the same coordinates as the surjection: if
    Λ(A) = 1 then A = ±1. Bridges `MinkowskiHerm2.kernel_of_conj_action`
    (which speaks of fixing Hermitian matrices) to the matrix Λ. -/
theorem kernel_lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (h1 : lorentzMat A = 1) : A = 1 ∨ A = -1 := by
  refine kernel_of_conj_action A hA ?_
  intro H hH
  have hfix : ∀ v : Fin 4 → ℝ, lorentzMap A v = v := by
    intro v
    rw [← lorentzMat_mulVec, h1, Matrix.one_mulVec]
  have hv := hfix (pauliCoord H)
  have hherm : (A * pauliHerm (pauliCoord H 0) (pauliCoord H 1) (pauliCoord H 2)
      (pauliCoord H 3) * Aᴴ)ᴴ
      = A * pauliHerm (pauliCoord H 0) (pauliCoord H 1) (pauliCoord H 2)
          (pauliCoord H 3) * Aᴴ :=
    conj_action_hermitian A _ (pauliHerm_isHermitian _ _ _ _)
  have hround := pauliHerm_pauliCoord _ hherm
  have hph := pauliHerm_pauliCoord H hH
  calc A * H * Aᴴ
      = A * pauliHerm (pauliCoord H 0) (pauliCoord H 1) (pauliCoord H 2)
          (pauliCoord H 3) * Aᴴ := by rw [hph]
    _ = pauliHerm (lorentzMap A (pauliCoord H) 0) (lorentzMap A (pauliCoord H) 1)
          (lorentzMap A (pauliCoord H) 2) (lorentzMap A (pauliCoord H) 3) := by
        rw [← hround]
        rfl
    _ = pauliHerm (pauliCoord H 0) (pauliCoord H 1) (pauliCoord H 2)
          (pauliCoord H 3) := by rw [hv]
    _ = H := hph

/-- **THE DOUBLE COVER, in one statement**: the map A ↦ Λ(A) from SL₂(ℂ)
    (i) lands in SO⁺(1,3), (ii) is multiplicative, (iii) is SURJECTIVE onto
    SO⁺(1,3), and (iv) has kernel exactly {±1}. Old gap #7, closed. -/
theorem double_cover :
    (∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1),
        lorentzUnit A hA ∈ SOplus13)
      ∧ (∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
          lorentzMat (A * B) = lorentzMat A * lorentzMat B)
      ∧ (∀ M ∈ SOplus13,
          ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1),
            lorentzUnit A hA = M)
      ∧ (∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 →
          lorentzMat A = 1 → A = 1 ∨ A = -1)
      ∧ ((1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) :=
  ⟨lorentzUnit_mem_SOplus13, lorentzMat_mul, SOplus13_surjective,
    kernel_lorentzMat, by
      intro h
      have h00 := Matrix.ext_iff.mpr h 0 0
      rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at h00
      exact (by norm_num : (1 : ℂ) ≠ -1) h00⟩

end LorentzSurjectivity
