/-
  SpinRotorFamilies.lean — the one-parameter rotor and boost families,
  matched against the SL₂(ℂ) chain family by family.

  WHY. `SL2Quotient` turned W7 step (d)'s residue into a MATCHING
  PROBLEM: surjectivity of the spin map holds iff for every
  `A ∈ SL₂(ℂ)` there is a spinor `g` with `ρ(g) = Λ(A)`. It then solved
  that problem at exactly one nontrivial point, `chains_agree_at_R₁₂'`,
  and said plainly that one point is not a family.

  This file supplies the families. The estate's own surjectivity proof
  on the SL₂ side (`LorentzSurjectivity.stabiliser_surjective`, and
  `LorentzGroup.exists_boost_factor` above it) is built out of exactly
  three ingredients: the `su2Z` family, the `su2Y` family, and one
  Hermitian factor. **Two of those three are matched here for every
  parameter value**, and the third is isolated as the entire residue.

  WHAT THIS FILE PROVES:
  1. **`spinPair`** and **`endo_spinPair`** — a general tool the estate
     was missing. `SpinPair.pair_mem` says every admissible pair of
     vectors is a spin element and `spinToEndo_pair` computes its
     action, but the bridge to `endo` — the form every matrix
     computation actually consumes — existed only for the two hand-built
     elements `R₁₂'` and `B'`, each with its own copy of the same three
     lines. Now it exists once, for every pair.
  2. **`rotorXY`**, **`rotorXZ`**, **`booster`** — three one-parameter
     families of genuine spin elements, each a product of two unit
     vectors, with their Lorentz matrices computed in closed form:
     `rotZ(c²−s², 2cs)`, `rotY(c²−s², 2cs)` and the `t`–`x` boost with
     `cosh = c²+s²`, `sinh = 2cs`. The doubled angle is visible in the
     formulas, which is the factor of two a double cover is made of.
  3. **`matches_su2Z`** and **`matches_su2Y`** — and each family agrees
     with the SL₂ family on the nose: `ρ(rotorXY c s) = Λ(U_z(c,s))`
     and `ρ(rotorXZ c s) = Λ(U_y(c,s))`, for every `c² + s² = 1`. The
     matching problem is solved on two one-parameter subgroups rather
     than at a point.
  4. **`spin_hits_rotZ`**, **`spin_hits_rotY`**, **`spin_hits_boost`** —
     and with `LorentzSurjectivity.half_angle` (built for the SL₂ chain,
     never used elsewhere) plus its hyperbolic twin **`hyp_half_angle`**,
     built here because the estate did not have one, the parameter
     disappears: the spin image contains `rotZ a b`, `rotY a b` for EVERY
     point of the circle and every future-directed `t`–`x` boost. That is
     the exact analogue of `exists_su2_rotZ`/`exists_su2_rotY`.
  5. **`surjectivity_iff_spinImage_top`** and
     **`surjectivity_of_stabiliser_and_boosts`** — the reduction, and
     it is the mirror of `LorentzGroup.surjective_of_stabiliser_surjective`
     on the spin side. If every rotation and every Hermitian boost is in
     the spin image, the spin map is onto. So the two obligations the
     next units must discharge are named, separated, and each is a
     statement about a family the estate already understands.

  **SUPERSEDED 8 AUG 2026**: everything the paragraph below calls
  missing is proved in `SpinSurjective`, and BOTH named residues
  resolved unexpectedly — (α) was already proved and thrown away inside
  `stabiliser_surjective`, and (β) was never needed, because the orbit
  argument conjugates nothing. Left standing per the house rule.

  WHAT THIS DOES NOT DO. **It does not prove surjectivity, and it does
  not prove either hypothesis of item 5.** Item 4 puts every `rotZ`,
  every `rotY` and every `t`–`x` boost in the image; item 5's `hrot`
  needs additionally that every rotation is a PRODUCT of those, which is
  the Euler decomposition at matrix level — inside
  `stabiliser_surjective`'s proof and not exported — and its `hboost`
  needs that an arbitrary-direction boost is a rotation conjugate of a
  `t`–`x` one. §8 names both. `SpinQuotient.SurjectivityStatement` is
  still a `def`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SL2Quotient

namespace SpinRotorFamilies

open SpinVectorRep SpinToOrthogonal MinkowskiSignature LorentzGroup
open SpinToLorentzMat SpinOrthochronous SpinPair
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. Two general tools

`polar_coords` is the polarisation of `Q₁₃` in coordinates, which the
estate had only for the four basis vectors and for `SpinBoost.w`; every
reflection below needs the general form.

`endo_spinPair` is the missing bridge. `SpinPair` proves `pair_mem` and
`spinToEndo_pair` for every admissible pair, but a matrix computation
consumes `endo`, and the passage from one to the other appeared twice in
`SpinToLorentzMat` as `endo_R₁₂'` and `endo_B'` — the same three lines,
each written for one element. Written once here.
-/

theorem polar_coords (v u : V) :
    QuadraticMap.polar Q₁₃ v u
      = 2 * (v.1.1 * u.1.1 - v.1.2 * u.1.2 - v.2.1 * u.2.1 - v.2.2 * u.2.2) := by
  rw [QuadraticMap.polar, Q₁₃_apply, Q₁₃_apply, Q₁₃_apply]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- An admissible pair of vectors, as an element of the spin group. -/
def spinPair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) : spinGroup Q₁₃ :=
  ⟨((pair hv hw : Clˣ) : Cl), pair_mem hv hw hprod⟩

/-- **Its action, at the level every matrix computation consumes.** -/
theorem endo_spinPair {v w : V} (hv : Q₁₃ v ≠ 0) (hw : Q₁₃ w ≠ 0)
    (hprod : Q₁₃ v * Q₁₃ w = 1) (u : V) :
    endo (spinPair hv hw hprod) u = vreflect v (vreflect w u) := by
  rw [endo, spinToEndo_congr (toUnits_mem _) (pair_mem hv hw hprod) (Units.ext rfl) u]
  exact spinToEndo_pair hv hw hprod u

/-! ## 2. The three second vectors

Each family is a product of two unit vectors: one fixed basis vector and
one moving vector in the plane. The moving one carries the parameter.
The sign condition `Q₁₃ v · Q₁₃ w = 1` is what `SpinPair.pair_mem`
needs, and it holds for two SPACELIKE units (`(−1)(−1)`) and for two
TIMELIKE units (`(+1)(+1)`) — which is why the rotations use `e₁` and
the boost uses `e₀`, and why no family here mixes the two.
-/

/-- `c·e₁ + s·e₂`, a unit spacelike vector in the `x`–`y` plane. -/
def uXY (c s : ℝ) : V := ((0, c), (s, 0))

/-- `c·e₁ + s·e₃`, a unit spacelike vector in the `x`–`z` plane. -/
def uXZ (c s : ℝ) : V := ((0, c), (0, s))

/-- `c·e₀ + s·e₁`, a unit TIMELIKE vector in the `t`–`x` plane. -/
def wTX (c s : ℝ) : V := ((c, s), (0, 0))

theorem Q_uXY (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Q₁₃ (uXY c s) = -1 := by
  rw [Q₁₃_apply]; simp only [uXY]; nlinarith [h]

theorem Q_uXZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Q₁₃ (uXZ c s) = -1 := by
  rw [Q₁₃_apply]; simp only [uXZ]; nlinarith [h]

theorem Q_wTX (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) : Q₁₃ (wTX c s) = 1 := by
  rw [Q₁₃_apply]; simp only [wTX]; nlinarith [h]

theorem uXY_ne (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Q₁₃ (uXY c s) ≠ 0 := by
  rw [Q_uXY c s h]; norm_num

theorem uXZ_ne (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Q₁₃ (uXZ c s) ≠ 0 := by
  rw [Q_uXZ c s h]; norm_num

theorem wTX_ne (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) : Q₁₃ (wTX c s) ≠ 0 := by
  rw [Q_wTX c s h]; norm_num

theorem prod_uXY_e₁ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Q₁₃ (uXY c s) * Q₁₃ e₁ = 1 := by rw [Q_uXY c s h, Q₁₃_e₁]; norm_num

theorem prod_e₁_uXZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    Q₁₃ e₁ * Q₁₃ (uXZ c s) = 1 := by rw [Q_uXZ c s h, Q₁₃_e₁]; norm_num

theorem prod_e₀_wTX (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) :
    Q₁₃ e₀ * Q₁₃ (wTX c s) = 1 := by rw [Q_wTX c s h, Q₁₃_e₀]; norm_num

/-! ## 3. The reflections, in coordinates -/

theorem vreflect_uXY (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (u : V) :
    vreflect (uXY c s) u
      = ((-u.1.1, 2 * c * (c * u.1.2 + s * u.2.1) - u.1.2),
         (2 * s * (c * u.1.2 + s * u.2.1) - u.2.1, -u.2.2)) := by
  rw [vreflect, Q_uXY c s h, polar_coords]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    · simp only [uXY, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
        smul_eq_mul, inv_neg, inv_one]
      ring

theorem vreflect_uXZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (u : V) :
    vreflect (uXZ c s) u
      = ((-u.1.1, 2 * c * (c * u.1.2 + s * u.2.2) - u.1.2),
         (-u.2.1, 2 * s * (c * u.1.2 + s * u.2.2) - u.2.2)) := by
  rw [vreflect, Q_uXZ c s h, polar_coords]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    · simp only [uXZ, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
        smul_eq_mul, inv_neg, inv_one]
      ring

theorem vreflect_wTX (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (u : V) :
    vreflect (wTX c s) u
      = ((2 * c * (c * u.1.1 - s * u.1.2) - u.1.1,
          2 * s * (c * u.1.1 - s * u.1.2) - u.1.2),
         (-u.2.1, -u.2.2)) := by
  rw [vreflect, Q_wTX c s h, polar_coords]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    · simp only [wTX, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
        smul_eq_mul, inv_one]
      ring

/-! ## 4. The three families, and their actions

Each action is stated already in doubled-angle form, so that the matrix
computations in §5 are pure arithmetic. The doubling is where the
factor of two lives: the parameter `(c,s)` on the spin side produces
`(c²−s², 2cs)` on the Lorentz side.
-/

/-- The rotor in the `x`–`y` plane. -/
def rotorXY (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : spinGroup Q₁₃ :=
  spinPair (uXY_ne c s h) Q₁₃_e₁_ne (prod_uXY_e₁ c s h)

/-- The rotor in the `x`–`z` plane. -/
def rotorXZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : spinGroup Q₁₃ :=
  spinPair Q₁₃_e₁_ne (uXZ_ne c s h) (prod_e₁_uXZ c s h)

/-- The boost rotor in the `t`–`x` plane. -/
def booster (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) : spinGroup Q₁₃ :=
  spinPair Q₁₃_e₀_ne (wTX_ne c s h) (prod_e₀_wTX c s h)

theorem endo_rotorXY (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (u : V) :
    endo (rotorXY c s h) u
      = ((u.1.1, (c ^ 2 - s ^ 2) * u.1.2 - 2 * c * s * u.2.1),
         (2 * c * s * u.1.2 + (c ^ 2 - s ^ 2) * u.2.1, u.2.2)) := by
  rw [rotorXY, endo_spinPair, vreflect_e₁, vreflect_uXY c s h]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · ring
  · linear_combination u.1.2 * h
  · linear_combination (-u.2.1) * h
  · ring

theorem endo_rotorXZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (u : V) :
    endo (rotorXZ c s h) u
      = ((u.1.1, (c ^ 2 - s ^ 2) * u.1.2 + 2 * c * s * u.2.2),
         (u.2.1, -(2 * c * s) * u.1.2 + (c ^ 2 - s ^ 2) * u.2.2)) := by
  rw [rotorXZ, endo_spinPair, vreflect_uXZ c s h, vreflect_e₁]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · ring
  · linear_combination u.1.2 * h
  · ring
  · linear_combination (-u.2.2) * h

theorem endo_booster (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) (u : V) :
    endo (booster c s h) u
      = (((c ^ 2 + s ^ 2) * u.1.1 - 2 * c * s * u.1.2,
          -(2 * c * s) * u.1.1 + (c ^ 2 + s ^ 2) * u.1.2),
         (u.2.1, u.2.2)) := by
  rw [booster, endo_spinPair, vreflect_wTX c s h, vreflect_e₀]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · linear_combination u.1.1 * h
  · linear_combination (-u.1.2) * h
  · ring
  · ring

/-! ## 5. The Lorentz matrices

`rotZ` and `rotY` are `LorentzSurjectivity`'s own rotation matrices, so
the comparison in §6 is against the estate's objects rather than against
freshly written ones.
-/

/-- The `t`–`x` boost matrix with the given hyperbolic entries. -/
def boostMat (C S : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![C, -S, 0, 0; -S, C, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem spinToO13_rotorXY_matrix (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ((spinToO13 (rotorXY c s h) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ)
      = LorentzSurjectivity.rotZ (c ^ 2 - s ^ 2) (2 * c * s) := by
  ext i j
  rw [spinToO13_apply_entry, endo_rotorXY c s h, symm_single]
  fin_cases i <;> fin_cases j <;>
    norm_num [LorentzSurjectivity.rotZ, e₀, e₁, e₂, e₃]

theorem spinToO13_rotorXZ_matrix (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    ((spinToO13 (rotorXZ c s h) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ)
      = LorentzSurjectivity.rotY (c ^ 2 - s ^ 2) (2 * c * s) := by
  ext i j
  rw [spinToO13_apply_entry, endo_rotorXZ c s h, symm_single]
  fin_cases i <;> fin_cases j <;>
    norm_num [LorentzSurjectivity.rotY, e₀, e₁, e₂, e₃]

theorem spinToO13_booster_matrix (c s : ℝ) (h : c ^ 2 - s ^ 2 = 1) :
    ((spinToO13 (booster c s h) : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ)
      = boostMat (c ^ 2 + s ^ 2) (2 * c * s) := by
  ext i j
  rw [spinToO13_apply_entry, endo_booster c s h, symm_single]
  fin_cases i <;> fin_cases j <;>
    norm_num [boostMat, e₀, e₁, e₂, e₃]

/-! ## 6. The matching, family by family

`SL2Quotient.surjectivity_iff_matches_sl2` asks for a spinor matching
each `A ∈ SL₂(ℂ)`. Here are two one-parameter subgroups' worth.
-/

/-- `U_z(c,s)` as an element of Mathlib's SL₂(ℂ). -/
def su2Zelt (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : SL2C :=
  ⟨LorentzSurjectivity.su2Z c s, LorentzSurjectivity.det_su2Z c s h⟩

/-- `U_y(c,s)` as an element of Mathlib's SL₂(ℂ). -/
def su2Yelt (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : SL2C :=
  ⟨LorentzSurjectivity.su2Y c s, LorentzSurjectivity.det_su2Y c s h⟩

/-- **The whole `U_z` family is matched.** -/
theorem matches_su2Z (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    spinToSOplus (rotorXY c s h) = lorentzSOplusHom (su2Zelt c s h) := by
  refine Subtype.ext (Units.ext ?_)
  have hL : ((spinToSOplus (rotorXY c s h) : SOplus13)
      : Matrix.GeneralLinearGroup (Fin 4) ℝ).val
      = LorentzSurjectivity.rotZ (c ^ 2 - s ^ 2) (2 * c * s) :=
    spinToO13_rotorXY_matrix c s h
  rw [hL, lorentzSOplusHom_apply]
  change _ = lorentzMat (LorentzSurjectivity.su2Z c s)
  rw [LorentzSurjectivity.lorentzMat_su2Z c s h]

/-- **And the whole `U_y` family.** -/
theorem matches_su2Y (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    spinToSOplus (rotorXZ c s h) = lorentzSOplusHom (su2Yelt c s h) := by
  refine Subtype.ext (Units.ext ?_)
  have hL : ((spinToSOplus (rotorXZ c s h) : SOplus13)
      : Matrix.GeneralLinearGroup (Fin 4) ℝ).val
      = LorentzSurjectivity.rotY (c ^ 2 - s ^ 2) (2 * c * s) :=
    spinToO13_rotorXZ_matrix c s h
  rw [hL, lorentzSOplusHom_apply]
  change _ = lorentzMat (LorentzSurjectivity.su2Y c s)
  rw [LorentzSurjectivity.lorentzMat_su2Y c s h]

/-- Both statements in the shape `SL2Quotient.surjectivity_iff_matches_sl2`
    consumes: the matching problem, solved on two one-parameter
    subgroups. -/
theorem matching_on_su2_families (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom (su2Zelt c s h))
      ∧ (∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom (su2Yelt c s h)) :=
  ⟨⟨rotorXY c s h, matches_su2Z c s h⟩, ⟨rotorXZ c s h, matches_su2Y c s h⟩⟩

/-! ## 7. Every rotZ and every rotY, not just the parameterised ones

`LorentzSurjectivity.half_angle` — "every point of the circle is a
doubled point" — was built for the SL₂ chain and never used elsewhere.
It applies verbatim here, and turns §6's two families into a statement
with no parameter left in it: the spin image contains `rotZ a b` and
`rotY a b` for EVERY point of the circle. That is the exact analogue of
`exists_su2_rotZ` and `exists_su2_rotY`, now on the Clifford side.

The boost needs the hyperbolic twin, which the estate did NOT have —
the SL₂ chain reached boosts by `exists_hermitian_sqrt`, a different
route that produces a matrix rather than a half-parameter.
`hyp_half_angle` is that twin, and it is the same one-square-root
argument with the signs moved.
-/

/-- **The hyperbolic half-angle**: every `(C,S)` with `C² − S² = 1` and
    `C > 0` is `(c²+s², 2cs)` for some `(c,s)` with `c² − s² = 1`. The
    twin of `LorentzSurjectivity.half_angle`, absent from the estate
    because the SL₂ chain reached boosts another way. -/
theorem hyp_half_angle (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (hC : 0 < C) :
    ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ c ^ 2 + s ^ 2 = C ∧ 2 * c * s = S := by
  have hC1 : 1 ≤ C := by nlinarith [sq_nonneg S]
  have hpos : (0:ℝ) < (C + 1) / 2 := by linarith
  set c := Real.sqrt ((C + 1) / 2) with hcdef
  have hc2 : c ^ 2 = (C + 1) / 2 := Real.sq_sqrt hpos.le
  have hcpos : 0 < c := Real.sqrt_pos.mpr hpos
  have hs2 : (S / (2 * c)) ^ 2 = (C - 1) / 2 := by
    rw [div_pow, mul_pow, hc2]
    rw [show S ^ 2 = (C - 1) * (C + 1) by nlinarith]
    field_simp
  refine ⟨c, S / (2 * c), ?_, ?_, ?_⟩
  · rw [hs2, hc2]; ring
  · rw [hs2, hc2]; ring
  · field_simp

/-- **Every `rotZ` is in the spin image.** -/
theorem spin_hits_rotZ (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ g : spinGroup Q₁₃,
      ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
        : Matrix (Fin 4) (Fin 4) ℝ) = LorentzSurjectivity.rotZ a b := by
  obtain ⟨c, s, hcs, hca, hcb⟩ := LorentzSurjectivity.half_angle a b h
  exact ⟨rotorXY c s hcs, by rw [spinToO13_rotorXY_matrix c s hcs, hca, hcb]⟩

/-- **Every `rotY` is in the spin image.** -/
theorem spin_hits_rotY (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ g : spinGroup Q₁₃,
      ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
        : Matrix (Fin 4) (Fin 4) ℝ) = LorentzSurjectivity.rotY a b := by
  obtain ⟨c, s, hcs, hca, hcb⟩ := LorentzSurjectivity.half_angle a b h
  exact ⟨rotorXZ c s hcs, by rw [spinToO13_rotorXZ_matrix c s hcs, hca, hcb]⟩

/-- **Every future-directed `t`–`x` boost is in the spin image.** -/
theorem spin_hits_boost (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (hC : 0 < C) :
    ∃ g : spinGroup Q₁₃,
      ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
        : Matrix (Fin 4) (Fin 4) ℝ) = boostMat C S := by
  obtain ⟨c, s, hcs, hcC, hcS⟩ := hyp_half_angle C S h hC
  exact ⟨booster c s hcs, by rw [spinToO13_booster_matrix c s hcs, hcC, hcS]⟩

/-! ## 8. The image as a subgroup, and the reduction

The mirror of `LorentzGroup.surjective_of_stabiliser_surjective`, on the
spin side. Every `M ∈ SO⁺(1,3)` factors as a Hermitian boost times a
rotation, by `exists_boost_factor`; if both factors are in the spin
image then so is `M`, because the image is a subgroup.

**Neither hypothesis is proved, and the gap between them and §7 is
exactly two named facts.** §7 puts every `rotZ`, every `rotY` and every
future-directed `t`–`x` boost in the image. `hrot` additionally needs
that every rotation is a product of `rotZ`s and `rotY`s — the Euler
decomposition at the level of ROTATION MATRICES, which exists inside
`LorentzSurjectivity.stabiliser_surjective`'s proof and is not exported.
`hboost` additionally needs that a boost in an arbitrary spatial
direction is a rotation conjugate of a `t`–`x` boost. Both are named
work items, neither is done here, and the residue is stated as
hypotheses rather than as prose so that a reader can see its exact
shape.
-/

/-- The spin image, as a subgroup object rather than as a predicate.
    §7's three theorems are membership facts about it, and what remains
    is whether they generate. -/
def spinImage : Subgroup SOplus13 := MonoidHom.range spinToSOplus

/-- **Surjectivity is exactly `spinImage = ⊤`.** Stated so that later
    units can argue by subgroup closure instead of by writing explicit
    products of matrices. -/
theorem surjectivity_iff_spinImage_top :
    SpinQuotient.SurjectivityStatement ↔ spinImage = ⊤ := by
  rw [spinImage, MonoidHom.range_eq_top]
  constructor
  · exact SpinQuotient.surjectivityStatement_implies
  · intro h M
    obtain ⟨g, hg⟩ := h M
    exact ⟨QuotientGroup.mk g, hg⟩

/-- **Surjectivity of the spin map reduces to rotations and boosts
    separately.** -/
theorem surjectivity_of_stabiliser_and_boosts
    (hrot : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat R → R.det = 1 →
        (∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) →
        ∃ g : spinGroup Q₁₃,
          ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
            : Matrix (Fin 4) (Fin 4) ℝ) = R)
    (hboost : ∀ S : Matrix (Fin 2) (Fin 2) ℂ, S.det = 1 → Sᴴ = S →
        ∃ g : spinGroup Q₁₃,
          ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
            : Matrix (Fin 4) (Fin 4) ℝ) = lorentzMat S) :
    SpinQuotient.SurjectivityStatement := by
  change Function.Surjective SpinQuotient.spinQuotEmbed
  intro M
  obtain ⟨hlor, hdet, h0⟩ := M.2
  obtain ⟨S, R, hSdet, hSherm, hRlor, hRdet, hRcol, hfac⟩ :=
    exists_boost_factor hlor hdet h0
  obtain ⟨g₁, hg₁⟩ := hboost S hSdet hSherm
  obtain ⟨g₂, hg₂⟩ := hrot R hRlor hRdet hRcol
  refine ⟨QuotientGroup.mk (g₁ * g₂), ?_⟩
  rw [SpinQuotient.spinQuotEmbed_mk, map_mul]
  refine Subtype.ext (Units.ext ?_)
  change ((spinToO13 g₁ : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ)
    * ((spinToO13 g₂ : Matrix.GeneralLinearGroup (Fin 4) ℝ)
      : Matrix (Fin 4) (Fin 4) ℝ) = _
  rw [hg₁, hg₂, ← hfac]

/-! ## 9. Review round 32 — that the families are families

Four ways §§4–6 could say less than they look like they say.

* If the three families were constant in `(c,s)` they would be three
  elements with a decoration. They are not: distinct parameters give
  distinct Lorentz matrices.
* If the families were already inside the estate's two hand-built
  elements, this would be repackaging. They are not — `R₁₂'` and `B'`
  are single points of them, which is the right relation and is proved
  rather than asserted.
* If the doubled angle were not doubled the matching would be against
  the wrong SL₂ elements. `rotorXY` at `(c,s) = (√2/2, √2/2)` — a
  quarter turn on the spin side — gives the HALF turn `diag(1,−1,−1,1)`.
* If `boostMat` were not a Lorentz matrix the boost family would land
  outside the group it claims to.
-/

/-- `R₁₂'` is a point of the rotor family, so §4 subsumes it. -/
theorem rotorXY_at_zero_one :
    spinToO13 (rotorXY 0 1 (by norm_num))
      = spinToO13 R₁₂' := by
  refine Subtype.ext (Units.ext ?_)
  rw [spinToO13_R₁₂'_matrix]
  have h := spinToO13_rotorXY_matrix 0 1 (by norm_num)
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LorentzSurjectivity.rotZ, Matrix.diagonal]

/-- `B'` is a point of the boost family, at `(5/4, 3/4)` — the estate's
    `17/8` and `15/8` are `c²+s²` and `2cs`. -/
theorem booster_at_five_four :
    spinToO13 (booster (5/4) (3/4) (by norm_num))
      = spinToO13 B' := by
  refine Subtype.ext (Units.ext ?_)
  rw [spinToO13_B'_matrix]
  have h := spinToO13_booster_matrix (5/4) (3/4) (by norm_num)
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boostMat]

/-- **The rotor family is not constant.** Two parameter values with
    different Lorentz matrices. -/
theorem rotorXY_nonconstant :
    spinToO13 (rotorXY 1 0 (by norm_num)) ≠ spinToO13 (rotorXY 0 1 (by norm_num)) := by
  intro hc
  have h1 := spinToO13_rotorXY_matrix 1 0 (by norm_num)
  have h2 := spinToO13_rotorXY_matrix 0 1 (by norm_num)
  have hm : LorentzSurjectivity.rotZ ((1:ℝ) ^ 2 - 0 ^ 2) (2 * 1 * 0)
      = LorentzSurjectivity.rotZ ((0:ℝ) ^ 2 - 1 ^ 2) (2 * 0 * 1) := by
    rw [← h1, ← h2]
    exact congrArg (fun y : O13 =>
      ((y : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)) hc
  have h11 := Matrix.ext_iff.mpr hm 1 1
  norm_num [LorentzSurjectivity.rotZ] at h11

/-- **The boost family is not constant either.** -/
theorem booster_nonconstant :
    spinToO13 (booster 1 0 (by norm_num))
      ≠ spinToO13 (booster (5/4) (3/4) (by norm_num)) := by
  intro hc
  have h1 := spinToO13_booster_matrix 1 0 (by norm_num)
  have h2 := spinToO13_booster_matrix (5/4) (3/4) (by norm_num)
  have hm : boostMat ((1:ℝ) ^ 2 + 0 ^ 2) (2 * 1 * 0)
      = boostMat ((5/4:ℝ) ^ 2 + (3/4) ^ 2) (2 * (5/4) * (3/4)) := by
    rw [← h1, ← h2]
    exact congrArg (fun y : O13 =>
      ((y : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)) hc
  have h00 := Matrix.ext_iff.mpr hm 0 0
  norm_num [boostMat] at h00

theorem sq_root_two_half : (Real.sqrt 2 / 2) ^ 2 + (Real.sqrt 2 / 2) ^ 2 = 1 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **The angle really is doubled**, on a second parameter value where
    both descriptions are recognisable. `(√2/2, √2/2)` is the 45° rotor,
    and its image is the QUARTER turn `rotZ(0,1)` — while `(0,1)`, the
    90° rotor, gives the HALF turn above. Two points, both doubled. -/
theorem rotorXY_root_two :
    ((spinToO13 (rotorXY (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) sq_root_two_half)
      : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
      = LorentzSurjectivity.rotZ 0 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [spinToO13_rotorXY_matrix]
  congr 1
  · ring
  · linear_combination h2 / 2

/-- **`boostMat` is a Lorentz matrix**, so §5's boost family lands where
    it says it does — checked independently of the spin chain. -/
theorem boostMat_isLorentz (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) :
    IsLorentzMat (boostMat C S) := by
  have hg : (gram : Matrix (Fin 4) (Fin 4) ℝ) = Matrix.diagonal ![1, -1, -1, -1] := rfl
  rw [IsLorentzMat, hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.transpose_apply] <;>
    linarith [h]

end

end SpinRotorFamilies
