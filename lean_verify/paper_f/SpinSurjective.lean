/-
  SpinSurjective.lean — the spin map is onto SO⁺(1,3). W7 step (d).

  WHY. This is the last part of W7 step (d), and the wall entry has
  called it research-level since it was written. `SpinRotorFamilies`
  reduced it to two named facts about matrices:

    (α) every rotation is a product of `rotZ`s and `rotY`s;
    (β) a boost in an arbitrary spatial direction is a rotation
        conjugate of a `t`–`x` boost.

  (α) turned out to be already proved and then thrown away —
  `LorentzSurjectivity.stabiliser_euler`, exported earlier today from
  the interior of `stabiliser_surjective`'s proof, where it was used to
  build an SL₂(ℂ) word and discarded. (β) is not needed in the form it
  was stated: instead of conjugating a boost, this file uses the ORBIT
  argument, which needs no conjugation at all. **Recorded because the
  estimate was published before the work: (α) was as cheap as predicted
  and (β) was avoidable, which the prediction did not see.**

  THE ARGUMENT, in four sentences. The spin image is a subgroup of
  SO⁺(1,3). It contains every rotation, by (α) together with
  `spin_hits_rotZ`/`spin_hits_rotY`, and every `t`–`x` boost, by
  `spin_hits_boost`. Given `M ∈ SO⁺(1,3)`, its first column is a future
  unit timelike vector `(t,x,y,z)`; a `t`–`x` boost carries `e₀` to
  `(t,ρ,0,0)` with `ρ = √(t²−1)`, and a rotation carries that to
  `(t,x,y,z)` — so the image contains an `N` with the same first column
  as `M`, and then `N⁻¹M` fixes `e₀`, hence is a rotation, hence is in
  the image. `M = N·(N⁻¹M)`. ∎

  WHAT THIS FILE PROVES:
  1. `lmat` and its arithmetic — the Lorentz matrix of a spin element as
     a plain matrix, multiplicative, with inverses. **After §1 no
     Clifford algebra appears anywhere in the file**; everything else is
     4×4 real matrix algebra.
  2. **`spin_hits_rotation`** — every time-axis-fixing Lorentz rotation
     is in the spin image. Fact (α), discharged.
  3. **`exists_rot_first_col`** — rotations act transitively on spheres,
     in the form the orbit argument wants. Built from
     `exists_unit_pair`, which is the "normalise, or take `(1,0)` at
     length zero" construction `stabiliser_surjective` performs inline;
     needed twice here, so extracted.
  4. **`spin_surjective`** — every proper orthochronous Lorentz matrix
     is the Lorentz matrix of a spin element.
  5. **`spinToSOplus_surjective`** and **`surjectivityStatement`** — the
     bundled forms. The `def` `SpinQuotient` introduced this morning to
     make the gap an object is now a theorem.
  6. **`spinDoubleCover : Spin(1,3) ⧸ {±1} ≃* SO⁺(1,3)`** — W7 step (d),
     closed — and **`spinEquivSL2Quot`**, which identifies the two
     chains: `SL2Quotient` built an injection `Spin(1,3) ⧸ {±1} ↪
     SL₂(ℂ) ⧸ {±1}` and said an injection is not an isomorphism. It is
     one now.

  WHAT IS STILL NOT TRUE, and ASSUMPTIONS 42 exists for this paragraph.
  **This is an ALGEBRAIC double cover, not a topological one.**
  `spinGroup Q₁₃` is Mathlib's algebraic object — the even unitary part
  of the Clifford algebra — and `SOplus13` is the algebraic definition
  of the proper orthochronous group, `det = 1` together with `Λ⁰₀ > 0`.
  **No topology appears anywhere in the chain**, so neither "the
  simply-connected double cover" nor "the identity component of O(1,3)"
  is proved, and neither follows from anything here. What §5 proves is
  an isomorphism of abstract groups, and the two sentences above are the
  ones a reader is most likely to substitute for it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinRotorFamilies

namespace SpinSurjective

open SpinVectorRep SpinToOrthogonal MinkowskiSignature LorentzGroup
open SpinToLorentzMat SpinDetOne SpinOrthochronous SpinRotorFamilies
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. The Lorentz matrix of a spin element, as a plain matrix

`lmat` is the last place the Clifford algebra appears. The three
restatements at the end of the section are `SpinRotorFamilies`' results
in this notation, and hold by definitional equality — they exist so that
nothing below has to unfold a coercion tower.
-/

/-- The Lorentz matrix of a spin element. -/
def lmat (g : spinGroup Q₁₃) : Matrix (Fin 4) (Fin 4) ℝ :=
  ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)

theorem lmat_mul (g h : spinGroup Q₁₃) : lmat (g * h) = lmat g * lmat h := by
  rw [lmat, lmat, lmat, map_mul]; rfl

theorem lmat_one : lmat (1 : spinGroup Q₁₃) = 1 := by
  rw [lmat, map_one]; rfl

theorem lmat_inv_mul (g : spinGroup Q₁₃) : lmat g⁻¹ * lmat g = 1 := by
  rw [← lmat_mul, inv_mul_cancel, lmat_one]

theorem lmat_mul_inv (g : spinGroup Q₁₃) : lmat g * lmat g⁻¹ = 1 := by
  rw [← lmat_mul, mul_inv_cancel, lmat_one]

theorem lmat_isLorentz (g : spinGroup Q₁₃) : IsLorentzMat (lmat g) := (spinToO13 g).2

theorem lmat_det (g : spinGroup Q₁₃) : (lmat g).det = 1 := det_spinToO13_eq_one g

theorem lmat_rotZ (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ g : spinGroup Q₁₃, lmat g = LorentzSurjectivity.rotZ a b := spin_hits_rotZ a b h

theorem lmat_rotY (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ g : spinGroup Q₁₃, lmat g = LorentzSurjectivity.rotY a b := spin_hits_rotY a b h

theorem lmat_boost (C S : ℝ) (h : C ^ 2 - S ^ 2 = 1) (hC : 0 < C) :
    ∃ g : spinGroup Q₁₃, lmat g = boostMat C S := spin_hits_boost C S h hC

/-! ## 2. Fact (α): every rotation is in the spin image -/

/-- **Every time-axis-fixing Lorentz rotation is the Lorentz matrix of a
    spin element.** -/
theorem spin_hits_rotation (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : IsLorentzMat R)
    (hdet : R.det = 1) (hcol : ∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i) :
    ∃ g : spinGroup Q₁₃, lmat g = R := by
  obtain ⟨a, b, p, q, u, v, hab, hpq, huv, heq⟩ :=
    LorentzSurjectivity.stabiliser_euler R hR hdet hcol
  obtain ⟨g1, h1⟩ := lmat_rotZ a b hab
  obtain ⟨g2, h2⟩ := lmat_rotY p q hpq
  obtain ⟨g3, h3⟩ := lmat_rotZ u v huv
  exact ⟨g1 * (g2 * g3), by rw [lmat_mul, lmat_mul, h1, h2, h3, heq]⟩

/-! ## 3. Rotations act transitively on spheres -/

/-- Any `(x,y)` of length `σ` is `σ·(p,q)` for a point `(p,q)` of the
    unit circle. Written multiplicatively so that `σ = 0` — where there
    is no direction to normalise — needs no special case downstream. -/
theorem exists_unit_pair (x y σ : ℝ) (hσ : 0 ≤ σ) (h : x ^ 2 + y ^ 2 = σ ^ 2) :
    ∃ p q : ℝ, p ^ 2 + q ^ 2 = 1 ∧ p * σ = x ∧ q * σ = y := by
  by_cases hz : σ = 0
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    exact ⟨1, 0, by norm_num, by rw [hz, hx]; ring, by rw [hz, hy]; ring⟩
  · have hpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
    refine ⟨x / σ, y / σ, ?_, by field_simp, by field_simp⟩
    field_simp
    linarith [h]

/-- **The transitivity, in the form the orbit argument wants.** For any
    `(x,y,z)` of length `ρ` there is a time-axis-fixing Lorentz rotation
    whose first spatial column is `(x,y,z)/ρ` — stated as three products
    with `ρ` so that `ρ = 0` is not a case. -/
theorem exists_rot_first_col (x y z ρ : ℝ) (hρ : 0 ≤ ρ)
    (hn : x ^ 2 + y ^ 2 + z ^ 2 = ρ ^ 2) :
    ∃ R : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat R ∧ R.det = 1
      ∧ (∀ i, R i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i)
      ∧ R 0 1 = 0 ∧ R 1 1 * ρ = x ∧ R 2 1 * ρ = y ∧ R 3 1 * ρ = z := by
  set σ := Real.sqrt (x ^ 2 + y ^ 2) with hσdef
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_unit_pair σ (-z) ρ hρ (by rw [hσ2]; linarith [hn])
  obtain ⟨p, q, hpq, hp, hq⟩ := exists_unit_pair x y σ hσ0 hσ2.symm
  refine ⟨LorentzSurjectivity.rotZ p q * LorentzSurjectivity.rotY a b,
    (LorentzSurjectivity.rotZ_facts p q hpq).1.mul
      (LorentzSurjectivity.rotY_facts a b hab).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, (LorentzSurjectivity.rotZ_facts p q hpq).2,
      (LorentzSurjectivity.rotY_facts a b hab).2]
    ring
  · intro i
    rw [Matrix.mul_apply, Fin.sum_univ_four, Pi.single_apply]
    fin_cases i <;> simp [LorentzSurjectivity.rotZ, LorentzSurjectivity.rotY]
  · rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [LorentzSurjectivity.rotZ, LorentzSurjectivity.rotY]
  · rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [LorentzSurjectivity.rotZ, LorentzSurjectivity.rotY]
    linear_combination p * ha + hp
  · rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [LorentzSurjectivity.rotZ, LorentzSurjectivity.rotY]
    linear_combination q * ha + hq
  · rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [LorentzSurjectivity.rotZ, LorentzSurjectivity.rotY]
    linear_combination -hb

/-! ## 4. The orbit argument -/

/-- **Every proper orthochronous Lorentz matrix is the Lorentz matrix of
    a spin element.** W7 step (d)'s last part. -/
theorem spin_surjective (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : IsLorentzMat M)
    (hdet : M.det = 1) (h0 : 0 < M 0 0) : ∃ g : spinGroup Q₁₃, lmat g = M := by
  have hn : M 0 0 ^ 2 - M 1 0 ^ 2 - M 2 0 ^ 2 - M 3 0 ^ 2 = 1 := col_zero_norm hM
  set ρ := Real.sqrt (M 1 0 ^ 2 + M 2 0 ^ 2 + M 3 0 ^ 2) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = M 1 0 ^ 2 + M 2 0 ^ 2 + M 3 0 ^ 2 := Real.sq_sqrt (by positivity)
  -- the boost carrying `e₀` to `(t, ρ, 0, 0)`
  have hbc : M 0 0 ^ 2 - (-ρ) ^ 2 = 1 := by rw [neg_pow, hρ2]; linarith [hn]
  obtain ⟨gB, hgB⟩ := lmat_boost (M 0 0) (-ρ) hbc h0
  -- the rotation carrying `(t, ρ, 0, 0)` to the first column of `M`
  obtain ⟨R, hRlor, hRdet, hRcol, hR01, hR11, hR21, hR31⟩ :=
    exists_rot_first_col (M 1 0) (M 2 0) (M 3 0) ρ hρ0 hρ2.symm
  obtain ⟨gR, hgR⟩ := spin_hits_rotation R hRlor hRdet hRcol
  have hR00 : R 0 0 = 1 := by rw [hRcol 0]; simp
  have hR10 : R 1 0 = 0 := by rw [hRcol 1]; simp
  have hR20 : R 2 0 = 0 := by rw [hRcol 2]; simp
  have hR30 : R 3 0 = 0 := by rw [hRcol 3]; simp
  have hNval : lmat (gR * gB) = R * boostMat (M 0 0) (-ρ) := by
    rw [lmat_mul, hgR, hgB]
  -- the product has the same first column as `M`
  have hcolN : ∀ i, lmat (gR * gB) i 0 = M i 0 := by
    intro i
    rw [hNval, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i
    · simp only [boostMat]
      simp [hR00, hR01]
    · simp only [boostMat]
      simp [hR10]
      linarith [hR11]
    · simp only [boostMat]
      simp [hR20]
      linarith [hR21]
    · simp only [boostMat]
      simp [hR30]
      linarith [hR31]
  -- the residue fixes the time axis, hence is a rotation
  set K := lmat (gR * gB)⁻¹ * M with hKdef
  have hKlor : IsLorentzMat K := (lmat_isLorentz _).mul hM
  have hKdet : K.det = 1 := by rw [hKdef, Matrix.det_mul, lmat_det, hdet]; ring
  have hKcol : ∀ i, K i 0 = (Pi.single (0 : Fin 4) 1 : Fin 4 → ℝ) i := by
    intro i
    have hsame : K i 0 = (lmat (gR * gB)⁻¹ * lmat (gR * gB)) i 0 := by
      rw [hKdef, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hcolN k]
    rw [hsame, lmat_inv_mul, Matrix.one_apply, Pi.single_apply]
  obtain ⟨gK, hgK⟩ := spin_hits_rotation K hKlor hKdet hKcol
  refine ⟨gR * gB * gK, ?_⟩
  rw [lmat_mul, hgK, hKdef, ← Matrix.mul_assoc, lmat_mul_inv, Matrix.one_mul]

/-! ## 5. The bundled forms, and W7 step (d) -/

/-- **`spinToSOplus` is surjective.** -/
theorem spinToSOplus_surjective : Function.Surjective spinToSOplus := by
  intro M
  obtain ⟨hlor, hdet, h0⟩ := M.2
  obtain ⟨g, hg⟩ := spin_surjective _ hlor hdet h0
  exact ⟨g, Subtype.ext (Units.ext hg)⟩

/-- **The gap `SpinQuotient` named as a `def` this morning is
    discharged.** -/
theorem surjectivityStatement : SpinQuotient.SurjectivityStatement := by
  change Function.Surjective SpinQuotient.spinQuotEmbed
  intro M
  obtain ⟨g, hg⟩ := spinToSOplus_surjective M
  exact ⟨QuotientGroup.mk g, hg⟩

/-- **W7 STEP (d): `Spin(1,3) ⧸ {±1} ≅ SO⁺(1,3)`**, as a single
    isomorphism. -/
def spinDoubleCover : SpinQuotient.SpinQuot ≃* SOplus13 :=
  MulEquiv.ofBijective SpinQuotient.spinQuotEmbed
    ⟨SpinQuotient.spinQuotEmbed_injective, surjectivityStatement⟩

@[simp] theorem spinDoubleCover_mk (g : spinGroup Q₁₃) :
    spinDoubleCover (QuotientGroup.mk g) = spinToSOplus g := rfl

/-- **And the two chains are the same group.** -/
def spinEquivSL2Quot : SpinQuotient.SpinQuot ≃* SL2Quotient.SL2Quot :=
  spinDoubleCover.trans SL2Quotient.sl2QuotEquiv.symm

theorem spinEquivSL2Quot_mk (g : spinGroup Q₁₃) :
    spinEquivSL2Quot (QuotientGroup.mk g)
      = SL2Quotient.sl2QuotEquiv.symm (spinToSOplus g) := rfl

/-- The matching problem of `SL2Quotient.surjectivity_iff_matches_sl2`,
    solved in general: every SL₂(ℂ) matrix's Lorentz transformation is
    realised by a spinor. `SL2Quotient.spin_realised_by_sl2` was the
    converse, so the two chains realise exactly the same
    transformations. -/
theorem matches_every_sl2 (A : SL2C) :
    ∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom A :=
  SL2Quotient.surjectivity_iff_matches_sl2.1 surjectivityStatement A

/-! ## 6. Review round 33 — that §5 is about a nontrivial group

Three ways §5 could be true and empty, and one way the assembly could
be reaching less than it claims.
-/

theorem spinDoubleCover_nontrivial :
    ∃ x : SpinQuotient.SpinQuot, spinDoubleCover x ≠ 1 :=
  ⟨QuotientGroup.mk R₁₂', SpinQuotient.spinQuotEmbed_ne_one⟩

/-- The cover is genuinely DOUBLE: `g` and `−g` are distinct spin
    elements with the same Lorentz matrix, so the quotient in §5 is not
    a quotient by nothing. -/
theorem fibre_has_two (g : spinGroup Q₁₃) :
    SpinFibre.negSpin g ≠ g
      ∧ spinToSOplus (SpinFibre.negSpin g) = spinToSOplus g := by
  refine ⟨SpinFibre.negSpin_ne g, Subtype.ext ?_⟩
  exact congrArg (fun M : O13 => (M : Matrix.GeneralLinearGroup (Fin 4) ℝ))
    (SpinFibre.spinToO13_negSpin g)

/-- **The rotation leg is exercised at a nontrivial rotation**, and the
    answer agrees with the matrix `SpinToLorentzMat` computed for the
    π-rotation by an unrelated route. -/
theorem rotation_leg_nontrivial :
    ∃ g : spinGroup Q₁₃, lmat g = Matrix.diagonal ![1, -1, -1, 1] :=
  ⟨R₁₂', spinToO13_R₁₂'_matrix⟩

/-- **The boost leg is exercised at a nontrivial boost**, against the
    `17/8` figure the estate computed for `B'`. -/
theorem boost_leg_nontrivial :
    ∃ g : spinGroup Q₁₃, lmat g = boostMat (17/8) (15/8) :=
  lmat_boost (17/8) (15/8) (by norm_num) (by norm_num)

/-- **And the surjection reaches outside both generating families.** A
    boost in the `y` direction moves the time axis out of the `t`–`x`
    plane, so it is neither a rotation nor a `t`–`x` boost; its first
    column is `(17/8, 0, −(15/8), 0)`. If §4's assembly were quietly
    reaching only the generators, this would fail. -/
theorem reaches_off_family :
    ∃ g : spinGroup Q₁₃,
      lmat g 0 0 = 17/8 ∧ lmat g 1 0 = 0 ∧ lmat g 2 0 = -(15/8) := by
  obtain ⟨gR, hgR⟩ := lmat_rotZ 0 1 (by norm_num)
  obtain ⟨gB, hgB⟩ := lmat_boost (17/8) (15/8) (by norm_num) (by norm_num)
  have hprod : lmat (gR * gB)
      = LorentzSurjectivity.rotZ 0 1 * boostMat (17/8) (15/8) := by
    rw [lmat_mul, hgR, hgB]
  refine ⟨gR * gB, ?_, ?_, ?_⟩ <;>
    · rw [hprod, Matrix.mul_apply, Fin.sum_univ_four]
      simp [LorentzSurjectivity.rotZ, boostMat]

end

end SpinSurjective
