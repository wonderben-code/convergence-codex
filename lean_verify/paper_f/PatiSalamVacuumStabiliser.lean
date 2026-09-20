/-
  PatiSalamVacuumStabiliser: the vacuum as an object, the unbroken algebra as its stabiliser,
  and hypercharge FORCED as the part of `u(1)_{B−L} ⊕ su(2)_R` that fixes the vacuum

  Campaign 3 hardening unit 178 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. L15's row says what the Higgs sector's Lean does not have: *no VEV as an object, no
  Goldstone theorem (the counting theorems are literal arithmetic), no `(1,2,2)` as a
  representation*; and `PatiSalamRightSector`'s own header says *no group, no bracket, no
  representation … `Submodule.span` is not spontaneous symmetry breaking*, and that hypercharge
  `Y = T₃R + (B − L)/2` is a convention. This file supplies the objects those sentences miss, at
  the level a finite-dimensional real Lie algebra allows: a representation, a vacuum vector, and
  the stabiliser of the vacuum — the unbroken directions — computed, with hypercharge coming out
  rather than going in.

  WHAT IS PROVED.
  (1) `act A B X = A * X + X * Bᵀ` on `Bidoublet := Matrix (Fin 4) (Fin 2) ℂ` — the
      `(4, 1, 2)` space, `su(4)` on the colour–lepton index and `su(2)_R` on the doublet index —
      and `act_bracket`: `act ⁅A₁, A₂⁆ ⁅B₁, B₂⁆ = ⁅act A₁ B₁, act A₂ B₂⁆`, for ALL matrices. It is
      a representation of the product Lie algebra, at the matrix level, with no hypothesis.
  (2) `vac := single 3 0 1`: the vacuum direction — the lepton row, the `T₃R = +½` column, the
      `ν^c` slot. `act_vac_eq_zero_iff`: `(A, B)` fixes it iff the last column of `A` vanishes off
      the corner, `A 3 3 + B 0 0 = 0`, and `B 1 0 = 0` — three entry conditions.
  (3) `orbitMap : traceless 4 × traceless 2 →ₗ[ℝ] Bidoublet`, `p ↦ act p.1 p.2 vac`, on the
      estate's own `su(4) ⊕ su(2)_R` (`TracelessSkewDimension.traceless`), and
      `stab := ker orbitMap` — **the unbroken subalgebra as a kernel**, `mem_stab_iff` its
      entrywise form; `stab_row_zero`: in `stab` the `su(4)` component is block-diagonal.
  (4) `yG_mem_stab`: hypercharge — `PatiSalamRightSector.yRep = (blT, 3 • t3RT)`, that is
      `6i · Y` — fixes the vacuum. `ofRight_mem_stab_iff`: **an element of `u(1)_{B−L} ⊕ su(2)_R`
      fixes the vacuum IF AND ONLY IF it lies on the hypercharge line.** So the surviving direction
      of the right sector is not chosen: given the vacuum, it is computed, and it is `Y`.

  NOT PROVED, said exactly.
  • The VACUUM DIRECTION is a convention. `vac = E₃₀` is the standard `ν^c` slot; nothing here
    derives it, and a different vector has a different stabiliser. What is no longer a convention
    is hypercharge GIVEN the vacuum — the file's contribution is that one implication.
  • No dynamics: no potential, no minimisation, no mass, no Goldstone theorem. *Symmetry
    breaking* here means exactly *the stabiliser of a vector*, and nothing else.
  • The DIMENSIONS are not computed here. That `finrank ℝ stab = 9` (`stab ≅ u(3)`) and that the
    quotient — the broken directions — has dimension `9 = 18 − 9`, matching
    `PatiSalamRightSector.broken_nine`'s `6 + 3`, is the next unit; this file proves membership
    statements and one biconditional, not a rank.
    ⚠ DONE, 20 September 2026 (hardening unit 179, `paper_f/PatiSalamStabiliserDimension.lean`):
    `stabEquivU3 : stab ≃ₗ[ℝ] skewAdjoint (Matrix (Fin 3) (Fin 3) ℂ)`, `finrank_stab = 9`,
    `finrank_broken = 9`, and `broken_exact` — the `6 + 3` as a short exact sequence
    `0 → RightSector ⧸ hyperchargeLine → PSLie ⧸ stab → (Fin 3 → ℂ) → 0`. The bullet is kept as
    written (`ERRATUM 94`); the leptoquark bullet below is answered by the same sequence's
    right-hand map.
  • The six leptoquark directions (`PatiSalamOffDiagonal.offDiagMapR`'s range) are not related
    to `stab` here; only the right sector is.
  • No group, no exponential, no `LieModule` instance: the bracket law is a matrix identity and
    the Lie algebra is a pair of `ℝ`-subspaces, as in the files this one extends.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `act_bracket` and `act_vac_apply` take
  arbitrary complex matrices; `act_vac_eq_zero_iff` is an unconditional biconditional;
  `ofRight_mem_stab_iff` quantifies over all of `RightSector`; `stab_row_zero` takes `p ∈ stab`.
  No theorem takes a positivity, hermiticity or non-degeneracy hypothesis beyond membership in
  `traceless n`, which is skew-adjointness and zero trace.

  NAMESAKES (`newnames_scan`, run after writing rather than before — a lapse against
  `ERRATUM 270`'s rule, recorded in the log). `act` is also `AlgebraicCurvature.act` (a
  curvature action), `vac` also `CascadeGNS.vac` (the GNS cyclic vector), `mat4` also
  `LovelockActComposition.mat4` (a `4 × 4` matrix); each lives in its own namespace and none is
  the object here. The one-letter `G` the first draft used was renamed `PSLie`.
-/

import PatiSalamRightSector

open Matrix TracelessSkewDimension PatiSalamRightSector

namespace PatiSalamVacuumStabiliser

/-- The `(4, 1, 2)` space: `4 × 2` complex matrices, colour–lepton index by doublet index. -/
abbrev Bidoublet := Matrix (Fin 4) (Fin 2) ℂ

/-- `su(4)` on the left, `su(2)_R` on the right (through the transpose, so that it is a left
action on the doublet index). -/
noncomputable def act (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (X : Bidoublet) : Bidoublet :=
  A * X + X * Bᵀ

/-- **`act` IS A REPRESENTATION**: the bracket law, for all matrices, with no hypothesis. -/
theorem act_bracket (A₁ A₂ : Matrix (Fin 4) (Fin 4) ℂ) (B₁ B₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (X : Bidoublet) :
    act ⁅A₁, A₂⁆ ⁅B₁, B₂⁆ X = act A₁ B₁ (act A₂ B₂ X) - act A₂ B₂ (act A₁ B₁ X) := by
  simp only [act, Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- The vacuum direction: the lepton row, the `T₃R = +½` column — the `ν^c` slot. -/
noncomputable def vac : Bidoublet := Matrix.single 3 0 1

/-- The entries of `act A B vac`. -/
theorem act_vac_apply (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4)
    (j : Fin 2) :
    act A B vac i j
      = (if (0 : Fin 2) = j then A i 3 else 0) + (if (3 : Fin 4) = i then B j 0 else 0) := by
  simp only [act, vac, Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.transpose_apply]
  simp [Finset.sum_ite_eq, ite_and]

/-- **FIXING THE VACUUM, ENTRYWISE**: three conditions. -/
theorem act_vac_eq_zero_iff (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    act A B vac = 0 ↔ (∀ i, i ≠ 3 → A i 3 = 0) ∧ A 3 3 + B 0 0 = 0 ∧ B 1 0 = 0 := by
  constructor
  · intro h
    have e : ∀ i j, act A B vac i j = 0 := fun i j => by rw [h]; rfl
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · have := e i 0; rw [act_vac_apply] at this; simpa [Ne.symm hi] using this
    · have := e 3 0; rw [act_vac_apply] at this; simpa using this
    · have := e 3 1; rw [act_vac_apply] at this; simpa using this
  · rintro ⟨h1, h2, h3⟩
    ext i j
    rw [act_vac_apply]
    fin_cases j
    · by_cases hi : (3 : Fin 4) = i
      · subst hi; simpa using h2
      · simp [hi, h1 i (Ne.symm hi)]
    · by_cases hi : (3 : Fin 4) = i
      · subst hi; simpa using h3
      · simp [hi]

/-- The Lie algebra `su(4) ⊕ su(2)_R`, as the estate has it: `traceless 4 × traceless 2`. -/
abbrev PSLie := traceless 4 × traceless 2

/-- The matrix of an element of `traceless 4`. -/
abbrev mat4 (x : traceless 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((x : skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ)) : Matrix (Fin 4) (Fin 4) ℂ)

/-- The matrix of an element of `traceless 2`. -/
abbrev mat2 (x : traceless 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((x : skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)

/-- The orbit map `g ↦ g · vac`, `ℝ`-linear. -/
noncomputable def orbitMap : PSLie →ₗ[ℝ] Bidoublet where
  toFun p := act (mat4 p.1) (mat2 p.2) vac
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, mat4, mat2, Submodule.coe_add, AddSubgroup.coe_add, act,
      Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, mat4, mat2, Submodule.coe_smul, skewAdjoint.val_smul,
      act, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, smul_add, RingHom.id_apply]

/-- **THE STABILISER OF THE VACUUM**: the unbroken subalgebra, as a kernel. -/
noncomputable def stab : Submodule ℝ PSLie := LinearMap.ker orbitMap

/-- Membership in the stabiliser, entrywise. -/
theorem mem_stab_iff (p : PSLie) :
    p ∈ stab ↔ (∀ i, i ≠ 3 → mat4 p.1 i 3 = 0) ∧ mat4 p.1 3 3 + mat2 p.2 0 0 = 0
      ∧ mat2 p.2 1 0 = 0 := by
  rw [stab, LinearMap.mem_ker]
  exact act_vac_eq_zero_iff _ _

/-- Hypercharge as an element of `PSLie`: `yRep` with its first component read in `traceless 4`. -/
noncomputable def yG : PSLie := (blT, (3 : ℝ) • t3RT)

/-- Hypercharge's `su(4)` component is `blGen = diag(i, i, i, −3i)`. -/
theorem mat4_yG : mat4 yG.1 = blGen := rfl

/-- Hypercharge's `su(2)_R` component is `3 • t3RGen = diag(3i, −3i)`. -/
theorem mat2_yG : mat2 yG.2 = (3 : ℝ) • t3RGen := rfl

/-- **HYPERCHARGE IS UNBROKEN.** -/
theorem yG_mem_stab : yG ∈ stab := by
  rw [mem_stab_iff, mat4_yG, mat2_yG]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · simp [blGen, Matrix.diagonal_apply_ne _ hi]
  · simp [blGen, t3RGen]
  · simp [t3RGen]

/-- The right sector sits inside `PSLie`. -/
noncomputable def ofRight (p : RightSector) : PSLie := ((p.1 : traceless 4), p.2)

/-- `yRep`, read in `PSLie`, is `yG`. -/
theorem ofRight_yRep : ofRight yRep = yG := rfl

/-- The inclusion is `ℝ`-homogeneous. -/
theorem ofRight_smul (t : ℝ) (p : RightSector) : ofRight (t • p) = t • ofRight p := rfl

/-- **THE UNBROKEN PART OF THE RIGHT SECTOR IS EXACTLY HYPERCHARGE.** An element of
`u(1)_{B−L} ⊕ su(2)_R` fixes the vacuum iff it lies on the hypercharge line. -/
theorem ofRight_mem_stab_iff (p : RightSector) : ofRight p ∈ stab ↔ p ∈ hyperchargeLine := by
  constructor
  · intro h
    rw [mem_stab_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp p.1.2
    have hA : mat4 (ofRight p).1 = t • blGen := by
      change mat4 (p.1 : traceless 4) = t • blGen
      rw [← ht]; rfl
    set B : Matrix (Fin 2) (Fin 2) ℂ := mat2 (ofRight p).2 with hB
    have hskew : star B = -B :=
      skewAdjoint.mem_iff.mp (p.2 : skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)).2
    have htr : Matrix.trace B = 0 := trace_eq_zero_of_mem_traceless p.2.2
    have h00 : B 0 0 = 3 * (t : ℂ) * Complex.I := by
      have := h2
      rw [hA] at this
      simp [blGen] at this
      linear_combination this
    have h10 : B 1 0 = 0 := h3
    have h01 : B 0 1 = 0 := by
      have := congrFun (congrFun hskew 0) 1
      rw [Matrix.star_apply, Matrix.neg_apply, h10] at this
      simpa using this.symm
    have h11 : B 1 1 = -(3 * (t : ℂ) * Complex.I) := by
      rw [Matrix.trace_fin_two] at htr
      linear_combination htr - h00
    have hBeq : B = (3 * t : ℝ) • t3RGen := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [t3RGen, h00, h10, h01, h11]
    refine Submodule.mem_span_singleton.mpr ⟨t, ?_⟩
    refine Prod.ext ?_ ?_
    · exact Subtype.ext ht
    · apply Subtype.ext
      apply Subtype.ext
      change (t • ((3 : ℝ) • t3RGen)) = B
      rw [hBeq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [t3RGen] <;> ring
  · intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    rw [← ht, ofRight_smul, ofRight_yRep]
    exact Submodule.smul_mem _ t yG_mem_stab

/-- In the stabiliser the `su(4)` component is BLOCK-DIAGONAL: with the last column zero off the
corner (the membership condition) and skew-adjointness, the last row is zero off the corner too. -/
theorem stab_row_zero (p : PSLie) (hp : p ∈ stab) (i : Fin 4) (hi : i ≠ 3) : mat4 p.1 3 i = 0 := by
  have hcol : mat4 p.1 i 3 = 0 := ((mem_stab_iff p).mp hp).1 i hi
  have hskew : star (mat4 p.1) = -(mat4 p.1) :=
    skewAdjoint.mem_iff.mp (p.1 : skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ)).2
  have := congrFun (congrFun hskew 3) i
  rw [Matrix.star_apply, Matrix.neg_apply, hcol] at this
  simpa using this.symm

end PatiSalamVacuumStabiliser
