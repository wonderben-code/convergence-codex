/-
  PatiSalamStabiliserDimension: the vacuum's stabiliser IS `u(3)`, the broken directions are
  nine as a CODIMENSION, and `9 = 6 + 3` is a short exact sequence rather than a sum of numbers

  Campaign 3 hardening unit 179 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. `PatiSalamVacuumStabiliser` (unit 178) built the vacuum `vac = E₃₀` and its stabiliser
  `stab ⊆ su(4) ⊕ su(2)_R` as a kernel, and left the dimensions to *the next unit*: it proved
  membership statements and one biconditional, not a rank. `PatiSalamRightSector.broken_nine`
  says `6 + 3 = 9` with both summands exhibited as spaces — the six as
  `PatiSalamOffDiagonal.offDiagMapR`'s range, the three as `RightSector ⧸ hyperchargeLine` — but
  the nine on its right-hand side is a numeral, and its docstring says *"the reading itself is
  still not proved"*. This file computes the stabiliser, counts the broken directions as a
  codimension, and shows the six and the three are the two ends of a short exact sequence whose
  middle is the broken space.

  WHAT IS PROVED.
  (1) `stabEquivU3 : stab ≃ₗ[ℝ] skewAdjoint (Matrix (Fin 3) (Fin 3) ℂ)` — the unbroken algebra
      is `u(3)` as a real vector space. Forward: the top-left `3 × 3` block of the `su(4)`
      component (`PatiSalamOffDiagonal.topBlock`). Back: `C ↦ (blockdiag(C, −tr C),
      diag(tr C, −tr C))` (`blockA`, `diagB`; lifted into `traceless 4 × traceless 2` as
      `blockAT`, `diagBT`, and into `stab` by `ofU3_mem_stab`). `ofU3_toU3` is the reconstruction:
      for `p ∈ stab`, the three entry conditions of `mem_stab_iff`, `stab_row_zero`,
      skew-adjointness and both zero traces determine `p` from its block.
  (2) `finrank_stab : finrank ℝ stab = 9`, from `finrank_U3 = 9`
      (`TracelessSkewDimension.finrank_traceless_add_one_eq_skewAdjoint` at `n = 3`);
      `finrank_PSLie = 18`; `finrank_broken : finrank ℝ (PSLie ⧸ stab) = 9` by rank–nullity
      (`Submodule.finrank_quotient_add_finrank`); `finrank_broken_eq_six_add_three` — the
      codimension is the number `broken_nine` adds up.
  (3) The exact sequence `0 → RightSector ⧸ hyperchargeLine → PSLie ⧸ stab → (Fin 3 → ℂ) → 0`:
      `rightLift` (the right sector into the broken space, descended along `hyperchargeLine`; its
      well-definedness and its injectivity are BOTH unit 178's `ofRight_mem_stab_iff`, one
      direction each); `leptoquarkLift` (`offDiagMapR` on the `su(4)` component, descended along
      `stab`; well defined because a stabiliser element's last column vanishes off the corner);
      `leptoquarkLift_surjective`; `range_rightLift_eq_ker` (exactness in the middle: `≤` because
      the `B − L` line is diagonal, `=` by counting `3 = 9 − 6`); `broken_exact` packages the
      three. So the broken space is an extension of the six leptoquark directions by the three
      broken right-sector directions — the `6 + 3` as spaces and maps.

  NOT PROVED, said exactly.
  • No SPLITTING is chosen. The sequence splits, as every short exact sequence of vector spaces
    does, but no isomorphism `PSLie ⧸ stab ≃ (RightSector ⧸ hyperchargeLine) × (Fin 3 → ℂ)` is
    stated: the six leptoquark directions have no canonical lift into the broken space, and this
    file does not pretend one.
  • The vacuum direction is still a convention (unit 178's first bullet), and nothing here is
    dynamics: no potential, no minimisation, no mass, no Goldstone theorem. The nine broken
    directions are nine Goldstone directions only under a theorem this estate does not have:
    three declarations carry the name — `F3_2_HiggsForced.goldstone_counting`,
    `F3_2_HiggsForced.goldstone_boson_count` (`3 = 3 ∧ 3 = 3 ∧ 3 + 3 = 6`) and
    `F4_1e_SpectralTripleArithmetic.eaten_goldstones` (`8 − 3 = 5`) — and each is arithmetic on
    numerals with the theorem in its docstring, which is the species `ERRATUM 559` records.
  • `u(3)` is reached as a real vector space, not as a Lie algebra: `stabEquivU3` is `ℝ`-linear
    and no bracket is carried across it. `PSLie` has no `LieRing` instance and `stab` is a
    `Submodule`, as in the two files this one extends.
  • The identification of `Fin 3 → ℂ` with "the six leptoquarks" is `offDiagMapR`'s reading of
    the last column, as `PatiSalamOffDiagonal` records; that these are leptoquarks is physics.
  • `PatiSalamRightSector`'s clause (iv) stands: `RightSector ⧸ hyperchargeLine` is not
    identified with `su(2)_R`, here or anywhere.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `blockA_skew` and `diagB_skew` take
  `star C = -C`; `ofU3_toU3` takes `p ∈ stab`; every finrank theorem and every exact-sequence
  theorem is hypothesis-free. Nothing takes positivity, a norm, or a group.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 50 names grepped against `paper_f`
  with `newnames_scan`'s own regex before this header was written — none taken). The top-left
  block is `PatiSalamOffDiagonal.topBlock`, reused rather than redefined; its `trace_topBlock` is
  not used because the reconstruction needs the three diagonal entries by name. The fact
  `star (tr C) = −tr C` for skew `C` is a local `have` inside
  `TracelessSkewDimension.trace_eq_zero_of_mem_traceless` and again in `TracelessSkewLie`; here
  it is the theorem `star_trace_of_skew`. `finrank ℝ (Fin 3 → ℂ) = 6` is computed inline by
  `PatiSalamOffDiagonal.finrank_range_offDiagMapR`; here it is `finrank_fin3_complex`.
  `PatiSalamOffDiagonal.leptoquarkCosetEquiv` is the COMPLEX statement
  `sl(4,ℂ) ⧸ (colour ⊕ B−L) ≃ ℂ³ × ℂ³`, a different quotient over a different field; the real
  broken space here is `(su(4) ⊕ su(2)_R) ⧸ stab`, and the two are not compared.
-/

import PatiSalamVacuumStabiliser

open Matrix TracelessSkewDimension PatiSalamRightSector PatiSalamVacuumStabiliser
  PatiSalamOffDiagonal

namespace PatiSalamStabiliserDimension

noncomputable section

/-- `u(3)`: the skew-adjoint `3 × 3` complex matrices, as a real vector space. -/
abbrev U3 := skewAdjoint (Matrix (Fin 3) (Fin 3) ℂ)

/-- `blockdiag(C, −tr C)`. -/
def blockA (C : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < 3 then (if hj : (j : ℕ) < 3 then C ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else (if (j : ℕ) < 3 then 0 else -Matrix.trace C)

/-- `diag(tr C, −tr C)`. -/
def diagB (C : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Matrix.trace C, -Matrix.trace C]

theorem topBlock_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 3) :
    topBlock M i j = M (fin3_to_fin4 i) (fin3_to_fin4 j) := rfl

theorem topBlock_blockA (C : Matrix (Fin 3) (Fin 3) ℂ) : topBlock (blockA C) = C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topBlock, blockA, fin3_to_fin4]

theorem star_trace_of_skew {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ} (hC : star C = -C) :
    star (Matrix.trace C) = -Matrix.trace C := by
  rw [Matrix.star_eq_conjTranspose] at hC
  rw [← Matrix.trace_conjTranspose, hC, Matrix.trace_neg]

theorem star_entry_of_skew {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ} (hC : star C = -C)
    (i j : Fin n) : star (C j i) = -C i j := by
  have h := congrFun (congrFun hC i) j
  rwa [Matrix.star_apply, Matrix.neg_apply] at h

theorem blockA_skew {C : Matrix (Fin 3) (Fin 3) ℂ} (hC : star C = -C) :
    star (blockA C) = -(blockA C) := by
  have e := star_entry_of_skew hC
  have t := star_trace_of_skew hC
  ext i j
  rw [Matrix.star_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [blockA, e, t]

theorem trace_blockA (C : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.trace (blockA C) = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three, blockA]

theorem diagB_skew {C : Matrix (Fin 3) (Fin 3) ℂ} (hC : star C = -C) :
    star (diagB C) = -(diagB C) := by
  have t := star_trace_of_skew hC
  ext i j
  rw [Matrix.star_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [diagB, t]

theorem trace_diagB (C : Matrix (Fin 3) (Fin 3) ℂ) : Matrix.trace (diagB C) = 0 := by
  simp [diagB, Matrix.trace_diagonal, Fin.sum_univ_two]

/-- `blockdiag(C, −tr C)` as an element of `su(4)`. -/
def blockAT (C : U3) : traceless 4 :=
  ⟨⟨blockA C, skewAdjoint.mem_iff.mpr (blockA_skew (skewAdjoint.mem_iff.mp C.2))⟩,
    by simp [traceless, traceIm, trace_blockA]⟩

/-- `diag(tr C, −tr C)` as an element of `su(2)_R`. -/
def diagBT (C : U3) : traceless 2 :=
  ⟨⟨diagB C, skewAdjoint.mem_iff.mpr (diagB_skew (skewAdjoint.mem_iff.mp C.2))⟩,
    by simp [traceless, traceIm, trace_diagB]⟩

theorem blockA_add (C D : Matrix (Fin 3) (Fin 3) ℂ) :
    blockA (C + D) = blockA C + blockA D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockA, Matrix.trace_add, add_comm]

theorem trace_real_smul (r : ℝ) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (r • C) = (r : ℂ) * Matrix.trace C := by
  simp [Matrix.trace, Finset.mul_sum]

theorem blockA_smul (r : ℝ) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    blockA (r • C) = r • blockA C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockA, trace_real_smul]

theorem diagB_add (C D : Matrix (Fin 3) (Fin 3) ℂ) :
    diagB (C + D) = diagB C + diagB D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagB, Matrix.trace_add, add_comm]

theorem diagB_smul (r : ℝ) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    diagB (r • C) = r • diagB C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagB, trace_real_smul]

/-- The candidate stabiliser element of `C ∈ u(3)`: `(blockdiag(C, −tr C), diag(tr C, −tr C))`. -/
def ofU3 : U3 →ₗ[ℝ] PSLie where
  toFun C := (blockAT C, diagBT C)
  map_add' C D := by
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
    · simp only [blockAT, AddSubgroup.coe_add]
      exact blockA_add _ _
    · simp only [diagBT, AddSubgroup.coe_add]
      exact diagB_add _ _
  map_smul' r C := by
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
    · simp only [blockAT, RingHom.id_apply, skewAdjoint.val_smul]
      exact blockA_smul _ _
    · simp only [diagBT, RingHom.id_apply, skewAdjoint.val_smul]
      exact diagB_smul _ _

theorem mat4_ofU3 (C : U3) : mat4 (ofU3 C).1 = blockA C := rfl

theorem mat2_ofU3 (C : U3) : mat2 (ofU3 C).2 = diagB C := rfl

theorem ofU3_mem_stab (C : U3) : ofU3 C ∈ stab := by
  rw [mem_stab_iff, mat4_ofU3, mat2_ofU3]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · fin_cases i <;> simp_all [blockA]
  · simp [blockA, diagB]
  · simp [diagB]

/-- The top-left block of the `su(4)` component, on all of `su(4) ⊕ su(2)_R`. -/
def toU3 : PSLie →ₗ[ℝ] U3 where
  toFun p := ⟨topBlock (mat4 p.1), skewAdjoint.mem_iff.mpr (by
    have e := star_entry_of_skew (skewAdjoint.mem_iff.mp p.1.1.2)
    ext i j
    rw [Matrix.star_apply, Matrix.neg_apply]
    exact e _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toU3_ofU3 (C : U3) : toU3 (ofU3 C) = C :=
  Subtype.ext (topBlock_blockA C)

theorem ofU3_toU3 (p : PSLie) (hp : p ∈ stab) : ofU3 (toU3 p) = p := by
  obtain ⟨hcol, hcorner, hB10⟩ := (mem_stab_iff p).mp hp
  have hrow := stab_row_zero p hp
  have hBs : star (mat2 p.2) = -(mat2 p.2) := skewAdjoint.mem_iff.mp p.2.1.2
  have htrA : Matrix.trace (mat4 p.1) = 0 := trace_eq_zero_of_mem_traceless p.1.2
  have htrB : Matrix.trace (mat2 p.2) = 0 := trace_eq_zero_of_mem_traceless p.2.2
  have htrA' : mat4 p.1 0 0 + mat4 p.1 1 1 + mat4 p.1 2 2 + mat4 p.1 3 3 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_four] using htrA
  have htrB' : mat2 p.2 0 0 + mat2 p.2 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htrB
  have hB01 : mat2 p.2 0 1 = 0 := by
    have h := star_entry_of_skew hBs 0 1
    rw [hB10, star_zero] at h
    exact neg_eq_zero.mp h.symm
  have htrBlock : Matrix.trace (topBlock (mat4 p.1))
      = mat4 p.1 0 0 + mat4 p.1 1 1 + mat4 p.1 2 2 := by
    simp [Matrix.trace, Fin.sum_univ_three, topBlock, fin3_to_fin4]
  have h03 : mat4 p.1 0 3 = 0 := hcol 0 (by decide)
  have h13 : mat4 p.1 1 3 = 0 := hcol 1 (by decide)
  have h23 : mat4 p.1 2 3 = 0 := hcol 2 (by decide)
  have h30 : mat4 p.1 3 0 = 0 := hrow 0 (by decide)
  have h31 : mat4 p.1 3 1 = 0 := hrow 1 (by decide)
  have h32 : mat4 p.1 3 2 = 0 := hrow 2 (by decide)
  have h33 : mat4 p.1 3 3 = -(mat4 p.1 0 0 + mat4 p.1 1 1 + mat4 p.1 2 2) := by
    linear_combination htrA'
  have hB00 : mat2 p.2 0 0 = mat4 p.1 0 0 + mat4 p.1 1 1 + mat4 p.1 2 2 := by
    linear_combination hcorner - htrA'
  have hB11 : mat2 p.2 1 1 = -(mat4 p.1 0 0 + mat4 p.1 1 1 + mat4 p.1 2 2) := by
    linear_combination htrB' - hB00
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
  · change blockA (topBlock (mat4 p.1)) = mat4 p.1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockA, topBlock_apply, fin3_to_fin4, htrBlock, h03, h13, h23, h30, h31, h32, h33]
  · change diagB (topBlock (mat4 p.1)) = mat2 p.2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagB, htrBlock, hB00, hB01, hB10, hB11]

/-- `ofU3`, landing in the stabiliser. -/
def ofU3' : U3 →ₗ[ℝ] stab := LinearMap.codRestrict stab ofU3 ofU3_mem_stab

/-- `toU3`, restricted to the stabiliser. -/
def toU3' : stab →ₗ[ℝ] U3 := toU3.comp stab.subtype

/-- **THE UNBROKEN ALGEBRA IS `u(3)`**, as real vector spaces: the stabiliser of the vacuum and the
skew-adjoint `3 × 3` matrices, by block extraction and `blockdiag(C, −tr C) ⊕ diag(tr C, −tr C)`. -/
def stabEquivU3 : stab ≃ₗ[ℝ] U3 :=
  LinearEquiv.ofLinear toU3' ofU3' (LinearMap.ext fun C => toU3_ofU3 C)
    (LinearMap.ext fun p => Subtype.ext (ofU3_toU3 p.1 p.2))

theorem finrank_U3 : Module.finrank ℝ U3 = 9 := by
  change Module.finrank ℝ (skewAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) = 9
  rw [← finrank_traceless_add_one_eq_skewAdjoint 3 (by norm_num), finrank_traceless_three]

/-- **`dim stab = 9`.** -/
theorem finrank_stab : Module.finrank ℝ stab = 9 := by
  rw [stabEquivU3.finrank_eq, finrank_U3]

theorem finrank_PSLie : Module.finrank ℝ PSLie = 18 := by
  rw [Module.finrank_prod, finrank_traceless_four, finrank_traceless_two]

/-- **THE BROKEN DIRECTIONS: `dim (su(4) ⊕ su(2)_R) / stab = 9`**, by rank–nullity. -/
theorem finrank_broken : Module.finrank ℝ (PSLie ⧸ stab) = 9 := by
  have h := Submodule.finrank_quotient_add_finrank stab
  rw [finrank_stab, finrank_PSLie] at h
  omega

/-- The codimension of the stabiliser is the number `PatiSalamRightSector.broken_nine` adds up. -/
theorem finrank_broken_eq_six_add_three :
    Module.finrank ℝ (PSLie ⧸ stab)
      = Module.finrank ℝ (LinearMap.range PatiSalamOffDiagonal.offDiagMapR)
        + Module.finrank ℝ (RightSector ⧸ hyperchargeLine) := by
  rw [finrank_broken, broken_nine]

/-! ## 3. The `6 + 3` as an exact sequence, not a sum of two numbers -/

theorem fin3_to_fin4_ne_three (i : Fin 3) : fin3_to_fin4 i ≠ 3 := by
  intro h
  have h' := congrArg Fin.val h
  simp [fin3_to_fin4] at h'
  omega

/-- `PatiSalamVacuumStabiliser.ofRight` as a linear map. -/
def ofRightL : RightSector →ₗ[ℝ] PSLie where
  toFun := ofRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hyperchargeLine_le_ker :
    hyperchargeLine ≤ LinearMap.ker (stab.mkQ ∘ₗ ofRightL) := by
  intro p hp
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact (ofRight_mem_stab_iff p).mpr hp

/-- **THE BROKEN RIGHT-SECTOR DIRECTIONS, INSIDE THE BROKEN DIRECTIONS.** -/
def rightLift : RightSector ⧸ hyperchargeLine →ₗ[ℝ] PSLie ⧸ stab :=
  hyperchargeLine.liftQ (stab.mkQ ∘ₗ ofRightL) hyperchargeLine_le_ker

theorem rightLift_injective : Function.Injective rightLift := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  intro p hp
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hp
  exact (ofRight_mem_stab_iff p).mp hp

/-- The leptoquark reading of an element of `su(4) ⊕ su(2)_R`: the last column of its `su(4)`
component off the corner — `PatiSalamOffDiagonal.offDiagMapR` on the first factor. -/
def leptoquarkOf : PSLie →ₗ[ℝ] (Fin 3 → ℂ) :=
  PatiSalamOffDiagonal.offDiagMapR ∘ₗ LinearMap.fst ℝ (traceless 4) (traceless 2)

theorem leptoquarkOf_apply (p : PSLie) (i : Fin 3) :
    leptoquarkOf p i = mat4 p.1 (fin3_to_fin4 i) 3 := rfl

theorem stab_le_ker_leptoquarkOf : stab ≤ LinearMap.ker leptoquarkOf := by
  intro p hp
  obtain ⟨hcol, -, -⟩ := (mem_stab_iff p).mp hp
  rw [LinearMap.mem_ker]
  funext i
  exact hcol (fin3_to_fin4 i) (fin3_to_fin4_ne_three i)

/-- **THE SIX LEPTOQUARK DIRECTIONS AS A QUOTIENT OF THE BROKEN DIRECTIONS.** -/
def leptoquarkLift : PSLie ⧸ stab →ₗ[ℝ] (Fin 3 → ℂ) :=
  stab.liftQ leptoquarkOf stab_le_ker_leptoquarkOf

theorem leptoquarkLift_surjective : Function.Surjective leptoquarkLift := by
  intro v
  obtain ⟨M, hM⟩ := PatiSalamOffDiagonal.offDiagMapR_surjective v
  exact ⟨Submodule.Quotient.mk (M, 0), hM⟩

/-- The right sector's `su(4)` component lies on the `B − L` line — a diagonal matrix — so the
leptoquark reading kills it. -/
theorem leptoquarkOf_ofRight (p : RightSector) : leptoquarkOf (ofRight p) = 0 := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp p.1.2
  funext i
  rw [leptoquarkOf_apply]
  have hA : mat4 (ofRight p).1 = t • blGen := by
    change mat4 (p.1 : traceless 4) = t • blGen
    rw [← ht]; rfl
  rw [hA]
  simp [blGen, Matrix.diagonal_apply_ne _ (fin3_to_fin4_ne_three i)]

theorem range_rightLift_le_ker :
    LinearMap.range rightLift ≤ LinearMap.ker leptoquarkLift := by
  rw [LinearMap.range_le_ker_iff]
  apply Submodule.linearMap_qext
  exact LinearMap.ext fun p => leptoquarkOf_ofRight p

theorem finrank_range_rightLift : Module.finrank ℝ (LinearMap.range rightLift) = 3 := by
  rw [LinearMap.finrank_range_of_inj rightLift_injective, finrank_broken_right]

theorem finrank_fin3_complex : Module.finrank ℝ (Fin 3 → ℂ) = 6 := by
  rw [Module.finrank_pi_fintype ℝ]
  simp [Complex.finrank_real_complex]

theorem finrank_ker_leptoquarkLift :
    Module.finrank ℝ (LinearMap.ker leptoquarkLift) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker leptoquarkLift
  rw [LinearMap.range_eq_top.mpr leptoquarkLift_surjective, finrank_top, finrank_fin3_complex,
    finrank_broken] at h
  omega

/-- **EXACTNESS IN THE MIDDLE**: the broken right-sector directions are EXACTLY the broken
directions the leptoquark reading kills. -/
theorem range_rightLift_eq_ker :
    LinearMap.range rightLift = LinearMap.ker leptoquarkLift :=
  Submodule.eq_of_le_of_finrank_eq range_rightLift_le_ker
    (by rw [finrank_range_rightLift, finrank_ker_leptoquarkLift])

/-- **`9 = 6 + 3` AS A SHORT EXACT SEQUENCE**
`0 → RightSector ⧸ hyperchargeLine → PSLie ⧸ stab → (Fin 3 → ℂ) → 0`: injective on the left,
exact in the middle, surjective on the right. -/
theorem broken_exact :
    Function.Injective rightLift ∧
      LinearMap.range rightLift = LinearMap.ker leptoquarkLift ∧
        Function.Surjective leptoquarkLift :=
  ⟨rightLift_injective, range_rightLift_eq_ker, leptoquarkLift_surjective⟩

end

end PatiSalamStabiliserDimension
