/-
  PatiSalamRankTwoVacuum.lean — the first stage of the Pati–Salam breaking, completely: a nonzero
  vacuum of the `(4, 1, 2)` Higgs field leaves `U(3)` unbroken IF AND ONLY IF it has rank one
  (`nonempty_stabilizer_equiv_U3_iff`). Unit 203 proved the "if" (`PatiSalamVacuumOrbit`); this file
  proves the "only if": the stabiliser of every rank-two vacuum is NOT isomorphic to `U(3)`
  (`not_nonempty_stabilizer_equiv_U3_of_rank_eq_two`). The invariant that tells them apart is the
  set of elements whose square is one: `U(3)` has infinitely many (`infinite_involutions_U3`), and
  the stabiliser of a rank-two vacuum at most four (`finite_involutions_stabilizer`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60. Unit 203 narrowed the chosen
  vacuum to its orbit type and said no theorem showed that the shape mattered. For the first stage
  it now does: rank one is not only sufficient for `U(3)` but necessary. Hardening unit 204,
  2026-09-25.

  WHAT IS PROVED.
  (1) **`eq_one_or_eq_neg_one_of_mul_self`**: a `2 × 2` complex matrix of determinant one whose
      square is the identity is `±1` — by its entries: a zero trace contradicts `det = 1`, and a
      nonzero one forces the off-diagonal entries to vanish.
  (2) `vac2 := e₂ e₀ᵀ + e₃ e₁ᵀ` has rank two (`rank_vac2`). **`eq_of_mem_stabilizer_of_mul_self`**:
      for `D` invertible, an element `(A, B)` of the stabiliser of `vac2 · D` whose square is one
      has `B = ε · 1` and `A = diag(δ, δ, ε, ε)` with `δ, ε = ±1` — `B = ±1` by (1); `A · vac2 =
      ε · vac2` after cancelling `D`; the orthogonality of `A`'s columns empties the lower-left
      block; the `2 + 2` determinant (`det_block22`) and (1) again settle the upper-left block.
      Hence **`finite_involutions_stabilizer`**.
  (3) `refl3 θ`, a real reflection in the first two coordinates, is unitary with square one
      (`refl3_mul_self`, `refl3_mem_unitaryGroup`); at `θ = π / (n + 2)` they are pairwise distinct
      (`Real.injOn_cos`), so **`infinite_involutions_U3`**; and
      **`not_nonempty_stabilizer_equiv_U3`**: an isomorphism would carry a finite set onto an
      infinite one.
  (4) **`exists_smul_eq_vac2_mul`**: every rank-two bidoublet `X` has `g • X = vac2 · D` for some
      gauge transformation `g` and invertible `D`. Two orthonormal vectors orthogonal to `X`'s
      columns (`exists_orthonormal_pair_perp`) are the first two columns of a matrix `A ∈ SU(4)`
      (`exists_specialUnitary_cols`, the determinant corrected on a third column,
      `exists_specialUnitary_eq_off`); `A⋆` empties the top two rows of `X`; `D` is invertible
      because the rank is preserved (`rank_mul_eq_right_of_isUnit_det`) and a full-rank `2 × 2`
      matrix is surjective, hence a unit (`mulVec_surjective_iff_isUnit`).
  (5) **`not_nonempty_stabilizer_equiv_U3_of_rank_eq_two`** (with `vac2` itself as
      `not_nonempty_stabilizer_vac2_equiv_U3`) and **`nonempty_stabilizer_equiv_U3_iff`**: for
      `X ≠ 0`, `X`'s stabiliser is isomorphic to `U(3)` iff `X.rank = 1` — the rank is at most two
      because `X` has two columns, and rank zero is `X = 0` (`eq_zero_of_rank_eq_zero`).

  NOT PROVED, said exactly.
  • What the rank-two stabiliser IS as a group: only that it is not `U(3)`.
    ⚠ 25 September 2026 (hardening unit 211): answered in `PatiSalamRankTwoStabiliser` up to
    one factor — for invertible `D` the stabiliser of `vac2 · D` is `SU(2) ×` the elements of
    `SU(2)` commuting with `D Dᴴ` (`stabilizerVac2Equiv`): `SU(2) × SU(2)` when `D Dᴴ` is a
    multiple of the identity, the second factor commutative otherwise (`commSU2_mul_comm`).
    That this factor is `U(1)` is not proved there. Kept as written (`ERRATUM 94`).
  • The second stage. Whether a pair of vacua that is not aligned can still leave `U(3)` unbroken
    is not decided here: unit 203's alignment is sufficient, and nothing in the estate shows it
    necessary.
    ⚠ 25 September 2026 (hardening unit 205): decided in `PatiSalamTwoComponentVacuum` — it can:
    alignment is not necessary (`exists_not_aligned_stabilizer_equiv_U3`), and every nonzero
    `diag(κ, κ')` leaves the same subgroup as `vacEW` (`stabilizer_vacKK_eq`). Kept as written
    (`ERRATUM 94`).
  • `X = 0`, whose stabiliser is the whole group, is excluded by hypothesis and not examined.
  • Why the vacuum should have rank one: that is a potential's minimum, and there is no potential;
    nor are the magnitudes fixed. Each `≃*` is of abstract groups.
    ⚠ 25 September 2026 (hardening unit 209): the criterion holds for topological groups too —
    `PatiSalamTopologicalCopies.nonempty_stabilizer_continuousEquiv_U3_iff`; and every
    stabiliser, the rank-two ones and `X = 0`'s included, is a closed, compact subgroup
    (`isClosed_stabilizer`, `compactSpace_stabilizer`). What the rank-two stabiliser is, as a
    group, stands. Kept as written (`ERRATUM 94`).
    ⚠ 25 September 2026 (hardening unit 211): answered up to what the commutative factor is —
    see the first bullet's pointer. Kept as written (`ERRATUM 94`).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `eq_one_or_eq_neg_one_of_mul_self` takes
  `P.det = 1` and `P * P = 1`; `eq_of_mem_stabilizer_of_mul_self`, `finite_involutions_stabilizer`
  and `not_nonempty_stabilizer_equiv_U3` take `IsUnit D.det`, the first also stabiliser membership
  and `g * g = 1`; `exists_orthonormal_pair_perp` takes `finrank W ≤ 2`;
  `exists_specialUnitary_eq_off` takes a unitary matrix; `exists_specialUnitary_cols` an
  orthonormal pair; `exists_smul_eq_vac2_mul` and `not_nonempty_stabilizer_equiv_U3_of_rank_eq_two`
  take `X.rank = 2`; `eq_zero_of_rank_eq_zero`
  takes `X.rank = 0`; `nonempty_stabilizer_equiv_U3_iff` takes `X ≠ 0`. Nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 23 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 203's: `PatiSalamVacuumOrbit.
  exists_specialUnitary_col` is the one-column case of `exists_specialUnitary_cols`, and its proof
  contains the determinant correction that `exists_specialUnitary_eq_off` states on its own.

  0 sorry. 0 new axioms. `#print axioms` on all 23 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamVacuumOrbit

open Matrix

namespace PatiSalamRankTwoVacuum

/-- A `2 × 2` matrix of determinant one whose square is the identity is `±1`. -/
theorem eq_one_or_eq_neg_one_of_mul_self {P : Matrix (Fin 2) (Fin 2) ℂ} (hdet : P.det = 1)
    (hsq : P * P = 1) : P = 1 ∨ P = -1 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp only [mul_apply, Fin.sum_univ_two, one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
  rw [det_fin_two] at hdet
  have htr : P 0 0 + P 1 1 ≠ 0 := by
    intro h
    have : P 1 1 = -P 0 0 := by linear_combination h
    rw [this] at hdet
    have h2 : (2 : ℂ) = 0 := by linear_combination -e00 - hdet
    exact two_ne_zero h2
  have hb : P 0 1 = 0 := by
    have : P 0 1 * (P 0 0 + P 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right htr
  have hc : P 1 0 = 0 := by
    have : P 1 0 * (P 0 0 + P 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right htr
  rw [hb, hc] at e00 e11 hdet
  have hda : P 1 1 = P 0 0 := by linear_combination (P 0 0) * hdet - (P 1 1) * e00 + 0 * e11
  have ha : P 0 0 = 1 ∨ P 0 0 = -1 := by
    have : (P 0 0 - 1) * (P 0 0 + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  rcases ha with ha | ha
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hda]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hda]

/-- A concrete `2 + 2` block determinant. -/
theorem det_block22 (a b c d e : ℂ) :
    (!![a, b, 0, 0; c, d, 0, 0; 0, 0, e, 0; 0, 0, 0, e] : Matrix (Fin 4) (Fin 4) ℂ).det
      = e ^ 2 * (a * d - b * c) := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, empty_val', cons_val_fin_one, Fin.succAbove]
  simp
  ring

open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamStabiliserGroup

/-- The rank-two first-stage vacuum `e₂ e₀ᵀ + e₃ e₁ᵀ`: its lower `2 × 2` block is the identity. -/
noncomputable def vac2 : Bidoublet := Matrix.single 2 0 1 + Matrix.single 3 1 1

theorem vac2_transpose_mul_self : vac2ᵀ * vac2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vac2, mul_apply, single_apply]

theorem rank_vac2 : vac2.rank = 2 := by
  refine le_antisymm ((rank_le_width vac2).trans (by simp)) ?_
  have h := rank_mul_le_right vac2ᵀ vac2
  rw [vac2_transpose_mul_self, rank_one, Fintype.card_fin] at h
  exact h

theorem mul_vac2_col0 (A : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4) : (A * vac2) i 0 = A i 2 := by
  simp [vac2, mul_apply, single_apply]

theorem mul_vac2_col1 (A : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4) : (A * vac2) i 1 = A i 3 := by
  simp [vac2, mul_apply, single_apply]

/-- **An element of `vac2`'s stabiliser that squares to one is one of four**: its `SU(2)` part is
`ε · 1` and its `SU(4)` part is `diag(δ, δ, ε, ε)`, with `δ, ε = ±1`. -/
theorem eq_of_mem_stabilizer_of_mul_self {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (g : Stage1Group) (hg : g ∈ MulAction.stabilizer Stage1Group (vac2 * D)) (h2 : g * g = 1) :
    ∃ δ ε : ℂ, (δ = 1 ∨ δ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = diagonal ![δ, δ, ε, ε] ∧
      (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = ε • 1 := by
  set A := (g.1 : Matrix (Fin 4) (Fin 4) ℂ) with hAdef
  set B := (g.2 : Matrix (Fin 2) (Fin 2) ℂ) with hBdef
  have hA2 : A * A = 1 := by
    have := congrArg (fun h : Stage1Group => (h.1 : Matrix (Fin 4) (Fin 4) ℂ)) h2
    simpa [hAdef] using this
  have hB2 : B * B = 1 := by
    have := congrArg (fun h : Stage1Group => (h.2 : Matrix (Fin 2) (Fin 2) ℂ)) h2
    simpa [hBdef] using this
  have hAu := (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2)
  have hBu := (Matrix.mem_specialUnitaryGroup_iff.mp g.2.2)
  obtain ⟨ε, hε, hBε⟩ : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ B = ε • 1 := by
    rcases eq_one_or_eq_neg_one_of_mul_self hBu.2 hB2 with h | h
    · exact ⟨1, Or.inl rfl, by rw [hBdef, h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [hBdef, h, neg_smul, one_smul]⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hstab : A * vac2 = ε • vac2 := by
    have h := MulAction.mem_stabilizer_iff.mp hg
    rw [stage1_smul_def, stage1Act, ← hAdef, ← hBdef, hBε, transpose_smul, transpose_one,
      Matrix.mul_smul, Matrix.mul_one] at h
    have h' : ε • (A * vac2) = vac2 := by
      have := congrArg (· * D⁻¹) h
      simpa only [Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD,
        Matrix.mul_one] using this
    calc A * vac2 = (ε * ε) • (A * vac2) := by rw [hεε, one_smul]
      _ = ε • vac2 := by rw [← smul_smul, h']
  have c2 : ∀ i, A i 2 = if (2 : Fin 4) = i then ε else 0 := fun i => by
    rw [show A i 2 = (A * vac2) i 0 from (mul_vac2_col0 A i).symm, hstab]
    simp [vac2, single_apply]
  have c3 : ∀ i, A i 3 = if (3 : Fin 4) = i then ε else 0 := fun i => by
    rw [show A i 3 = (A * vac2) i 1 from (mul_vac2_col1 A i).symm, hstab]
    simp [vac2, single_apply]
  have hsA : star A * A = 1 := (Matrix.mem_unitaryGroup_iff').mp hAu.1
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have orth : ∀ j k : Fin 4, k = 2 ∨ k = 3 → j ≠ k → star (A k j) = 0 := by
    intro j k hk hjk
    have e := congrFun (congrFun hsA j) k
    rw [mul_apply, Fin.sum_univ_four, one_apply_ne hjk] at e
    rcases hk with rfl | rfl
    · simp only [c2] at e
      simpa [hεne] using e
    · simp only [c3] at e
      simpa [hεne] using e
  have z20 : A 2 0 = 0 := star_eq_zero.mp (orth 0 2 (Or.inl rfl) (by decide))
  have z21 : A 2 1 = 0 := star_eq_zero.mp (orth 1 2 (Or.inl rfl) (by decide))
  have z30 : A 3 0 = 0 := star_eq_zero.mp (orth 0 3 (Or.inr rfl) (by decide))
  have z31 : A 3 1 = 0 := star_eq_zero.mp (orth 1 3 (Or.inr rfl) (by decide))
  have hAform : A = !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, ε, 0; 0, 0, 0, ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c2, c3, z20, z21, z30, z31]
  set Pm : Matrix (Fin 2) (Fin 2) ℂ := !![A 0 0, A 0 1; A 1 0, A 1 1] with hPm
  have hPdet : Pm.det = 1 := by
    have h : A.det = 1 := hAu.2
    rw [hAform, det_block22] at h
    rw [det_fin_two, hPm]
    simpa [pow_two, hεε] using h
  have hPsq : Pm * Pm = 1 := by
    have e00 := congrFun (congrFun hA2 0) 0
    have e01 := congrFun (congrFun hA2 0) 1
    have e10 := congrFun (congrFun hA2 1) 0
    have e11 := congrFun (congrFun hA2 1) 1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, c2, c3, hPm] using e00
    · simpa [mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, c2, c3, hPm] using e01
    · simpa [mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, c2, c3, hPm] using e10
    · simpa [mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, c2, c3, hPm] using e11
  obtain ⟨δ, hδ, hPδ⟩ : ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧ Pm = δ • 1 := by
    rcases eq_one_or_eq_neg_one_of_mul_self hPdet hPsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_smul, one_smul]⟩
  have p00 : A 0 0 = δ := by simpa [hPm] using congrFun (congrFun hPδ 0) 0
  have p01 : A 0 1 = 0 := by simpa [hPm] using congrFun (congrFun hPδ 0) 1
  have p10 : A 1 0 = 0 := by simpa [hPm] using congrFun (congrFun hPδ 1) 0
  have p11 : A 1 1 = δ := by simpa [hPm] using congrFun (congrFun hPδ 1) 1
  refine ⟨δ, ε, hδ, hε, ?_, hBε⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c2, c3, z20, z21, z30, z31, p00, p01, p10, p11]

/-- The four candidates, as a finite set of matrix pairs. -/
theorem finite_involutions_stabilizer {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    {s : MulAction.stabilizer Stage1Group (vac2 * D) | s * s = 1}.Finite := by
  let f : MulAction.stabilizer Stage1Group (vac2 * D) →
      Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ :=
    fun s => (((s : Stage1Group).1 : Matrix (Fin 4) (Fin 4) ℂ),
      ((s : Stage1Group).2 : Matrix (Fin 2) (Fin 2) ℂ))
  have hf : Function.Injective f := by
    intro s t h
    simp only [f, Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
  let T : Set (Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
    (fun p : ℂ × ℂ => (diagonal ![p.1, p.1, p.2, p.2], p.2 • 1)) ''
      (({1, -1} : Set ℂ) ×ˢ ({1, -1} : Set ℂ))
  have hT : T.Finite := ((Set.toFinite _).prod (Set.toFinite _)).image _
  refine (hT.preimage hf.injOn).subset ?_
  intro s hs
  obtain ⟨δ, ε, hδ, hε, h1, h2⟩ := eq_of_mem_stabilizer_of_mul_self hD (s : Stage1Group) s.2
    (by simpa using congrArg Subtype.val (show s * s = 1 from hs))
  refine ⟨(δ, ε), ⟨?_, ?_⟩, ?_⟩
  · rcases hδ with rfl | rfl <;> simp
  · rcases hε with rfl | rfl <;> simp
  · simp only [f, h1, h2]

/-- A real reflection in the first two coordinates. -/
noncomputable def refl3 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(Real.cos θ : ℂ), Real.sin θ, 0; Real.sin θ, -Real.cos θ, 0; 0, 0, 1]

theorem refl3_mul_self (θ : ℝ) : refl3 θ * refl3 θ = 1 := by
  have h : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have h1 : (Real.cos θ : ℂ) * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    linear_combination h
  have h2 : (Real.sin θ : ℂ) * Real.sin θ + Real.cos θ * Real.cos θ = 1 := by
    linear_combination h
  have h3 : (Real.cos θ : ℂ) * Real.sin θ + -(Real.sin θ * Real.cos θ) = 0 := by ring
  have h4 : (Real.sin θ : ℂ) * Real.cos θ + -(Real.cos θ * Real.sin θ) = 0 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [refl3, mul_apply, Fin.sum_univ_three, -Complex.ofReal_cos, -Complex.ofReal_sin,
      h1, h2, h3, h4]

theorem star_refl3 (θ : ℝ) : star (refl3 θ) = refl3 θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [refl3, star_apply, Complex.conj_ofReal, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem refl3_mem_unitaryGroup (θ : ℝ) : refl3 θ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_refl3, refl3_mul_self]

/-- **`U(3)` has infinitely many elements of square one**: the reflections `refl3 (π / (n + 2))`
are pairwise distinct, since their corner entries `cos (π / (n + 2))` are. -/
theorem infinite_involutions_U3 : {h : GroupU3 | h * h = 1}.Infinite := by
  let f : ℕ → GroupU3 := fun n =>
    ⟨refl3 (Real.pi / (n + 2)), refl3_mem_unitaryGroup _⟩
  have hf : Function.Injective f := by
    intro n m h
    have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
    simp only [f, refl3, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
      Complex.ofReal_inj] at h00
    have hmem : ∀ k : ℕ, Real.pi / (k + 2) ∈ Set.Icc 0 Real.pi := fun k =>
      ⟨by positivity, div_le_self Real.pi_pos.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])⟩
    have := Real.injOn_cos (hmem n) (hmem m) h00
    field_simp at this
    exact_mod_cast (by linarith : (n : ℝ) = m)
  refine Set.infinite_of_injective_forall_mem hf fun n => ?_
  change f n * f n = 1
  exact Subtype.ext (refl3_mul_self _)

/-- **The rank-two vacuum does NOT leave `U(3)` unbroken**: its stabiliser has finitely many
elements of square one, and `U(3)` infinitely many. -/
theorem not_nonempty_stabilizer_equiv_U3 {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    ¬ Nonempty (MulAction.stabilizer Stage1Group (vac2 * D) ≃* GroupU3) := by
  rintro ⟨φ⟩
  apply infinite_involutions_U3
  have : {h : GroupU3 | h * h = 1} = φ '' {s | s * s = 1} := by
    ext h
    constructor
    · intro hh
      refine ⟨φ.symm h, ?_, φ.apply_symm_apply h⟩
      change φ.symm h * φ.symm h = 1
      rw [← map_mul, show h * h = 1 from hh, map_one]
    · rintro ⟨s, hs, rfl⟩
      change φ s * φ s = 1
      rw [← map_mul, show s * s = 1 from hs, map_one]
  rw [this]
  exact (finite_involutions_stabilizer hD).image _

/-- Two orthonormal vectors orthogonal to a subspace of dimension at most two in `ℂ⁴`. -/
theorem exists_orthonormal_pair_perp (W : Submodule ℂ (EuclideanSpace ℂ (Fin 4)))
    (hW : Module.finrank ℂ W ≤ 2) :
    ∃ w : Fin 2 → EuclideanSpace ℂ (Fin 4), Orthonormal ℂ w ∧ ∀ i, w i ∈ Wᗮ := by
  have hWp : 2 ≤ Module.finrank ℂ Wᗮ := by
    have h := Submodule.finrank_add_finrank_orthogonal W
    rw [finrank_euclideanSpace_fin] at h
    omega
  let bW := stdOrthonormalBasis ℂ Wᗮ
  let φ : Fin 2 → Fin (Module.finrank ℂ Wᗮ) := fun i => ⟨i, by omega⟩
  have hφ : Function.Injective φ := fun a b h => Fin.ext (by simpa [φ] using congrArg Fin.val h)
  refine ⟨fun i => (bW (φ i) : EuclideanSpace ℂ (Fin 4)), ?_, fun i => (bW (φ i)).2⟩
  exact (bW.orthonormal.comp φ hφ).comp_linearIsometry Wᗮ.subtypeₗᵢ

/-- A unitary matrix can be made special by a phase on one column `j`, keeping every other
column. -/
theorem exists_specialUnitary_eq_off {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∃ A ∈ Matrix.specialUnitaryGroup (Fin n) ℂ, ∀ i k, k ≠ j → A i k = U i k := by
  have hc : star U.det * U.det = 1 := Unitary.star_mul_self_of_mem (det_of_mem_unitary hU)
  let d : Fin n → ℂ := fun i => if i = j then star U.det else 1
  have hd : ∀ i, d i * star (d i) = 1 := by
    intro i
    by_cases hi : i = j
    · simp only [d, hi, if_true, star_star]
      exact hc
    · simp only [d, hi, if_false, star_one, mul_one]
  have hD : diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hd)
  refine ⟨U * diagonal d, ?_, fun i k hk => ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨mul_mem hU hD, ?_⟩
    rw [det_mul, det_diagonal, Fintype.prod_ite_eq']
    rw [mul_comm]
    exact hc
  · rw [mul_diagonal]
    simp [d, hk]

/-- An orthonormal pair of `ℂ⁴` is the first two columns of a matrix in `SU(4)`. -/
theorem exists_specialUnitary_cols (w : Fin 2 → EuclideanSpace ℂ (Fin 4)) (hw : Orthonormal ℂ w) :
    ∃ A ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ, ∀ i, A i 0 = w 0 i ∧ A i 1 = w 1 i := by
  let v : Fin 4 → EuclideanSpace ℂ (Fin 4) := fun k => if k = 0 then w 0 else w 1
  have hv : Orthonormal ℂ (({0, 1} : Set (Fin 4)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    have hw' := orthonormal_iff_ite.mp hw
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [v, hw', hw.1]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  obtain ⟨A, hA, hAeq⟩ := exists_specialUnitary_eq_off
    (OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
      (EuclideanSpace.basisFun (Fin 4) ℂ) b) 2
  refine ⟨A, hA, fun i => ⟨?_, ?_⟩⟩
  · rw [hAeq i 0 (by decide), Module.Basis.toMatrix_apply, hb 0 (by simp)]
    simp [v]
  · rw [hAeq i 1 (by decide), Module.Basis.toMatrix_apply, hb 1 (by simp)]
    simp [v]

/-- **Every rank-two bidoublet is carried by the gauge group to `vac2 · D`, `D` invertible.** The
columns of `X` span a plane `W`; two orthonormal vectors of `Wᗮ` become the first two columns of a
matrix `A ∈ SU(4)`, and `A⋆` kills the top two rows of `X`. -/
theorem exists_smul_eq_vac2_mul (X : Bidoublet) (hX : X.rank = 2) :
    ∃ g : Stage1Group, ∃ D : Matrix (Fin 2) (Fin 2) ℂ, IsUnit D.det ∧ g • X = vac2 * D := by
  classical
  let cols : Fin 2 → EuclideanSpace ℂ (Fin 4) := fun j => WithLp.toLp 2 (fun i => X i j)
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin 4)) := Submodule.span ℂ (Set.range cols)
  have hW : Module.finrank ℂ W ≤ 2 := by
    simpa using finrank_range_le_card (R := ℂ) cols
  obtain ⟨w, hw, hwW⟩ := exists_orthonormal_pair_perp W hW
  obtain ⟨A, hA, hAc⟩ := exists_specialUnitary_cols w hw
  have hA' := Matrix.mem_specialUnitaryGroup_iff.mp hA
  have hAs : star A ∈ Matrix.specialUnitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨Unitary.star_mem hA'.1,
      by rw [star_eq_conjTranspose, det_conjTranspose, hA'.2, star_one]⟩
  let g : Stage1Group := (⟨star A, hAs⟩, 1)
  have hgX : g • X = star A * X := by
    rw [stage1_smul_def, stage1Act]
    simp [g]
  have hrow : ∀ (k : Fin 2) (j : Fin 2), (star A * X) (Fin.castLE (by norm_num) k) j = 0 := by
    intro k j
    have hin : inner ℂ (w k) (cols j) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self j))
        (hwW k)
    rw [mul_apply]
    rw [PiLp.inner_apply] at hin
    convert hin using 2 with i
    fin_cases k <;> simp [star_apply, (hAc i).1, (hAc i).2, cols, mul_comm]
  let D : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(star A * X) 2 0, (star A * X) 2 1; (star A * X) 3 0, (star A * X) 3 1]
  have h00 := hrow 0 0
  have h01 := hrow 0 1
  have h10 := hrow 1 0
  have h11 := hrow 1 1
  have hM : star A * X = vac2 * D := by
    ext k j
    fin_cases k <;> fin_cases j <;>
      simp_all [D, vac2, mul_apply, single_apply]
  refine ⟨g, D, ?_, by rw [hgX, hM]⟩
  have hdetA : IsUnit (star A).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp hAs).2]
    exact isUnit_one
  have hr : (vac2 * D).rank = 2 := by
    rw [← hM, rank_mul_eq_right_of_isUnit_det _ _ hdetA, hX]
  have hrD : D.rank = 2 :=
    le_antisymm ((rank_le_width D).trans (by simp)) (by
      have h := rank_mul_le_right vac2 D
      rwa [hr] at h)
  have hsurj : Function.Surjective D.mulVec := by
    have htop : LinearMap.range D.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank, hrD]
      simp
    exact LinearMap.range_eq_top.mp htop
  exact (isUnit_iff_isUnit_det D).mp (mulVec_surjective_iff_isUnit.mp hsurj)

/-- **A rank-two first-stage vacuum never leaves `U(3)` unbroken.** -/
theorem not_nonempty_stabilizer_equiv_U3_of_rank_eq_two (X : Bidoublet) (hX : X.rank = 2) :
    ¬ Nonempty (MulAction.stabilizer Stage1Group X ≃* GroupU3) := by
  rintro ⟨φ⟩
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  exact not_nonempty_stabilizer_equiv_U3 hD
    ⟨(MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer Stage1Group) hgX)).symm.trans
      ((MulAction.stabilizerEquivStabilizer rfl).symm.trans φ)⟩

/-- `vac2` itself is `vac2 · 1`. -/
theorem not_nonempty_stabilizer_vac2_equiv_U3 :
    ¬ Nonempty (MulAction.stabilizer Stage1Group vac2 ≃* GroupU3) :=
  not_nonempty_stabilizer_equiv_U3_of_rank_eq_two vac2 rank_vac2

/-- A matrix of rank zero is zero. -/
theorem eq_zero_of_rank_eq_zero {X : Matrix (Fin 4) (Fin 2) ℂ} (h : X.rank = 0) : X = 0 := by
  have h1 : LinearMap.range X.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have h2 : X.mulVecLin = 0 := LinearMap.range_eq_bot.mp h1
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h2
  simpa [mulVec_single_one] using this

/-- **The first stage, completely: a nonzero vacuum of the `(4, 1, 2)` field leaves `U(3)`
unbroken if and only if it has rank one.** Rank one is unit 203's orbit of `vac`; rank two is
never `U(3)`. -/
theorem nonempty_stabilizer_equiv_U3_iff (X : Bidoublet) (hX : X ≠ 0) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* GroupU3) ↔ X.rank = 1 := by
  refine ⟨fun h => ?_, PatiSalamVacuumOrbit.nonempty_stabilizer_equiv_U3 X⟩
  have hle : X.rank ≤ 2 := (rank_le_width X).trans (by simp)
  have h0 : X.rank ≠ 0 := fun h0 => hX (eq_zero_of_rank_eq_zero h0)
  have h2 : X.rank ≠ 2 := fun h2 => not_nonempty_stabilizer_equiv_U3_of_rank_eq_two X h2 h
  omega

end PatiSalamRankTwoVacuum
