/-
  OrderOneQuaternion.lean — the quaternions as test algebra. The order-one condition is bilinear
  in its two test matrices, so testing against two sets is testing against their spans; and the
  quaternions, sitting in `M₂(ℂ)` as `1`, `i σ₁`, `i σ₃` and their product
  (`QuaternionComplexification.qToM`), span `M₂(ℂ)` over `ℂ`. So on `ℂ² ⊗ ℂ²` order-one against
  `ℍ` is order-one against `M₂(ℂ)`: `D = C ⊗ 1 + 1 ⊗ B`; with the real structure
  `D = A ⊗ 1 + 1 ⊗ Ā`; and with unit 170's grading `D = t · Dsym`, `t` real — the answers of
  units 168, 169 and 170, unchanged.

  SPINE L6 / `WALLS` §W9 rung 2 — the quaternionic factor, for the regular bimodule of `M₂(ℂ)`.
  Hardening unit 237, 26 September 2026.

  WHY. CCM's finite algebra is `ℂ ⊕ ℍ ⊕ M₃(ℂ)`, and `ℍ` is its one factor that is not a complex
  matrix algebra. Unit 232 (`OrderOneCommutant`) put `ℍ` inside `M₂(ℂ)` among the admissible test
  sets, and its pointer in `OrderOneBlockDiagonal` says *"the commutants for `ℍ` are not computed"*
  (its own NOT list: *"for `ℍ` … which `X` and `Y` occur is not computed"*). They are the
  commutants of `M₂(ℂ)`, because order-one cannot tell a test set from its complex span.

  WHAT IS PROVED.
  (1) **`orderOne_iff_span`** (any finite `ι`, `κ`, any field `K`, any sets of test matrices):
      order-one against `S_L`, `S_R` holds iff it holds against `span K S_L`, `span K S_R`.
      **`orderOne_iff_kron_of_span_eq_top`**: test sets that span everything give unit 228's
      full-matrix answer, `M = C ⊗ 1 + 1 ⊗ B` (`OrderOneBlockDiagonal.orderOne_iff_kron_of_const`).
  (2) **`span_range_qToM`**: the image of `ℍ` spans `M₂(ℂ)` over `ℂ` (from `images_span`).
      **`orderOne_quat_iff`**: order-one against `ℍ` on both sides iff `M = C ⊗ 1 + 1 ⊗ B`;
      `orderOne_quat_left_iff`: the same with `ℍ` on the left and all of `M₂(ℂ)` on the right.
  (3) **`orderOne_quat_exchConj_iff`**: with invariance under exchange-conjugation (unit 230's
      `exchConj`), iff `M = A ⊗ 1 + 1 ⊗ Ā`. **`ccm_fixes_dirac_quat`**: with anticommutation with
      unit 170's `gammaMat` too, iff `M = t • Dsym` for a real `t`.

  NOT PROVED, said exactly.
  • `ℍ` inside a product: CCM's `ℂ ⊕ ℍ ⊕ M₃(ℂ)` acting on `H_F`, where `ℍ` is one block among
    others, is not done; neither is any bimodule but the regular bimodule of `M₂(ℂ)`.
  • The real structure proper to a quaternionic algebra. `J` here is `M₂(ℂ)`'s exchange-
    conjugation, and the theorems are about operators that satisfy the conditions with THAT `J`;
    whether CCM's `J` on `H_F` restricts to it on the doublet is not asked.
  • `UNLOCK_WATCHLIST` 262 — whether the doubled algebra acts faithfully in the real case — is
    untouched: the span argument is about the test sets of the order-one condition, not about
    faithfulness.
  • Nothing about the cascade, its `D` (`L40433`), the factor list, or a tag: rung 2 is not
    climbed.
    ⚠ 26 September 2026 (unit 239, `ERRATUM 700`): the watchlist item meant, *the cascade's `D`
    AS A TENSOR SUM*, stood at `L40927` when this was written; the number given, 40433, was its
    line on 20 September, copied from an older record.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). (1)'s second statement takes the two span
  hypotheses; everything else takes elements of its types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 7 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. The nearest statements are unit 228's
  `orderOne_iff_kron_of_const`, unit 230's `orderOne_exchConj_iff` and unit 170's
  `ccm_fixes_dirac`, whose versions with `ℍ` as test algebra are `orderOne_quat_iff`,
  `orderOne_quat_exchConj_iff` and `ccm_fixes_dirac_quat`; and `QuaternionComplexification`'s
  `images_span`, of which `span_range_qToM` is the submodule form.

  `#print axioms` on all 7 declarations below: `[propext, Classical.choice, Quot.sound]`.
-/

import OrderOneRealBlock
import GammaFixesDirac
import QuaternionComplexification
import Mathlib.Algebra.Lie.OfAssociative

open Matrix
open scoped Kronecker Quaternion

namespace OrderOneQuaternion

open OrderOneBlockDiagonal OrderOneRealBlock QuaternionComplexification

/-! ## 1. Order-one sees only the spans of the test sets -/

section Span

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Field K]

/-- **ORDER-ONE SEES ONLY THE SPANS OF THE TEST SETS.** The order-one expression is bilinear in
the two test matrices, so testing against two sets is testing against their spans. -/
theorem orderOne_iff_span (S_L : Set (Matrix ι ι K)) (S_R : Set (Matrix κ κ K))
    (M : Matrix (ι × κ) (ι × κ) K) :
    (∀ a ∈ S_L, ∀ b ∈ S_R, ⁅⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆, (1 : Matrix ι ι K) ⊗ₖ b⁆ = 0) ↔
      (∀ a ∈ Submodule.span K S_L, ∀ b ∈ Submodule.span K S_R,
        ⁅⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆, (1 : Matrix ι ι K) ⊗ₖ b⁆ = 0) := by
  constructor
  · intro h a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha' =>
      induction hb using Submodule.span_induction with
      | mem b hb' => exact h a ha' b hb'
      | zero => simp
      | add b b' _ _ hb1 hb2 => rw [Matrix.kronecker_add, lie_add, hb1, hb2, add_zero]
      | smul c b _ hb1 => rw [Matrix.kronecker_smul, lie_smul, hb1, smul_zero]
    | zero => simp
    | add a a' _ _ ha1 ha2 => rw [Matrix.add_kronecker, lie_add, add_lie, ha1, ha2, add_zero]
    | smul c a _ ha1 => rw [Matrix.smul_kronecker, lie_smul, smul_lie, ha1, smul_zero]
  · intro h a ha b hb
    exact h a (Submodule.subset_span ha) b (Submodule.subset_span hb)

/-- Test sets spanning everything give the full-matrix answer: order-one against them holds iff
`M = C ⊗ 1 + 1 ⊗ B` (unit 228's `orderOne_iff_kron_of_const`). -/
theorem orderOne_iff_kron_of_span_eq_top (S_L S_R : Set (Matrix ι ι K))
    (hL : Submodule.span K S_L = ⊤) (hR : Submodule.span K S_R = ⊤)
    (M : Matrix (ι × ι) (ι × ι) K) :
    (∀ a ∈ S_L, ∀ b ∈ S_R, ⁅⁅M, a ⊗ₖ (1 : Matrix ι ι K)⁆, (1 : Matrix ι ι K) ⊗ₖ b⁆ = 0) ↔
      ∃ C B : Matrix ι ι K, M = C ⊗ₖ (1 : Matrix ι ι K) + (1 : Matrix ι ι K) ⊗ₖ B := by
  rw [orderOne_iff_span, hL, hR, ← orderOne_iff_kron_of_const]
  simp only [Submodule.mem_top, true_implies]

end Span

/-! ## 2. The quaternions inside `M₂(ℂ)` -/

/-- The images of `1, i, j, k` span `M₂(ℂ)` over `ℂ` (`images_span`). -/
theorem span_range_qToM : Submodule.span ℂ (Set.range qToM) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  obtain ⟨a, b, c, d, rfl⟩ := images_span M
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **ORDER-ONE AGAINST `ℍ` IS ORDER-ONE AGAINST `M₂(ℂ)`.** On `ℂ² ⊗ ℂ²`, an operator satisfies
order-one against the quaternions acting on the left and on the right iff it is
`C ⊗ 1 + 1 ⊗ B` — unit 168's answer for all of `M₂(ℂ)`. -/
theorem orderOne_quat_iff (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (∀ p q : ℍ[ℝ], ⁅⁅M, qToM p ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qToM q⁆ = 0) ↔
      ∃ C B : Matrix (Fin 2) (Fin 2) ℂ,
        M = C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B := by
  rw [← orderOne_iff_kron_of_span_eq_top _ _ span_range_qToM span_range_qToM]
  simp only [Set.forall_mem_range]

/-- The same with `ℍ` on one side only: `ℍ` on the left, all of `M₂(ℂ)` on the right. -/
theorem orderOne_quat_left_iff (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (∀ (p : ℍ[ℝ]) (b : Matrix (Fin 2) (Fin 2) ℂ), ⁅⁅M, qToM p ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ b⁆ = 0) ↔
      ∃ C B : Matrix (Fin 2) (Fin 2) ℂ,
        M = C ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ B := by
  rw [← orderOne_iff_kron_of_span_eq_top _ Set.univ span_range_qToM Submodule.span_univ]
  simp only [Set.forall_mem_range, Set.mem_univ, true_implies]

/-- **With the real structure too**: order-one against `ℍ` on both sides and invariance under
exchange-conjugation hold iff `M = A ⊗ 1 + 1 ⊗ Ā` — unit 169's answer, at `M₂(ℂ)`. -/
theorem orderOne_quat_exchConj_iff (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ((∀ p q : ℍ[ℝ], ⁅⁅M, qToM p ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qToM q⁆ = 0) ∧ exchConj M = M) ↔
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
        M = A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ) := by
  have hall : ∀ a : Matrix (Fin 2) (Fin 2) ℂ, a ∈ blockDiagSet (fun _ : Fin 2 => ()) :=
    fun _ _ _ h => absurd rfl h
  have hOO : (∀ p q : ℍ[ℝ], ⁅⁅M, qToM p ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qToM q⁆ = 0) ↔ OrderOne (fun _ : Fin 2 => ()) M := by
    rw [orderOne_quat_iff, ← orderOne_iff_kron_of_const]
    exact ⟨fun h a _ b _ => h a b, fun h a b => h a (hall a) b (hall b)⟩
  rw [hOO, orderOne_exchConj_iff]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A (), by rw [hA, ← blockKron_const]⟩
  · rintro ⟨A, hA⟩
    exact ⟨fun _ => A, by rw [hA, blockKron_const]⟩

/-- **AND WITH THE GRADING: UNIT 170'S ANSWER FOR `ℍ`.** Order-one against `ℍ` on both sides,
invariance under exchange-conjugation and anticommutation with `gammaMat` hold iff
`M = t • Dsym` for a real `t`. -/
theorem ccm_fixes_dirac_quat (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ((∀ p q : ℍ[ℝ], ⁅⁅M, qToM p ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)⁆,
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ qToM q⁆ = 0) ∧ exchConj M = M ∧
      M * RealSpectralWitness.gammaMat = -(RealSpectralWitness.gammaMat * M)) ↔
      ∃ t : ℝ, M = (t : ℂ) • RealSpectralWitness.Dsym := by
  constructor
  · rintro ⟨h1, hJ, hγ⟩
    obtain ⟨A, rfl⟩ := (orderOne_quat_exchConj_iff _).mp ⟨h1, hJ⟩
    obtain ⟨h01, h10, h11⟩ := GammaFixesDirac.entries_of_anticomm A hγ
    exact ⟨(A 0 0).re, GammaFixesDirac.kron_eq_re_smul_Dsym A h01 h10 h11⟩
  · rintro ⟨t, rfl⟩
    have hkron : (t : ℂ) • RealSpectralWitness.Dsym =
        ((t : ℂ) • SpectralTripleBimodule.pauli3) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((t : ℂ) • SpectralTripleBimodule.pauli3) := by
      rw [RealSpectralWitness.Dsym, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
    refine ⟨(orderOne_quat_iff _).mpr ⟨_, _, hkron⟩, ?_, ?_⟩
    · have := RealSpectralWitness.submatrix_prodSwap_Dsym
      ext a b
      have e := congrFun (congrFun this a) b
      simp only [Matrix.map_apply, Matrix.submatrix_apply] at e
      simp only [exchConj, Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply,
        smul_eq_mul, map_mul, Complex.conj_ofReal]
      rw [← e]
      rfl
    · rw [smul_mul_assoc, RealSpectralWitness.Dsym_anticomm_gammaMat, mul_smul_comm, smul_neg]

end OrderOneQuaternion
