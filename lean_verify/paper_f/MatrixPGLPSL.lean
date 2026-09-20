/-
  MatrixPGLPSL: `PSL(n, K) ≅ PGL(n, K)` over an algebraically closed field, `SL₂(ℂ) ⧸ {±1} ≅
  PGL(2, ℂ)`, and so `Aut(M₂(ℂ)) ≅ SO⁺(1,3)` — the automorphism group of the cascade's first
  level IS the proper orthochronous Lorentz group

  Campaign 3 hardening unit 187 (20 September 2026). Spine links L8 (spacetime dimension), L9
  (Lorentzian signature) and L11.

  WHY. `F1_7_SpacetimeForced`'s *Aut lineage* reads `M₂ → Aut(M₂) → PGL₂(ℂ) → SL₂(ℂ) ≅ Spin(3,1) →
  dim = 4`, and states `PGL₂(ℂ) ≅ SO⁺(3,1)` (once also as `PSL₂(ℂ) ≅ SO⁺(3,1)`) *"by standard Lie
  theory"*. Unit 186 made the first arrow a theorem (`MatrixAutPGL.autM2EquivPGL`) and named the
  missing bridge: the estate's Lorentz chain ends in `SL2Quotient.sl2QuotEquiv : SL₂(ℂ) ⧸ {±1} ≃*
  SO⁺(1,3)`, while the automorphism group lands in Mathlib's `PGL(2, ℂ) = GL ⧸ centre`, and nothing
  identified the two quotients. This file writes the bridge and composes the lineage.

  WHAT IS PROVED.
  (1) `slToPGL : SL(n, K) →* PGL(n, K)` (include, then project), with **`ker_slToPGL`: the kernel is
      the centre of `SL(n, K)`** (the scalar matrices of determinant one — Mathlib's
      `SpecialLinearGroup.mem_center_iff` and
      `GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`), for every field and every `n`; and
      **`slToPGL_surjective`** for `n ≥ 1` over an algebraically closed field: every unit has an
      `n`-th root, so every class in `PGL` contains a matrix of determinant one. Hence
      **`pslEquivPGL : PSL(n, K) ≃* PGL(n, K)`** — Mathlib has both groups as separate definitions
      and no map between them (queried: the two files defining them are the only two mentioning
      them).
  (2) **`center_sl2C_eq_sl2PmOne`**: the centre of `SL₂(ℂ)` is `{±1}`, i.e. this estate's
      `SL2Quotient.sl2PmOne` (`r² = 1 ⇒ r = ±1`), so **`sl2QuotEquivPGL : SL₂(ℂ) ⧸ {±1} ≃*
      PGL(2, ℂ)`** — the bridge.
  (3) **`autM2EquivSOplus13 : (M₂(ℂ) ≃ₐ[ℂ] M₂(ℂ)) ≃* SOplus13`** — `Aut(M₂(ℂ)) ≅ PGL₂(ℂ) ≅
      SL₂(ℂ) ⧸ {±1} ≅ SO⁺(1,3)` as one isomorphism, with **`autM2EquivSOplus13_conjAut`**:
      conjugation by `A ∈ SL₂(ℂ)` goes to `LorentzGroup.lorentzSOplusHom A`, the Lorentz
      transformation the estate has attached to `A` since 1 August. `F1_7`'s two sentences
      `PGL₂(ℂ) ≅ SO⁺(3,1)` and `PSL₂(ℂ) ≅ SO⁺(3,1)` are declarations, and the Aut lineage's
      composite `Aut(M₂(ℂ)) → SO⁺(1,3)` is a single `MulEquiv`.

  NOT PROVED, said exactly.
  • `SL₂(ℂ) ≅ Spin(3,1)` AS GROUPS is not here and not in the estate: what exists is the
    identification of the two QUOTIENTS, `SpinSurjective.spinEquivSL2Quot : Spin(1,3) ⧸ {±1} ≃*
    SL₂(ℂ) ⧸ {±1}` (queried: no declaration has type `_ ≃* SL2C` or `spinGroup Q₁₃ ≃* _`). So the
    lineage's third arrow is a theorem about `PSL`, and `F1_7`'s `SL₂(ℂ) ≅ Spin(3,1)` (seven prose
    lines) stays prose.
  • Nothing topological: `SO⁺(1,3)` is `LorentzGroup.SOplus13`, a subgroup of `GL (Fin 4) ℝ`;
    connectedness, the Lie structure and `dim = 6` (the lineage's *dim = 4* is its own numeral,
    `F1_7`'s) are not touched, and the estate's `LorentzIdentityComponent` and
    `LorentzConnectedReduction` files are neither used nor needed here.
  • Algebraic closure is USED, not incidental: `slToPGL_surjective` takes `[IsAlgClosed K]`
    (ℂ's instance is Mathlib's), and no statement is made about `PGL(n, K)` against `PSL(n, K)`
    over a field that is not algebraically closed.
  • `ASSUMPTIONS_LEDGER` 11 (from a matrix factor to `SU(n)`) is untouched, as in unit 186: the
    group here is the automorphism group of the algebra and the Lorentz group, not a compact form.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `slToPGL_surjective`, `pslEquivPGL` and
  `pslEquivPGL_mk` take `[NeZero n]` and `[IsAlgClosed K]`; `slToPGL`, `slToPGL_apply` and
  `ker_slToPGL` hold at every `n` over every field; the five declarations at `ℂ`, `n = 2` take
  nothing. `K : Type` (universe 0), inherited from unit 186's `autEquivPGL`.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 11 names run against `paper_f` with
  `newnames_scan`'s regex before this header was written — none taken). Before unit 186 no
  declaration in `paper_f` was named for `PGL` or `PSL` (the five `psl` hits are `PSLie`, the
  Pati–Salam Lie algebra, another word); `sl2PmOne`, `SL2Quot` and `sl2QuotEquiv` are reused from
  `SL2Quotient`, not rebuilt, and `SOplus13`, `lorentzSOplusHom` from `LorentzGroup`.
-/

import MatrixAutPGL
import SL2Quotient
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Matrix
open scoped MatrixGroups

namespace MatrixPGLPSL

variable (K : Type) [Field K] (n : ℕ)

/-- `SL(n, K) →* PGL(n, K)`: include into `GL`, then project onto `GL ⧸ centre`. -/
def slToPGL : SpecialLinearGroup (Fin n) K →* PGL(Fin n, K) :=
  Matrix.ProjGenLinGroup.mk.comp SpecialLinearGroup.toGL

theorem slToPGL_apply (A : SpecialLinearGroup (Fin n) K) :
    slToPGL K n A = Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) := rfl

/-- The kernel of `SL → PGL` is the centre of `SL`: the scalar matrices of determinant one. -/
theorem ker_slToPGL : (slToPGL K n).ker = Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  ext A
  rw [MonoidHom.mem_ker, slToPGL_apply, ← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar,
    SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr⟩
    have hr' : Matrix.scalar (Fin n) r = (A : Matrix (Fin n) (Fin n) K) := hr
    refine ⟨r, ?_, hr'⟩
    have h1 : Matrix.det (Matrix.scalar (Fin n) r) = 1 := by
      rw [hr']; exact SpecialLinearGroup.det_coe A
    rw [Fintype.card_fin]
    rwa [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩

/-- Over an algebraically closed field every unit has an `n`-th root, so every class in `PGL`
contains a matrix of determinant one. -/
theorem slToPGL_surjective [NeZero n] [IsAlgClosed K] : Function.Surjective (slToPGL K n) := by
  intro q
  induction q using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    have hdet : Matrix.det (g : Matrix (Fin n) (Fin n) K) ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
    obtain ⟨z, hz⟩ :=
      IsAlgClosed.exists_pow_nat_eq (Matrix.det (g : Matrix (Fin n) (Fin n) K)) (NeZero.pos n)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hdet (by rw [← hz, zero_pow (NeZero.ne n)])
    have hAdet : Matrix.det (z⁻¹ • (g : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz, inv_mul_cancel₀ hdet]
    refine ⟨⟨z⁻¹ • (g : Matrix (Fin n) (Fin n) K), hAdet⟩, ?_⟩
    have hu : (SpecialLinearGroup.toGL
        (⟨z⁻¹ • (g : Matrix (Fin n) (Fin n) K), hAdet⟩ : SpecialLinearGroup (Fin n) K))
        = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 z hz0)⁻¹ * g := by
      apply Units.ext
      change z⁻¹ • (g : Matrix (Fin n) (Fin n) K) = _
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]
    rw [slToPGL_apply, hu, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

/-- **`PSL(n, K) ≅ PGL(n, K)` over an algebraically closed field.** -/
noncomputable def pslEquivPGL [NeZero n] [IsAlgClosed K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* PGL(Fin n, K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_slToPGL K n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (slToPGL K n) (slToPGL_surjective K n))

theorem pslEquivPGL_mk [NeZero n] [IsAlgClosed K] (A : SpecialLinearGroup (Fin n) K) :
    pslEquivPGL K n (QuotientGroup.mk A) = slToPGL K n A := rfl

/-- The centre of `SL₂(ℂ)` is `{±1}` — `SL2Quotient.sl2PmOne`. -/
theorem center_sl2C_eq_sl2PmOne :
    Subgroup.center (SpecialLinearGroup (Fin 2) ℂ) = SL2Quotient.sl2PmOne := by
  ext A
  rw [SpecialLinearGroup.mem_center_iff, SL2Quotient.mem_sl2PmOne]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Fintype.card_fin, pow_two, mul_self_eq_one_iff] at hr
    rcases hr with rfl | rfl
    · left; rw [← hA]; simp
    · right; rw [← hA, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, by simp, by rw [h]; simp⟩
    · exact ⟨-1, by simp, by rw [h, map_neg, map_one]⟩

/-- **`SL₂(ℂ) ⧸ {±1} ≅ PGL(2, ℂ)`** — the bridge between the estate's Lorentz chain and its
automorphism group. -/
noncomputable def sl2QuotEquivPGL : SL2Quotient.SL2Quot ≃* PGL(2, ℂ) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2C_eq_sl2PmOne.symm).trans (pslEquivPGL ℂ 2)

theorem sl2QuotEquivPGL_mk (A : SpecialLinearGroup (Fin 2) ℂ) :
    sl2QuotEquivPGL (QuotientGroup.mk A) = slToPGL ℂ 2 A := rfl

/-- **`Aut(M₂(ℂ)) ≅ SO⁺(1,3)`** — `F1_7_SpacetimeForced`'s Aut lineage as one isomorphism:
`Aut(M₂(ℂ)) ≅ PGL₂(ℂ) ≅ SL₂(ℂ) ⧸ {±1} ≅ SO⁺(1,3)`. -/
noncomputable def autM2EquivSOplus13 :
    (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃* LorentzGroup.SOplus13 :=
  MatrixAutPGL.autM2EquivPGL.trans (sl2QuotEquivPGL.symm.trans SL2Quotient.sl2QuotEquiv)

/-- Conjugation by `A ∈ SL₂(ℂ)` goes to `A`'s Lorentz transformation. -/
theorem autM2EquivSOplus13_conjAut (A : SpecialLinearGroup (Fin 2) ℂ) :
    autM2EquivSOplus13 (MatrixAutPGL.conjAut ℂ 2 (SpecialLinearGroup.toGL A))
      = LorentzGroup.lorentzSOplusHom A := by
  have h1 : MatrixAutPGL.autM2EquivPGL (MatrixAutPGL.conjAut ℂ 2 (SpecialLinearGroup.toGL A))
      = sl2QuotEquivPGL (QuotientGroup.mk A) := by
    rw [sl2QuotEquivPGL_mk]
    exact MatrixAutPGL.autEquivPGL_conjAut ℂ 2 _
  simp only [autM2EquivSOplus13, MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply,
    SL2Quotient.sl2QuotEquiv_mk]

end MatrixPGLPSL
