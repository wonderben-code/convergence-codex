/-
  MatrixAutPGL: `Aut(Mₙ(K)) ≅ PGL(n, K)` — the automorphism group of a matrix algebra over a
  field is the projective general linear group, as a group isomorphism

  Campaign 3 hardening unit 186 (20 September 2026). Spine link L11 (Pati–Salam uniqueness).

  WHY. `SPINE.md`'s L11 row says *"what is still unwritten is the statement `Aut(Mₙ) ≅ PGLₙ`
  itself, and it is no longer blocked on an absence"*; `SkolemNoether.lean`'s header lists it
  first under *what is NOT proved*, and `StarStructureMatrix.lean`'s header says the centre —
  the half L11's row named as missing — is now available and *"the statement itself is not
  written"*. `F1_7_SpacetimeForced` states `Aut(M₂(ℂ)) ≅ PGL₂(ℂ)` three times in prose and
  `F3_8h_BackgroundIndependence` states `Aut(M₄(ℂ)) = Inn(M₄(ℂ)) = PGL₄(ℂ)` once, each *"by
  Skolem–Noether"*, with no declaration behind the sentence (queried: `PGL` occurs in four
  `paper_f` files, in eleven comment lines and no declaration). This file writes the statement.

  WHAT IS PROVED, for every field `K` and every `n` (the isomorphism needs `n ≥ 1`).
  (1) `conjAut : GL (Fin n) K →* (Mₙ(K) ≃ₐ[K] Mₙ(K))` — conjugation `A ↦ P A P⁻¹` as a group
      homomorphism into the `K`-algebra automorphisms (`conjAut_apply`, definitional), built
      from Mathlib's conjugation action of the units and `MulSemiringAction.toAlgAut`.
  (2) `conjAut_surjective` — **every automorphism is inner**: this estate's own
      `SkolemNoether.skolemNoether` supplies the unit. `exists_conjAut_eq` is the same fact in
      the form `Aut = Inn`.
  (3) `ker_conjAut : (conjAut K n).ker = Subgroup.center (GL (Fin n) K)` — **the kernel is the
      centre**: a unit conjugating trivially commutes with every matrix
      (`mem_ker_conjAut_iff`), hence is a scalar by this estate's
      `StarStructureMatrix.matrix_center_scalar`, and the centre of `GL` is the scalar units by
      Mathlib's `GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`. `conjAut_scalar`:
      scalar units act trivially. `conjAut_eq_iff`: **two units conjugate identically iff they
      differ by a scalar unit** — the kernel statement `SkolemNoether.lean`'s header asks for in
      exactly those words.
  (4) `autEquivPGL : (Mₙ(K) ≃ₐ[K] Mₙ(K)) ≃* PGL(Fin n, K)` — **`Aut(Mₙ(K)) ≅ PGL(n, K)`**, by
      the first isomorphism theorem on (2) and (3) (`QuotientGroup.quotientKerEquivOfSurjective`
      and `quotientMulEquivOfEq`), with `autEquivPGL_conjAut`: the class of `P` is the image of
      conjugation by `P`. `PGL(n, K)` is Mathlib's `Matrix.ProjGenLinGroup`, `GL ⧸ centre`.
  (5) The spine's two instances: `autM2EquivPGL : Aut(M₂(ℂ)) ≃* PGL(2, ℂ)` (`F1_7`'s sentence)
      and `autM4EquivPGL : Aut(CascadeAlgebra) ≃* PGL(4, ℂ)` (`F3_8h`'s sentence, on the
      cascade's own algebra `M₄(ℂ)`).

  NOT PROVED, said exactly.
  • `ASSUMPTIONS_LEDGER` 11 — from a matrix factor to the gauge GROUP `SU(n)` — is untouched.
    `PGL(n, K)` is the automorphism group of the ALGEBRA; nothing here is a compact real form,
    a Lie group, a topology, or a determinant condition.
  • `F1_7`'s next sentence — `PGL₂(ℂ) ≅ SO⁺(3,1)`, also written there as `PSL₂(ℂ) ≅ SO⁺(3,1)`
    — is NOT stated, and its two halves now are:
    `Aut(M₂(ℂ)) ≅ PGL(2, ℂ)` here, and `SL₂(ℂ) ⧸ {±1} ≃* SO⁺(1,3)` in
    `SL2Quotient.sl2QuotEquiv` (with `SpinSurjective.spinDoubleCover` beside it) — the estate's
    Lorentz chain, 64 declarations named `lorentz…` by query, which this file neither touches
    nor needs. **The bridge between them, `PGL(2, ℂ) ≃* SL₂(ℂ) ⧸ {±1}`** (every complex unit
    is a square, so `PGL(n, ℂ) ≅ PSL(n, ℂ)`), **is not written** — queried: no declaration's
    name contains `pgl` or `psl`, and the only `PGL` in `paper_f` is the eleven prose lines.
    ⚠ DONE, 20 September 2026 (hardening unit 187, `paper_f/MatrixPGLPSL.lean`): the bridge is
    `sl2QuotEquivPGL`, via `pslEquivPGL : PSL(n, K) ≃* PGL(n, K)` over any algebraically closed
    field, and the composite is `autM2EquivSOplus13 : Aut(M₂(ℂ)) ≃* SO⁺(1,3)`. The bullet is kept
    as written (`ERRATUM 94`).
  • L11's headline, *"`M₁₆` forces `(4,2,2)` with no alternatives"*, is not closed by knowing
    `Aut(M₁₆)`: every `abc = 16` still decomposes `M₁₆` by Kronecker and nothing here prefers
    one. Cascade depth, which factor decomposes, and `b = 2` remain postulates
    (`ASSUMPTIONS_LEDGER` 5, 10, 30, 35).
  • `dim PGL₄(ℂ) = 15` (`F3_8h`'s next line) is a manifold dimension the estate has no object
    for; `F3_8h.b4_automorphism_dim` remains the numeral it was.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `conjAut_surjective`, `exists_conjAut_eq`,
  `autEquivPGL` and `autEquivPGL_conjAut` take `[NeZero n]` (Skolem–Noether needs a non-empty
  index); `conjAut`, `conjAut_apply`, `mem_ker_conjAut_iff`, `ker_conjAut`, `conjAut_scalar` and
  `conjAut_eq_iff` hold at every `n`. `K` is any field. Nothing takes positivity, a norm, or a
  star.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 12 names run against `paper_f`
  with `newnames_scan`'s regex before this header was written — none taken).
  `SkolemNoether.algEquiv_matrix_unique_up_to_inner` is (2) for two identifications of one
  algebra; it does not build the homomorphism, the kernel, or the group.
  `Matrix.GeneralLinearGroup` occurs in the estate as the ambient of `LorentzGroup.O13` and
  `SOplus13` (`GL (Fin 4) ℝ`) and in the Gaussian-field symmetry files
  (`FieldSymmetryInclusion.linSymGL`); no file conjugates a matrix algebra by it or forms a
  quotient of it.
-/

import SkolemNoether
import StarStructureMatrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Ring.Action.ConjAct

open Matrix
open scoped MatrixGroups

namespace MatrixAutPGL

variable (K : Type) [Field K] (n : ℕ)

/-- **Conjugation as a group homomorphism** `GL(n, K) →* Aut_K(Mₙ(K))`, `P ↦ (A ↦ P A P⁻¹)`. -/
def conjAut : GL (Fin n) K →* (Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :=
  (MulSemiringAction.toAlgAut (ConjAct (Matrix (Fin n) (Fin n) K)ˣ) K
    (Matrix (Fin n) (Fin n) K)).comp ConjAct.toConjAct.toMonoidHom

theorem conjAut_apply (P : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) K) :
    conjAut K n P A =
      (P : Matrix (Fin n) (Fin n) K) * A * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

/-- **Every automorphism is inner** — this estate's Skolem–Noether, repackaged as surjectivity
of `conjAut`. -/
theorem conjAut_surjective [NeZero n] : Function.Surjective (conjAut K n) := fun φ => by
  obtain ⟨P, hP⟩ := SkolemNoether.skolemNoether K n φ
  exact ⟨P, AlgEquiv.ext fun A => (hP A).symm⟩

/-- `Aut = Inn`: for every automorphism there is a unit conjugating to it. -/
theorem exists_conjAut_eq [NeZero n] (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ P : GL (Fin n) K, conjAut K n P = φ :=
  conjAut_surjective K n φ

/-- A unit conjugates trivially iff it commutes with every matrix. -/
theorem mem_ker_conjAut_iff (P : GL (Fin n) K) :
    P ∈ (conjAut K n).ker ↔
      ∀ A : Matrix (Fin n) (Fin n) K, (P : Matrix (Fin n) (Fin n) K) * A = A * P := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h A
    have hA : (P : Matrix (Fin n) (Fin n) K) * A
        * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A := by
      have := congrArg
        (fun ψ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K => ψ A) h
      simpa [conjAut_apply] using this
    calc (P : Matrix (Fin n) (Fin n) K) * A
        = (P : Matrix (Fin n) (Fin n) K) * A
            * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P := by
          rw [Units.inv_mul_cancel_right]
      _ = A * P := by rw [hA]
  · intro h
    ext A
    simp only [AlgEquiv.one_apply]
    rw [conjAut_apply, h A, Units.mul_inv_cancel_right]

/-- **The kernel of conjugation is the centre of `GL(n, K)`.** -/
theorem ker_conjAut : (conjAut K n).ker = Subgroup.center (GL (Fin n) K) := by
  ext P
  rw [mem_ker_conjAut_iff, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := StarStructureMatrix.matrix_center_scalar (P : Matrix (Fin n) (Fin n) K) h
    exact ⟨c, by rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩ A
    rw [← hc]
    exact (Matrix.scalar_commute c (fun r => mul_comm c r) A).eq

/-- Scalar units conjugate trivially. -/
theorem conjAut_scalar (c : Kˣ) :
    conjAut K n (Matrix.GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  rw [← MonoidHom.mem_ker, ker_conjAut, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨c, rfl⟩

/-- **Two units conjugate identically iff they differ by a scalar unit.** -/
theorem conjAut_eq_iff (P Q : GL (Fin n) K) :
    conjAut K n P = conjAut K n Q ↔
      ∃ c : Kˣ, Q = P * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : conjAut K n P = conjAut K n Q ↔ P⁻¹ * Q ∈ (conjAut K n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
  rw [h1, ker_conjAut, Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, mul_inv_cancel_left]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, inv_mul_cancel_left]⟩

/-- **`Aut(Mₙ(K)) ≅ PGL(n, K)`**: the first isomorphism theorem on `conjAut`, which is
surjective (Skolem–Noether) with kernel the centre. -/
noncomputable def autEquivPGL [NeZero n] :
    (Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) ≃* PGL(Fin n, K) :=
  (QuotientGroup.quotientKerEquivOfSurjective (conjAut K n) (conjAut_surjective K n)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_conjAut K n))

/-- The isomorphism sends conjugation by `P` to the class of `P`. -/
theorem autEquivPGL_conjAut [NeZero n] (P : GL (Fin n) K) :
    autEquivPGL K n (conjAut K n P) = Matrix.ProjGenLinGroup.mk P := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective (conjAut K n) (conjAut_surjective K n))
      (QuotientGroup.mk P) = conjAut K n P := by
    simp [QuotientGroup.quotientKerEquivOfSurjective]
  change (QuotientGroup.quotientMulEquivOfEq (ker_conjAut K n))
      ((QuotientGroup.quotientKerEquivOfSurjective (conjAut K n)
        (conjAut_surjective K n)).symm (conjAut K n P)) = _
  rw [← he, MulEquiv.symm_apply_apply]
  rfl

/-- `Aut(M₂(ℂ)) ≅ PGL(2, ℂ)` — the sentence `F1_7_SpacetimeForced`'s header states three times
*"by Skolem–Noether"*, now a declaration. -/
noncomputable def autM2EquivPGL :
    (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃* PGL(2, ℂ) :=
  autEquivPGL ℂ 2

/-- `Aut(M₄(ℂ)) ≅ PGL(4, ℂ)` on the cascade's own algebra — `F3_8h_BackgroundIndependence`'s
Phase 4 sentence *"Aut(M₄(ℂ)) = Inn(M₄(ℂ)) = PGL₄(ℂ) by Skolem-Noether"*, now a declaration. -/
noncomputable def autM4EquivPGL : (CascadeAlgebra ≃ₐ[ℂ] CascadeAlgebra) ≃* PGL(4, ℂ) :=
  autEquivPGL ℂ 4

end MatrixAutPGL
