/-
  SkolemNoether.lean — every algebra automorphism of a matrix algebra over a
  field is INNER, and the two consequences the cascade has been missing:
  a matrix-algebra identification is unique up to conjugation, and the two
  routes `End(M_b) → M_{b²}` agree.

  **SPINE link L11 (Pati–Salam uniqueness), gap N5 — SPINE CAMPAIGN unit 7.**
  **This is the theorem `F1_6_PatiSalamForced`'s header calls "Azumaya
  uniqueness, Skolem–Noether … established theorems not yet in Mathlib in the
  form needed", and `ERRATUM 550` records that half of that sentence was false
  when written. This is the other half, and it was true: Mathlib has no
  Skolem–Noether. Now the estate does.**

  ## The gap this closes

  July rated L11 PARTIAL and named the residue: *"justifying C2/C3 from
  structure (Skolem–Noether formalisation — moderate-hard)"*. C2 (`a = b²`) and
  C3 (`b = c`) became theorems on 14 September (`CascadeEnd.size_eq_of_end_equiv`,
  `factor_eq_of_end_equiv_tensor`), and the recompute's L11 audit then named what
  was still missing:

  > *Skolem–Noether for matrix algebras over `ℂ` (gap N5 proper, absent from
  > Mathlib and the estate — both queried) … Corollaries that give `F1_6`'s prose
  > its first statements: any two identifications `End(M_b) ≃ₐ M_b ⊗ M_b` differ
  > by an inner automorphism (the "Azumaya uniqueness" of Part 1b), the two
  > routes `End(M₂) → M₄` agree up to conjugation.*

  Queried before writing, and counted rather than glossed (`ERRATUM 541`):
  `grep -rn 'Skolem-Noether\|Skolem–Noether'` over the pinned Mathlib returns
  exactly **two lines, both comments** — `LinearAlgebra/Determinant.lean:464` and
  `LinearAlgebra/Trace.lean:324`, each reading `-- (using Skolem-Noether)`; `grep
  -rn 'skolemNoether\|SkolemNoether\|skolem_noether'` returns **nothing**, so
  there is no declaration. (The 31 files matching `skolem` case-insensitively are
  Skolemization and model theory, a different subject.) In the estate, `grep -rn
  -i 'Skolem|IsSimpleModule|MulAut.conj|inner automorphism' paper_f/*.lean *.lean`
  found only prose, in `F1_6_PatiSalamForced.lean` and
  `F3_8h_BackgroundIndependence.lean`. Neither library had the theorem.

  ## What is proved

  1. **`exists_mulVec_eq`** — a non-zero column vector can be carried to ANY
     vector by some matrix. Absent from Mathlib in this form; nine lines through
     `Matrix.vecMulVec_mulVec` and `single_dotProduct` (the latter is in Mathlib's
     ROOT namespace, not `Matrix`'s — `Data/Matrix/Mul.lean:183` sits above that
     file's `namespace Matrix`, and `--cites-lean` caught the qualified spelling
     this header first carried). This is the transitivity that makes the column
     module simple.
  2. **`isSimpleModule_column`**, **`isSimpleModule_twisted`** — the standard
     column module `Kⁿ` over `Mₙ(K)` is simple, and so is its twist by any
     algebra automorphism `φ` (the same module with `A • v := φ A *ᵥ v`).
     Mathlib has the Morita equivalence `Mathlib/RingTheory/Morita/Matrix.lean`
     but no *the column module is simple* lemma.
  3. **`exists_linearEquiv_twisted`** — the two are isomorphic as
     `Mₙ(K)`-modules, because a simple Artinian ring is **isotypic**: all its
     modules are built from one simple module. `IsSimpleRing.isIsotypic` is the
     Mathlib import that makes this route work at all, and no file in this estate
     had ever mentioned `IsIsotypic`.
  4. **`skolemNoether`** — **the theorem.** For every field `K`, every `n` with
     `NeZero n`, and every `φ : Mₙ(K) ≃ₐ[K] Mₙ(K)`, there is a unit `P` with
     `φ A = P * A * P⁻¹` for all `A`. The module isomorphism of 3 is `K`-linear
     (`hfc`, `hfc'`: a scalar `c` acts as the matrix `c • 1`, and `φ` fixes it
     because an `AlgEquiv` commutes with `algebraMap`), so it is a matrix, and
     invertible because the inverse map is one too.
  5. **`algEquiv_matrix_unique_up_to_inner`** — **"AZUMAYA UNIQUENESS", the
     statement `F1_6` Part 1b names in prose.** Any two identifications
     `e₁, e₂ : A ≃ₐ[K] Mₙ(K)` of the same algebra differ by conjugation:
     `e₂ a = P * e₁ a * P⁻¹`. The decomposition is unique up to an inner
     automorphism, which is what the word *uniqueness* in the cascade's prose has
     always meant.
  6. **`endMatrixEquiv_routes_agree`** — **the comparison `CascadeEnd`'s header
     declines to assert and `ERRATUM 548` records as open.** For every `b` with
     `NeZero b`, the two routes from `End(M_b)` to `M_{b²}` — the basis route
     `CascadeEnd.endMatrixEquiv b` and the Azumaya route
     `CascadeEnd.endTensorSq b` followed by `F4_1a`'s Kronecker isomorphism —
     agree up to conjugation by a single unit. **`endM2_routes_agree`** is the
     `b = 2` case, i.e. the cascade's own `End(M₂) → M₄` step, and
     **`endM4_routes_agree`** the `End(M₄) → M₁₆` one.

  ## What is NOT proved, said exactly

  - **`Aut(Mₙ(K)) ≅ PGLₙ(K)` is NOT stated.** `skolemNoether` gives surjectivity
    of conjugation onto the automorphisms; the kernel statement — that two units
    conjugate identically exactly when they differ by a central unit — needs the
    centre of `Mₙ(K)` to be the scalars, and the pinned Mathlib has no
    `Matrix.mem_center_iff` (queried: the `mem_center_iff` hits are
    `SpecialLinearGroup`'s, a different statement about `SL`). No group is built
    here, and `ASSUMPTIONS_LEDGER` 11 — from a matrix factor to the gauge group
    `SU(n)` — is untouched.
    ⚠ DONE, 20 September 2026 (hardening unit 186, `paper_f/MatrixAutPGL.lean`):
    `MatrixAutPGL.autEquivPGL : (Mₙ(K) ≃ₐ[K] Mₙ(K)) ≃* PGL(Fin n, K)` at every field and `n ≥ 1`,
    with `conjAut_eq_iff` the kernel statement in this bullet's own words; the centre came from
    `StarStructureMatrix.matrix_center_scalar`. `ASSUMPTIONS_LEDGER` 11 is still untouched. The
    bullet is kept as written (`ERRATUM 94`).
  - **The three-factor uniqueness of L11's headline is NOT closed.** "M₁₆ forces
    (4,2,2) with no alternatives" is still false as a statement about `M₁₆`
    itself: `M₁₆ ≃ₐ M_a ⊗ M_b ⊗ M_c` exists for every `abc = 16` by Kronecker,
    and nothing here prefers one. What this file supplies is the *up to
    conjugation* half that `F1_6`'s prose invoked without a statement.
  - **Cascade depth, which factor decomposes, `b = 2`** — all still postulates
    (`ASSUMPTIONS_LEDGER` 5, 10, 35), and the SU(n) identification with them.
  - **`F1_6` Part 2's "the transpose is the unique antiautomorphism up to inner
    automorphism"** is a different statement (antiautomorphisms, not
    automorphisms) and is not proved; it follows from this theorem applied to
    `φ ∘ transpose` and is one unit away, named here rather than attempted.

  ## Adversarial review, folded in

  **"This is Mathlib's theorem with a wrapper."** It is not: the pinned Mathlib
  has no Skolem–Noether (queried above). What Mathlib supplies is
  `IsSimpleRing.isIsotypic` — all modules over a simple Artinian ring are
  isotypic — which is the hard half of the classical proof; the four steps here
  are the column module's simplicity, the twist, the `K`-linearity of the module
  isomorphism, and its matrix.

  **"`Twisted` is a bare `def`, so the types are the same and the proof is
  circular."** The types are the same and the MODULE STRUCTURES are not: `Twisted
  n φ` carries `Module.compHom _ φ.toRingHom`, so `A • v = φ A *ᵥ v` there and
  `A *ᵥ v` in the untwisted module. Because the underlying type is shared, a
  type ascription is a no-op and `c • x` silently elaborates in the wrong
  structure — the explicit `toTwisted`/`ofTwisted` casts exist to stop exactly
  that, and they are identity functions whose only job is to pin which structure
  a `•` is read in.

  **"Two routes agreeing up to conjugation is weaker than agreeing."** Yes, and
  it is the truth: the two routes pick different bases, so they cannot be equal.
  Up to conjugation is what `ERRATUM 548` asked for, and `endMatrixEquiv_routes_agree`
  is stated with the conjugating unit existentially quantified, not hidden.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import CascadeEnd
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Data.Matrix.Action

namespace SkolemNoether

open Matrix

universe u

/-! ## 1. Transitivity on non-zero vectors -/

/-- **A NON-ZERO COLUMN VECTOR CAN BE CARRIED ANYWHERE.** Absent from Mathlib in
this form; it is what makes the column module simple. Uses `vecMulVec_mulVec` and
`single_dotProduct` (root namespace). -/
theorem exists_mulVec_eq {K : Type*} [Field K] {n : ℕ} {x : Fin n → K} (hx : x ≠ 0)
    (w : Fin n → K) : ∃ A : Matrix (Fin n) (Fin n) K, A *ᵥ x = w := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine ⟨vecMulVec w (Pi.single i (x i)⁻¹), ?_⟩
  rw [vecMulVec_mulVec, single_dotProduct, inv_mul_cancel₀ hi]
  ext j
  simp

/-! ## 2. The column module and its twist are simple -/

section

variable (K : Type u) [Field K] (n : ℕ) [NeZero n]

instance instIsSimpleRingMatrix : IsSimpleRing (Matrix (Fin n) (Fin n) K) :=
  IsSimpleRing.matrix (Fin n) K

instance instIsArtinianRingMatrix : IsArtinianRing (Matrix (Fin n) (Fin n) K) :=
  IsArtinianRing.of_finite K _

/-- The standard column module `Kⁿ` over `Mₙ(K)` is simple. -/
theorem isSimpleModule_column : IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx w => ?_⟩
  obtain ⟨A, hA⟩ := exists_mulVec_eq hx w
  exact ⟨A, hA⟩

/-- The column module twisted by an algebra automorphism: the same underlying
type, with `A • v := φ A *ᵥ v`. -/
def Twisted (_φ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) : Type u :=
  Fin n → K

variable (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K)

instance : AddCommGroup (Twisted K n φ) := inferInstanceAs (AddCommGroup (Fin n → K))

instance instModuleTwisted : Module (Matrix (Fin n) (Fin n) K) (Twisted K n φ) :=
  Module.compHom (Fin n → K) φ.toRingHom

/-- The identity cast INTO the twisted module. Its only job is to pin which
module structure a `•` is read in: `Twisted` is a `def`, so an ascription is a
no-op and `c • x` would elaborate in the wrong structure. -/
def toTwisted (v : Fin n → K) : Twisted K n φ := v

/-- The identity cast OUT of the twisted module. -/
def ofTwisted (v : Twisted K n φ) : Fin n → K := v

omit [NeZero n] in
theorem twisted_smul_def (A : Matrix (Fin n) (Fin n) K) (v : Twisted K n φ) :
    A • v = (φ A *ᵥ ofTwisted K n φ v : Fin n → K) := rfl

/-- The twisted column module is simple too. -/
theorem isSimpleModule_twisted :
    IsSimpleModule (Matrix (Fin n) (Fin n) K) (Twisted K n φ) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstanceAs (Nontrivial (Fin n → K)), fun x hx w => ?_⟩
  obtain ⟨A, hA⟩ := exists_mulVec_eq (x := x) hx w
  exact ⟨φ.symm A, by
    change φ (φ.symm A) *ᵥ x = w
    rw [φ.apply_symm_apply]
    exact hA⟩

/-- **ISOTYPY DOES THE WORK.** A simple Artinian ring has, up to isomorphism, one
simple module (`IsSimpleRing.isIsotypic` — the Mathlib import this route turns on,
and one no file in this estate had mentioned), so the column module and its twist
are isomorphic. -/
theorem exists_linearEquiv_twisted :
    Nonempty ((Fin n → K) ≃ₗ[Matrix (Fin n) (Fin n) K] Twisted K n φ) := by
  haveI := isSimpleModule_column K n
  haveI := isSimpleModule_twisted K n φ
  have h := IsSimpleRing.isIsotypic (Matrix (Fin n) (Fin n) K)
    ((Fin n → K) × Twisted K n φ)
  let e₁ := LinearEquiv.ofInjective
    (LinearMap.inl (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ))
    LinearMap.inl_injective
  let e₂ := LinearEquiv.ofInjective
    (LinearMap.inr (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ))
    LinearMap.inr_injective
  haveI : IsSimpleModule (Matrix (Fin n) (Fin n) K)
      (LinearMap.range
        (LinearMap.inl (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ))) :=
    IsSimpleModule.congr e₁.symm
  haveI : IsSimpleModule (Matrix (Fin n) (Fin n) K)
      (LinearMap.range
        (LinearMap.inr (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ))) :=
    IsSimpleModule.congr e₂.symm
  obtain ⟨e⟩ :=
    h (LinearMap.range
        (LinearMap.inr (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ)))
      (LinearMap.range
        (LinearMap.inl (Matrix (Fin n) (Fin n) K) (Fin n → K) (Twisted K n φ)))
  exact ⟨e₁.trans (e.trans e₂.symm)⟩

/-! ## 3. Skolem–Noether -/

/-- **SKOLEM–NOETHER FOR MATRIX ALGEBRAS.** Every `K`-algebra automorphism of
`Mₙ(K)` is inner. Absent from the pinned Mathlib (`grep -rli skolem` finds only
Skolem functions) and, before this file, from the estate. -/
theorem skolemNoether :
    ∃ P : (Matrix (Fin n) (Fin n) K)ˣ, ∀ A : Matrix (Fin n) (Fin n) K,
      φ A = P * A * (P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) := by
  obtain ⟨f⟩ := exists_linearEquiv_twisted K n φ
  have hf : ∀ (A : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
      ofTwisted K n φ (f (A *ᵥ v)) = φ A *ᵥ ofTwisted K n φ (f v) := fun A v => by
    rw [← smul_eq_mulVec, f.map_smul]; rfl
  have hfc : ∀ (c : K) (v : Fin n → K),
      ofTwisted K n φ (f (c • v)) = c • ofTwisted K n φ (f v) := fun c v => by
    have hcv : c • v = (c • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v := by
      rw [smul_mulVec, one_mulVec]
    rw [hcv, hf, ← Algebra.algebraMap_eq_smul_one, φ.commutes,
      Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
  have hfc' : ∀ (c : K) (v : Fin n → K),
      ofTwisted K n φ (f.symm (toTwisted K n φ (c • v)))
        = c • ofTwisted K n φ (f.symm (toTwisted K n φ v)) := fun c v => by
    apply f.injective
    change f (f.symm (toTwisted K n φ (c • v)))
      = f (c • ofTwisted K n φ (f.symm (toTwisted K n φ v)))
    rw [f.apply_symm_apply]
    apply congrArg (toTwisted K n φ)
    change c • v
      = ofTwisted K n φ (f (c • ofTwisted K n φ (f.symm (toTwisted K n φ v))))
    rw [hfc]
    change c • v = c • ofTwisted K n φ (f (f.symm (toTwisted K n φ v)))
    rw [f.apply_symm_apply]
    rfl
  let g : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun v => ofTwisted K n φ (f v)
      map_add' := fun a b => f.map_add a b
      map_smul' := hfc }
  let g' : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun v => ofTwisted K n φ (f.symm (toTwisted K n φ v))
      map_add' := fun a b => f.symm.map_add (toTwisted K n φ a) (toTwisted K n φ b)
      map_smul' := hfc' }
  have hgg' : g ∘ₗ g' = LinearMap.id :=
    LinearMap.ext fun v => f.apply_symm_apply (toTwisted K n φ v)
  have hg'g : g' ∘ₗ g = LinearMap.id := LinearMap.ext fun v => f.symm_apply_apply v
  let P : (Matrix (Fin n) (Fin n) K)ˣ :=
    ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' g',
      by rw [← LinearMap.toMatrix'_comp, hgg', LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hg'g, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun A => ?_⟩
  rw [Units.eq_mul_inv_iff_mul_eq]
  change φ A * LinearMap.toMatrix' g = LinearMap.toMatrix' g * A
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' (φ A)]
  conv_rhs => rw [← LinearMap.toMatrix'_toLin' A]
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, toLin'_apply]
  exact (hf A v).symm

end

/-! ## 4. Azumaya uniqueness: a matrix identification is unique up to conjugation -/

/-- **"AZUMAYA UNIQUENESS".** Any two identifications of the same algebra with
`Mₙ(K)` differ by an inner automorphism. This is the statement
`F1_6_PatiSalamForced`'s Part 1b invokes in prose (*"Azumaya uniqueness"*) and
which had no Lean counterpart. -/
theorem algEquiv_matrix_unique_up_to_inner {K : Type*} [Field K] {n : ℕ} [NeZero n]
    {A : Type*} [Ring A] [Algebra K A]
    (e₁ e₂ : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ P : (Matrix (Fin n) (Fin n) K)ˣ, ∀ a : A,
      e₂ a = P * e₁ a * (P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) := by
  obtain ⟨P, hP⟩ := skolemNoether K n (e₁.symm.trans e₂)
  refine ⟨P, fun a => ?_⟩
  have := hP (e₁ a)
  simpa using this

/-! ## 5. The two cascade routes `End(M_b) → M_{b²}` agree up to conjugation -/

/-- The Azumaya route: `End(M_b) ≃ₐ M_b ⊗ M_b ≃ₐ M_{b·b}`. -/
noncomputable def endTensorRoute (b : ℕ) [NeZero b] :
    Module.End ℂ (CascadeEnd.Mb b) ≃ₐ[ℂ] Matrix (Fin (b * b)) (Fin (b * b)) ℂ :=
  (CascadeEnd.endTensorSq b).trans (cascadeStepIso b b)

/-- **THE COMPARISON `CascadeEnd`'s HEADER DECLINES TO ASSERT, AND `ERRATUM 548`
RECORDS AS OPEN.** The basis route `CascadeEnd.endMatrixEquiv b` and the Azumaya
route agree up to conjugation by a single unit — which is the strongest true
statement, since the two routes choose different bases and cannot be equal. -/
theorem endMatrixEquiv_routes_agree (b : ℕ) [NeZero b] :
    ∃ P : (Matrix (Fin (b * b)) (Fin (b * b)) ℂ)ˣ,
      ∀ T : Module.End ℂ (CascadeEnd.Mb b),
        endTensorRoute b T
          = P * CascadeEnd.endMatrixEquiv b T
              * (P⁻¹ : (Matrix (Fin (b * b)) (Fin (b * b)) ℂ)ˣ) :=
  algEquiv_matrix_unique_up_to_inner (CascadeEnd.endMatrixEquiv b) (endTensorRoute b)

/-- The cascade's own `D₁ → D₂` step: the two routes `End(M₂) → M₄` agree up to
conjugation. -/
theorem endM2_routes_agree :
    ∃ P : (Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ)ˣ,
      ∀ T : Module.End ℂ (CascadeEnd.Mb 2),
        endTensorRoute 2 T
          = P * CascadeEnd.endMatrixEquiv 2 T
              * (P⁻¹ : (Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ)ˣ) :=
  endMatrixEquiv_routes_agree 2

/-- The `D₂ → D₃` step: the two routes `End(M₄) → M₁₆` agree up to conjugation. -/
theorem endM4_routes_agree :
    ∃ P : (Matrix (Fin (4 * 4)) (Fin (4 * 4)) ℂ)ˣ,
      ∀ T : Module.End ℂ (CascadeEnd.Mb 4),
        endTensorRoute 4 T
          = P * CascadeEnd.endMatrixEquiv 4 T
              * (P⁻¹ : (Matrix (Fin (4 * 4)) (Fin (4 * 4)) ℂ)ˣ) :=
  endMatrixEquiv_routes_agree 4

end SkolemNoether
