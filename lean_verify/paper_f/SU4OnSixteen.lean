/-
  SU4OnSixteen.lean — the `sl₄` action on the chiral 16 as a REPRESENTATION,
  `(4, 2, 1) ⊕ (4̄, 1, 2)`, and the cubic anomaly vanishing on it as a theorem
  about that representation rather than about a weighted sum.

  WHY THIS FILE EXISTS — SPINE LINK L16. The link's July rating is *MISSING (as
  representation theory)*, and the qualifier is exact: `AnomalyTraces` proves
  the cubic trace form and its identities on matrices — antifund = −fund by the
  transpose antiautomorphism, `su(2)` vanishing, the Pati–Salam sum — but
  **`sl₄` acts on the 16 nowhere**: every operator on `PSIndex` in the estate
  is the identity on the `Fin 4` index (`Su2ModuleSixteen`'s `EL`, `FL`, `ER`,
  `FR` are `1 ⊗ₖ e2`-shaped) or diagonal (`WeinbergIndex`'s charges) — queried,
  not recalled. `pati_salam_anomaly_free` is a sum with
  the multiplicities written into the statement, which `ASSUMPTIONS_LEDGER` 31
  records as *"equal multiplicity written into the statement"* and *"L/R
  collapsed"*. `WeinbergIndex` and `Su2ModuleSixteen` index the 16 as
  `PSIndex = (Fin 4 × Fin 2) ⊕ (Fin 4 × Fin 2)` and act on it with `sl₂_L`,
  `sl₂_R`, `T₃` and `B−L`, and `WeinbergIndex`'s own header names its residue
  as *"the full su(4) colour action beyond its B−L direction"*. The 24-link
  recompute's L16 auditor named this file, declaration by declaration.

  WHAT THIS FILE PROVES.

  1. **`su4Rep`** — `X ↦ fromBlocks (X ⊗ 1) 0 0 ((−Xᵀ) ⊗ 1)`: `gl₄ ⊇ sl₄` acting
     on the 16 as the fundamental on the left-handed block and the
     antifundamental on the right-handed one, tensored with the identity on the
     `sl₂` index. **`su4Rep_bracket`**: it is a Lie algebra action —
     `su4Rep [X, Y] = [su4Rep X, su4Rep Y]`. This is the object L16's qualifier
     says is missing.
  2. `trace_fromBlocks_any`, **`cubicTrace_blockDiag`** — the cubic trace form
     is ADDITIVE over a block-diagonal decomposition. Absent from Mathlib in
     the trace form (`Matrix.trace_fromBlocks` does not exist under that name
     in the pinned library, checked) and absent from `AnomalyTraces`, whose
     lemmas are all on Kronecker products of a single block. The estate has
     the trace half for `Fin p`/`Fin q` blocks only
     (`BlockDiagonalSplit.trace_fromBlocks_diag`); `PSIndex`'s blocks are
     `Fin 4 × Fin 2`, so it is restated for arbitrary finite index types.
  3. **`su4_cubic_on_sixteen`** — `d(su4Rep X₁, su4Rep X₂, su4Rep X₃) = 0`: the
     `SU(4)³` anomaly vanishes on the 16 BECAUSE the two blocks are `4` and
     `4̄`, each with multiplicity 2 from the `sl₂` index — the multiplicity is
     `Fintype.card (Fin 2)`, read off the representation, not a literal.
  4. **`su4_su4_su2L_on_sixteen`, `su4_su4_su2R_on_sixteen`** — the mixed
     `SU(4)²–SU(2)_L` and `SU(4)²–SU(2)_R` anomalies vanish on the 16, with the
     two `sl₂` factors DISTINGUISHED: `EL` acts on the left block only and
     `ER` on the right block only, which is what `ASSUMPTIONS_LEDGER` 31's
     *"L/R collapsed"* said the trace-identity layer could not do.

  WHAT THIS DOES NOT DO. **It does not build a `LieModule`** — `su4Rep` is a
  function on matrices with the bracket law proved, not a Mathlib `LieHom
  (sl (Fin 4) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ)`; that packaging is one
  definition away and no theorem here needs it. **It does not identify the
  cubic trace with the triangle anomaly** — that is the Adler–Bell–Jackiw
  reading, cited in `AnomalyTraces`'s header and a postulate of the physics,
  not of this file. **The fermion content `(4,2,1) ⊕ (4̄,1,2)` is the INPUT** —
  it is `PSIndex`'s two summands with `su4Rep`'s two blocks — and whether it
  is a consequence of the cascade is L12/L16's postulate, untouched here.
  **No `SU(2)²–SU(4)` or gravitational-mixed term** is stated; the two here are
  the ones the audit named as the L/R separation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import AnomalyTraces
import WeinbergIndex
import Su2ModuleSixteen

namespace SU4OnSixteen

open Matrix WeinbergIndex AnomalyTraces Su2ModuleSixteen
open scoped Kronecker

noncomputable section

/-! ## 1. The representation -/

/-- **`gl₄` ON THE 16**: `X` on the left-handed block (the `4`), `−Xᵀ` on the
right-handed block (the `4̄`), each tensored with the identity on the `sl₂`
index. -/
def su4Rep (X : Matrix (Fin 4) (Fin 4) ℂ) : Matrix PSIndex PSIndex ℂ :=
  fromBlocks (X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
    ((-Xᵀ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- Kronecker with `1` is additive on the left (a local lemma; Mathlib has
`add_kronecker` and this file needs the subtraction form). -/
theorem sub_kronecker_one (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    (A - B) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) = A ⊗ₖ 1 - B ⊗ₖ 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [kroneckerMap_apply, sub_mul]

/-- Blockwise subtraction (Mathlib has `fromBlocks_add` and `fromBlocks_neg`, not this). -/
theorem fromBlocks_sub' {m n : Type*} (A A' : Matrix m m ℂ) (B B' : Matrix m n ℂ)
    (C C' : Matrix n m ℂ) (D D' : Matrix n n ℂ) :
    fromBlocks A B C D - fromBlocks A' B' C' D'
      = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp only [sub_eq_add_neg]

theorem su4Rep_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    su4Rep X * su4Rep Y
      = fromBlocks ((X * Y) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
          ((Xᵀ * Yᵀ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  unfold su4Rep
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, neg_mul_neg]

/-- **A LIE ALGEBRA ACTION.** -/
theorem su4Rep_bracket (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    su4Rep (X * Y - Y * X) = su4Rep X * su4Rep Y - su4Rep Y * su4Rep X := by
  rw [su4Rep_mul, su4Rep_mul, fromBlocks_sub', sub_zero]
  unfold su4Rep
  rw [sub_kronecker_one]
  congr 2
  rw [transpose_sub, transpose_mul, transpose_mul, neg_sub, sub_kronecker_one]

/-! ## 2. The cubic trace form is additive over block-diagonal matrices -/

/-- The trace of a block matrix is the sum of the diagonal blocks' traces, for
ANY finite index types. `BlockDiagonalSplit.trace_fromBlocks_diag` is the
`Fin p`/`Fin q` case with zero off-diagonal blocks; `PSIndex` is
`(Fin 4 × Fin 2) ⊕ (Fin 4 × Fin 2)`, outside its reach. -/
theorem trace_fromBlocks_any {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    trace (fromBlocks A B C D) = trace A + trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂]

/-- **THE CUBIC FORM SPLITS OVER A BLOCK-DIAGONAL DECOMPOSITION.** -/
theorem cubicTrace_blockDiag {m n : Type*} [Fintype m] [Fintype n]
    (A₁ A₂ A₃ : Matrix m m ℂ) (D₁ D₂ D₃ : Matrix n n ℂ) :
    cubicTrace (fromBlocks A₁ 0 0 D₁) (fromBlocks A₂ 0 0 D₂)
        (fromBlocks A₃ 0 0 D₃)
      = cubicTrace A₁ A₂ A₃ + cubicTrace D₁ D₂ D₃ := by
  unfold cubicTrace
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [fromBlocks_add, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  exact trace_fromBlocks_any _ _ _ _

/-! ## 3. The `SU(4)³` anomaly vanishes on the 16 -/

/-- **`d(su4Rep X₁, su4Rep X₂, su4Rep X₃) = 0`.** The left block contributes
`card (Fin 2) · d(X₁, X₂, X₃)`, the right block `card (Fin 2) · d(−X₁ᵀ, −X₂ᵀ, −X₃ᵀ)
= −card (Fin 2) · d(X₁, X₂, X₃)`: the multiplicity is the `sl₂` index, read
off the representation. -/
theorem su4_cubic_on_sixteen (X₁ X₂ X₃ : Matrix (Fin 4) (Fin 4) ℂ) :
    cubicTrace (su4Rep X₁) (su4Rep X₂) (su4Rep X₃) = 0 := by
  unfold su4Rep
  rw [cubicTrace_blockDiag, cubicTrace_kronecker_pure, cubicTrace_kronecker_pure,
    cubicTrace_neg_transpose]
  ring

/-! ## 4. The mixed anomalies, with `L` and `R` distinguished -/

/-- `EL`, carried to `ℂ`. -/
def ELc : Matrix PSIndex PSIndex ℂ := EL.map (algebraMap ℚ ℂ)

/-- `ER`, carried to `ℂ`. -/
def ERc : Matrix PSIndex PSIndex ℂ := ER.map (algebraMap ℚ ℂ)

theorem trace_e2c : trace ((e2.map (algebraMap ℚ ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [e2, Matrix.trace_fin_two]

theorem ELc_eq :
    ELc = fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ e2.map (algebraMap ℚ ℂ))
      0 0 0 := by
  unfold ELc EL
  rw [fromBlocks_map]
  congr 1
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [kroneckerMap_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  · simp
  · simp
  · simp

theorem ERc_eq :
    ERc = fromBlocks 0 0 0
      ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ e2.map (algebraMap ℚ ℂ)) := by
  unfold ERc ER
  rw [fromBlocks_map]
  congr 1
  · simp
  · simp
  · simp
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [kroneckerMap_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem cubicTrace_zero_right {k : Type*} [Fintype k] (T₁ T₂ : Matrix k k ℂ) :
    cubicTrace T₁ T₂ (0 : Matrix k k ℂ) = 0 := by
  unfold cubicTrace
  simp

/-- **`SU(4)²–SU(2)_L` vanishes on the 16**, with `EL` acting on the LEFT block only. -/
theorem su4_su4_su2L_on_sixteen (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    cubicTrace (su4Rep X) (su4Rep Y) ELc = 0 := by
  rw [ELc_eq]
  unfold su4Rep
  rw [cubicTrace_blockDiag, cubicTrace_zero_right, add_zero]
  exact mixed_cubic_kronecker_vanishes X Y _ trace_e2c

/-- **`SU(4)²–SU(2)_R` vanishes on the 16**, with `ER` acting on the RIGHT block only. -/
theorem su4_su4_su2R_on_sixteen (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    cubicTrace (su4Rep X) (su4Rep Y) ERc = 0 := by
  rw [ERc_eq]
  unfold su4Rep
  rw [cubicTrace_blockDiag, cubicTrace_zero_right, zero_add]
  exact mixed_cubic_kronecker_vanishes (-Xᵀ) (-Yᵀ) _ trace_e2c

/-! ## 5. Review round 76 — the ways this could be hollow

**"§3 is `pati_salam_anomaly_free` again."** It is the same cancellation, and
the difference is where the `2` and the `−` come from. There they are written
into the statement as the multiplicities of `4` and `4̄`; here they are
`Fintype.card (Fin 2)` and `cubicTrace_neg_transpose`, produced by evaluating
the cubic form on a representation that was DEFINED first. That is the
qualifier *as representation theory* on L16, answered for this term.

**"`su4Rep` is not a Mathlib representation."** It is a function with the
bracket law; the `LieHom` into `Module.End` is a packaging step this file does
not take, and the header says so. Nothing in §3–§4 would change under it.

**"§2 is trivial."** The block-diagonal additivity of the cubic form is four
lines, and it is the lemma that lets §3 and §4 be read off two Kronecker
lemmas each. It was not in the estate: `AnomalyTraces` works on a single
Kronecker block throughout, and `Matrix.trace_fromBlocks` is not in the pinned
Mathlib under that name. `BlockDiagonalSplit.trace_fromBlocks_diag` has the
trace half for `Fin`-indexed blocks; it does not apply to `PSIndex`.

**"The L/R separation is notational."** `ELc_eq` and `ERc_eq` are the
separation: the `sl₂_L` generator has its whole support in the left block and
`sl₂_R`'s in the right, as matrices, and the two mixed anomalies are then
computed on different blocks by `cubicTrace_blockDiag`. `ASSUMPTIONS_LEDGER`
31's *L/R collapsed* was about the statement `pati_salam_anomaly_free` makes
with one `su(2)` factor for both; this file has two.
-/

end

end SU4OnSixteen
