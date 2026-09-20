/-
# The Pati–Salam algebra on the chiral 16: the whole anomaly table vanishes on
# the representation, and the three trace forms coincide

**SPINE links L16 (anomaly cancellation) and L17 (Weinberg angle) — SPINE CAMPAIGN unit 5.**

`SU4OnSixteen` (this morning) put `sl₄` on the chiral 16 as `4 ⊕ 4̄` and evaluated the `SU(4)³`
and `SU(4)²–SU(2)_{L,R}` cubic traces ON THAT REPRESENTATION. Two things were still evaluated on
generator patterns rather than on the 16 (`SU(2)³` — `AnomalyTraces.su2_cubic_vanishes` is a
statement about `2 × 2` matrices), and the three factors were never put together as ONE action of
the product algebra. This file finishes the perturbative table.

## What is proved

1. **`su2LRep`, `su2RRep`, `psRep`** — `sl₂_L` on the left block as `1₄ ⊗ A`, `sl₂_R` on the
   right block as `1₄ ⊗ B`, and the Pati–Salam algebra `gl₄ × gl₂ × gl₂ ⊇ sl₄ × sl₂ × sl₂` on the
   16 as `psRep (X, A, B) := su4Rep X + su2LRep A + su2RRep B`. **`psRep_bracket`** — this is a
   Lie algebra action of the PRODUCT algebra: the three pieces are actions (`su4Rep_bracket`,
   `su2LRep_bracket`, `su2RRep_bracket`) and commute pairwise (`su4Rep_comm_su2LRep`,
   `su4Rep_comm_su2RRep`, `su2LRep_mul_su2RRep`, `su2RRep_mul_su2LRep`).
2. **`cubicTrace_add₁/₂/₃`** — the cubic form is trilinear (absent from `AnomalyTraces`, which
   never needed it); **`cubicTrace_one_kronecker`** — the right-factor multiplicity lemma, the
   mirror of `cubicTrace_kronecker_pure`; **`cubicTrace_kronecker_sum`** — on one Kronecker block
   the cubic form of three generators `T ⊗ 1 + 1 ⊗ S` of `gl_k × gl_m` with all six inputs
   traceless is `card m · d(T) + card k · d(S)`: every mixed term vanishes.
3. **`psRep_cubic_vanishes`** — **THE WHOLE CUBIC TABLE.** For every triple of Pati–Salam
   generators with traceless components, `d(psRep g₁, psRep g₂, psRep g₃) = 0`. The `SU(4)`
   contributions cancel between `4` and `4̄` (`+2·d(X)` from the left block, `−2·d(X)` from the
   right, `cubicTrace_neg_transpose`), the `SU(2)_L` and `SU(2)_R` contributions vanish by the
   pseudo-reality argument on the 16 (`4 · d(A) = 0`), and all `SU(4)²–SU(2)`, `SU(2)²–SU(4)`
   and cross-block terms vanish. **`psRep_trace_vanishes`** — every linear (gauge-gravitational)
   trace vanishes on the 16.
4. **`trace_su4Rep_mul`, `trace_su2LRep_mul`, `trace_su2RRep_mul`** — the trace forms of the 16
   restricted to the three factors are each `4 ×` the fundamental trace form: `Tr₁₆(ρX ρY) =
   4·Tr(XY)`, `Tr₁₆(ρA ρB) = 4·Tr(AB)`, `Tr₁₆(ρB ρB') = 4·Tr(BB')`. **`index_ratio_one`** — the
   `sl₄` and `sl₂_L` Dynkin indices on the 16 agree: with the fundamental normalisation
   `Tr(T_aT_b) = ½δ_ab` in both, both indices are `2`. L17's July text asked for "Dynkin indices
   of the embedding"; the abelian ones were computed 2 Aug (`WeinbergIndex`), these are the
   non-abelian ones.
5. **`sinSqThetaWPhys`, `weinberg_of_coupling_matching`** — the physics bridge as a NAMED
   hypothesis instead of prose: with `sin²θ_W := g'²/(g² + g'²)` and the coupling-matching
   hypothesis `g'²/g² = Tr(T₃L²)/Tr(Y²)` (one invariant form normalising every generator — the
   unified normalisation that Pati–Salam alone does not supply and `SO(10)` would), `sin²θ_W =
   3/8`. The hypothesis is `ASSUMPTIONS_LEDGER` entry 57. `WeinbergIndex.sinSqThetaW = 3/8` is a
   theorem about a named rational; this is a theorem about the angle UNDER a stated postulate.

## What is NOT proved, said exactly

- The Adler–Bell–Jackiw identification of the cubic trace with the triangle anomaly, and the
  Witten global `SU(2)` anomaly (`π₄(SU(2)) = ℤ/2`, no computed homotopy group in Mathlib) — as
  in `SU4OnSixteen` and `AnomalyTraces`; `ASSUMPTIONS_LEDGER` 31.
- That the fermion content is a CONSEQUENCE of the cascade: `PSIndex` with its two blocks is the
  input, and the chiral split is L12's postulate (`ASSUMPTIONS_LEDGER` 5, 34).
- Any group: `SU(4)`, `SU(2)`, `Spin(10)` exist nowhere in the estate. "Dynkin index" here means
  the trace form of the representation restricted to a factor, compared with the fundamental's.
  ⚠ 20 September 2026 (hardening unit 188, `paper_f/SkewAdjointExponential.lean`): `SU(4)` and
  `SU(2)` now exist as Mathlib's `specialUnitaryGroup (Fin 4) ℂ` and `(Fin 2) ℂ`, reached from the
  estate's `su(4) ⊕ su(2) ⊕ su(2)` by `expFull`; `Spin(10)` still exists nowhere. No group acts on
  the 16 here — `psRep` is still a Lie-algebra representation. The bullet is kept as written
  (`ERRATUM 94`).
- The coupling-matching hypothesis itself. `weinberg_of_coupling_matching` takes it; nothing
  derives it. Without an `SO(10)`-type completion it is a modelling assumption, and it is recorded
  as one.
- `LieModule` packaging of `psRep` (one definition away, unconsumed, as in `SU4OnSixteen`).

## Adversarial review, folded in

**"The cubic table is a finite computation dressed as a theorem."** It is a theorem about ALL
traceless generators, quantified, not a table of numbers — `psRep_cubic_vanishes` has six matrix
variables and six trace hypotheses. Its proof is the block decomposition (`cubicTrace_blockDiag`)
plus the one-block expansion (`cubicTrace_kronecker_sum`), which is where the multiplicities `2`
and `4` come from `Fintype.card`, not from a literal.

**"`index_ratio_one` is a tautology once the trace forms are `4×`."** Yes: that is the content.
Equal indices on the 16 is the representation-theoretic fact that makes "one invariant form"
consistent; it does not supply the physics matching, which stays a hypothesis.

**"Why `gl` and not `sl`?"** The representation is defined on all of `gl₄ × gl₂ × gl₂` (the
formulas make sense there) and the anomaly statements assume tracelessness where they need it;
the `sl` restriction is a hypothesis on each theorem, not a subtype, exactly as in `AnomalyTraces`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SU4OnSixteen

namespace PatiSalamOnSixteen

open Matrix WeinbergIndex AnomalyTraces Su2ModuleSixteen SU4OnSixteen
open scoped Kronecker

noncomputable section

/-! ## 1. The three factors on the 16, and the product action -/

/-- `sl₂_L` on the 16: `1₄ ⊗ A` on the left-handed block, nothing on the right. -/
def su2LRep (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix PSIndex PSIndex ℂ :=
  fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ A) 0 0 0

/-- `sl₂_R` on the 16: `1₄ ⊗ B` on the right-handed block, nothing on the left. -/
def su2RRep (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix PSIndex PSIndex ℂ :=
  fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ B)

/-- **THE PATI–SALAM ALGEBRA ON THE 16**: `(X, A, B) ↦ su4Rep X + su2LRep A + su2RRep B`. -/
def psRep (g : Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix PSIndex PSIndex ℂ :=
  su4Rep g.1 + su2LRep g.2.1 + su2RRep g.2.2

theorem one_kronecker_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ (A - B) = 1 ⊗ₖ A - 1 ⊗ₖ B := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [kroneckerMap_apply, mul_sub]

theorem su2LRep_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2LRep A * su2LRep B = su2LRep (A * B) := by
  unfold su2LRep
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [← mul_kronecker_mul, Matrix.one_mul]

theorem su2RRep_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2RRep A * su2RRep B = su2RRep (A * B) := by
  unfold su2RRep
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add]
  rw [← mul_kronecker_mul, Matrix.one_mul]

/-- `sl₂_L` acts. -/
theorem su2LRep_bracket (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2LRep (A * B - B * A) = su2LRep A * su2LRep B - su2LRep B * su2LRep A := by
  rw [su2LRep_mul, su2LRep_mul]
  unfold su2LRep
  rw [fromBlocks_sub', one_kronecker_sub, sub_zero]

/-- `sl₂_R` acts. -/
theorem su2RRep_bracket (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2RRep (A * B - B * A) = su2RRep A * su2RRep B - su2RRep B * su2RRep A := by
  rw [su2RRep_mul, su2RRep_mul]
  unfold su2RRep
  rw [fromBlocks_sub', one_kronecker_sub, sub_zero]

/-- The `sl₄` and `sl₂_L` actions commute. -/
theorem su4Rep_comm_su2LRep (X : Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    su4Rep X * su2LRep A = su2LRep A * su4Rep X := by
  unfold su4Rep su2LRep
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- The `sl₄` and `sl₂_R` actions commute. -/
theorem su4Rep_comm_su2RRep (X : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    su4Rep X * su2RRep B = su2RRep B * su4Rep X := by
  unfold su4Rep su2RRep
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- The two `sl₂` actions live on different blocks: their products vanish. -/
theorem su2LRep_mul_su2RRep (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2LRep A * su2RRep B = 0 := by
  unfold su2LRep su2RRep
  rw [fromBlocks_multiply]
  simp

theorem su2RRep_mul_su2LRep (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    su2RRep B * su2LRep A = 0 := by
  unfold su2LRep su2RRep
  rw [fromBlocks_multiply]
  simp

/-- **A LIE ALGEBRA ACTION OF THE PRODUCT.** The bracket of the product algebra
`gl₄ × gl₂ × gl₂` is componentwise; `psRep` carries it to the commutator on the 16. -/
theorem psRep_bracket (X Y : Matrix (Fin 4) (Fin 4) ℂ) (A A' B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    psRep (X * Y - Y * X, A * A' - A' * A, B * B' - B' * B)
      = psRep (X, A, B) * psRep (Y, A', B') - psRep (Y, A', B') * psRep (X, A, B) := by
  unfold psRep
  simp only
  rw [su4Rep_bracket, su2LRep_bracket, su2RRep_bracket]
  simp only [add_mul, mul_add, su4Rep_comm_su2LRep, su4Rep_comm_su2RRep,
    su2LRep_mul_su2RRep, su2RRep_mul_su2LRep, add_zero]
  abel

/-! ## 2. Trilinearity of the cubic form, and the one-block expansion -/

section Trilinear

variable {k : Type*} [Fintype k]

theorem cubicTrace_add₁ (T T' T₂ T₃ : Matrix k k ℂ) :
    cubicTrace (T + T') T₂ T₃ = cubicTrace T T₂ T₃ + cubicTrace T' T₂ T₃ := by
  unfold cubicTrace
  simp only [Matrix.add_mul, trace_add]

theorem cubicTrace_add₂ (T₁ T T' T₃ : Matrix k k ℂ) :
    cubicTrace T₁ (T + T') T₃ = cubicTrace T₁ T T₃ + cubicTrace T₁ T' T₃ := by
  unfold cubicTrace
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add]
  abel

theorem cubicTrace_add₃ (T₁ T₂ T T' : Matrix k k ℂ) :
    cubicTrace T₁ T₂ (T + T') = cubicTrace T₁ T₂ T + cubicTrace T₁ T₂ T' := by
  unfold cubicTrace
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add]
  abel

/-- The mirror of `cubicTrace_kronecker_pure`: three SECOND-factor generators pick up the
first factor's dimension. -/
theorem cubicTrace_one_kronecker {m : Type*} [Fintype m] [DecidableEq k]
    (S₁ S₂ S₃ : Matrix m m ℂ) :
    cubicTrace ((1 : Matrix k k ℂ) ⊗ₖ S₁) (1 ⊗ₖ S₂) (1 ⊗ₖ S₃)
      = (Fintype.card k : ℂ) * cubicTrace S₁ S₂ S₃ := by
  unfold cubicTrace
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, ← kronecker_add,
    ← mul_kronecker_mul, Matrix.one_mul, trace_kronecker, trace_one]

/-- **ON ONE KRONECKER BLOCK.** For generators `T ⊗ 1 + 1 ⊗ S` of `gl_k × gl_m` with every
component traceless, the cubic form is `card m · d(T) + card k · d(S)`: all six mixed terms
vanish (`mixed_cubic_kronecker_vanishes`, `_left`, and their permutations). -/
theorem cubicTrace_kronecker_sum {m : Type*} [Fintype m] [DecidableEq k] [DecidableEq m]
    (T₁ T₂ T₃ : Matrix k k ℂ) (S₁ S₂ S₃ : Matrix m m ℂ)
    (hT₁ : trace T₁ = 0) (hT₂ : trace T₂ = 0) (hT₃ : trace T₃ = 0)
    (hS₁ : trace S₁ = 0) (hS₂ : trace S₂ = 0) (hS₃ : trace S₃ = 0) :
    cubicTrace (T₁ ⊗ₖ (1 : Matrix m m ℂ) + (1 : Matrix k k ℂ) ⊗ₖ S₁)
        (T₂ ⊗ₖ 1 + 1 ⊗ₖ S₂) (T₃ ⊗ₖ 1 + 1 ⊗ₖ S₃)
      = (Fintype.card m : ℂ) * cubicTrace T₁ T₂ T₃
        + (Fintype.card k : ℂ) * cubicTrace S₁ S₂ S₃ := by
  -- the eight terms of the trilinear expansion
  rw [cubicTrace_add₁, cubicTrace_add₂, cubicTrace_add₂, cubicTrace_add₃, cubicTrace_add₃,
    cubicTrace_add₃, cubicTrace_add₃]
  -- pure terms
  rw [cubicTrace_kronecker_pure, cubicTrace_one_kronecker]
  -- two first-factor, one second-factor
  have h12 : ∀ (T T' : Matrix k k ℂ) (S : Matrix m m ℂ), trace S = 0 →
      cubicTrace (T ⊗ₖ (1 : Matrix m m ℂ)) ((1 : Matrix k k ℂ) ⊗ₖ S) (T' ⊗ₖ 1) = 0 := by
    intro T T' S hS
    rw [cubicTrace_swap₂₃]
    exact mixed_cubic_kronecker_vanishes T T' S hS
  have h21 : ∀ (T T' : Matrix k k ℂ) (S : Matrix m m ℂ), trace S = 0 →
      cubicTrace ((1 : Matrix k k ℂ) ⊗ₖ S) (T ⊗ₖ (1 : Matrix m m ℂ)) (T' ⊗ₖ 1) = 0 := by
    intro T T' S hS
    rw [cubicTrace_swap₁₂, cubicTrace_swap₂₃]
    exact mixed_cubic_kronecker_vanishes T T' S hS
  -- one first-factor, two second-factor
  have h12' : ∀ (T : Matrix k k ℂ) (S S' : Matrix m m ℂ), trace T = 0 →
      cubicTrace ((1 : Matrix k k ℂ) ⊗ₖ S) (T ⊗ₖ (1 : Matrix m m ℂ)) (1 ⊗ₖ S') = 0 := by
    intro T S S' hT
    rw [cubicTrace_swap₁₂]
    exact mixed_cubic_kronecker_vanishes_left T S S' hT
  have h21' : ∀ (T : Matrix k k ℂ) (S S' : Matrix m m ℂ), trace T = 0 →
      cubicTrace ((1 : Matrix k k ℂ) ⊗ₖ S) (1 ⊗ₖ S') (T ⊗ₖ (1 : Matrix m m ℂ)) = 0 := by
    intro T S S' hT
    rw [cubicTrace_swap₂₃, cubicTrace_swap₁₂]
    exact mixed_cubic_kronecker_vanishes_left T S S' hT
  rw [mixed_cubic_kronecker_vanishes T₁ T₂ S₃ hS₃, h12 T₁ T₃ S₂ hS₂, h21 T₂ T₃ S₁ hS₁,
    mixed_cubic_kronecker_vanishes_left T₁ S₂ S₃ hT₁, h12' T₂ S₁ S₃ hT₂, h21' T₃ S₁ S₂ hT₃]
  ring

end Trilinear

/-! ## 3. The whole cubic table, and the linear traces, on the 16 -/

/-- `psRep` is block-diagonal, with the `(4,2)` generator on the left and the `(4̄,2)` generator
on the right. -/
theorem psRep_eq (X : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    psRep (X, A, B)
      = fromBlocks (X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ A)
          0 0 ((-Xᵀ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ B) := by
  unfold psRep su4Rep su2LRep su2RRep
  rw [fromBlocks_add, fromBlocks_add]
  simp only [add_zero]

theorem trace_neg_transpose (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : trace X = 0) :
    trace (-Xᵀ) = 0 := by
  rw [trace_neg, trace_transpose, hX, neg_zero]

/-- **THE WHOLE CUBIC ANOMALY TABLE VANISHES ON THE 16.** For any three Pati–Salam generators
with traceless components — every `SU(4)³`, `SU(2)_L³`, `SU(2)_R³`, `SU(4)²–SU(2)`,
`SU(2)²–SU(4)`, `SU(2)_L²–SU(2)_R` and `SU(4)–SU(2)_L–SU(2)_R` combination at once, and every
mixture — the cubic trace of the representation is zero. -/
theorem psRep_cubic_vanishes (X₁ X₂ X₃ : Matrix (Fin 4) (Fin 4) ℂ)
    (A₁ A₂ A₃ B₁ B₂ B₃ : Matrix (Fin 2) (Fin 2) ℂ)
    (hX₁ : trace X₁ = 0) (hX₂ : trace X₂ = 0) (hX₃ : trace X₃ = 0)
    (hA₁ : trace A₁ = 0) (hA₂ : trace A₂ = 0) (hA₃ : trace A₃ = 0)
    (hB₁ : trace B₁ = 0) (hB₂ : trace B₂ = 0) (hB₃ : trace B₃ = 0) :
    cubicTrace (psRep (X₁, A₁, B₁)) (psRep (X₂, A₂, B₂)) (psRep (X₃, A₃, B₃)) = 0 := by
  rw [psRep_eq, psRep_eq, psRep_eq, cubicTrace_blockDiag,
    cubicTrace_kronecker_sum X₁ X₂ X₃ A₁ A₂ A₃ hX₁ hX₂ hX₃ hA₁ hA₂ hA₃,
    cubicTrace_kronecker_sum (-X₁ᵀ) (-X₂ᵀ) (-X₃ᵀ) B₁ B₂ B₃ (trace_neg_transpose X₁ hX₁)
      (trace_neg_transpose X₂ hX₂) (trace_neg_transpose X₃ hX₃) hB₁ hB₂ hB₃,
    cubicTrace_neg_transpose, su2_cubic_vanishes A₁ A₂ A₃ hA₁ hA₂ hA₃,
    su2_cubic_vanishes B₁ B₂ B₃ hB₁ hB₂ hB₃]
  ring

/-- **EVERY LINEAR (GAUGE-GRAVITATIONAL) TRACE VANISHES ON THE 16.** -/
theorem psRep_trace_vanishes (X : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : trace X = 0) (hA : trace A = 0) (hB : trace B = 0) :
    trace (psRep (X, A, B)) = 0 := by
  rw [psRep_eq, trace_fromBlocks_any, trace_add, trace_add, trace_kronecker, trace_kronecker,
    trace_kronecker, trace_kronecker, hX, hA, hB, trace_neg_transpose X hX]
  ring

/-! ## 4. The trace forms of the 16 on the three factors: equal Dynkin indices -/

/-- `Tr₁₆(ρX · ρY) = 4 · Tr(XY)`: the `4` and the `4̄` each contribute `2 · Tr(XY)`. -/
theorem trace_su4Rep_mul (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    trace (su4Rep X * su4Rep Y) = 4 * trace (X * Y) := by
  rw [su4Rep_mul, trace_fromBlocks_any, trace_kronecker, trace_kronecker, trace_one,
    ← transpose_mul, trace_transpose, trace_mul_comm Y X]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- `Tr₁₆(ρA · ρB) = 4 · Tr(AB)` for `sl₂_L`. -/
theorem trace_su2LRep_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2LRep A * su2LRep B) = 4 * trace (A * B) := by
  rw [su2LRep_mul]
  unfold su2LRep
  rw [trace_fromBlocks_any, trace_kronecker, trace_one, trace_zero]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- `Tr₁₆(ρB · ρB') = 4 · Tr(BB')` for `sl₂_R`. -/
theorem trace_su2RRep_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (su2RRep A * su2RRep B) = 4 * trace (A * B) := by
  rw [su2RRep_mul]
  unfold su2RRep
  rw [trace_fromBlocks_any, trace_kronecker, trace_one, trace_zero]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- **EQUAL DYNKIN INDICES.** The index of a factor on the 16 is the constant `c` with
`Tr₁₆(ρT ρT') = c · Tr_fund(T T')`; it is `4` for `sl₄`, for `sl₂_L` and for `sl₂_R` alike, so
the ratio of any two is `1`. This is the representation-theoretic half of "one invariant form
normalises every generator"; the other half is a hypothesis (§5). -/
theorem index_ratio_one (X Y : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hXY : trace (X * Y) ≠ 0) (hAB : trace (A * B) ≠ 0) :
    trace (su4Rep X * su4Rep Y) / trace (X * Y)
      = trace (su2LRep A * su2LRep B) / trace (A * B) := by
  rw [trace_su4Rep_mul, trace_su2LRep_mul, mul_div_assoc, mul_div_assoc, div_self hXY,
    div_self hAB]

/-! ## 5. The physics bridge as a named hypothesis — over `ℝ`, because over `ℚ` it is empty

**`ERRATUM 557`.** This section first stated the bridge over `ℚ`, and two of the recompute's
refuters independently machine-checked that the hypothesis has NO rational solutions: it demands
`g'²/g² = 3/5`, and `3/5` is not the square of a rational. The theorem was therefore vacuously
true and said nothing about any coupling pair. It is kept below as
`weinberg_of_coupling_matching_rat` (`ERRATUM 94`: the statement is not deleted), the
impossibility is proved beside it as
`no_rat_coupling_matching`, and the bridge is restated over `ℝ` where the hypothesis is
**inhabited** — `coupling_matching_inhabited` exhibits the witness. -/

/-- `sin²θ_W` in terms of the two couplings, the textbook definition, over `ℝ`. -/
noncomputable def sinSqThetaWReal (g g' : ℝ) : ℝ := g' ^ 2 / (g ^ 2 + g' ^ 2)

/-- The rational version, kept for the record. See `ERRATUM 557`: its hypothesis class is empty. -/
def sinSqThetaWPhys (g g' : ℚ) : ℚ := g' ^ 2 / (g ^ 2 + g' ^ 2)

/-- **THE WEINBERG ANGLE UNDER COUPLING MATCHING, OVER `ℝ`.** If the couplings are normalised by
one invariant form on the chiral 16 — `g'² = (Tr(T₃L²)/Tr(Y²)) · g²`, which is
`ASSUMPTIONS_LEDGER` 57 — then `sin²θ_W = 3/8`. The hypothesis is the whole of the physics; the
arithmetic is `WeinbergIndex.trace_T3L_sq` and `trace_Y_sq`, and `coupling_matching_inhabited`
below shows the hypothesis is satisfiable, which over `ℚ` it is not. -/
theorem weinberg_of_coupling_matching_real (g g' : ℝ) (hg : g ≠ 0)
    (hmatch : g' ^ 2 = ((T3L * T3L).trace / (Y * Y).trace : ℚ) * g ^ 2) :
    sinSqThetaWReal g g' = 3 / 8 := by
  rw [trace_T3L_sq, trace_Y_sq] at hmatch
  norm_num at hmatch
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  unfold sinSqThetaWReal
  rw [hmatch]
  have hden : g ^ 2 + 3 / 5 * g ^ 2 = 8 / 5 * g ^ 2 := by ring
  rw [hden, div_eq_iff (by
    exact mul_ne_zero (by norm_num) hg2)]
  ring

/-- **THE HYPOTHESIS IS INHABITED.** With `g = 1` and `g' = √(3/5)` the matching holds, so
`weinberg_of_coupling_matching_real` is not vacuous. This is the check the `ℚ` version lacked. -/
theorem coupling_matching_inhabited :
    ∃ g g' : ℝ, g ≠ 0 ∧
      g' ^ 2 = ((T3L * T3L).trace / (Y * Y).trace : ℚ) * g ^ 2 := by
  refine ⟨1, Real.sqrt (3 / 5), one_ne_zero, ?_⟩
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3 / 5), trace_T3L_sq, trace_Y_sq]
  norm_num

/-- **AND OVER `ℚ` IT IS EMPTY — the finding that forced `ERRATUM 557`.** No pair of rationals
satisfies the matching, because `Tr(T₃L²)/Tr(Y²) = 3/5` is not the square of a rational: if
`g'² = (3/5)g²` then `(5g'/g)² = 15`, and `15` is not a rational square
(`Nat.Prime.irrational_sqrt` on `3`, through `Irrational`). -/
theorem no_rat_coupling_matching :
    ¬ ∃ g g' : ℚ, g ≠ 0 ∧ g' ^ 2 / g ^ 2 = (T3L * T3L).trace / (Y * Y).trace := by
  rintro ⟨g, g', hg, hmatch⟩
  rw [trace_T3L_sq, trace_Y_sq] at hmatch
  have hg2 : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  -- the matching makes `15` a square in `ℚ`, with witness `5 g' / g`
  have hsq : IsSquare (15 : ℚ) := by
    refine ⟨5 * g' / g, ?_⟩
    field_simp at hmatch ⊢
    linarith
  -- and `15` is not a square in `ℕ`, hence not in `ℚ`
  have h15 : ¬ IsSquare (15 : ℕ) := by
    rintro ⟨r, hr⟩
    have hr4 : r < 4 := by nlinarith
    interval_cases r <;> omega
  rw [show ((15 : ℚ)) = ((15 : ℕ) : ℚ) by norm_num,
    Rat.isSquare_natCast_iff] at hsq
  exact h15 hsq

/-- The rational statement, KEPT as first written (`ERRATUM 94`) beside the theorem that shows its
hypothesis class is empty. It is true, and it is true vacuously. -/
theorem weinberg_of_coupling_matching_rat (g g' : ℚ) (hg : g ≠ 0)
    (hmatch : g' ^ 2 / g ^ 2 = (T3L * T3L).trace / (Y * Y).trace) :
    sinSqThetaWPhys g g' = 3 / 8 :=
  absurd ⟨g, g', hg, hmatch⟩ no_rat_coupling_matching

end

end PatiSalamOnSixteen
