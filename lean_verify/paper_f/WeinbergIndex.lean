/-
  WeinbergIndex: sin²θ_W = 3/8 as a Trace-Form Theorem — Gap N8
  ==============================================================

  The estate claims "sin²θ_W = 3/8 from Dynkin index ratio"
  (`F4_1_Foundations`), but its theorem proves only 0 < 3/8 < 1 plus
  dim su(2) = 3 and dim su(3) = 8 — no index, no trace, no
  representation (SPINE gap N8; the published PROVED tag is
  contradicted on exactly this point). This file supplies the missing
  computation, honestly framed. `SMEmbeddingHonest` proved the Standard
  Model algebra does NOT sit inside su(4) alone, so the frame here is
  the honest Pati–Salam one: gauge algebra su(4)⊕su(2)_L⊕su(2)_R,
  fermions in the CHIRAL 16 = (4,2,1) ⊕ (4̄,1,2), hypercharge
  Y = T₃R + (B−L)/2, electric charge Q = T₃L + Y, with B−L the
  diag(1/3,1/3,1/3,−1) direction — the estate's own `u1EmbedFn (1/3)`,
  proven so below. All generators are exact diagonal ℚ-matrices; every
  trace is exact rational arithmetic.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. The ANCHORS `charge_up/down/neutrino/electron/positron` plus
     `charge_antidown/antiup/antineutrino`: the charge operator Q
     assigns the physical charges (2/3, −1/3, 0, −1; conjugate block
     +1/3, −2/3, +1, 0) — every distinct charge value of the 16 is
     anchored (colour copies are identical by construction). The
     construction is the textbook one, not reverse-engineered.
  2. `trace_T3L_sq` = 2, `trace_T3R_sq` = 2, `trace_BL_sq` = 16/3,
     `trace_T3R_BL` = 0, `trace_T3L_Y` = 0, `trace_Y_sq` = 10/3,
     `trace_Q_sq` = 16/3 — the full second-order index inventory (trace
     forms) of the representation's diagonal directions, with BOTH
     orthogonalities proven, so Tr(Y²) = Tr(T₃R²) + ¼·Tr((B−L)²) is a
     theorem chain, not prose.
  3. **`sinSqThetaW_eq_three_eighths`** — Tr(T₃L²)/Tr(Q²) = 3/8, and
     **`coupling_ratio_three_fifths`** — Tr(T₃L²)/Tr(Y²) = 3/5 (the
     GUT-normalisation ratio g'²/g² = 3/5, i.e. g₁² = (5/3)g'²).
     PHYSICS BRIDGE, stated as prose and NOT formalised: at a
     unification scale where one invariant form normalises all
     generators, coupling matching gives g'²/g² = Tr(T₃²)/Tr(Y²) and
     hence sin²θ_W = g'²/(g²+g'²) = Tr(T₃²)/Tr(Q²) — the trace
     identities are the theorems; the matching argument is gauge
     theory, outside the estate. No claim about running, breaking, or
     the measured 0.231 is made.
  4. THE CONTROLS. `tensor_ratio_three_sevenths`: the SAME
     construction on the NON-chiral tensor cube (4,2,2) = ℂ⁴⊗ℂ²⊗ℂ² —
     the estate's own space, `F4_1_Foundations.tensor_decomp_dim` —
     gives Tr(T₃L²)/Tr(Q²) = 3/7 ≠ 3/8: same algebra, same dimensions
     3 and 8, different representation, different ratio, so the value
     is NOT a function of the dimensions and the agreement of 3/8 with
     "dim su(2)/dim su(3)" is a coincidence, refuted AS A MECHANISM
     (`weinberg_not_from_dimensions`). Scope, stated precisely: the
     controls certify REPRESENTATION-dependence; they do not isolate
     which single feature of the chiral 16 is responsible. The second
     control `mirror_ratio_three_eighths` — the split (4,2,1)⊕(4,1,2)
     with B−L UNCONJUGATED on the right block — still gives 3/8, so
     conjugation is not the operative difference either: among the
     computed weight systems, what separates 3/8 from 3/7 is the SPLIT
     structure (each state charged under exactly one su(2)) versus the
     cube (every state under both). The physical chiral 16 is a split
     form. This is the honest verdict on the estate's
     numerator/denominator story.
  5. `bl_eq_u1Embed` — the B−L direction used here IS the estate's
     embedding matrix: diagonal(1/3,1/3,1/3,−1) = `u1EmbedFn (1/3)`,
     tying the computation to `LieAlgebraEmbedding` as the spine route
     demanded ("trace forms on the embedded u(1) — computable with
     existing LieAlgebraEmbedding matrices").

  NOT proven here: gauge coupling unification (an assumption about
  physics, not mathematics — inside SO(10) it is automatic, and no
  SO(10) exists in the estate); renormalisation running; symmetry
  breaking; anything about the measured low-energy angle; the full
  su(4) colour action beyond its B−L direction. The su(2)×su(2) half of
  the module identification IS now formalised — `Su2ModuleSixteen`
  builds the ladder operators and proves both sl₂ triples, the
  commuting of the two sides, and the centrality of B−L, so the
  diagonals here are proven Cartan data of a genuine representation,
  not free-floating weights. The Dynkin indices of NON-abelian
  generators beyond the diagonal ones remain unformalised (for the
  diagonal/abelian directions used here, the trace form IS the index
  computation).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import LieAlgebraEmbedding
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix Module

noncomputable section

namespace WeinbergIndex

/-! ## 1. The chiral 16 and the generator directions -/

/-- The chiral fermion index: (4,2,1) ⊕ (4̄,1,2). Left block: colour ×
    weak isospin. Right block: anti-colour × right isospin. One
    generation, 16 states. -/
abbrev PSIndex := (Fin 4 × Fin 2) ⊕ (Fin 4 × Fin 2)

/-- The isospin-½ diagonal: (1/2, −1/2). -/
def t3 : Fin 2 → ℚ := fun i => if i.val = 0 then 1 / 2 else -(1 / 2)

/-- The B−L values on the Pati–Salam 4: quarks 1/3 (three colours),
    lepton −1. This is the diagonal of `u1EmbedFn (1/3)` — proven in
    `bl_eq_u1Embed`. -/
def b4 : Fin 4 → ℚ := fun c => if c.val < 3 then 1 / 3 else -1

theorem t3_zero : t3 0 = 1 / 2 := rfl
theorem t3_one : t3 1 = -(1 / 2) := rfl
theorem b4_zero : b4 0 = 1 / 3 := rfl
theorem b4_one : b4 1 = 1 / 3 := rfl
theorem b4_two : b4 2 = 1 / 3 := rfl
theorem b4_three : b4 3 = -1 := rfl

/-- T₃L: weak isospin, acting on the (4,2,1) block only. -/
def t3Lval : PSIndex → ℚ := Sum.elim (fun p => t3 p.2) (fun _ => 0)

/-- T₃R: right isospin, acting on the (4̄,1,2) block only. -/
def t3Rval : PSIndex → ℚ := Sum.elim (fun _ => 0) (fun p => t3 p.2)

/-- B−L on the chiral 16: b on the 4, −b on the 4̄ (conjugate). -/
def blval : PSIndex → ℚ := Sum.elim (fun p => b4 p.1) (fun p => -(b4 p.1))

/-- Hypercharge: Y = T₃R + (B−L)/2 — the Pati–Salam decomposition of
    the Standard Model hypercharge. -/
def yval : PSIndex → ℚ := fun s => t3Rval s + blval s / 2

/-- Electric charge: Q = T₃L + Y. -/
def qval : PSIndex → ℚ := fun s => t3Lval s + yval s

/-- The generators as diagonal matrices on the 16. -/
def T3L : Matrix PSIndex PSIndex ℚ := Matrix.diagonal t3Lval

def Y : Matrix PSIndex PSIndex ℚ := Matrix.diagonal yval

def Q : Matrix PSIndex PSIndex ℚ := Matrix.diagonal qval

/-! ## 2. The anchor: Q assigns the physical charges -/

/-- The up quark (colour 0, isospin up): Q = 1/2 + 0 + 1/6 = 2/3. -/
theorem charge_up : qval (Sum.inl (0, 0)) = 2 / 3 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The down quark: Q = −1/2 + 1/6 = −1/3. -/
theorem charge_down : qval (Sum.inl (0, 1)) = -(1 / 3) := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The neutrino (fourth colour, isospin up): Q = 1/2 − 1/2 = 0. -/
theorem charge_neutrino : qval (Sum.inl (3, 0)) = 0 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The electron: Q = −1/2 − 1/2 = −1. -/
theorem charge_electron : qval (Sum.inl (3, 1)) = -1 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The positron (conjugate block): Q = 1/2 + 1/2 = +1. -/
theorem charge_positron : qval (Sum.inr (3, 0)) = 1 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The conjugate down quark: Q = 1/2 − 1/6 = +1/3. -/
theorem charge_antidown : qval (Sum.inr (0, 0)) = 1 / 3 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The conjugate up quark: Q = −1/2 − 1/6 = −2/3. -/
theorem charge_antiup : qval (Sum.inr (0, 1)) = -(2 / 3) := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-- The conjugate neutrino: Q = −1/2 + 1/2 = 0. -/
theorem charge_antineutrino : qval (Sum.inr (3, 1)) = 0 := by
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_three]

/-! ## 3. The trace forms (second-order indices) of the chiral 16 -/

/-- The weak-isospin index: Tr(T₃L²) = 4 colours × (1/4 + 1/4) = 2. -/
theorem trace_T3L_sq : (T3L * T3L).trace = 2 := by
  rw [T3L, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [t3Lval, t3_zero, t3_one, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The right-isospin index: Tr(T₃R²) = 2 — equal to the left one, the
    g_L = g_R symmetry of the Pati–Salam frame in index form. -/
theorem trace_T3R_sq :
    (Matrix.diagonal t3Rval * Matrix.diagonal t3Rval).trace = 2 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [t3Rval, t3_zero, t3_one, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The B−L index: Tr((B−L)²) = 16/3. -/
theorem trace_BL_sq :
    (Matrix.diagonal blval * Matrix.diagonal blval).trace = 16 / 3 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [blval, b4_zero, b4_one, b4_two, b4_three, Fin.sum_univ_four,
    Fin.sum_univ_two]

/-- **T₃R ⊥ B−L**: the second orthogonality — with it, the chain
    Tr(Y²) = Tr(T₃R²) + ¼·Tr((B−L)²) = 2 + 4/3 = 10/3 is fully proven
    (`trace_T3R_sq`, `trace_BL_sq`, this, `trace_Y_sq`). -/
theorem trace_T3R_BL :
    (Matrix.diagonal t3Rval * Matrix.diagonal blval).trace = 0 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [t3Rval, blval, t3_zero, t3_one, b4_zero, b4_one, b4_two,
    b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The LITERAL decomposition (review round 8: links became one chain):
    Tr(Y²) = Tr(T₃R²) + Tr(T₃R·(B−L)) + ¼·Tr((B−L)²) as a single
    identity — with `trace_T3R_sq`, `trace_T3R_BL`, `trace_BL_sq` this
    derives `trace_Y_sq`'s 10/3 rather than merely being consistent
    with it. -/
theorem trace_Y_sq_decomposition :
    (Y * Y).trace
      = (Matrix.diagonal t3Rval * Matrix.diagonal t3Rval).trace
        + (Matrix.diagonal t3Rval * Matrix.diagonal blval).trace
        + (1 / 4 : ℚ) * (Matrix.diagonal blval * Matrix.diagonal blval).trace := by
  simp only [Y, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Fintype.sum_congr _ _ fun s => ?_
  simp only [yval]
  ring

/-- **T₃L ⊥ Y in the trace form**: the cross term vanishes, block by
    block — this is why Tr(Q²) = Tr(T₃L²) + Tr(Y²). -/
theorem trace_T3L_Y : (T3L * Y).trace = 0 := by
  rw [T3L, Y, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [t3Lval, t3Rval, blval, yval, t3_zero, t3_one, b4_zero, b4_one,
    b4_two, b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The hypercharge index: Tr(Y²) = 10/3 — the decomposition
    Tr(T₃R²) + ¼·Tr((B−L)²) = 2 + 4/3 with vanishing cross term is the
    proven chain `trace_T3R_sq` + `trace_BL_sq` + `trace_T3R_BL`. -/
theorem trace_Y_sq : (Y * Y).trace = 10 / 3 := by
  rw [Y, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [yval, t3Rval, blval, t3_zero, t3_one, b4_zero, b4_one, b4_two,
    b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-- The charge index: Tr(Q²) = 2 + 0 + 10/3 = 16/3. -/
theorem trace_Q_sq : (Q * Q).trace = 16 / 3 := by
  rw [Q, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [qval, yval, t3Lval, t3Rval, blval, t3_zero, t3_one, b4_zero,
    b4_one, b4_two, b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-! ## 4. The Weinberg ratio -/

/-- The group-theoretic Weinberg ratio of the representation:
    Tr(T₃L²)/Tr(Q²). Under coupling matching at a unification scale
    (one invariant form for all generators — prose bridge, see header)
    this ratio is sin²θ_W. The DEFINITION is representation data; the
    physics name is the bridge. -/
def sinSqThetaW : ℚ := (T3L * T3L).trace / (Q * Q).trace

/-- **THE WEINBERG ANGLE AT UNIFICATION (under the prose bridge of
    header item 3): Tr(T₃L²)/Tr(Q²) = 3/8** — an actual index ratio on
    an actual representation, not the dimension count
    dim su(2)/dim su(3) (see `weinberg_not_from_dimensions` for why
    that reading is refuted). -/
theorem sinSqThetaW_eq_three_eighths : sinSqThetaW = 3 / 8 := by
  rw [sinSqThetaW, trace_T3L_sq, trace_Q_sq]
  norm_num

/-- **The GUT normalisation: Tr(T₃L²)/Tr(Y²) = 3/5** — the matching
    ratio g'²/g² (under the prose bridge, header item 3), whence the
    conventional normalisation g₁² ≡ (5/3)·g'². -/
theorem coupling_ratio_three_fifths : (T3L * T3L).trace / (Y * Y).trace = 3 / 5 := by
  rw [trace_T3L_sq, trace_Y_sq]
  norm_num

/-! ## 5. The control: the non-chiral tensor cube gives 3/7, not 3/8 -/

/-- The estate's tensor cube (4,2,2) = ℂ⁴⊗ℂ²⊗ℂ²
    (`F4_1_Foundations.tensor_decomp_dim`), as an index type. NOT the
    fermion representation: both isospins act on the same 4, so B−L
    enters unconjugated. -/
abbrev TIndex := Fin 4 × Fin 2 × Fin 2

def t3LvalT : TIndex → ℚ := fun p => t3 p.2.1

def yvalT : TIndex → ℚ := fun p => t3 p.2.2 + b4 p.1 / 2

def qvalT : TIndex → ℚ := fun p => t3LvalT p + yvalT p

def T3Lt : Matrix TIndex TIndex ℚ := Matrix.diagonal t3LvalT

def Qt : Matrix TIndex TIndex ℚ := Matrix.diagonal qvalT

theorem trace_T3Lt_sq : (T3Lt * T3Lt).trace = 4 := by
  rw [T3Lt, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Fintype.sum_prod_type]
  norm_num [t3LvalT, t3_zero, t3_one, Fin.sum_univ_four, Fin.sum_univ_two]

theorem trace_Qt_sq : (Qt * Qt).trace = 28 / 3 := by
  rw [Qt, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Fintype.sum_prod_type]
  norm_num [qvalT, yvalT, t3LvalT, t3_zero, t3_one, b4_zero, b4_one, b4_two,
    b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **The control ratio: 3/7.** Same algebra, same construction,
    non-chiral representation — different answer. -/
theorem tensor_ratio_three_sevenths : (T3Lt * T3Lt).trace / (Qt * Qt).trace = 3 / 7 := by
  rw [trace_T3Lt_sq, trace_Qt_sq]
  norm_num

/-- **The dimension story is refuted as a mechanism**: dim su(2) = 3
    and dim su(3) = 8 (the estate's numerator and denominator) are
    representation-independent, yet the trace ratio is 3/8 on the
    chiral 16 and 3/7 on the tensor cube. The value is a property of
    the REPRESENTATION — the physical chiral 16 among them — not of the
    dimensions; the agreement with "dim su(2)/dim su(3)" is a
    coincidence, not a derivation. (For what the controls do and do not
    isolate, see `mirror_ratio_three_eighths`.) -/
theorem weinberg_not_from_dimensions :
    Module.finrank ℂ (TracelessMatrix 2) = 3
      ∧ Module.finrank ℂ (TracelessMatrix 3) = 8
      ∧ sinSqThetaW = 3 / 8
      ∧ (T3Lt * T3Lt).trace / (Qt * Qt).trace = 3 / 7
      ∧ (3 / 8 : ℚ) ≠ 3 / 7 :=
  ⟨traceless_dim_2, traceless_dim_3, sinSqThetaW_eq_three_eighths,
    tensor_ratio_three_sevenths, by norm_num⟩

/-- The mirror B−L: UNCONJUGATED on the right block. -/
def blvalM : PSIndex → ℚ := Sum.elim (fun p => b4 p.1) (fun p => b4 p.1)

def yvalM : PSIndex → ℚ := fun s => t3Rval s + blvalM s / 2

def qvalM : PSIndex → ℚ := fun s => t3Lval s + yvalM s

def QM : Matrix PSIndex PSIndex ℚ := Matrix.diagonal qvalM

theorem trace_QM_sq : (QM * QM).trace = 16 / 3 := by
  rw [QM, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  norm_num [qvalM, yvalM, t3Lval, t3Rval, blvalM, t3_zero, t3_one, b4_zero,
    b4_one, b4_two, b4_three, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **The mirror control: STILL 3/8.** Conjugating B−L on the right
    block does not move the ratio — so conjugation is not what
    separates 3/8 from the cube's 3/7; the split structure is. This
    delimits precisely what the controls do and do not isolate. -/
theorem mirror_ratio_three_eighths :
    (T3L * T3L).trace / (QM * QM).trace = 3 / 8 := by
  rw [trace_T3L_sq, trace_QM_sq]
  norm_num

/-! ## 6. The tie to the estate's embedding matrices -/

/-- **B−L here IS the estate's u(1) embedding matrix**:
    diagonal(1/3, 1/3, 1/3, −1) = `u1EmbedFn (1/3)`. The spine route
    ("trace forms computable with existing LieAlgebraEmbedding
    matrices") is honoured literally: the B−L INGREDIENT of the
    hypercharge is the matrix the estate built. This also CORRECTS the
    estate's label — `LieAlgebraEmbedding` calls `u1EmbedFn` "the
    U(1)_Y hypercharge direction inside sl₄(ℂ)"; it is the B−L
    direction, and hypercharge Y = T₃R + (B−L)/2 is NOT an sl₄ element
    (see `SMEmbeddingHonest`). -/
theorem bl_eq_u1Embed :
    (Matrix.diagonal fun c : Fin 4 => ((b4 c : ℚ) : ℂ)) = u1EmbedFn (1 / 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [u1EmbedFn, b4, Matrix.diagonal_apply]

end WeinbergIndex
