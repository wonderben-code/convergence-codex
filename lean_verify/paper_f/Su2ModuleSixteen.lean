/-
  Su2ModuleSixteen: the su(2)×su(2) Module Structure on the Chiral 16
  ====================================================================

  `WeinbergIndex` computes the Weinberg trace forms from DIAGONAL
  matrices, and its header names the honest gap: identifying those
  diagonals as the Cartan images of an actual su(4)⊕su(2)⊕su(2) action
  was "the standard unformalised identification, mapped on the
  watchlist". This file discharges the su(2)×su(2) part of that clause:
  the ladder operators exist as explicit 16×16 matrices, and the full
  commutation structure is proven — so T₃L and T₃R ARE the Cartan
  generators of two commuting sl₂-actions on the 16, with B−L central
  for both. The 16 decomposes visibly: the (4,2,1) block is four
  su(2)_L-doublets (1₄ ⊗ standard 2-dim rep), the (4̄,1,2) block is
  eight su(2)_L-singlets, and symmetrically for su(2)_R.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `EL`/`FL`/`ER`/`FR` — the raising/lowering operators as block
     matrices (Kronecker 1₄ ⊗ e, f on the respective block), and the
     bridges: `WeinbergIndex.T3L`, `Matrix.diagonal t3Rval`,
     `Matrix.diagonal blval` are EXACTLY the corresponding block
     matrices (`T3L_blocks`, `T3R_blocks`, `BL_blocks`).
  2. **The two sl₂ triples**: [E,F] = 2·T₃ and [T₃,E] = E, [T₃,F] = −F,
     on each side (`ladder_L_cartan`, `cartan_EL`, `cartan_FL`;
     `ladder_R_cartan`, `cartan_ER`, `cartan_FR`) — the defining
     relations of sl₂ in the spin-½ normalisation, as 16×16 matrix
     identities. Plus nilpotency E² = F² = 0 (the 2-dim rep signature).
  3. **The two sides commute — ALL 21 generator-pair brackets** (review
     round 9 completed the accounting): ladder-ladder cross-products
     vanish (`LR_commute`), each Cartan commutes with the opposite
     side's ladders (`cartanL_commutes_ER/FR`, `cartanR_commutes_EL/FL`),
     and the Cartans commute (`T3L_T3R_commute`).
  4. **B−L is central for ALL six generators**: the four ladders
     (`BL_central_EL` … `BL_central_FR`) and both Cartans
     (`BL_central_T3L`, `BL_central_T3R`) — B−L is colour data,
     constant on isospin doublets, exactly as Pati–Salam demands.
  5. `su2_su2_module_structure` — the package: both triples, the full
     cross-commutation, and full centrality in one statement; plus the
     bridge to MATHLIB'S OFFICIAL sl₂ API — `isSl2Triple_L`/`_R`
     instantiate `IsSl2Triple ((2:ℚ)•T₃) E F` in the commutator Lie
     ring, so the weight machinery of `Mathlib.Algebra.Lie.Sl2`
     applies. The decomposition reading is theorem-backed too:
     `EL_mulVec_down` (raising: down ↦ up), `EL_mulVec_up` (highest
     weight annihilated), `EL_mulVec_inr`/`T3L_mulVec_inr` (the eight
     right-block states are genuine su(2)_L singlets),
     `T3L_mulVec_up`/`T3L_mulVec_down` (eigenvalues ±½).

  NOT proven here: the su(4) (colour) action beyond its Cartan data —
  the B−L direction is the only su(4) generator these files use, and
  nothing about the full 15-dimensional colour action is claimed; the
  su(2) actions are on the RATIONAL 16 (the trace forms live over ℚ) —
  complexification is routine and not needed by any downstream claim.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import WeinbergIndex
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Lie.Sl2

open Matrix WeinbergIndex
open scoped Kronecker

noncomputable section

namespace Su2ModuleSixteen

/-! ## 1. The 2×2 building blocks -/

def e2 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]

def f2 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

def h2 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

theorem sl2_h : e2 * f2 - f2 * e2 = h2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e2, f2, h2, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_he : ((1 / 2 : ℚ) • h2) * e2 - e2 * ((1 / 2 : ℚ) • h2) = e2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e2, h2, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_hf : ((1 / 2 : ℚ) • h2) * f2 - f2 * ((1 / 2 : ℚ) • h2) = -f2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f2, h2, Matrix.mul_apply, Fin.sum_univ_two]

theorem e2_sq : e2 * e2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem f2_sq : f2 * f2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 2. The 16×16 operators and the bridges to WeinbergIndex -/

/-- su(2)_L raising: acts on the (4,2,1) block as 1₄ ⊗ e. -/
def EL : Matrix PSIndex PSIndex ℚ :=
  Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2) 0 0 0

/-- su(2)_L lowering. -/
def FL : Matrix PSIndex PSIndex ℚ :=
  Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2) 0 0 0

/-- su(2)_R raising: acts on the (4̄,1,2) block. -/
def ER : Matrix PSIndex PSIndex ℚ :=
  Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2)

/-- su(2)_R lowering. -/
def FR : Matrix PSIndex PSIndex ℚ :=
  Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2)

/-- The right Cartan and B−L, as the matrices WeinbergIndex uses. -/
def T3R : Matrix PSIndex PSIndex ℚ := Matrix.diagonal t3Rval

def BL : Matrix PSIndex PSIndex ℚ := Matrix.diagonal blval

-- The four bridge proofs chain `fin_cases` over branch-varying case
-- counts; the seq-focus linter flags the uniform `<;>` chain. Silenced
-- for the bridges only, re-enabled after.
set_option linter.unnecessarySeqFocus false

/-- WeinbergIndex's T₃L IS the block matrix 1₄ ⊗ (½h) on the left
    block. -/
theorem T3L_blocks : T3L
    = Matrix.fromBlocks
        ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ ((1 / 2 : ℚ) • h2)) 0 0 0 := by
  ext i j
  rcases i with ⟨c, s⟩ | ⟨c, s⟩ <;> rcases j with ⟨c', s'⟩ | ⟨c', s'⟩ <;>
    fin_cases s <;> fin_cases s' <;>
      simp [T3L, t3Lval, t3, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
        h2, Matrix.one_apply] <;>
    split_ifs <;> norm_num

theorem two_smul_T3L_blocks : (2 : ℚ) • T3L
    = Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ h2) 0 0 0 := by
  ext i j
  rcases i with ⟨c, s⟩ | ⟨c, s⟩ <;> rcases j with ⟨c', s'⟩ | ⟨c', s'⟩ <;>
    fin_cases s <;> fin_cases s' <;>
      simp [T3L, t3Lval, t3, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
        h2, Matrix.one_apply] <;>
    split_ifs <;> norm_num

theorem T3R_blocks : T3R
    = Matrix.fromBlocks 0 0 0
        ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ ((1 / 2 : ℚ) • h2)) := by
  ext i j
  rcases i with ⟨c, s⟩ | ⟨c, s⟩ <;> rcases j with ⟨c', s'⟩ | ⟨c', s'⟩ <;>
    fin_cases s <;> fin_cases s' <;>
      simp [T3R, t3Rval, t3, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
        h2, Matrix.one_apply] <;>
    split_ifs <;> norm_num

theorem two_smul_T3R_blocks : (2 : ℚ) • T3R
    = Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ h2) := by
  ext i j
  rcases i with ⟨c, s⟩ | ⟨c, s⟩ <;> rcases j with ⟨c', s'⟩ | ⟨c', s'⟩ <;>
    fin_cases s <;> fin_cases s' <;>
      simp [T3R, t3Rval, t3, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
        h2, Matrix.one_apply] <;>
    split_ifs <;> norm_num

/-- B−L is colour-diagonal tensor identity on each block (sign-flipped
    on the conjugate block). -/
theorem BL_blocks : BL
    = Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℚ))
        0 0 (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1) := by
  ext i j
  rcases i with ⟨c, s⟩ | ⟨c, s⟩ <;> rcases j with ⟨c', s'⟩ | ⟨c', s'⟩ <;>
    simp [BL, blval, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.ext_iff] <;>
    split_ifs <;> simp_all

set_option linter.unnecessarySeqFocus true

/-! ## 3. The generic block-commutator engine -/

/-- Upper-block commutators reduce to 2×2 commutators. -/
theorem upperBlock_comm (X Y Z : Matrix (Fin 2) (Fin 2) ℚ)
    (h : X * Y - Y * X = Z) :
    (Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0
          : Matrix PSIndex PSIndex ℚ)
        * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y) 0 0 0
      - Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y) 0 0 0
        * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0
      = Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Z) 0 0 0 := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  rcases i with p | p <;> rcases j with q | q
  · have hz := congr_fun (congr_fun h p.2) q.2
    simp only [Matrix.sub_apply] at hz
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.kroneckerMap_apply]
    linear_combination ((1 : Matrix (Fin 4) (Fin 4) ℚ) p.1 q.1) * hz
  · simp
  · simp
  · simp

/-- Lower-block commutators reduce to 2×2 commutators. -/
theorem lowerBlock_comm (X Y Z : Matrix (Fin 2) (Fin 2) ℚ)
    (h : X * Y - Y * X = Z) :
    (Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X)
          : Matrix PSIndex PSIndex ℚ)
        * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y)
      - Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y)
        * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X)
      = Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Z) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext i j
  rcases i with p | p <;> rcases j with q | q
  · simp
  · simp
  · simp
  · have hz := congr_fun (congr_fun h p.2) q.2
    simp only [Matrix.sub_apply] at hz
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.kroneckerMap_apply]
    linear_combination ((1 : Matrix (Fin 4) (Fin 4) ℚ) p.1 q.1) * hz

/-- Negation passes through the upper-block form. -/
theorem neg_upperBlock (X : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ (-X)) 0 0 0
          : Matrix PSIndex PSIndex ℚ)
      = -Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0 := by
  ext i j
  rcases i with p | p <;> rcases j with q | q <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.kroneckerMap_apply, mul_comm]

/-- Negation passes through the lower-block form. -/
theorem neg_lowerBlock (X : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ (-X))
          : Matrix PSIndex PSIndex ℚ)
      = -Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) := by
  ext i j
  rcases i with p | p <;> rcases j with q | q <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.kroneckerMap_apply, mul_comm]

/-! ## 4. The two sl₂ triples -/

/-- **[E_L, F_L] = 2·T₃L** — the sl₂ relation on the left. -/
theorem ladder_L_cartan : EL * FL - FL * EL = (2 : ℚ) • T3L := by
  rw [two_smul_T3L_blocks]
  exact upperBlock_comm e2 f2 h2 sl2_h

/-- **[T₃L, E_L] = E_L**. -/
theorem cartan_EL : T3L * EL - EL * T3L = EL := by
  rw [T3L_blocks]
  exact upperBlock_comm ((1 / 2 : ℚ) • h2) e2 e2 sl2_he

/-- **[T₃L, F_L] = −F_L**. -/
theorem cartan_FL : T3L * FL - FL * T3L = -FL := by
  rw [T3L_blocks, show -FL = Matrix.fromBlocks
    ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ (-f2)) 0 0 0 from (neg_upperBlock f2).symm]
  exact upperBlock_comm ((1 / 2 : ℚ) • h2) f2 (-f2) sl2_hf

/-- **[E_R, F_R] = 2·T₃R** — the sl₂ relation on the right. -/
theorem ladder_R_cartan : ER * FR - FR * ER = (2 : ℚ) • T3R := by
  rw [two_smul_T3R_blocks]
  exact lowerBlock_comm e2 f2 h2 sl2_h

/-- **[T₃R, E_R] = E_R**. -/
theorem cartan_ER : T3R * ER - ER * T3R = ER := by
  rw [T3R_blocks]
  exact lowerBlock_comm ((1 / 2 : ℚ) • h2) e2 e2 sl2_he

/-- **[T₃R, F_R] = −F_R**. -/
theorem cartan_FR : T3R * FR - FR * T3R = -FR := by
  rw [T3R_blocks, show -FR = Matrix.fromBlocks 0 0 0
    ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ (-f2)) from (neg_lowerBlock f2).symm]
  exact lowerBlock_comm ((1 / 2 : ℚ) • h2) f2 (-f2) sl2_hf

/-- Nilpotency: the 2-dim rep signature, E² = F² = 0 on both sides. -/
theorem EL_sq : EL * EL = 0 := by
  rw [EL, Matrix.fromBlocks_multiply]
  simp [← Matrix.mul_kronecker_mul, e2_sq]

theorem FL_sq : FL * FL = 0 := by
  rw [FL, Matrix.fromBlocks_multiply]
  simp [← Matrix.mul_kronecker_mul, f2_sq]

theorem ER_sq : ER * ER = 0 := by
  rw [ER, Matrix.fromBlocks_multiply]
  simp [← Matrix.mul_kronecker_mul, e2_sq]

theorem FR_sq : FR * FR = 0 := by
  rw [FR, Matrix.fromBlocks_multiply]
  simp [← Matrix.mul_kronecker_mul, f2_sq]

/-! ## 5. The two sides commute; B−L is central -/

/-- Any upper-block operator annihilates any lower-block operator. -/
theorem upper_mul_lower (X Y : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0
          : Matrix PSIndex PSIndex ℚ)
      * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y) = 0 := by
  rw [Matrix.fromBlocks_multiply]
  simp

theorem lower_mul_upper (X Y : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ Y)
          : Matrix PSIndex PSIndex ℚ)
      * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0 = 0 := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **The L and R actions commute** — every cross-commutator vanishes
    (indeed every cross-PRODUCT vanishes: block orthogonality). -/
theorem LR_commute : EL * ER - ER * EL = 0 ∧ EL * FR - FR * EL = 0
    ∧ FL * ER - ER * FL = 0 ∧ FL * FR - FR * FL = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [EL, FL, ER, FR] <;>
    rw [upper_mul_lower, lower_mul_upper] <;>
    simp

/-- Centrality engine: colour-diagonal ⊗ 1 commutes with 1 ⊗ X on the
    same block. -/
theorem central_upper (Dm : Matrix (Fin 4) (Fin 4) ℚ)
    (X : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks (Dm ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℚ)) 0 0 0
          : Matrix PSIndex PSIndex ℚ)
        * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0
      = Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X) 0 0 0
        * Matrix.fromBlocks (Dm ⊗ₖ 1) 0 0 0 := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem central_lower (Dm : Matrix (Fin 4) (Fin 4) ℚ)
    (X : Matrix (Fin 2) (Fin 2) ℚ) :
    (Matrix.fromBlocks 0 0 0 (Dm ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℚ))
          : Matrix PSIndex PSIndex ℚ)
        * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X)
      = Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ X)
        * Matrix.fromBlocks 0 0 0 (Dm ⊗ₖ 1) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- **B−L commutes with E_L** — and by the same engine with all four
    ladders: B−L is colour data, constant on isospin doublets. -/
theorem BL_central_EL : BL * EL = EL * BL := by
  rw [BL_blocks, EL]
  calc Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
        (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1)
      * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2) 0 0 0
      = Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ e2) 0 0 0 := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]
    _ = Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2) 0 0 0
        * Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
            (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]

theorem BL_central_FL : BL * FL = FL * BL := by
  rw [BL_blocks, FL]
  calc Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
        (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1)
      * Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2) 0 0 0
      = Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ f2) 0 0 0 := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]
    _ = Matrix.fromBlocks ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2) 0 0 0
        * Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
            (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]

theorem BL_central_ER : BL * ER = ER * BL := by
  rw [BL_blocks, ER]
  calc Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
        (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1)
      * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2)
      = Matrix.fromBlocks 0 0 0 (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ e2) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          zero_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]
    _ = Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ e2)
        * Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
            (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          zero_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]

theorem BL_central_FR : BL * FR = FR * BL := by
  rw [BL_blocks, FR]
  calc Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
        (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1)
      * Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2)
      = Matrix.fromBlocks 0 0 0 (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ f2) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          zero_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]
    _ = Matrix.fromBlocks 0 0 0 ((1 : Matrix (Fin 4) (Fin 4) ℚ) ⊗ₖ f2)
        * Matrix.fromBlocks (Matrix.diagonal b4 ⊗ₖ 1) 0 0
            (((-1 : ℚ) • Matrix.diagonal b4) ⊗ₖ 1) := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero,
          zero_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_one]

/-! ## 6. Review round 9: the remaining brackets, the Mathlib bridge,
and the decomposition made theorem-backed -/

theorem cartanL_commutes_ER : T3L * ER - ER * T3L = 0 := by
  rw [T3L_blocks, ER, upper_mul_lower, lower_mul_upper, sub_zero]

theorem cartanL_commutes_FR : T3L * FR - FR * T3L = 0 := by
  rw [T3L_blocks, FR, upper_mul_lower, lower_mul_upper, sub_zero]

theorem cartanR_commutes_EL : T3R * EL - EL * T3R = 0 := by
  rw [T3R_blocks, EL, lower_mul_upper, upper_mul_lower, sub_zero]

theorem cartanR_commutes_FL : T3R * FL - FL * T3R = 0 := by
  rw [T3R_blocks, FL, lower_mul_upper, upper_mul_lower, sub_zero]

theorem T3L_T3R_commute : T3L * T3R - T3R * T3L = 0 := by
  simp [T3L, T3R, Matrix.diagonal_mul_diagonal, mul_comm]

theorem BL_central_T3L : BL * T3L = T3L * BL := by
  simp [BL, T3L, Matrix.diagonal_mul_diagonal, mul_comm]

theorem BL_central_T3R : BL * T3R = T3R * BL := by
  simp [BL, T3R, Matrix.diagonal_mul_diagonal, mul_comm]

/-- **Mathlib's official sl₂ API, instantiated (left)**: the file's
    identities assemble into `IsSl2Triple` in the commutator Lie ring. -/
theorem isSl2Triple_L : IsSl2Triple ((2 : ℚ) • T3L) EL FL where
  h_ne_zero := by
    intro h
    have h00 := congrFun (congrFun h (Sum.inl (0, 0))) (Sum.inl (0, 0))
    simp [T3L, t3Lval, t3] at h00
  lie_e_f := by
    rw [Ring.lie_def]
    exact ladder_L_cartan
  lie_h_e_nsmul := by
    rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, cartan_EL,
      two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, cartan_FL,
      two_smul, two_smul]
    module

/-- **Mathlib's official sl₂ API, instantiated (right)**. -/
theorem isSl2Triple_R : IsSl2Triple ((2 : ℚ) • T3R) ER FR where
  h_ne_zero := by
    intro h
    have h00 := congrFun (congrFun h (Sum.inr (0, 0))) (Sum.inr (0, 0))
    simp [T3R, t3Rval, t3] at h00
  lie_e_f := by
    rw [Ring.lie_def]
    exact ladder_R_cartan
  lie_h_e_nsmul := by
    rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, cartan_ER,
      two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [Ring.lie_def, smul_mul_assoc, mul_smul_comm, ← smul_sub, cartan_FR,
      two_smul, two_smul]
    module

/-- Raising acts: E_L moves isospin-down to isospin-up, per colour. -/
theorem EL_mulVec_down (c : Fin 4) :
    EL.mulVec (Pi.single (Sum.inl (c, 1)) 1)
      = Pi.single (Sum.inl (c, 0)) 1 := by
  funext i
  rw [Matrix.mulVec_single]
  rcases i with ⟨c', s'⟩ | p
  · fin_cases s' <;>
      simp [EL, Matrix.fromBlocks_apply₁₁, Matrix.kroneckerMap_apply, e2,
        Matrix.one_apply, Pi.single_apply, Prod.ext_iff, eq_comm]
  · simp [EL, Matrix.fromBlocks_apply₂₁]

/-- The top of each doublet is annihilated: highest weight. -/
theorem EL_mulVec_up (c : Fin 4) :
    EL.mulVec (Pi.single (Sum.inl (c, 0)) 1) = 0 := by
  funext i
  rw [Matrix.mulVec_single]
  rcases i with ⟨c', s'⟩ | p
  · fin_cases s' <;>
      simp [EL, Matrix.fromBlocks_apply₁₁, Matrix.kroneckerMap_apply, e2,
        Matrix.one_apply]
  · simp [EL, Matrix.fromBlocks_apply₂₁]

/-- The eight right-block states are genuine su(2)_L singlets: E_L
    annihilates them. -/
theorem EL_mulVec_inr (p : Fin 4 × Fin 2) :
    EL.mulVec (Pi.single (Sum.inr p) 1) = 0 := by
  funext i
  rw [Matrix.mulVec_single]
  rcases i with q | q <;>
    simp [EL, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem T3L_mulVec_inr (p : Fin 4 × Fin 2) :
    T3L.mulVec (Pi.single (Sum.inr p) 1) = 0 := by
  funext i
  rw [Matrix.mulVec_single]
  simp [T3L, t3Lval]

/-- T₃L eigenvalue +½ on the up states. -/
theorem T3L_mulVec_up (c : Fin 4) :
    T3L.mulVec (Pi.single (Sum.inl (c, 0)) 1)
      = (1 / 2 : ℚ) • Pi.single (Sum.inl (c, 0)) 1 := by
  funext i
  rw [Matrix.mulVec_single]
  rcases i with ⟨c', s'⟩ | p <;>
    simp [T3L, t3Lval, t3, Pi.single_apply]

/-- T₃L eigenvalue −½ on the down states. -/
theorem T3L_mulVec_down (c : Fin 4) :
    T3L.mulVec (Pi.single (Sum.inl (c, 1)) 1)
      = (-(1 / 2) : ℚ) • Pi.single (Sum.inl (c, 1)) 1 := by
  funext i
  rw [Matrix.mulVec_single]
  rcases i with ⟨c', s'⟩ | p <;>
    simp [T3L, t3Lval, t3, Pi.single_apply]

/-! ## 7. The package -/

/-- **The su(2)×su(2) module structure on the chiral 16, complete**:
    two sl₂ triples with Cartans T₃L, T₃R; ALL cross-brackets zero
    (ladder-ladder, Cartan-ladder, Cartan-Cartan); B−L central for all
    six generators. Every pairwise bracket of the seven generators is
    now a literal conjunct — the `WeinbergIndex` diagonals are
    genuinely the Cartan data of a representation, not free-floating
    weights. -/
theorem su2_su2_module_structure :
    (EL * FL - FL * EL = (2 : ℚ) • T3L
        ∧ T3L * EL - EL * T3L = EL ∧ T3L * FL - FL * T3L = -FL)
      ∧ (ER * FR - FR * ER = (2 : ℚ) • T3R
        ∧ T3R * ER - ER * T3R = ER ∧ T3R * FR - FR * T3R = -FR)
      ∧ (EL * ER - ER * EL = 0 ∧ EL * FR - FR * EL = 0
        ∧ FL * ER - ER * FL = 0 ∧ FL * FR - FR * FL = 0)
      ∧ (T3L * ER - ER * T3L = 0 ∧ T3L * FR - FR * T3L = 0
        ∧ T3R * EL - EL * T3R = 0 ∧ T3R * FL - FL * T3R = 0
        ∧ T3L * T3R - T3R * T3L = 0)
      ∧ (BL * EL = EL * BL ∧ BL * FL = FL * BL
        ∧ BL * ER = ER * BL ∧ BL * FR = FR * BL
        ∧ BL * T3L = T3L * BL ∧ BL * T3R = T3R * BL) :=
  ⟨⟨ladder_L_cartan, cartan_EL, cartan_FL⟩,
    ⟨ladder_R_cartan, cartan_ER, cartan_FR⟩,
    LR_commute,
    ⟨cartanL_commutes_ER, cartanL_commutes_FR, cartanR_commutes_EL,
      cartanR_commutes_FL, T3L_T3R_commute⟩,
    ⟨BL_central_EL, BL_central_FL, BL_central_ER, BL_central_FR,
      BL_central_T3L, BL_central_T3R⟩⟩

end Su2ModuleSixteen
