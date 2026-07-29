/-
  HiggsBridge: The Algebraic Bridge of the Chamseddine–Connes Higgs Sector
  ========================================================================

  The algebraic half of the Higgs-mass gap (tree §6.8, old gap #11; spine
  L15). What existed: F3_2_HiggsForced does representation counting; the
  actual C–C machinery (trace functionals of the Yukawa matrix, the
  boundary condition on the quartic coupling, m_H² = 2λv²) appeared only in
  docstrings. This file formalises the algebraic skeleton.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  For a Yukawa matrix Y over ℂ on any finite fermion index type (the
  cascade case is n = 96), with P := Yᴴ·Y and the C–C trace functionals
  a := Tr(P), b := Tr(P·P):

  1. `traceP_nonneg`, `traceP_sq_nonneg` — a ≥ 0 and b ≥ 0 in the complex
     order: both functionals are genuinely nonnegative (P is PSD; P·P = Pᴴ·P
     is PSD since P is Hermitian).
  2. `diag_re_nonneg`, `re_trace_eq_sum`, `re_tracePP_eq_sum` — the real
     bookkeeping AS NAMED THEOREMS: a and b are real sums; diagonal
     entries of P are real nonnegative.
  3. `trace_sq_le_card_mul_trace_sq` — **the Cauchy–Schwarz/Chebyshev
     bound**: (Tr P)² ≤ N·Tr(P·P) (real parts), proven via
     `sq_sum_le_card_mul_sum_sq` plus the entrywise identity
     (P·P)ᵢᵢ = Σⱼ |Pᵢⱼ|² ≥ (Pᵢᵢ)².
  4. `ccLambda_lower_bound` — the C–C boundary coupling λ̃(Λ) := g²·b/a²
     (CCM 2007 §5.2 eq (5.6); the g there is g₃, defensible at
     unification) satisfies **λ̃(Λ) ≥ g²/N** whenever a = Tr(P) ≠ 0 — and
     `traceP_re_ne_zero_of_ne_zero` proves that condition is implied by
     Y ≠ 0, so the bound genuinely holds for every nonzero Yukawa matrix.
     (Cascade N = 96: λ̃ ≥ g²/96 — `cascade_ccLambda_lower`.)
  5. `higgsMassSq_transfer` — NORMALISATION per CCM: the SM quartic is
     λ = 4λ̃ (CCM §5.2), and the tree-level mass relation is
     m_H² = 2λv² = 8λ̃v² (CCM eq (5.15)); `higgsMassSq` encodes 8λ̃v²
     accordingly, and the bound transfers: m_H² ≥ 8(g²/N)v². NOTE: the
     mass relation itself is DEFINITIONAL here (deriving m_H² = 2λv² from
     a Higgs potential is not formalised — listed in NOT-proven), and the
     transfer is monotonicity, nothing deeper.

  NOT proven here (named stairs, so the [CLAIMED] tag stays honest):
  the tree-level relation m_H² = 2λv² itself (definitional here; its
  derivation from the Higgs potential is standard but unformalised);
  the UPPER bound b ≤ a² (the Schur/minor trace inequality
  Tr(P²) ≤ (Tr P)² for PSD P — needs the 2×2-minor entry bound; next
  stair, would give λ ≤ g² and the upper mass bound); the spectral-action
  DERIVATION of the boundary condition λ(Λ) = g²·b/a² itself (here λ(Λ)
  is a definition, its C–C origin cited: Chamseddine–Connes 2007, §5);
  the RG running from Λ to the electroweak scale producing ≈125 GeV
  (verified-numerics ODE integration — out of Lean's current reach,
  cited). The 125 GeV number is NEVER claimed as proven content.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.StarOrdered

open Matrix
open scoped ComplexOrder

noncomputable section

namespace HiggsBridge

variable {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ)

/-- The squared Yukawa matrix P = Yᴴ·Y — Hermitian and PSD. -/
def P : Matrix (Fin n) (Fin n) ℂ := Yᴴ * Y

theorem P_posSemidef : (P Y).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self Y

theorem P_hermitian : (P Y)ᴴ = P Y :=
  (P_posSemidef Y).1

/-- a = Tr(P) ≥ 0 in the complex order. -/
theorem traceP_nonneg : 0 ≤ trace (P Y) :=
  (P_posSemidef Y).trace_nonneg

/-- P·P is PSD (it is Pᴴ·P for Hermitian P), hence b = Tr(P·P) ≥ 0. -/
theorem PP_posSemidef : ((P Y) * (P Y)).PosSemidef := by
  have h : (P Y) * (P Y) = (P Y)ᴴ * (P Y) := by rw [P_hermitian]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self (P Y)

theorem traceP_sq_nonneg : 0 ≤ trace ((P Y) * (P Y)) :=
  (PP_posSemidef Y).trace_nonneg

/-! ## 2. Real bookkeeping -/

/-- Off-diagonal pairing: for Hermitian P, P j i = conj (P i j). -/
theorem P_conj_symm (i j : Fin n) :
    (P Y) j i = (starRingEnd ℂ) ((P Y) i j) := by
  have := congrFun (congrFun (P_hermitian Y) j) i
  simp only [Matrix.conjTranspose_apply] at this
  rw [← this]
  rfl

/-- The (i,i) entry of P·P is Σⱼ |Pᵢⱼ|², a real cast. -/
theorem PP_diag (i : Fin n) :
    ((P Y) * (P Y)) i i = ((∑ j, Complex.normSq ((P Y) i j) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  have hterm : ∀ j, (P Y) i j * (P Y) j i
      = ((Complex.normSq ((P Y) i j) : ℝ) : ℂ) := fun j => by
    rw [P_conj_symm Y i j, Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  norm_cast

/-- Diagonal entries of P are nonnegative in the complex order. -/
theorem diag_nonneg (i : Fin n) : 0 ≤ (P Y) i i := by
  have := (P_posSemidef Y).2 (Finsupp.single i 1)
  simpa using this

/-- Diagonal entries of P have nonnegative real part. -/
theorem diag_re_nonneg (i : Fin n) : 0 ≤ ((P Y) i i).re := by
  have h := (Complex.le_def.mp (diag_nonneg Y i)).1
  simpa using h

/-- a as a named real sum: (Tr P).re = Σᵢ (Pᵢᵢ).re. -/
theorem re_trace_eq_sum :
    (trace (P Y)).re = ∑ i, ((P Y) i i).re := by
  unfold Matrix.trace Matrix.diag
  exact Complex.re_sum (s := Finset.univ) _

/-- b as a named real sum: (Tr P·P).re = Σᵢⱼ |Pᵢⱼ|². -/
theorem re_tracePP_eq_sum :
    (trace ((P Y) * (P Y))).re = ∑ i, ∑ j, Complex.normSq ((P Y) i j) := by
  unfold Matrix.trace Matrix.diag
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [PP_diag]; exact Complex.ofReal_re _

/-- The entry formula for P itself: Pᵢᵢ = Σⱼ |Yⱼᵢ|². -/
theorem P_diag (i : Fin n) :
    (P Y) i i = ((∑ j, Complex.normSq (Y j i) : ℝ) : ℂ) := by
  unfold P
  rw [Matrix.mul_apply]
  have hterm : ∀ j, Yᴴ i j * Y j i = ((Complex.normSq (Y j i) : ℝ) : ℂ) :=
    fun j => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm,
        Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  norm_cast

/-- **The non-degeneracy bridge**: Y ≠ 0 implies Tr(P).re ≠ 0 (indeed
    Tr(P) = ‖Y‖²_F > 0), so `ccLambda_lower_bound`'s hypothesis holds for
    every nonzero Yukawa matrix. -/
theorem traceP_re_ne_zero_of_ne_zero (hY : Y ≠ 0) :
    (trace (P Y)).re ≠ 0 := by
  rw [re_trace_eq_sum]
  have hentry : ∀ i, ((P Y) i i).re = ∑ j, Complex.normSq (Y j i) := by
    intro i
    rw [P_diag]
    exact Complex.ofReal_re _
  intro hzero
  apply hY
  ext j i
  have hnn : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ ∑ j, Complex.normSq (Y j i) :=
    fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by
    rw [← Finset.sum_congr rfl (fun i _ => hentry i)]
    exact hzero)
  have hcol := hall i (Finset.mem_univ i)
  have hnn2 : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ Complex.normSq (Y j i) :=
    fun j _ => Complex.normSq_nonneg _
  have hentry0 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp hcol j
    (Finset.mem_univ j)
  simpa using Complex.normSq_eq_zero.mp hentry0

/-! ## 3. The Cauchy–Schwarz/Chebyshev bound -/

/-- **(Tr P)² ≤ N · Tr(P·P)** in real parts: Chebyshev on the diagonal plus
    the entrywise lower bound (P·P)ᵢᵢ = Σⱼ|Pᵢⱼ|² ≥ (Pᵢᵢ)². -/
theorem trace_sq_le_card_mul_trace_sq :
    ((trace (P Y)).re) ^ 2 ≤ (n : ℝ) * (trace ((P Y) * (P Y))).re := by
  rw [re_trace_eq_sum, re_tracePP_eq_sum]
  calc (∑ i, ((P Y) i i).re) ^ 2
      ≤ (Finset.univ.card : ℝ) * ∑ i, ((P Y) i i).re ^ 2 := by
        exact_mod_cast sq_sum_le_card_mul_sum_sq
          (s := Finset.univ) (f := fun i => ((P Y) i i).re)
    _ ≤ (n : ℝ) * ∑ i, ∑ j, Complex.normSq ((P Y) i j) := by
        rw [Finset.card_univ, Fintype.card_fin]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        apply Finset.sum_le_sum
        intro i _
        have hsingle : Complex.normSq ((P Y) i i)
            ≤ ∑ j, Complex.normSq ((P Y) i j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq ((P Y) i j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
        have hii : Complex.normSq ((P Y) i i) = ((P Y) i i).re ^ 2 := by
          have him : ((P Y) i i).im = 0 := by
            have hc := P_conj_symm Y i i
            have := congrArg Complex.im hc
            simp only [Complex.conj_im] at this
            linarith
          rw [Complex.normSq_apply, him]
          ring
        rw [← hii]
        exact hsingle

/-! ## 4. The boundary coupling and the mass transfer -/

/-- The C–C boundary coupling λ(Λ) = g²·b/a² (a DEFINITION here; its
    spectral-action derivation is cited, not formalised). -/
def ccLambda (g : ℝ) : ℝ :=
  g ^ 2 * (trace ((P Y) * (P Y))).re / ((trace (P Y)).re) ^ 2

/-- **The lower bound on the boundary coupling**: λ(Λ) ≥ g²/N whenever the
    Yukawa trace is nonzero. The quartic coupling at unification is bounded
    below by the gauge coupling over the fermion multiplicity — the
    algebraic half of the C–C Higgs-mass estimate. -/
theorem ccLambda_lower_bound (g : ℝ) (hn : 0 < n)
    (ha : (trace (P Y)).re ≠ 0) :
    g ^ 2 / (n : ℝ) ≤ ccLambda Y g := by
  have hcs := trace_sq_le_card_mul_trace_sq Y
  have ha2 : 0 < ((trace (P Y)).re) ^ 2 := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [ccLambda, div_le_div_iff₀ hnpos ha2]
  calc g ^ 2 * ((trace (P Y)).re) ^ 2
      ≤ g ^ 2 * ((n : ℝ) * (trace ((P Y) * (P Y))).re) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg g)
    _ = g ^ 2 * (trace ((P Y) * (P Y))).re * (n : ℝ) := by ring


/-- The cascade instantiation: N = 96 fermion degrees of freedom,
    λ(Λ) ≥ g²/96. -/
theorem cascade_ccLambda_lower (Y : Matrix (Fin 96) (Fin 96) ℂ) (g : ℝ)
    (ha : (trace (P Y)).re ≠ 0) :
    g ^ 2 / 96 ≤ ccLambda Y g := by
  have := ccLambda_lower_bound Y g (by norm_num) ha
  simpa using this

/-- The tree-level Higgs mass-square in CCM normalisation:
    m_H² = 2λv² with the SM quartic λ = 4λ̃, i.e. m_H² = 8λ̃v²
    (CCM 2007 §5.2, eq (5.15)). The relation is DEFINITIONAL here — its
    derivation from the Higgs potential is not formalised (see header). -/
def higgsMassSq (lamTilde v : ℝ) : ℝ := 8 * lamTilde * v ^ 2

/-- The mass transfer (monotonicity of the definition, nothing deeper):
    λ̃ ≥ g²/N gives m_H² = 8λ̃v² ≥ 8(g²/N)v². (The ≈125 GeV number requires
    the RG running, cited not proven.) -/
theorem higgsMassSq_transfer (g v : ℝ) (hn : 0 < n)
    (ha : (trace (P Y)).re ≠ 0) :
    higgsMassSq (g ^ 2 / (n : ℝ)) v ≤ higgsMassSq (ccLambda Y g) v := by
  unfold higgsMassSq
  have h := ccLambda_lower_bound Y g hn ha
  have hv : 0 ≤ v ^ 2 := sq_nonneg v
  nlinarith

end HiggsBridge
