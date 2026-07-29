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
  4. `psd_normSq_entry_le`, `psd_re_trace_mul_self_le_sq` — **the Schur
     bound**, in the opposite direction and in full generality (any PSD
     matrix over ℂ on any finite index type): |Mᵢⱼ|² ≤ Mᵢᵢ·Mⱼⱼ from the
     nonnegativity of the 2×2 principal minor, summed to
     Tr(M·M) ≤ (Tr M)². At P = Yᴴ·Y this is **b ≤ a²**
     (`tracePP_le_traceP_sq`).
  5. `ccLambda_lower_bound`, `ccLambda_upper_bound` — the C–C boundary
     coupling λ̃(Λ) := g²·b/a² (CCM 2007 §5.2 eq (5.6); the g there is g₃,
     defensible at unification) is **bracketed on both sides**:
     **g²/N ≤ λ̃(Λ) ≤ g²** whenever a = Tr(P) ≠ 0 — and
     `traceP_re_ne_zero_of_ne_zero` proves that condition is implied by
     Y ≠ 0, so the window holds for every nonzero Yukawa matrix.
     (Cascade N = 96: g²/96 ≤ λ̃ ≤ g² — `cascade_ccLambda_window`.)
  6. `ccLambda_lower_sharp`, `ccLambda_upper_sharp` — **both endpoints are
     attained**, so neither inequality can be improved: the democratic
     Yukawa matrix Y = 1 (all couplings equal) gives exactly λ̃ = g²/N,
     and the rank-one matrix diag(1,0,…,0) — one dominant coupling, the
     top-quark regime CCM actually works in — gives exactly λ̃ = g².
     The window is therefore the true range of the C–C boundary coupling
     over Yukawa textures, not a slack estimate.
  7. `higgsMassSq_transfer`, `higgsMassSq_upper`,
     `cascade_higgsMassSq_window` — NORMALISATION per CCM: the SM quartic
     is λ = 4λ̃ (CCM §5.2) and the tree-level mass relation is
     m_H² = 2λv² = 8λ̃v² (CCM eq (5.15)); `higgsMassSq` encodes 8λ̃v²
     accordingly, and the window transfers: 8(g²/N)v² ≤ m_H² ≤ 8g²v².
     NOTE: the mass relation itself is DEFINITIONAL here (deriving
     m_H² = 2λv² from a Higgs potential is not formalised — listed in
     NOT-proven), and the transfer is monotonicity, nothing deeper.

NOT proven here (named stairs, so the [CLAIMED] tag stays honest):
  the tree-level relation m_H² = 2λv² itself (definitional here; its
  derivation from the Higgs potential is standard but unformalised); the
  spectral-action DERIVATION of the boundary condition λ(Λ) = g²·b/a²
  itself (here λ(Λ) is a definition, its C–C origin cited:
  Chamseddine–Connes 2007, §5); WHICH Yukawa texture the cascade actually
  produces — the window is proven for every nonzero Y and its endpoints
  are attained, so pinning λ̃ to a single value inside it requires the
  texture, which is not derived anywhere in the estate; the RG running
  from Λ to the electroweak scale producing ≈125 GeV (verified-numerics
  ODE integration — out of Lean's current reach, cited). The 125 GeV
  number is NEVER claimed as proven content.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.StarOrdered

open Matrix
open scoped ComplexOrder

noncomputable section

namespace HiggsBridge

/-! ## 0. General facts about Hermitian and positive-semidefinite matrices

    Nothing in this section is special to the Yukawa setting: everything is
    stated for an arbitrary matrix over ℂ on an arbitrary finite index type.
    Sections 1–5 instantiate it at P = Yᴴ·Y. -/

section General

variable {N : Type*}

/-- Hermitian symmetry, entrywise: M j i = conj (M i j). -/
theorem herm_conj_symm {M : Matrix N N ℂ} (hM : M.IsHermitian) (i j : N) :
    M j i = (starRingEnd ℂ) (M i j) := by
  have h := congrFun (congrFun hM j) i
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  rfl

/-- Diagonal entries of a Hermitian matrix are real. -/
theorem herm_diag_im {M : Matrix N N ℂ} (hM : M.IsHermitian) (i : N) :
    (M i i).im = 0 := by
  have h := congrArg Complex.im (herm_conj_symm hM i i)
  simp only [Complex.conj_im] at h
  linarith

/-- The real part of a trace is the sum of the real parts of the diagonal. -/
theorem re_trace_eq_sum_diag [Fintype N] (M : Matrix N N ℂ) :
    (trace M).re = ∑ i, (M i i).re := by
  unfold Matrix.trace Matrix.diag
  exact Complex.re_sum (s := Finset.univ) _

/-- For Hermitian M the diagonal of M·M is a sum of squared moduli. -/
theorem herm_mul_self_diag [Fintype N] {M : Matrix N N ℂ} (hM : M.IsHermitian) (i : N) :
    (M * M) i i = ((∑ j, Complex.normSq (M i j) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  have hterm : ∀ j, M i j * M j i = ((Complex.normSq (M i j) : ℝ) : ℂ) :=
    fun j => by rw [herm_conj_symm hM i j, Complex.mul_conj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  norm_cast

/-- Tr(M·M) in real parts is the total squared modulus of the entries (the
    squared Frobenius norm) for Hermitian M. -/
theorem re_trace_mul_self_eq_sum [Fintype N] {M : Matrix N N ℂ} (hM : M.IsHermitian) :
    (trace (M * M)).re = ∑ i, ∑ j, Complex.normSq (M i j) := by
  rw [re_trace_eq_sum_diag]
  exact Finset.sum_congr rfl fun i _ => by
    rw [herm_mul_self_diag hM]; exact Complex.ofReal_re _

/-- **The 2×2 principal-minor bound**: for positive-semidefinite M,
    |Mᵢⱼ|² ≤ Mᵢᵢ·Mⱼⱼ. Proven by applying `Matrix.PosSemidef.det_nonneg` to
    the principal submatrix on rows and columns {i, j} — no spectral
    theorem and no case split on i = j (at i = j the minor degenerates and
    the statement is the equality |Mᵢᵢ|² = (Mᵢᵢ)², which holds because the
    diagonal is real). This is the entrywise Cauchy–Schwarz inequality for
    the pre-inner product defined by M. -/
theorem psd_normSq_entry_le {M : Matrix N N ℂ} (hM : M.PosSemidef) (i j : N) :
    Complex.normSq (M i j) ≤ (M i i).re * (M j j).re := by
  have hdet : (0 : ℂ) ≤ (M.submatrix ![i, j] ![i, j]).det :=
    (hM.submatrix ![i, j]).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [herm_conj_symm hM.1 i j, Complex.mul_conj] at hdet
  have hre := (Complex.le_def.mp hdet).1
  simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re] at hre
  rw [herm_diag_im hM.1 i, herm_diag_im hM.1 j] at hre
  linarith

/-- **The Schur trace bound**: for positive-semidefinite M over ℂ,
    Tr(M·M) ≤ (Tr M)² in real parts. It is the sum of the 2×2 minor
    bounds: Σᵢⱼ |Mᵢⱼ|² ≤ Σᵢⱼ Mᵢᵢ·Mⱼⱼ = (Σᵢ Mᵢᵢ)². -/
theorem psd_re_trace_mul_self_le_sq [Fintype N] {M : Matrix N N ℂ} (hM : M.PosSemidef) :
    (trace (M * M)).re ≤ ((trace M).re) ^ 2 := by
  rw [re_trace_mul_self_eq_sum hM.1, re_trace_eq_sum_diag, sq,
    Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => psd_normSq_entry_le hM i j

end General

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

/-! ## 5. The Schur bound at P: the coupling window and its sharpness -/

/-- **b ≤ a²**: the Schur bound instantiated at P = Yᴴ·Y. This closes the
    stair named as open in the first version of this file. -/
theorem tracePP_le_traceP_sq :
    (trace ((P Y) * (P Y))).re ≤ ((trace (P Y)).re) ^ 2 :=
  psd_re_trace_mul_self_le_sq (P_posSemidef Y)

/-- **The upper bound on the boundary coupling**: λ̃(Λ) ≤ g². Together with
    `ccLambda_lower_bound` the quartic coupling at unification is trapped in
    [g²/N, g²] for every nonzero Yukawa matrix. -/
theorem ccLambda_upper_bound (g : ℝ) (ha : (trace (P Y)).re ≠ 0) :
    ccLambda Y g ≤ g ^ 2 := by
  have hb := tracePP_le_traceP_sq Y
  have ha2 : 0 < ((trace (P Y)).re) ^ 2 := by positivity
  rw [ccLambda, div_le_iff₀ ha2]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg g)

/-- **The coupling window**, both sides at once, with the hypothesis in
    physical form (Y ≠ 0 rather than a trace condition). -/
theorem ccLambda_window (g : ℝ) (hn : 0 < n) (hY : Y ≠ 0) :
    g ^ 2 / (n : ℝ) ≤ ccLambda Y g ∧ ccLambda Y g ≤ g ^ 2 :=
  ⟨ccLambda_lower_bound Y g hn (traceP_re_ne_zero_of_ne_zero Y hY),
    ccLambda_upper_bound Y g (traceP_re_ne_zero_of_ne_zero Y hY)⟩

/-- **The lower endpoint is attained**: the democratic Yukawa matrix Y = 1
    (all couplings equal) gives exactly λ̃ = g²/N, so `ccLambda_lower_bound`
    is sharp. -/
theorem ccLambda_lower_sharp (g : ℝ) (hn : 0 < n) :
    ccLambda (1 : Matrix (Fin n) (Fin n) ℂ) g = g ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hP : P (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold P
    rw [Matrix.conjTranspose_one, one_mul]
  rw [ccLambda, hP, one_mul, Matrix.trace_one, Fintype.card_fin,
    Complex.natCast_re, sq]
  field_simp

/-- **The upper endpoint is attained**: the rank-one Yukawa matrix
    diag(1,0,…,0) — a single dominant coupling, which is exactly the
    top-quark-dominance regime CCM works in — gives λ̃ = g², so
    `ccLambda_upper_bound` is sharp. -/
theorem ccLambda_upper_sharp (g : ℝ) (hn : 0 < n) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ≠ 0 ∧ ccLambda Y g = g ^ 2 := by
  classical
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set d : Fin n → ℂ := fun k => if k = i₀ then 1 else 0 with hd
  have hdd : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : k = i₀ <;> simp [hd, hk]
  refine ⟨Matrix.diagonal d, ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h i₀) i₀
    rw [Matrix.diagonal_apply_eq] at h00
    simp [hd] at h00
  · have hP : P (Matrix.diagonal d) = Matrix.diagonal d := by
      unfold P
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      by_cases hk : k = i₀ <;> simp [hd, hk]
    have htr : trace (Matrix.diagonal d) = 1 := by
      rw [Matrix.trace_diagonal]
      simp [hd]
    rw [ccLambda, hP, hdd, htr]
    simp

/-- The cascade window: g²/96 ≤ λ̃ ≤ g² for every nonzero Yukawa matrix on
    the 96 cascade fermion degrees of freedom. -/
theorem cascade_ccLambda_window (Y : Matrix (Fin 96) (Fin 96) ℂ) (g : ℝ)
    (hY : Y ≠ 0) :
    g ^ 2 / 96 ≤ ccLambda Y g ∧ ccLambda Y g ≤ g ^ 2 :=
  ⟨cascade_ccLambda_lower Y g (traceP_re_ne_zero_of_ne_zero Y hY),
    ccLambda_upper_bound Y g (traceP_re_ne_zero_of_ne_zero Y hY)⟩

/-- The mass transfer, upper side: m_H² = 8λ̃v² ≤ 8g²v². -/
theorem higgsMassSq_upper (g v : ℝ) (ha : (trace (P Y)).re ≠ 0) :
    higgsMassSq (ccLambda Y g) v ≤ higgsMassSq (g ^ 2) v := by
  unfold higgsMassSq
  nlinarith [ccLambda_upper_bound Y g ha, sq_nonneg v]

/-- **The cascade Higgs-mass window**: for every nonzero Yukawa matrix on the
    96 cascade degrees of freedom, 8(g²/96)v² ≤ m_H² ≤ 8g²v². Both ends are
    attained by actual Yukawa matrices (`ccLambda_lower_sharp`,
    `ccLambda_upper_sharp`), so this is the full tree-level range the C–C
    boundary condition allows — the ≈125 GeV value still requires the RG
    running and the actual texture, neither of which is formalised. -/
theorem cascade_higgsMassSq_window (Y : Matrix (Fin 96) (Fin 96) ℂ) (g v : ℝ)
    (hY : Y ≠ 0) :
    higgsMassSq (g ^ 2 / 96) v ≤ higgsMassSq (ccLambda Y g) v ∧
      higgsMassSq (ccLambda Y g) v ≤ higgsMassSq (g ^ 2) v := by
  have ha := traceP_re_ne_zero_of_ne_zero Y hY
  refine ⟨?_, higgsMassSq_upper Y g v ha⟩
  have h := higgsMassSq_transfer Y g v (by norm_num) ha
  simpa using h


end HiggsBridge
