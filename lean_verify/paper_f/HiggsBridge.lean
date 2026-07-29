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
  4. `psd_normSq_entry_le`, `psd_re_trace_mul_self_le_sq` — **the minor
     trace bound**, in the opposite direction and in full generality (any
     PSD matrix over ℂ, any index type): |Mᵢⱼ|² ≤ Mᵢᵢ·Mⱼⱼ from the
     nonnegativity of the 2×2 principal minor, summed to
     Tr(M·M) ≤ (Tr M)². At P = Yᴴ·Y this is **b ≤ a²**
     (`tracePP_le_traceP_sq`). It genuinely needs positive semidefiniteness:
     for the Hermitian diag(1,−1), Tr M = 0 while Tr(M·M) = 2.
  5. `ccLambda_lower_bound`, `ccLambda_upper_bound` — the C–C boundary
     coupling λ̃(Λ) := g²·b/a² (CCM 2007 §5.2 eq (5.6); the g there is g₃,
     defensible at unification only to the extent that the three couplings
     do meet — CCM's own Fig. 1 says they do not meet exactly) is
     **bracketed on both sides**: **g²/N ≤ λ̃(Λ) ≤ g²**. The upper bound is
     unconditional; the lower bound needs a = Tr(P) ≠ 0, and
     `traceP_re_pos_of_ne_zero` proves a > 0 for every Y ≠ 0, so the window
     holds for every nonzero Yukawa matrix on N ≥ 1 indices.
     (At N = 96: g²/96 ≤ λ̃ ≤ g² — `cascade_ccLambda_window`.)
  6. `ccLambda_indicator` — **an exactly-computed family**: if the Yukawa
     matrix is the identity on a set s of directions and zero elsewhere then
     λ̃ = g²/|s| exactly. Consequences, all theorems, none assumed:
     |s| = N (flavour-degenerate Y = 1, all N Yukawa eigenvalues equal) hits
     the lower endpoint; |s| = 1 (a single dominant coupling) hits the upper
     endpoint, so neither constant can be improved; and |s| = 3 gives
     λ̃ = g²/3, which is exactly the value CCM's own top-dominance
     estimate produces (their eq (5.10): colour triplication makes the
     dominant Yukawa effectively threefold degenerate, a ≈ 3m_t², b ≈ 3m_t⁴,
     so b/a² = 1/3), while |s| = 4 gives g²/4, the value of their Remark 5.1
     once the tau-neutrino Yukawa is included. CCM's working point is thus
     INSIDE this window and computed here rather than cited.
     What is NOT claimed: that every real number in [g²/N, g²] is attained.
     Containment is proven and the values g²/k for 1 ≤ k ≤ N are attained;
     surjectivity onto the interval is not proven.
  7. `higgsMassSq_transfer`, `higgsMassSq_upper`,
     `cascade_higgsMassSq_window` — NORMALISATION per CCM: the SM quartic
     is λ = 4λ̃ (CCM §5.2, after eq (5.10) — cited, not derived here) and
     the tree-level mass relation is m_H² = 2λv² = 8λ̃v² (CCM eq (5.15)
     with v = 2M/g from (5.7)); `higgsMassSq` DEFINES 8λ̃v² accordingly,
     and the window transfers: 8(g²/N)v² ≤ m_H² ≤ 8g²v². The transfer is
     monotonicity of a definition, nothing deeper.

NOT proven here (named stairs, so the [CLAIMED] tag stays honest):
  the tree-level relation m_H² = 2λv² itself, and the normalisation λ = 4λ̃
  (both are CCM's, cited, not derived here); the spectral-action DERIVATION
  of the boundary condition λ̃(Λ) = g²·b/a² (here it is a definition, its
  C–C origin cited: Chamseddine–Connes 2007, §5); **that N = 96 is the right
  multiplicity** — CCM's eq (3.16) computes a and b as traces over 3×3
  generation matrices with an explicit colour weight 3, i.e. over 24 Yukawa
  eigenvalues, and b/a² is NOT invariant under changing the multiplicity
  with which each eigenvalue is counted (counting each eigenvalue four times
  scales b/a² by 1/4), so the choice of index set is a real assumption here,
  not a relabelling — in the bound's direction it is at least the
  conservative choice, since g²/96 is weaker than g²/24; **that the physical
  Yukawa texture space is all of Matrix (Fin N) (Fin N) ℂ** — it is not
  (CCM's textures carry colour weight 3, and within them a dominant quark
  Yukawa cannot reach the upper endpoint); that every value in the window is
  attained (see item 6); and the RG running from Λ to the electroweak scale
  producing ≈125 GeV (verified-numerics ODE integration — out of Lean's
  current reach, cited). The 125 GeV number is NEVER claimed as proven
  content.

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
    the principal submatrix on rows and columns {i, j}, with no case split
    on i = j (at i = j the minor degenerates and the statement is the
    equality |Mᵢᵢ|² = (Mᵢᵢ)², which holds because the diagonal is real).
    This is the entrywise Cauchy–Schwarz inequality for the pre-inner
    product xᴴMy defined by M. NOTE on provenance: nothing spectral appears
    in THIS file, but Mathlib's `det_nonneg` is itself proven through
    `IsHermitian.det_eq_prod_eigenvalues` and hence through the spectral
    theorem — so the spectral theorem is in the dependency graph, one layer
    down, and this proof is not an elementary-means proof of the bound. -/
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
    (P Y) j i = (starRingEnd ℂ) ((P Y) i j) :=
  herm_conj_symm (P_posSemidef Y).1 i j

/-- The (i,i) entry of P·P is Σⱼ |Pᵢⱼ|², a real cast. -/
theorem PP_diag (i : Fin n) :
    ((P Y) * (P Y)) i i = ((∑ j, Complex.normSq ((P Y) i j) : ℝ) : ℂ) :=
  herm_mul_self_diag (P_posSemidef Y).1 i

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
    (trace (P Y)).re = ∑ i, ((P Y) i i).re :=
  re_trace_eq_sum_diag (P Y)

/-- b as a named real sum: (Tr P·P).re = Σᵢⱼ |Pᵢⱼ|². -/
theorem re_tracePP_eq_sum :
    (trace ((P Y) * (P Y))).re = ∑ i, ∑ j, Complex.normSq ((P Y) i j) :=
  re_trace_mul_self_eq_sum (P_posSemidef Y).1

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

/-- The C–C boundary coupling λ̃(Λ) = g²·b/a² (a DEFINITION here; its
    spectral-action derivation is cited, not formalised). The SM quartic is
    λ = 4λ̃; every bound below is on λ̃, not on λ. -/
def ccLambda (g : ℝ) : ℝ :=
  g ^ 2 * (trace ((P Y) * (P Y))).re / ((trace (P Y)).re) ^ 2

/-- **The lower bound on the boundary coupling**: λ̃(Λ) ≥ g²/N whenever the
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
    λ̃(Λ) ≥ g²/96. (See the header: N = 96 is an assumption about the right
    multiplicity, not a theorem — CCM's own a, b are 24-eigenvalue traces.) -/
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

/-! ## 5. The minor trace bound at P: the coupling window and its sharpness

    Naming note: `Tr(M²) ≤ (Tr M)²` for PSD M is sometimes called a Schur
    bound in the physics literature, but in matrix analysis "Schur" normally
    refers to the Schur product theorem or the Schur complement. The
    ingredient used here, |Mᵢⱼ|² ≤ Mᵢᵢ·Mⱼⱼ, is standardly the 2×2 principal
    minor test (equivalently Cauchy–Schwarz for xᴴMy). -/

/-- **b ≤ a²**: the Schur bound instantiated at P = Yᴴ·Y. This closes the
    stair named as open in the first version of this file. -/
theorem tracePP_le_traceP_sq :
    (trace ((P Y) * (P Y))).re ≤ ((trace (P Y)).re) ^ 2 :=
  psd_re_trace_mul_self_le_sq (P_posSemidef Y)

/-- **The upper bound on the boundary coupling**: λ̃(Λ) ≤ g², with no
    hypothesis at all — if the Yukawa trace vanishes the definition gives
    λ̃ = 0 (Lean's x/0 = 0) and the bound is trivial; otherwise it is the
    minor trace bound b ≤ a² divided by a² > 0. -/
theorem ccLambda_upper_bound (g : ℝ) : ccLambda Y g ≤ g ^ 2 := by
  rcases eq_or_ne ((trace (P Y)).re) 0 with h | h
  · have hz : ccLambda Y g = 0 := by rw [ccLambda, h]; simp
    rw [hz]
    positivity
  · have hb := tracePP_le_traceP_sq Y
    have ha2 : 0 < ((trace (P Y)).re) ^ 2 := by positivity
    rw [ccLambda, div_le_iff₀ ha2]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg g)

/-- Strict positivity of the Yukawa trace for Y ≠ 0: a = Tr(P) = ‖Y‖²_F > 0.
    (The nonvanishing form `traceP_re_ne_zero_of_ne_zero` is what the lower
    bound consumes; this is the sharper statement its docstring claimed.) -/
theorem traceP_re_pos_of_ne_zero (hY : Y ≠ 0) : 0 < (trace (P Y)).re := by
  have hnn : 0 ≤ (trace (P Y)).re := by
    rw [re_trace_eq_sum]
    exact Finset.sum_nonneg fun i _ => diag_re_nonneg Y i
  exact lt_of_le_of_ne hnn (Ne.symm (traceP_re_ne_zero_of_ne_zero Y hY))

/-- **The coupling window**, both sides at once, with the hypothesis in
    physical form (Y ≠ 0 rather than a trace condition). -/
theorem ccLambda_window (g : ℝ) (hn : 0 < n) (hY : Y ≠ 0) :
    g ^ 2 / (n : ℝ) ≤ ccLambda Y g ∧ ccLambda Y g ≤ g ^ 2 :=
  ⟨ccLambda_lower_bound Y g hn (traceP_re_ne_zero_of_ne_zero Y hY),
    ccLambda_upper_bound Y g⟩

/-! ### The exactly-computed textures

    The window's contents are not a mystery: for the Yukawa matrix that is
    the identity on a set s of directions and zero elsewhere, λ̃ = g²/|s|
    exactly. |s| = N is the flavour-degenerate case (Y = 1) at the lower
    endpoint, |s| = 1 is a single dominant coupling at the upper endpoint,
    and |s| = 3 reproduces CCM's own top-dominance value g²/3. -/

/-- **The k-fold degenerate texture, computed**: λ̃ = g²/|s|. -/
theorem ccLambda_indicator (s : Finset (Fin n)) (hs : s.Nonempty) (g : ℝ) :
    ccLambda (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)) g
      = g ^ 2 / (s.card : ℝ) := by
  classical
  have hdd : Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)
      * Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)
      = Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i ∈ s <;> simp [h]
  have hP : P (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0))
      = Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) := by
    unfold P
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i ∈ s <;> simp [h]
  have htr : trace (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0))
      = (s.card : ℂ) := by
    rw [Matrix.trace_diagonal]
    simp
  have hne : (s.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
    exact ne_of_gt this
  rw [ccLambda, hP, hdd, htr]
  simp only [Complex.natCast_re]
  rw [div_eq_div_iff (pow_ne_zero 2 hne) hne]
  ring

/-- The same, indexed by the multiplicity k. -/
theorem ccLambda_card (s : Finset (Fin n)) {k : ℕ} (hk : 0 < k) (hs : s.card = k)
    (g : ℝ) :
    ccLambda (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)) g
      = g ^ 2 / (k : ℝ) := by
  rw [ccLambda_indicator s (Finset.card_pos.mp (by omega)) g, hs]

/-- **CCM's own working point, computed rather than cited**: a threefold
    degenerate texture gives λ̃ = g²/3 exactly. That is the value CCM's
    eq (5.10) produces — there colour triplication makes the dominant Yukawa
    effectively threefold degenerate (a ≈ 3m_t², b ≈ 3m_t⁴, so b/a² = 1/3).
    Their Remark 5.1, which adds a comparable tau-neutrino Yukawa, is the
    |s| = 4 case, g²/4. Both lie strictly inside the window proven above. -/
theorem ccLambda_ccm_top_dominance (s : Finset (Fin n)) (hs : s.card = 3) (g : ℝ) :
    ccLambda (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)) g
      = g ^ 2 / 3 := by
  have h := ccLambda_card s (k := 3) (by norm_num) hs g
  simpa using h

/-- The flavour-degenerate texture Y = 1 — all N Yukawa eigenvalues equal —
    computes to the lower endpoint exactly. (Note: this is NOT the
    "democratic" matrix of flavour physics, which has all *entries* equal
    and is rank one; that one sits at the upper endpoint.) -/
theorem ccLambda_one (g : ℝ) (hn : 0 < n) :
    ccLambda (1 : Matrix (Fin n) (Fin n) ℂ) g = g ^ 2 / (n : ℝ) := by
  classical
  have h := ccLambda_indicator (n := n) Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ g
  have hdiag : Matrix.diagonal
      (fun i : Fin n => if i ∈ (Finset.univ : Finset (Fin n)) then (1 : ℂ) else 0)
      = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp
  rw [hdiag, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- **The lower endpoint is attained by a nonzero Yukawa matrix**, so
    `ccLambda_lower_bound` cannot be improved. -/
theorem ccLambda_lower_sharp (g : ℝ) (hn : 0 < n) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ≠ 0 ∧ ccLambda Y g = g ^ 2 / (n : ℝ) := by
  refine ⟨1, ?_, ccLambda_one g hn⟩
  intro h
  have h00 := congrFun (congrFun h (⟨0, hn⟩ : Fin n)) (⟨0, hn⟩ : Fin n)
  rw [Matrix.one_apply_eq] at h00
  simp at h00

/-- **The upper endpoint is attained by a nonzero Yukawa matrix** — a single
    dominant coupling — so `ccLambda_upper_bound` cannot be improved either.
    (Sharpness is over all of `Matrix (Fin n) (Fin n) ℂ`; the physical CCM
    texture space is smaller — see the header.) -/
theorem ccLambda_upper_sharp (g : ℝ) (hn : 0 < n) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ≠ 0 ∧ ccLambda Y g = g ^ 2 := by
  classical
  refine ⟨Matrix.diagonal
    (fun i => if i ∈ ({⟨0, hn⟩} : Finset (Fin n)) then (1 : ℂ) else 0), ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h (⟨0, hn⟩ : Fin n)) (⟨0, hn⟩ : Fin n)
    rw [Matrix.diagonal_apply_eq] at h00
    simp at h00
  · rw [ccLambda_indicator _ ⟨⟨0, hn⟩, Finset.mem_singleton_self _⟩ g]
    simp

/-- The cascade window: g²/96 ≤ λ̃ ≤ g² for every nonzero Yukawa matrix on
    the 96 cascade indices (N = 96 assumed, not derived — see header). -/
theorem cascade_ccLambda_window (Y : Matrix (Fin 96) (Fin 96) ℂ) (g : ℝ)
    (hY : Y ≠ 0) :
    g ^ 2 / 96 ≤ ccLambda Y g ∧ ccLambda Y g ≤ g ^ 2 :=
  ⟨cascade_ccLambda_lower Y g (traceP_re_ne_zero_of_ne_zero Y hY),
    ccLambda_upper_bound Y g⟩

/-- The mass transfer, upper side: m_H² = 8λ̃v² ≤ 8g²v². -/
theorem higgsMassSq_upper (g v : ℝ) :
    higgsMassSq (ccLambda Y g) v ≤ higgsMassSq (g ^ 2) v := by
  unfold higgsMassSq
  nlinarith [ccLambda_upper_bound Y g, sq_nonneg v]

/-- **The cascade Higgs-mass window**: for every nonzero Yukawa matrix on the
    96 cascade indices, 8(g²/96)v² ≤ m_H² ≤ 8g²v² — where m_H² := 8λ̃v² is
    the DEFINITION `higgsMassSq` (CCM eq (5.15) normalisation), not a derived
    physical quantity. Both constants are sharp over all complex 96×96
    matrices; the ≈125 GeV value still requires the RG running and the actual
    Yukawa texture, and N = 96 is itself an assumption (see header). -/
theorem cascade_higgsMassSq_window (Y : Matrix (Fin 96) (Fin 96) ℂ) (g v : ℝ)
    (hY : Y ≠ 0) :
    higgsMassSq (g ^ 2 / 96) v ≤ higgsMassSq (ccLambda Y g) v ∧
      higgsMassSq (ccLambda Y g) v ≤ higgsMassSq (g ^ 2) v := by
  have ha := traceP_re_ne_zero_of_ne_zero Y hY
  refine ⟨?_, higgsMassSq_upper Y g v⟩
  have h := higgsMassSq_transfer Y g v (by norm_num) ha
  simpa using h

end HiggsBridge
