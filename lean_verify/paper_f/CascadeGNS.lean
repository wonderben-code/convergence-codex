/-
  CascadeGNS: The GNS Construction Applied to the Cascade Algebra M₄(ℂ)
  =====================================================================

  Upgrades: the "GNS reconstruction" claim, previously carried by
  `gns_produces_hilbert_space` in F4_4d — a counting proxy proving
  `card (Fin 3) = 3 ∧ exp 0 = 1 ∧ card (Fin 4 × Fin 4) = 16 ∧ 0 < exp(−1)`.
  Published tag [CLAIMED]; MATHS_ORG_STATE's "✅ FIXED in F4_4d" was found
  false by the Phase 0 audit. This file replaces the proxy with the actual
  Gelfand–Naimark–Segal construction from Mathlib, applied to the cascade's
  spacetime-level algebra M₄(ℂ).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `traceState` — the normalised trace ω(a) = Tr(a)/4 on the C⋆-algebra
     `CStarMatrix (Fin 4) (Fin 4) ℂ`, as a genuine `PositiveLinearMap`:
     positivity is DERIVED (star-ordered-ring closure induction reduces to
     Tr(sᴴs) ≥ 0, i.e. `posSemidef_conjTranspose_mul_self` + `trace_nonneg`),
     not assumed. `traceState_one`: ω(1) = 1 — a state, not just positive.
  2. `gnsRep := traceState.gnsStarAlgHom` — Mathlib's GNS ⋆-representation of
     M₄(ℂ) on the GNS Hilbert space `traceState.GNS` (a unital ⋆-algebra
     homomorphism into the bounded operators — supplied by Mathlib, cited).
  3. `vac` — the vacuum vector Ω (the image of 1 ∈ M₄ in the GNS space), with
     `vac_norm_one`: ‖Ω‖ = 1.
  4. `gnsRep_apply_vac` — π(a)Ω is the image of a itself: the GNS action on
     the vacuum is left multiplication.
  5. `state_recovery` — ⟪Ω, π(a)Ω⟫ = ω(a): the state is the vacuum
     expectation value. (This and cyclicity are the content Mathlib's GNS file
     lists as its own TODO; here they are proven for this concrete state.)
  6. `vac_cyclic` — Ω is a cyclic vector: {π(a)Ω : a ∈ M₄} is dense in the
     GNS space.
  7. `traceState_faithful` — ω(aᴴa) = 0 → a = 0 (faithfulness of the trace
     state; via `trace_conjTranspose_mul_self_eq_zero_iff`).

  NOT proven here: uniqueness of the GNS triple up to unitary equivalence;
  the GNS construction for states other than the normalised trace; anything
  about infinite-dimensional algebras. The Hilbert-space completion machinery
  is Mathlib's; this file's contribution is the state, its positivity, and
  the vacuum theorems 3–7.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped ComplexOrder

noncomputable section

namespace CascadeGNS

/-- The cascade's spacetime-level algebra M₄(ℂ), carried by the C⋆-matrix
    type (operator norm). -/
abbrev M4 : Type := CStarMatrix (Fin 4) (Fin 4) ℂ

/-- The normalised trace as a ℂ-linear functional on M₄. -/
def traceLin : M4 →ₗ[ℂ] ℂ :=
  (4 : ℂ)⁻¹ • ((Matrix.traceLinearMap (Fin 4) ℂ ℂ).comp
    (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap)

theorem traceLin_apply (a : M4) :
    traceLin a
      = (4 : ℂ)⁻¹ * Matrix.trace ((CStarMatrix.ofMatrixₗ (R := ℂ)).symm a) :=
  rfl

/-- 0 ≤ 1/4 in the complex order (real, nonnegative). -/
private theorem inv_four_nonneg : (0 : ℂ) ≤ (4 : ℂ)⁻¹ := by
  have h : ((4⁻¹ : ℝ) : ℂ) = (4 : ℂ)⁻¹ := by push_cast; ring
  rw [← h]
  exact_mod_cast (by norm_num : (0 : ℝ) ≤ 4⁻¹)

/-- Positivity of the normalised trace, DERIVED: a ≥ 0 in the C⋆-order means
    a lies in the additive closure of {sᴴs}; the trace of each sᴴs is
    nonnegative (`posSemidef_conjTranspose_mul_self`), and positivity is
    preserved by 0 and addition. -/
theorem traceLin_nonneg (a : M4) (ha : 0 ≤ a) : 0 ≤ traceLin a := by
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      have hps : (Matrix.PosSemidef (star s * s : Matrix (Fin 4) (Fin 4) ℂ)) :=
        Matrix.posSemidef_conjTranspose_mul_self s
      have htr : 0 ≤ Matrix.trace (star s * s : Matrix (Fin 4) (Fin 4) ℂ) :=
        hps.trace_nonneg
      exact mul_nonneg inv_four_nonneg htr
  | zero => simp
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact add_nonneg ihx ihy

/-- The normalised trace as a positive linear functional (a state after
    `traceState_one`). -/
def traceState : M4 →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ traceLin traceLin_nonneg

theorem traceState_apply (a : M4) : traceState a = traceLin a := rfl

/-- ω(1) = 1: the trace state is normalised. -/
theorem traceState_one : traceState (1 : M4) = 1 := by
  rw [traceState_apply]
  change (4 : ℂ)⁻¹ * Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1
  rw [Matrix.trace_one]
  norm_num

/-! ## The GNS data -/

/-- The GNS representation of M₄(ℂ) on the GNS Hilbert space of the trace
    state — Mathlib's construction, instantiated. -/
def gnsRep : M4 →⋆ₐ[ℂ] (traceState.GNS →L[ℂ] traceState.GNS) :=
  traceState.gnsStarAlgHom

/-- The vacuum vector Ω: the image of 1 ∈ M₄ in the GNS Hilbert space. -/
def vac : traceState.GNS :=
  ((traceState.toPreGNS 1 : traceState.PreGNS) : traceState.GNS)

/-- π(a)Ω is the image of a: the GNS action on the vacuum is left
    multiplication by a (on the dense copy of the algebra). -/
theorem gnsRep_apply_vac (a : M4) :
    gnsRep a vac
      = ((traceState.toPreGNS a : traceState.PreGNS) : traceState.GNS) := by
  change traceState.gnsNonUnitalStarAlgHom a
      ((traceState.toPreGNS 1 : traceState.PreGNS) : traceState.GNS)
    = ((traceState.toPreGNS a : traceState.PreGNS) : traceState.GNS)
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  congr 1
  change traceState.toPreGNS
      (a * traceState.ofPreGNS (traceState.toPreGNS 1)) = traceState.toPreGNS a
  rw [PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]

/-- **State recovery**: ⟪Ω, π(a)Ω⟫ = ω(a). The trace state is the vacuum
    expectation value of its GNS representation. -/
theorem state_recovery (a : M4) :
    (inner ℂ vac (gnsRep a vac)) = traceState a := by
  rw [gnsRep_apply_vac, vac, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]

/-- **Cyclicity of the vacuum**: the orbit {π(a)Ω : a ∈ M₄} is dense in the
    GNS Hilbert space. (Since π(a)Ω is the image of a, the orbit is exactly
    the canonical dense copy of the algebra in its completion.) -/
theorem vac_cyclic : DenseRange (fun a : M4 => gnsRep a vac) := by
  have hrange : Set.range (fun a : M4 => gnsRep a vac)
      = Set.range ((↑) : traceState.PreGNS → traceState.GNS) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨traceState.toPreGNS a, (gnsRep_apply_vac a).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨traceState.ofPreGNS b, ?_⟩
      change gnsRep (traceState.ofPreGNS b) vac = (b : traceState.GNS)
      rw [gnsRep_apply_vac, PositiveLinearMap.toPreGNS_ofPreGNS]
  have h2 : DenseRange ((↑) : traceState.PreGNS → traceState.GNS) :=
    UniformSpace.Completion.denseRange_coe
  unfold DenseRange at h2 ⊢
  rwa [hrange]

/-- ‖Ω‖ = 1: the vacuum is a unit vector (via ‖Ω‖² = ω(1ᴴ·1) = 1). -/
theorem vac_norm_one : ‖vac‖ = 1 := by
  rw [vac, UniformSpace.Completion.norm_coe]
  have h := PositiveLinearMap.preGNS_norm_sq traceState (traceState.toPreGNS 1)
  rw [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, traceState_one] at h
  have hsq : (‖(traceState.toPreGNS 1 : traceState.PreGNS)‖ : ℝ) ^ 2 = 1 := by
    exact_mod_cast h
  nlinarith [norm_nonneg (traceState.toPreGNS 1 : traceState.PreGNS)]

/-- **Faithfulness**: ω(aᴴa) = 0 forces a = 0 — the trace state separates
    points, so the GNS inner product is definite on the algebra copy. -/
theorem traceState_faithful (a : M4) (h : traceState (star a * a) = 0) :
    a = 0 := by
  rw [traceState_apply] at h
  have h' : (4 : ℂ)⁻¹
      * Matrix.trace ((star a * a : Matrix (Fin 4) (Fin 4) ℂ)) = 0 := h
  have h4 : (4 : ℂ)⁻¹ ≠ 0 := by norm_num
  have htr : Matrix.trace ((star a * a : Matrix (Fin 4) (Fin 4) ℂ)) = 0 :=
    (mul_eq_zero.mp h').resolve_left h4
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr

end CascadeGNS
