/-
  CascadeGNS: The GNS Construction — General Vacuum Lemmas + the Cascade
  Algebra M₄(ℂ)
  =====================================================================

  Upgrades: the "GNS reconstruction" claim, previously carried by
  `gns_produces_hilbert_space` in F4_4d — a counting proxy proving
  `card (Fin 3) = 3 ∧ exp 0 = 1 ∧ card (Fin 4 × Fin 4) = 16 ∧ 0 < exp(−1)`.
  Published tag [CLAIMED]; MATHS_ORG_STATE's "✅ FIXED in F4_4d" was found
  false by the Phase 0 audit. This file supplies the actual
  Gelfand–Naimark–Segal vacuum theorems and applies them to the cascade's
  spacetime-level algebra M₄(ℂ).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  A. GENERAL (any positive linear functional f on any UNITAL C⋆-algebra —
     this is the unital half of the TODO in Mathlib's GelfandNaimarkSegal
     file; the non-unital half, which needs approximate identities, is NOT
     touched here):
  1. `gnsVac f` — the vacuum vector Ω = image of 1 in f's GNS space, with
     `gnsVac_norm_sq`: ‖Ω‖² = f(1) (so Ω is a unit vector iff f is a state).
  2. `gnsStarAlgHom_apply_vac` — π(a)Ω is the image of a (near-definitional:
     the GNS action is left multiplication by construction).
  3. `gns_state_recovery` — ⟪Ω, π(a)Ω⟫ = f(a): the functional is recovered
     as the vacuum expectation value. (Mathlib's inner product is
     conjugate-linear in the FIRST slot; the TODO's ⟨π(a)ζ, ζ⟩ is the
     conjugate of this — equivalent data via a ↦ a*.)
  4. `gnsVac_cyclic` — Ω is cyclic: {π(a)Ω : a ∈ A} is dense in f.GNS
     (it is the canonical dense copy of A in its completion — the proof is
     exactly that observation, via `Completion.denseRange_coe`).
  5. `vacuum_functional_nonneg` — a ↦ ⟪Ω, π(a)Ω⟫ is a positive functional
     (with 3 and f(1) = 1 it is therefore a state).

  B. THE CASCADE INSTANCE (the trace state on M₄(ℂ)):
  6. `traceState` — ω(a) = Tr(a)/4 on `CStarMatrix (Fin 4) (Fin 4) ℂ` as a
     `PositiveLinearMap`: positivity is DERIVED (star-ordered-ring closure
     induction down to `posSemidef_conjTranspose_mul_self` +
     `PosSemidef.trace_nonneg`), not assumed. `traceState_one`: ω(1) = 1.
  7. `vac`, `gnsRep` — instances of A for ω, with `vac_norm_one`: ‖Ω‖ = 1,
     plus `state_recovery`/`vac_cyclic` in the concrete types.
  8. `traceState_faithful` — ω(aᴴa) = 0 → a = 0 (via Mathlib's
     `trace_conjTranspose_mul_self_eq_zero_iff` plus 4⁻¹-cancellation), and
     its GNS meaning made formal: `preGNS_inner_definite` — the GNS
     pre-inner product of ω is DEFINITE (⟪x,x⟫ = 0 → x = 0), i.e. no null
     vectors, so for this state the pre-GNS space is already an inner
     product space.

  Contribution audit (to keep this header honest): the mathematically
  substantive new proofs here are `traceLin_nonneg` (derived positivity),
  `preGNS_inner_definite`, and the assembly of A.1–A.5 in the general
  unital case; A.2–A.4 are individually thin (unfold + `mul_one`,
  `inner_coe` + simp, `denseRange_coe`) — their value is that the claims
  become theorems instead of prose. `gnsRep` itself is Mathlib's
  construction, cited not re-proven. In the finite-dimensional faithful
  case the "dense copy" is in fact everything; no completion analysis is
  exercised (and none is claimed).

  NOT proven here: the non-unital GNS TODO (approximate identities);
  uniqueness of the GNS triple up to unitary equivalence; Mathlib has no
  bundled `State` structure to instantiate, so "is a state" is carried by
  the pair (`vacuum_functional_nonneg`, `gns_state_recovery` + f(1) = 1).

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

/-! ## A. General vacuum lemmas: any positive functional, any unital C⋆-algebra -/

section General

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ)

/-- The vacuum vector Ω: the image of 1 ∈ A in the GNS Hilbert space of f. -/
def gnsVac : f.GNS := ((f.toPreGNS 1 : f.PreGNS) : f.GNS)

/-- π(a)Ω is the image of a: the GNS action on the vacuum is left
    multiplication (which is what the GNS representation is, by
    construction — this lemma makes it available as an equation). -/
theorem gnsStarAlgHom_apply_vac (a : A) :
    f.gnsStarAlgHom a (gnsVac f)
      = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
  change f.gnsNonUnitalStarAlgHom a ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
    = ((f.toPreGNS a : f.PreGNS) : f.GNS)
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  congr 1
  change f.toPreGNS (a * f.ofPreGNS (f.toPreGNS 1)) = f.toPreGNS a
  rw [PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]

/-- **State recovery**: ⟪Ω, π(a)Ω⟫ = f(a). The functional is the vacuum
    expectation value of its GNS representation. -/
theorem gns_state_recovery (a : A) :
    (inner ℂ (gnsVac f) (f.gnsStarAlgHom a (gnsVac f))) = f a := by
  rw [gnsStarAlgHom_apply_vac, gnsVac, UniformSpace.Completion.inner_coe,
    PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]

/-- **Cyclicity of the vacuum**: {π(a)Ω : a ∈ A} is dense in the GNS space —
    it is exactly the canonical dense copy of A in its completion. -/
theorem gnsVac_cyclic :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVac f)) := by
  have hrange : Set.range (fun a : A => f.gnsStarAlgHom a (gnsVac f))
      = Set.range ((↑) : f.PreGNS → f.GNS) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨f.toPreGNS a, (gnsStarAlgHom_apply_vac f a).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨f.ofPreGNS b, ?_⟩
      change f.gnsStarAlgHom (f.ofPreGNS b) (gnsVac f) = (b : f.GNS)
      rw [gnsStarAlgHom_apply_vac, PositiveLinearMap.toPreGNS_ofPreGNS]
  have h2 : DenseRange ((↑) : f.PreGNS → f.GNS) :=
    UniformSpace.Completion.denseRange_coe
  unfold DenseRange at h2 ⊢
  rwa [hrange]

/-- ‖Ω‖² = f(1): the vacuum is a unit vector exactly when f is normalised. -/
theorem gnsVac_norm_sq : ((‖gnsVac f‖ : ℂ)) ^ 2 = f 1 := by
  rw [gnsVac, UniformSpace.Completion.norm_coe]
  have h := PositiveLinearMap.preGNS_norm_sq f (f.toPreGNS 1)
  rwa [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul] at h

/-- The vacuum expectation functional a ↦ ⟪Ω, π(a)Ω⟫ is positive; together
    with `gns_state_recovery` and f(1) = 1 this says it is a STATE. -/
theorem vacuum_functional_nonneg (a : A) (ha : 0 ≤ a) :
    0 ≤ (inner ℂ (gnsVac f) (f.gnsStarAlgHom a (gnsVac f))) := by
  rw [gns_state_recovery]
  exact map_nonneg f ha

end General

/-! ## B. The cascade instance: the trace state on M₄(ℂ) -/

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

/-- The GNS representation of M₄(ℂ) for the trace state — Mathlib's
    construction, instantiated (an alias, cited not re-proven). -/
def gnsRep : M4 →⋆ₐ[ℂ] (traceState.GNS →L[ℂ] traceState.GNS) :=
  traceState.gnsStarAlgHom

/-- The vacuum vector of the trace state. -/
def vac : traceState.GNS := gnsVac traceState

theorem gnsRep_apply_vac (a : M4) :
    gnsRep a vac
      = ((traceState.toPreGNS a : traceState.PreGNS) : traceState.GNS) :=
  gnsStarAlgHom_apply_vac traceState a

/-- ⟪Ω, π(a)Ω⟫ = ω(a) for the cascade's trace state. -/
theorem state_recovery (a : M4) :
    (inner ℂ vac (gnsRep a vac)) = traceState a :=
  gns_state_recovery traceState a

/-- The vacuum of the trace state is cyclic. -/
theorem vac_cyclic : DenseRange (fun a : M4 => gnsRep a vac) :=
  gnsVac_cyclic traceState

/-- ‖Ω‖ = 1: the trace-state vacuum is a unit vector (ω(1) = 1). -/
theorem vac_norm_one : ‖vac‖ = 1 := by
  have h := gnsVac_norm_sq traceState
  rw [traceState_one] at h
  have hsq : (‖gnsVac traceState‖ : ℝ) ^ 2 = 1 ^ 2 := by
    rw [one_pow]; exact_mod_cast h
  rw [vac]
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp hsq

/-- **Faithfulness**: ω(aᴴa) = 0 forces a = 0 (Mathlib's
    `trace_conjTranspose_mul_self_eq_zero_iff` plus 4⁻¹-cancellation). -/
theorem traceState_faithful (a : M4) (h : traceState (star a * a) = 0) :
    a = 0 := by
  rw [traceState_apply] at h
  have h' : (4 : ℂ)⁻¹
      * Matrix.trace ((star a * a : Matrix (Fin 4) (Fin 4) ℂ)) = 0 := h
  have h4 : (4 : ℂ)⁻¹ ≠ 0 := by norm_num
  have htr : Matrix.trace ((star a * a : Matrix (Fin 4) (Fin 4) ℂ)) = 0 :=
    (mul_eq_zero.mp h').resolve_left h4
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr

/-- **Definiteness of the GNS pre-inner product** for the trace state:
    ⟪x, x⟫ = 0 forces x = 0 — no null vectors, so the pre-GNS space of ω is
    already a genuine inner product space (the formal content of "the trace
    state is faithful" at the GNS level). -/
theorem preGNS_inner_definite (x : traceState.PreGNS)
    (h : (inner ℂ x x : ℂ) = 0) : x = 0 := by
  rw [PositiveLinearMap.preGNS_inner_def] at h
  have hz : traceState.ofPreGNS x = 0 := traceState_faithful _ h
  have := congrArg traceState.toPreGNS hz
  rwa [PositiveLinearMap.toPreGNS_ofPreGNS, map_zero] at this

end CascadeGNS
