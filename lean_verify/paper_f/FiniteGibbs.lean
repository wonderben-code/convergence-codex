/-
  FiniteGibbs: the Gibbs Measure as a DEFINITION, and Invariance at Every β
  =========================================================================

  Successor item 1 of the `_proof_004_logos` split (UNLOCK_WATCHLIST). The
  estate's phase-transition file axiomatises `GibbsMeasure` as an opaque
  constant, so no statement about it is provable or refutable. This file
  builds the finite-volume Gibbs measure as an honest DEFINITION — the
  normalised exponential reweighting of a reference measure — and proves
  the theorem that the split showed was hiding inside clause (1) of the
  refuted statement:

  A SYMMETRY OF THE HAMILTONIAN AND THE REFERENCE MEASURE IS A SYMMETRY OF
  THE GIBBS MEASURE — AT EVERY INVERSE TEMPERATURE. No β_c. Invariance is
  not a high-temperature phenomenon at finite volume; it is unconditional.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `Z`, `gibbs` — the partition function ∫ e^{−βH} dν and the measure
     Z⁻¹·e^{−βH}dν, as definitions (no axiom).
  2. `Z_ne_zero` / `Z_ne_top` / `isProbabilityMeasure_gibbs` — for BOUNDED
     H and a finite nonzero reference measure, Z ∈ (0, ∞) and the Gibbs
     measure is an honest probability measure. (Bounded H covers every
     finite spin system; measurability of H is not even needed for the
     normalisation — it IS needed for the invariance theorem, and appears
     exactly there.)
  3. **`gibbs_map_of_invariant`** — if T preserves ν and H∘T = H, then
     T-pushforward fixes `gibbs β H ν`, for EVERY β ∈ ℝ.
  4. `gibbs_smul_invariant` / **`no_finite_volume_breaking`** — the group
     form, and the punchline: for a G-invariant finite-volume system,
     clause (2) of the refuted phase-transition statement FAILS at every
     candidate β_c. Finite-volume Gibbs measures NEVER break a symmetry
     of (H, ν) at the level of measure non-invariance. This PROVES the
     remark recorded on the watchlist: symmetry breaking is a
     thermodynamic-limit phenomenon, and any honest per-model Peierls
     formulation must be about boundary conditions or magnetisation
     bounds, not finite-volume measure non-invariance.
  5. The concrete witness — the TWO-SITE ISING MODEL: Ω = Bool × Bool,
     H(σ) = −1 if the spins agree and +1 if not, reference measure the
     sum of the four Dirac masses, and the global spin flip. The flip is
     a NONTRIVIAL involution (it moves every configuration), H is
     genuinely non-constant, and `two_site_gibbs_invariant` instantiates
     the invariance theorem at every β. So the no-breaking theorem has
     bite on an honest interacting symmetric system — this is NOT the
     trivial-action degeneracy of ERRATA 34.

  NOT proven here:

  * Anything about the OPAQUE `GibbsMeasure` axiom of `_proof_004_logos` —
    this file does not import it, and adopting this definition there is
    the author's DECISIONS NEEDED 2.
  * The thermodynamic limit, boundary conditions, correlation decay, or
    any Peierls-type bound — the successor watchlist item, a mapped wall.
  * Any connection between β and physics scales; β here is a real number.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 axioms
  beyond [propext, Classical.choice, Quot.sound] on every declaration.
-/

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace FiniteGibbs

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. The definitions -/

/-- The partition function Z_β = ∫ e^{−βH} dν. -/
def Z (β : ℝ) (H : Ω → ℝ) (ν : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (-β * H ω)) ∂ν

/-- The finite-volume Gibbs measure Z⁻¹·e^{−βH}dν — a DEFINITION, not an
    axiom. -/
def gibbs (β : ℝ) (H : Ω → ℝ) (ν : Measure Ω) : Measure Ω :=
  (Z β H ν)⁻¹ • ν.withDensity (fun ω => ENNReal.ofReal (Real.exp (-β * H ω)))

/-! ## 2. Probability, under stated hypotheses -/

omit [MeasurableSpace Ω] in
theorem weight_le (β : ℝ) {H : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |H ω| ≤ C) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-β * H ω)) ≤ ENNReal.ofReal (Real.exp (|β| * C)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  calc -β * H ω ≤ |(-β) * H ω| := le_abs_self _
    _ = |β| * |H ω| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * C := by
        have h0 : (0 : ℝ) ≤ |β| := abs_nonneg β
        exact mul_le_mul_of_nonneg_left (hC ω) h0

omit [MeasurableSpace Ω] in
theorem weight_ge (β : ℝ) {H : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |H ω| ≤ C) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-(|β| * C))) ≤ ENNReal.ofReal (Real.exp (-β * H ω)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have h1 : -β * H ω ≥ -|(-β) * H ω| := neg_abs_le _
  have h2 : |(-β) * H ω| ≤ |β| * C := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg β)
  linarith

theorem Z_ne_top (β : ℝ) {H : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |H ω| ≤ C)
    (ν : Measure Ω) [IsFiniteMeasure ν] : Z β H ν ≠ ⊤ := by
  have hle : Z β H ν ≤ ENNReal.ofReal (Real.exp (|β| * C)) * ν Set.univ := by
    calc Z β H ν ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (|β| * C)) ∂ν :=
          lintegral_mono fun ω => weight_le β hC ω
      _ = ENNReal.ofReal (Real.exp (|β| * C)) * ν Set.univ := lintegral_const _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)) hle

theorem Z_ne_zero (β : ℝ) {H : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |H ω| ≤ C)
    (ν : Measure Ω) (hν : ν ≠ 0) : Z β H ν ≠ 0 := by
  have hge : ENNReal.ofReal (Real.exp (-(|β| * C))) * ν Set.univ ≤ Z β H ν := by
    calc ENNReal.ofReal (Real.exp (-(|β| * C))) * ν Set.univ
        = ∫⁻ _, ENNReal.ofReal (Real.exp (-(|β| * C))) ∂ν := (lintegral_const _).symm
      _ ≤ Z β H ν := lintegral_mono fun ω => weight_ge β hC ω
  intro h0
  rw [h0] at hge
  have heq : ENNReal.ofReal (Real.exp (-(|β| * C))) * ν Set.univ = 0 :=
    le_antisymm hge (zero_le _)
  rcases mul_eq_zero.mp heq with h | h
  · exact absurd h (by simp [Real.exp_pos])
  · exact hν (Measure.measure_univ_eq_zero.mp h)

/-- Under bounded H and a finite nonzero reference measure, the Gibbs
    measure is an honest probability measure. (No measurability of H is
    needed — an adversarial review probed the theorem at an arbitrary
    bounded function.) -/
theorem isProbabilityMeasure_gibbs (β : ℝ) {H : Ω → ℝ}
    {C : ℝ} (hC : ∀ ω, |H ω| ≤ C) (ν : Measure Ω) [IsFiniteMeasure ν]
    (hν : ν ≠ 0) : IsProbabilityMeasure (gibbs β H ν) := by
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rw [show (∫⁻ ω, ENNReal.ofReal (Real.exp (-β * H ω)) ∂ν) = Z β H ν from rfl,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Z_ne_zero β hC ν hν) (Z_ne_top β hC ν)

/-! ## 3. THE invariance theorem: every β, no β_c -/

/-- **A symmetry of (H, ν) is a symmetry of the Gibbs measure at EVERY
    inverse temperature.** If T preserves ν and H ∘ T = H, then the
    pushforward of `gibbs β H ν` along T is `gibbs β H ν` — for all β ∈ ℝ,
    with no critical-temperature caveat. -/
theorem gibbs_map_of_invariant (β : ℝ) {H : Ω → ℝ} (hmeas : Measurable H)
    {ν : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T ν ν)
    (hH : ∀ ω, H (T ω) = H ω) :
    Measure.map T (gibbs β H ν) = gibbs β H ν := by
  rw [gibbs, Measure.map_smul]
  congr 1
  have hf : Measurable fun ω => ENNReal.ofReal (Real.exp (-β * H ω)) := by
    fun_prop
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hT.measurable hA,
    withDensity_apply _ (hT.measurable hA), withDensity_apply _ hA]
  have h1 : ∫⁻ ω in T ⁻¹' A, ENNReal.ofReal (Real.exp (-β * H ω)) ∂ν
      = ∫⁻ ω in T ⁻¹' A, ENNReal.ofReal (Real.exp (-β * H (T ω))) ∂ν := by
    refine lintegral_congr fun ω => ?_
    rw [hH]
  have h2 : ∫⁻ ω in T ⁻¹' A, ENNReal.ofReal (Real.exp (-β * H (T ω))) ∂ν
      = ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-β * H ω)) ∂(Measure.map T ν) :=
    (setLIntegral_map hA hf hT.measurable).symm
  rw [h1, h2, hT.map_eq]

/-- The group form: if every g ∈ G preserves ν and H is G-invariant, the
    Gibbs measure is G-invariant at every β. -/
theorem gibbs_smul_invariant {G : Type*} [Group G] [MulAction G Ω]
    {H : Ω → ℝ} (hmeas : Measurable H) {ν : Measure Ω}
    (hact : ∀ g : G, MeasurePreserving (fun ω => g • ω) ν ν)
    (hH : ∀ (g : G) (ω : Ω), H (g • ω) = H ω) (β : ℝ) (g : G) :
    Measure.map (fun ω => g • ω) (gibbs β H ν) = gibbs β H ν :=
  gibbs_map_of_invariant β hmeas (hact g) (hH g)

/-- **No finite-volume symmetry breaking.** For a G-invariant finite-volume
    system, the clause-(2) SHAPE of the refuted phase-transition statement
    — stated here for the `gibbs` DEFINED in this file, not for the opaque
    `GibbsMeasure` axiom of the logos file, to which no formal bridge
    exists (see the NOT-proven box) — fails at EVERY candidate β_c: the
    Gibbs measure equals every pushforward, at every β. Symmetry breaking,
    if it is anywhere, is in the thermodynamic limit — not in any finite
    volume. -/
theorem no_finite_volume_breaking {G : Type*} [Group G] [MulAction G Ω]
    {H : Ω → ℝ} (hmeas : Measurable H) {ν : Measure Ω}
    (hact : ∀ g : G, MeasurePreserving (fun ω => g • ω) ν ν)
    (hH : ∀ (g : G) (ω : Ω), H (g • ω) = H ω) :
    ¬ ∃ β_c : ℝ, ∀ β > β_c, ∃ g : G,
        gibbs β H ν ≠ Measure.map (fun ω => g • ω) (gibbs β H ν) := by
  rintro ⟨β_c, h⟩
  obtain ⟨g, hg⟩ := h (β_c + 1) (by linarith)
  exact hg (gibbs_smul_invariant hmeas hact hH (β_c + 1) g).symm

/-! ## 4. The concrete witness: the two-site Ising model -/

/-- Two spins; H = −1 when they agree, +1 when they differ. -/
def H2 : Bool × Bool → ℝ := fun σ => if σ.1 = σ.2 then -1 else 1

/-- The global spin flip. -/
def flip : Bool × Bool → Bool × Bool := fun σ => (!σ.1, !σ.2)

/-- The uniform reference: the sum of the four Dirac masses. -/
def ν₄ : Measure (Bool × Bool) :=
  Measure.dirac (true, true) + Measure.dirac (true, false)
    + Measure.dirac (false, true) + Measure.dirac (false, false)

theorem measurable_H2 : Measurable H2 := measurable_of_countable H2

theorem H2_bounded : ∀ σ, |H2 σ| ≤ 1 := by
  intro σ
  rcases σ with ⟨a, b⟩
  cases a <;> cases b <;> simp [H2]

theorem H2_flip_invariant : ∀ σ, H2 (flip σ) = H2 σ := by
  intro ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- The flip moves EVERY configuration: this symmetry is as far from the
    trivial action of ERRATA 34 as possible. -/
theorem flip_nontrivial : ∀ σ : Bool × Bool, flip σ ≠ σ := by
  intro ⟨a, b⟩
  cases a <;> cases b <;> simp [flip]

/-- The flip is an involution — the header calls it one, so the file
    proves it (adversarial review round 5, F2). -/
theorem flip_involutive : ∀ σ : Bool × Bool, flip (flip σ) = σ := by
  intro ⟨a, b⟩
  cases a <;> cases b <;> rfl

theorem measurePreserving_flip : MeasurePreserving flip ν₄ ν₄ := by
  refine ⟨measurable_of_countable flip, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_of_countable flip) hA]
  simp only [ν₄, Measure.add_apply, Measure.dirac_apply]
  have hin : ∀ x : Bool × Bool,
      (flip ⁻¹' A).indicator (1 : (Bool × Bool) → ℝ≥0∞) x
        = A.indicator 1 (flip x) := by
    intro x
    by_cases hx : flip x ∈ A <;> simp [Set.mem_preimage, hx]
  simp only [hin, flip, Bool.not_true, Bool.not_false]
  ring

instance : IsFiniteMeasure ν₄ := by
  rw [ν₄]
  infer_instance

theorem ν₄_ne_zero : ν₄ ≠ 0 := by
  intro h
  have h1 := congrArg (fun μ : Measure (Bool × Bool) => μ Set.univ) h
  simp only [ν₄, Measure.coe_zero, Pi.zero_apply, Measure.add_apply] at h1
  rw [Measure.dirac_apply_of_mem (Set.mem_univ _)] at h1
  simp at h1

/-- The two-site Ising Gibbs measure is a genuine probability measure. -/
theorem two_site_isProbability (β : ℝ) :
    IsProbabilityMeasure (gibbs β H2 ν₄) :=
  isProbabilityMeasure_gibbs β H2_bounded ν₄ ν₄_ne_zero

/-- **The two-site Ising model witnesses the invariance theorem**: the
    spin-flip symmetry fixes the Gibbs measure at every β — a nontrivial
    involution, a non-constant Hamiltonian, and still no breaking at any
    finite volume. -/
theorem two_site_gibbs_invariant (β : ℝ) :
    Measure.map flip (gibbs β H2 ν₄) = gibbs β H2 ν₄ :=
  gibbs_map_of_invariant β measurable_H2 measurePreserving_flip
    H2_flip_invariant

end FiniteGibbs
