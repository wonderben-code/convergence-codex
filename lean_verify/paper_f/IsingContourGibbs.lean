/-
  IsingContourGibbs.lean — the contour identity, carried across to the Gibbs
  measure.

  WHY. `IsingContourEnergy` and `IsingContourSeparation` are both statements
  about the HAMILTONIAN. **Peierls is a statement about a measure.** The
  estate has had a finite-volume Gibbs measure since `FiniteGibbs` and has
  instantiated it at the real 2-d Ising model since `IsingFiniteVolume`, and
  nothing connected the two lines. This is the bridge.

  WHAT THIS FILE PROVES:
  1. **`peierls_weight`** — `e^{−βH(σ)} = e^{−4β|γ(σ)|} · e^{−βH(ground)}`.
     Literally the term a Peierls sum consumes, and one line from
     `isingH_eq_ground_add_contour`.
  2. **`gibbs_singleton`** — the Gibbs mass of a single configuration is
     `Z⁻¹ · e^{−βH(σ)}`, and hence `gibbs_singleton_contour`, the same thing
     written in terms of the contour.
  3. **`gibbs_eq_ground_iff`** — **THE MODE.** For `β > 0` and `n ≥ 1` the
     Gibbs measure of a single configuration is maximised exactly at the two
     constant configurations and is strictly smaller at every other one;
     `card_gibbs_maximisers` says there are exactly two of them.

  WHAT THIS DOES NOT DO, and one clause of it is a warning rather than a
  limitation. There is no sum over contours, no enumeration, no circuits, no
  `3^{|γ|}`, no thermodynamic limit, and
  `IsingBoundaryField.MagnetisationBound` is untouched.
  **A MODE IS NOT A PHASE TRANSITION**, and the estate already contains the
  theorem that says why. The mode sits at the two constants for EVERY
  `β > 0`, and `IsingFiniteVolume.ising_no_finite_volume_breaking` proves
  there is no `β_c` at finite volume at all. The two are consistent because
  **the mode is a SYMMETRIC PAIR**: `gibbs_allFalse_eq_allTrue` shows the two
  maximisers carry equal mass, so the global flip permutes them and the mode
  carries no symmetry-breaking information whatever. Beyond that, Peierls
  needs the total probability of the minority phase to be small — a SUM over
  exponentially many configurations — and knowing which single configuration
  is likeliest says nothing about that sum.

  The mathematical content here is modest and the header should not pretend
  otherwise: §3 is `IsingContourSeparation.isingH_lt_of_not_const` pushed
  through a monotone function. The value is that the contour line and the
  measure line now meet.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourSeparation

namespace IsingContourGibbs

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation MeasureTheory

/-! ## 1. The Peierls weight -/

/-- **THE PEIERLS WEIGHT.** The Boltzmann factor of a configuration is the
    ground-state factor times `e^{−4β}` per unit of contour length. This is
    the term a Peierls estimate sums over contours. -/
theorem peierls_weight (n : ℕ) (β : ℝ) (σ : Config n) :
    Real.exp (-β * isingH n σ)
      = Real.exp (-(4 * β) * ((contour σ).card : ℝ))
        * Real.exp (-β * isingH n (fun _ => true)) := by
  rw [← Real.exp_add, isingH_eq_ground_add_contour σ]
  congr 1
  ring

theorem peierls_weight_le (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (σ : Config n) :
    Real.exp (-β * isingH n σ) ≤ Real.exp (-β * isingH n (fun _ => true)) := by
  apply Real.exp_le_exp.mpr
  have := isingH_ground_le σ
  nlinarith

theorem peierls_weight_lt (n : ℕ) (hn : 0 < n) {β : ℝ} (hβ : 0 < β) (σ : Config n)
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    Real.exp (-β * isingH n σ) < Real.exp (-β * isingH n (fun _ => true)) := by
  apply Real.exp_lt_exp.mpr
  have := isingH_lt_of_not_const hn σ h1 h2
  nlinarith

/-! ## 2. The Gibbs mass of a single configuration -/

/-- The Gibbs mass of one configuration under the counting reference
    measure: the Boltzmann factor over the partition function, with no
    integral left in it. -/
theorem gibbs_singleton (n : ℕ) (β : ℝ) (σ : Config n) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      = (FiniteGibbs.Z β (isingH n) (Measure.count : Measure (Config n)))⁻¹
        * ENNReal.ofReal (Real.exp (-β * isingH n σ)) := by
  rw [FiniteGibbs.gibbs, Measure.smul_apply,
    withDensity_apply _ (measurableSet_singleton σ),
    lintegral_singleton, Measure.count_singleton, mul_one, smul_eq_mul]

/-- The same thing in contour form — the shape a Peierls argument uses. -/
theorem gibbs_singleton_contour (n : ℕ) (β : ℝ) (σ : Config n) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      = ENNReal.ofReal (Real.exp (-(4 * β) * ((contour σ).card : ℝ)))
        * FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)} := by
  rw [gibbs_singleton, gibbs_singleton, peierls_weight n β σ,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ring

/-! ## 3. The mode

Both facts needed about `Z⁻¹` — nonzero and finite — come from
`FiniteGibbs`, at the exact hypotheses `IsingFiniteVolume.ising_isProbability`
already discharges.
-/

theorem invZ_ne_zero (n : ℕ) (β : ℝ) :
    (FiniteGibbs.Z β (isingH n) (Measure.count : Measure (Config n)))⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (FiniteGibbs.Z_ne_top β (isingH_bound n) Measure.count)

theorem invZ_ne_top (n : ℕ) (β : ℝ) :
    (FiniteGibbs.Z β (isingH n) (Measure.count : Measure (Config n)))⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr
    (FiniteGibbs.Z_ne_zero β (isingH_bound n) Measure.count Measure.count_ne_zero'')

/-- At `β ≥ 0` no configuration is likelier than the ground state. -/
theorem gibbs_le_ground (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (σ : Config n) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      ≤ FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
          {(fun _ => true)} := by
  rw [gibbs_singleton, gibbs_singleton]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (peierls_weight_le n hβ σ)) _

/-- The two ground states carry equal mass — the tie a boundary field is
    introduced to break. -/
theorem gibbs_allFalse_eq_allTrue (n : ℕ) (β : ℝ) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
        {(fun _ => false)}
      = FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
          {(fun _ => true)} := by
  rw [gibbs_singleton, gibbs_singleton, isingH_allFalse_eq_allTrue]

/-- At `β > 0`, every non-constant configuration is STRICTLY less likely. -/
theorem gibbs_lt_ground (n : ℕ) (hn : 0 < n) {β : ℝ} (hβ : 0 < β) (σ : Config n)
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      < FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
          {(fun _ => true)} := by
  rw [gibbs_singleton, gibbs_singleton]
  exact ENNReal.mul_lt_mul_right (invZ_ne_zero n β) (invZ_ne_top n β)
    ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
      (peierls_weight_lt n hn hβ σ h1 h2))

/-- **THE MODE.** For `β > 0` on a box of side at least 1, the Gibbs measure
    of a single configuration attains its maximum exactly at the two constant
    configurations.

    Read the header before quoting this: it holds at EVERY positive `β`,
    including the disordered regime, so it is not evidence of a transition. -/
theorem gibbs_eq_ground_iff (n : ℕ) (hn : 0 < n) {β : ℝ} (hβ : 0 < β) (σ : Config n) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
        = FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)}
      ↔ (σ = fun _ => true) ∨ (σ = fun _ => false) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd h (ne_of_lt (gibbs_lt_ground n hn hβ σ hc.1 hc.2))
  · rintro (rfl | rfl)
    · rfl
    · exact gibbs_allFalse_eq_allTrue n β

theorem card_gibbs_maximisers (n : ℕ) (hn : 0 < n) {β : ℝ} (hβ : 0 < β) :
    (Finset.univ.filter (fun σ : Config n =>
        FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
          = FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
              {(fun _ => true)})).card = 2 := by
  classical
  have hset : (Finset.univ.filter (fun σ : Config n =>
      FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
        = FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)}))
      = {(fun _ => true), (fun _ => false)} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact gibbs_eq_ground_iff n hn hβ σ
  rw [hset, Finset.card_insert_of_notMem (by simpa using allTrue_ne_allFalse hn),
    Finset.card_singleton]

/-! ## 4. Review round 66 — the ways this could be hollow

**"§3 could be a restatement of the energy theorem with extra symbols."**
That is very nearly what it is, and the header says so: the content is
`isingH_lt_of_not_const` composed with monotonicity of `exp` and of
multiplication by `Z⁻¹`. What is NOT free is the last of those. Scaling by
`Z⁻¹` preserves strict inequality only because `Z⁻¹` is both nonzero and
finite in `ℝ≥0∞`, and both need `FiniteGibbs`'s bounds on the partition
function at `IsingFiniteVolume.isingH_bound`. Drop either and
`gibbs_lt_ground` is false as stated, because `0 < 0` and `⊤ < ⊤` both fail.
`invZ_ne_zero` and `invZ_ne_top` are named rather than inlined for that
reason.

**"`gibbs_singleton` could be the wrong reading of the measure."** It is
checked against the estate: `IsingFiniteVolume.ising_isProbability` already
establishes the same measure is a probability measure through
`FiniteGibbs.isProbabilityMeasure_gibbs`, using the identical pair of
hypotheses this file uses (`isingH_bound`, `Measure.count_ne_zero''`). The
two computations agree on what `gibbs` is.

**"The mode could be vacuous — maybe every configuration has equal mass."**
`gibbs_lt_ground` is a strict inequality at every non-constant
configuration, and `card_gibbs_maximisers` pins the maximiser set at exactly
`2` out of `IsingContourSeparation.card_config = 2^(n²)`. For `n ≥ 2` those
are different numbers, so the measure is genuinely non-uniform.

**"This could be presented as progress toward the phase transition."** It is
not, and the header says so in capitals because this is the one claim in
this file a reader might take too far. The check is not rhetorical: the
estate's own `IsingFiniteVolume.ising_no_finite_volume_breaking` proves
there is no `β_c` at finite volume, so ANY finite-volume statement that
looked like evidence of a transition would be in trouble, and this one is
not, because `gibbs_allFalse_eq_allTrue` makes the mode a flip-symmetric
pair. That is the ERRATA-34 test applied to this file's own headline rather
than asserted about someone else's. Peierls needs the minority phase to have
small TOTAL probability — a sum over exponentially many configurations,
controlled by enumerating contours. This file has no sum and no enumeration.
`MagnetisationBound` is exactly as unproved as before.
-/

end IsingContourGibbs
