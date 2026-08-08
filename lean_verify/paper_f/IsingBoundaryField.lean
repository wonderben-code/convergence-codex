/-
  IsingBoundaryField.lean — the Ising model with a boundary field, and
  the theorem that says why it is the right object.

  WHY. `WALLS.md` W3 (the Peierls leg) names its prerequisite in one
  line: *"What would have to exist: a finite-box Ising model with
  BOUNDARY FIELD + a formal contour decomposition. All measure-theoretic
  plumbing is done and reviewed."* This file builds the first conjunct.

  BUT THE POINT IS NOT THE DEFINITION. W3 also records the constraint
  that shapes everything on that wall:
  **`FiniteGibbs.no_finite_volume_breaking`** proves that a finite-volume
  Gibbs measure NEVER breaks a symmetry of `(H, ν)` — so any
  finite-volume statement of the form "the measure is not invariant" is
  refuted before it is written, at every β. That is ERRATA 34's lesson
  and it is why `IsingFiniteVolume` had to stop where it did.

  **A boundary field escapes that theorem, and this file proves it
  does.** The field is odd under the global flip, so `isingHB` is not
  flip-invariant, so the no-breaking theorem's hypothesis is FALSE and
  the theorem does not apply. That is the ERRATA-34 test — write the
  statement, try to refute it BEFORE proving it — passed rather than
  asserted, and it is what makes a Peierls-shaped statement well-posed
  at all.

  WHAT THIS FILE PROVES:
  1. `isBoundary`, `boundaryTerm`, **`isingHB`** — the Ising Hamiltonian
     of `IsingFiniteVolume` plus `−h ∑_{p ∈ ∂} σ_p`, the boundary field.
     `isingHB_zero` says it is the old Hamiltonian at `h = 0`, so this
     extends rather than replaces.
  2. **`boundaryTerm_flip`** — the field term is ODD under the global
     flip. Everything else follows from that one line.
  3. **`isingHB_not_flip_invariant`** and **`field_is_load_bearing`** —
     the Hamiltonian is flip-invariant at `h = 0` and is NOT at `h ≠ 0`.
     The second half is the theorem the wall needed: the hypothesis of
     `no_finite_volume_breaking` fails, so the no-breaking theorem is
     silent about this model.
  4. **`isingHB_bound`**, **`isingHB_isProbability`** — and it is still
     an honest probability measure at every β, so nothing was bought by
     breaking a hypothesis that mattered.
  5. **`allTrue_lower_energy`** — the field selects: with `h > 0` the
     all-up configuration has strictly lower energy than all-down. The
     tie the symmetric model could never break is broken.
  6. **`MagnetisationBound`** — the Peierls conclusion, as a `def`
     naming the gap in the shape `SpinQuotient.SurjectivityStatement`
     was named: uniform-in-volume magnetisation per site. NOT proved,
     and §6 says exactly what is missing.

  WHAT THIS DOES NOT DO. **It does not prove symmetry breaking, and it
  does not prove the magnetisation bound.** Contour counting — contours
  as geometric objects, the energy–entropy estimate, the `3^{|γ|}`
  bound — has no formal counterpart here or anywhere, and that is W3's
  failing step, unchanged. What has changed is that the statement one
  would try to prove is now expressible against a model that exists,
  and is not refuted the moment it is written.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingFiniteVolume
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace IsingBoundaryField

open MeasureTheory IsingFiniteVolume

/-! ## 1. The boundary, and the field term -/

/-- The boundary of the `n × n` box: any site in the first or last row
    or column. Written with `p.1.val + 1 = n` rather than
    `p.1.val = n - 1` so that no truncated subtraction appears. -/
def isBoundary {n : ℕ} (p : Site n) : Bool :=
  decide (p.1.val = 0 ∨ p.1.val + 1 = n ∨ p.2.val = 0 ∨ p.2.val + 1 = n)

/-- The corner is always on the boundary, so the boundary is never
    empty. -/
theorem isBoundary_corner (n : ℕ) (hn : 0 < n) :
    isBoundary (⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n) = true := by
  simp [isBoundary]

/-- `∑_{p ∈ ∂} σ_p`: the total spin on the boundary. -/
def boundaryTerm (n : ℕ) (σ : Config n) : ℝ :=
  ∑ p : Site n, if isBoundary p then spin (σ p) else 0

/-- **The field term is ODD under the global flip.** One line, and
    every theorem in the file is a consequence of it. -/
theorem boundaryTerm_flip (n : ℕ) (σ : Config n) :
    boundaryTerm n (flip σ) = -boundaryTerm n σ := by
  rw [boundaryTerm, boundaryTerm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : isBoundary p
  · simp only [hp, if_true]
    change spin (!(σ p)) = -spin (σ p)
    exact spin_not (σ p)
  · simp [hp]

/-- On the all-up configuration the boundary term counts the boundary,
    so it is strictly positive whenever the box is nonempty. -/
theorem boundaryTerm_allTrue_pos (n : ℕ) (hn : 0 < n) :
    0 < boundaryTerm n (fun _ => true) := by
  refine Finset.sum_pos' (fun p _ => ?_) ⟨(⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n),
    Finset.mem_univ _, ?_⟩
  · by_cases hp : isBoundary p
    · simp [hp, spin]
    · simp [hp]
  · rw [if_pos (isBoundary_corner n hn)]
    simp [spin]

/-- Crude bound: at most one unit per site. -/
theorem boundaryTerm_bound (n : ℕ) (σ : Config n) :
    |boundaryTerm n σ| ≤ (n : ℝ) * n := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p : Site n, |if isBoundary p then spin (σ p) else 0| ≤ 1 := by
    intro p
    by_cases hp : isBoundary p
    · simp [hp, abs_spin]
    · simp [hp]
  calc ∑ p : Site n, |if isBoundary p then spin (σ p) else 0|
      ≤ ∑ _p : Site n, (1 : ℝ) := Finset.sum_le_sum fun p _ => hterm p
    _ = (n : ℝ) * n := by simp [Finset.card_univ]

/-! ## 2. The Hamiltonian with a boundary field -/

/-- **The Ising Hamiltonian with a boundary field of strength `h`.** -/
def isingHB (n : ℕ) (h : ℝ) (σ : Config n) : ℝ :=
  isingH n σ - h * boundaryTerm n σ

/-- At zero field this IS the model `IsingFiniteVolume` built, so the
    file extends rather than replaces. -/
theorem isingHB_zero (n : ℕ) (σ : Config n) : isingHB n 0 σ = isingH n σ := by
  rw [isingHB, zero_mul, sub_zero]

/-- Under the flip the interaction survives and the field reverses. -/
theorem isingHB_flip (n : ℕ) (h : ℝ) (σ : Config n) :
    isingHB n h (flip σ) = isingH n σ + h * boundaryTerm n σ := by
  rw [isingHB, isingH_flip, boundaryTerm_flip]
  ring

/-! ## 3. The theorem the wall needed

`FiniteGibbs.no_finite_volume_breaking` applies to a Hamiltonian
satisfying `∀ g ω, H (g • ω) = H ω`. With a boundary field that
hypothesis is FALSE, so the theorem is silent — which is exactly what a
Peierls-shaped statement needs in order not to be refuted before it is
written.
-/

/-- **The boundary field breaks flip-invariance.** -/
theorem isingHB_not_flip_invariant (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : h ≠ 0) :
    ∃ σ : Config n, isingHB n h (flip σ) ≠ isingHB n h σ := by
  refine ⟨fun _ => true, ?_⟩
  rw [isingHB_flip, isingHB]
  intro hcon
  have hB := boundaryTerm_allTrue_pos n hn
  have : h * boundaryTerm n (fun _ => true) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hh h0
  · exact absurd h0 (ne_of_gt hB)

/-- **The field is exactly what escapes `no_finite_volume_breaking`.**
    At `h = 0` the hypothesis holds and the no-breaking theorem applies
    (which is `IsingFiniteVolume.ising_no_finite_volume_breaking`); at
    `h ≠ 0` it fails. Stated as one theorem because the contrast is the
    content. -/
theorem field_is_load_bearing (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : h ≠ 0) :
    (∀ σ : Config n, isingHB n 0 (flip σ) = isingHB n 0 σ)
      ∧ (∃ σ : Config n, isingHB n h (flip σ) ≠ isingHB n h σ) := by
  refine ⟨fun σ => ?_, isingHB_not_flip_invariant n hn h hh⟩
  rw [isingHB_zero, isingHB_zero, isingH_flip]

/-- The same statement in the ℤ₂-action language the no-breaking theorem
    is phrased in: its invariance hypothesis is false for this
    Hamiltonian. -/
theorem zflip_hypothesis_fails (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : h ≠ 0) :
    ¬ (∀ (g : Multiplicative (ZMod 2)) (σ : Config n),
        isingHB n h (zflip n g σ) = isingHB n h σ) := by
  intro hinv
  obtain ⟨σ, hσ⟩ := isingHB_not_flip_invariant n hn h hh
  refine hσ ?_
  have := hinv (Multiplicative.ofAdd (1 : ZMod 2)) σ
  rwa [show zflip n (Multiplicative.ofAdd (1 : ZMod 2)) σ = flip σ by
    simp [zflip]] at this

/-! ## 4. It is still an honest probability measure

Breaking a hypothesis is only progress if nothing else broke with it.
-/

theorem isingHB_bound (n : ℕ) (h : ℝ) (σ : Config n) :
    |isingHB n h σ| ≤ ((n : ℝ) * n) ^ 2 + |h| * ((n : ℝ) * n) := by
  rw [isingHB]
  refine le_trans (abs_sub _ _) ?_
  have h1 := isingH_bound n σ
  have h2 : |h * boundaryTerm n σ| ≤ |h| * ((n : ℝ) * n) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (boundaryTerm_bound n σ) (abs_nonneg h)
  linarith

theorem measurable_isingHB (n : ℕ) (h : ℝ) : Measurable (isingHB n h) :=
  measurable_of_countable _

/-- **The boundary-field Gibbs measure is a probability measure at every
    β and every field strength.** -/
theorem isingHB_isProbability (n : ℕ) (h β : ℝ) :
    IsProbabilityMeasure
      (FiniteGibbs.gibbs β (isingHB n h) (Measure.count : Measure (Config n))) :=
  FiniteGibbs.isProbabilityMeasure_gibbs β (isingHB_bound n h)
    Measure.count Measure.count_ne_zero''

/-! ## 5. The field selects

The symmetric model cannot prefer up to down — that is the whole content
of `no_finite_volume_breaking`. With a positive field it can, and does.
-/

/-- **With `h > 0` the all-up configuration has strictly lower energy
    than all-down.** -/
theorem allTrue_lower_energy (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 < h) :
    isingHB n h (fun _ => true) < isingHB n h (fun _ => false) := by
  have hflip : (fun _ => false : Config n)
      = IsingFiniteVolume.flip (fun _ => true) := by
    funext p; simp [IsingFiniteVolume.flip]
  rw [hflip, isingHB_flip, isingHB]
  have hB := boundaryTerm_allTrue_pos n hn
  nlinarith [hB, hh]

/-! ## 6. The Peierls conclusion, as a statement rather than a theorem

The magnetisation per site, bounded below uniformly in the box size, is
what a Peierls argument delivers and what "symmetry breaking survives
the thermodynamic limit" means in finite-volume language. It is stated
here as a `def` — the same device `SpinQuotient` used for the
surjectivity gap — so that its absence is an object rather than a
sentence in a header.

**WHAT IS MISSING IS CONTOUR COMBINATORICS**, unchanged from W3: contours
as geometric objects, the energy–entropy estimate, the `3^{|γ|}` bound
on the number of contours of a given length, and the surgery on
configurations that turns a contour bound into a magnetisation bound.
None of it exists formally, here or in Mathlib, and none of it is
attempted.
-/

/-- Total spin. -/
def magnetisation (n : ℕ) (σ : Config n) : ℝ := ∑ p : Site n, spin (σ p)

theorem magnetisation_flip (n : ℕ) (σ : Config n) :
    magnetisation n (flip σ) = -magnetisation n σ := by
  rw [magnetisation, magnetisation, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact spin_not (σ p)

/-- The boundary-field Gibbs measure. -/
noncomputable def isingMeasure (n : ℕ) (h β : ℝ) : Measure (Config n) :=
  FiniteGibbs.gibbs β (isingHB n h) Measure.count

/-- **The Peierls conclusion, named and NOT proved.** At inverse
    temperature `β` and field `h`, the magnetisation per site is bounded
    below by `m` uniformly in the box size. -/
def MagnetisationBound (β h m : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β)

/-- How to review a `def` that states a gap: it cannot be tested by
    proving it, so test that it says what it is meant to. At `m ≤ 0` the
    statement is weak but not vacuous, and the bound scales with the
    VOLUME — which is what "per site" means and what makes it a
    thermodynamic statement rather than a finite-box accident. -/
theorem magnetisationBound_scales (β h m : ℝ) (hm : MagnetisationBound β h m)
    (n : ℕ) (hn : 0 < n) :
    m * ((n : ℝ) * n) ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β) :=
  hm n hn

/-! ## 7. Review round 36 — that §3 is a real escape

Three ways this file could be saying nothing.

* If the boundary were empty the field term would be zero and §3 would
  be false. It is not: the corner is always a boundary site.
* If the field term were even rather than odd under the flip, breaking
  invariance would need a different mechanism and §3's proof would be
  wrong. It is odd, and `boundaryTerm_flip` is the whole argument.
* If `isingHB` were unbounded the Gibbs measure would not exist and §4
  would be vacuous. It is bounded, with the bound exhibited.

And one check that the escape is not bought too cheaply: the model must
still reduce to the reviewed one at `h = 0`, which `isingHB_zero` gives
definitionally rather than by a fresh argument.
-/

theorem boundary_nonempty (n : ℕ) (hn : 0 < n) :
    ∃ p : Site n, isBoundary p = true :=
  ⟨⟨⟨0, hn⟩, ⟨0, hn⟩⟩, isBoundary_corner n hn⟩

/-- **The oddness is not an artefact of the all-up configuration:** it
    holds pointwise, for every configuration, which is what makes §3
    work at a single witness. -/
theorem boundaryTerm_flip_all (n : ℕ) :
    ∀ σ : Config n, boundaryTerm n (flip σ) = -boundaryTerm n σ :=
  boundaryTerm_flip n

/-- **At `h = 0` the no-breaking theorem still bites**, so §3's escape is
    genuinely due to the field and not to some feature of `isingHB`'s
    definition. -/
theorem zero_field_still_blocked (n : ℕ) :
    ¬ ∃ β_c : ℝ, ∀ β > β_c, ∃ g : Multiplicative (ZMod 2),
        FiniteGibbs.gibbs β (isingHB n 0) (Measure.count : Measure (Config n))
          ≠ Measure.map (fun σ => zflip n g σ)
              (FiniteGibbs.gibbs β (isingHB n 0) Measure.count) := by
  have hEq : isingHB n 0 = isingH n := by
    funext σ; exact isingHB_zero n σ
  rw [hEq]
  exact IsingFiniteVolume.ising_no_finite_volume_breaking n

end IsingBoundaryField
