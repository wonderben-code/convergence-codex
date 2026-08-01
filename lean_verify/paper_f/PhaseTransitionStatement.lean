/-
  PhaseTransitionStatement: the `_proof_004_logos` Sorry, Split
  =============================================================

  The oldest item on UNLOCK_WATCHLIST: "`_proof_004_logos.lean:200` —
  blocked on measure-level OS2 in d > 1; when it lands, the sorry SPLITS."
  Measure-level OS2 landed (`OS2MeasureLevel`). This file is the split —
  and the split's first discovery is not the one the watchlist predicted.

  **THE FINDING: the sorry'd statement is FALSE as stated, and provably
  so.** `phase_transition_symmetry_breaking` quantifies over EVERY group
  action on EVERY configuration space. Its clause (2) demands, above β_c,
  a group element g with μ_β ≠ (g • ·)_* μ_β. For the TRIVIAL action —
  which is a legal instance of the theorem's hypotheses — the pushforward
  along g is the pushforward along the identity, which is μ_β itself, for
  EVERY measure μ_β whatsoever. No interpretation of the axiomatised
  `GibbsMeasure` can make clause (2) hold. The sorry is therefore
  UNFILLABLE: no future mathematics closes it; only a corrected statement
  can. This is proven here two ways:

  1. `no_breaking_of_trivial_action` — the abstract core, axiom-free: for
     ANY β-indexed family of measures on ANY space, clause (2) fails under
     a trivial action. (Not just Gibbs measures: any family.)
  2. `phase_transition_statement_refuted` — the universally-quantified
     closure of the sorry'd theorem, with the estate's actual
     `GibbsMeasure` axiom in place, implies False. Instantiation: Ω = Unit,
     G = PUnit acting trivially, the zero Hamiltonian, the Dirac measure.
     PRECISION (adversarial review round 4, F4): the closure refuted here
     is the universe-(0,0) instance of the original `Type*`-polymorphic
     statement — a Prop cannot quantify over universes. This loses
     nothing: any fill of the sorry specializes to universe 0, so the
     refutation still proves the sorry unfillable (the review
     machine-checked this by deriving False from the sorry'd theorem
     applied verbatim).

  **The repair, stated honestly.** The physics intent (the file's own
  header names the Z₂ Ising symmetry) needs hypotheses the formal
  statement never required: a NONTRIVIAL action, an INVARIANT Hamiltonian
  — and even then the ∀-closure stays false, because symmetry breaking is
  a property of SPECIFIC models (the 1-d Ising model has invariant
  Hamiltonian, nontrivial Z₂ action, and NO phase transition). The honest
  reformulation is therefore a PREDICATE on models:

  3. `ExhibitsSymmetryBreaking` — the three-clause property as a
     definition, per model. Not claimed for anything; the claim FOR A
     GIVEN MODEL is exactly what Steps 1–5 of the original file's
     citation list (Ruelle, Gallavotti–Miracle-Solé, Peierls, Georgii,
     Wilson) would establish for that model. The citations survive the
     split unchanged; what changes is what they are citations FOR.
  4. `exhibitsSymmetryBreaking_nontrivial_action` — the positive theorem
     the refutation sharpens into: NONTRIVIALITY OF THE ACTION IS A
     NECESSARY CONDITION for the property. Any model exhibiting
     symmetry breaking in the sense of the original statement has a
     group element genuinely moving a configuration.

  **What the landed OS2 feeds — the honest account.** The watchlist
  predicted this revisit would be unlocked by measure-level OS2; the
  trigger fired as written, but the connection must not be overstated.
  Reflection positivity is the entry point of the
  Fröhlich–Simon–Spencer/chessboard route to Step 3 (Peierls) for
  REFLECTION-POSITIVE INTERACTING lattice measures. What the estate now
  has is a measure-level reflection-positive GAUSSIAN (free) field — the
  right LANGUAGE for a corrected Step-3 attempt, and strictly more than
  the covariance-level statement, but not itself an interacting Gibbs
  measure, a chessboard estimate, or an infrared bound. None of Steps 1–5
  is closed by it, and this file claims no such thing. What IS closed by
  today's work: the statement those steps were meant to assemble into is
  now known to need repair before any assembly can start.

  Part (3) of the original conjunction — existence of exponents satisfying
  Rushbrooke — was always provable and IS proven in the original file
  (`scaling_relations_satisfiable`, no sorry); nothing here touches it.

  **Axiom bookkeeping (stated so the probe surprises nobody):** the
  declarations that MENTION `GibbsMeasure` (items 2–4) necessarily carry
  the `GibbsMeasure` axiom in `#print axioms` — a statement about an
  axiomatised object cannot avoid naming it. Item 1 is axiom-clean
  ([propext, Classical.choice, Quot.sound]). NOTHING in this file depends
  on the sorry'd theorem itself: no `sorryAx` appears anywhere below.

  **DECISION FOR THE AUTHOR (recorded in PROGRESS_LOG — the campaign's
  ledger, kept with UNLOCK_WATCHLIST in the companion repository
  `codex-internal`, directory `formalisation/`; neither file lives in this
  repository):** whether to amend
  `phase_transition_symmetry_breaking` in the pre-existing file to the
  per-model predicate form (this file supplies it), or to keep the file
  frozen as a historical specification with a pointer here. Amending a
  pre-existing estate file's flagship statement is the author's call, not
  the campaign's; until ruled on, the sorry stays where it is and this
  file stands beside it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry.
  New axioms: none introduced; `GibbsMeasure` (pre-existing) referenced in
  statements about it, as documented above.
-/

import _proof_004_logos

open MeasureTheory

noncomputable section

namespace PhaseTransitionStatement

/-! ## 1. The abstract core: trivial actions never break, for ANY measures -/

/-- **No family of measures exhibits symmetry breaking under a trivial
    action.** Abstract and axiom-free: `μfam` is ANY assignment of a
    measure to each inverse temperature — Gibbs or otherwise. Clause (2)
    of the phase-transition statement fails for every candidate `β_c`,
    because the pushforward along `g • ·` is the pushforward along the
    identity. -/
theorem no_breaking_of_trivial_action
    {Ω : Type*} [MeasurableSpace Ω]
    (G : Type*) [Group G] [MulAction G Ω]
    (htriv : ∀ (g : G) (ω : Ω), g • ω = ω)
    (μfam : ℝ → Measure Ω) :
    ¬ ∃ β_c : ℝ, ∀ β > β_c, ∃ g : G,
        μfam β ≠ Measure.map (fun ω => g • ω) (μfam β) := by
  rintro ⟨β_c, h2⟩
  obtain ⟨g, hg⟩ := h2 (β_c + 1) (by linarith)
  apply hg
  have hid : (fun ω : Ω => g • ω) = id := funext fun ω => htriv g ω
  rw [hid, Measure.map_id]

/-! ## 2. The sorry'd statement, refuted -/

/-- The trivial action of the one-element group on any type. Used only as
    the counterexample instance; deliberately NOT a global instance. -/
@[reducible] def trivialAction (Ω : Type*) : MulAction PUnit Ω where
  smul _ ω := ω
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The zero Hamiltonian on the one-point configuration space. -/
def hamZero : Hamiltonian Unit where
  H _ _ := 0
  measurable _ := measurable_const

/-- **The universally-quantified closure of `phase_transition_symmetry_breaking`
    is FALSE** — with the estate's actual `GibbsMeasure` axiom in place.
    Whatever measure the axiom denotes at the counterexample instance,
    clause (2) cannot hold above any candidate `β_c`. The sorry at
    `_proof_004_logos.lean:200` is therefore unfillable as stated: it
    guards a false proposition, not a hard one. -/
theorem phase_transition_statement_refuted :
    ¬ (∀ (Ω : Type) [MeasurableSpace Ω] [TopologicalSpace Ω]
        (G : Type) [Group G] [MulAction G Ω]
        (Ham : Hamiltonian Ω) (ν : Measure Ω), IsProbabilityMeasure ν →
        ∃ (β_c : ℝ),
          (∀ β < β_c, ∀ g : G,
            GibbsMeasure Ham β ν
              = Measure.map (fun ω => g • ω) (GibbsMeasure Ham β ν)) ∧
          (∀ β > β_c, ∃ g : G,
            GibbsMeasure Ham β ν
              ≠ Measure.map (fun ω => g • ω) (GibbsMeasure Ham β ν)) ∧
          (∃ (exps : CriticalExponents), rushbrooke exps)) := by
  intro h
  letI : MulAction PUnit Unit := trivialAction Unit
  obtain ⟨β_c, -, h2, -⟩ :=
    h Unit PUnit hamZero (Measure.dirac ()) inferInstance
  exact no_breaking_of_trivial_action PUnit (fun _ _ => rfl)
    (fun β => GibbsMeasure hamZero β (Measure.dirac ())) ⟨β_c, h2⟩

/-! ## 3. The honest reformulation: a predicate on models -/

/-- **The three-clause phase-transition property, as a PREDICATE on a
    model** (Ω, G, Ham, ν) — the form the original statement should have
    taken. Establishing this property FOR A SPECIFIC MODEL is what the
    original file's citations (Ruelle; Gallavotti–Miracle-Solé; Peierls;
    Georgii; Wilson) are about; no model is claimed here. -/
def ExhibitsSymmetryBreaking
    {Ω : Type*} [MeasurableSpace Ω]
    (G : Type*) [Group G] [MulAction G Ω]
    (Ham : Hamiltonian Ω) (ν : Measure Ω) : Prop :=
  ∃ (β_c : ℝ),
    (∀ β < β_c, ∀ g : G,
      GibbsMeasure Ham β ν
        = Measure.map (fun ω => g • ω) (GibbsMeasure Ham β ν)) ∧
    (∀ β > β_c, ∃ g : G,
      GibbsMeasure Ham β ν
        ≠ Measure.map (fun ω => g • ω) (GibbsMeasure Ham β ν)) ∧
    (∃ (exps : CriticalExponents), rushbrooke exps)

/-- **Necessary condition: the action must be nontrivial.** The positive
    theorem the refutation sharpens into — any model exhibiting symmetry
    breaking has a group element that genuinely moves a configuration.
    (The converse is FALSE — the 1-d Ising model has a nontrivial action
    and no transition — which is exactly why the property must be
    per-model.) -/
theorem exhibitsSymmetryBreaking_nontrivial_action
    {Ω : Type*} [MeasurableSpace Ω]
    (G : Type*) [Group G] [MulAction G Ω]
    (Ham : Hamiltonian Ω) (ν : Measure Ω)
    (h : ExhibitsSymmetryBreaking G Ham ν) :
    ∃ (g : G) (ω : Ω), g • ω ≠ ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨β_c, -, h2, -⟩ := h
  exact no_breaking_of_trivial_action G hcon
    (fun β => GibbsMeasure Ham β ν) ⟨β_c, h2⟩

end PhaseTransitionStatement
