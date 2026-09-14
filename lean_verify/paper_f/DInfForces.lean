/-
  DInfForces.lean — Lawvere's fixed-point theorem in the category of ω-CPOs,
  and the estate's own reflexive domain made to FORCE what the spine says it
  forces.

  WHY THIS FILE EXISTS — SPINE LINKS L1 AND L2. Link L2's headline is that a
  non-trivial reflexive domain exists AND forces (i) a fixed point for every
  endomorphism, (ii) a unique internal representation of every endomorphism,
  (iii) inexhaustibility. The estate proved the two halves under DIFFERENT
  hypotheses and never joined them: `CanonicalTower.dInfExists_orderIso` builds
  a non-trivial `D` with `D ≃o (D →𝒄 D)` (the Scott reading, 2026-08-12), while
  every "forces" theorem — `ReflexiveDomainFP`, `root_equation_fixed_point`,
  `GToECoherence` — takes `φ : D ≃ (D → D)`, the FULL function space, whose only
  models are nonempty subsingletons (`ReflexiveDomainObstruction.isSetReflexive_iff`,
  machine-checked). So the forces half was true of a trivial `D`, and the
  non-trivial `D` had no forces theorem over it. **The 24-link recompute's
  auditors for L1 and L2 named this same theorem independently as the next step
  on each link**, and this file is it.

  WHAT THIS FILE PROVES.

  1. `OrderIso.map_ωSup'`, **`orderIso_ωScottContinuous`** — an order isomorphism
     between ω-CPOs preserves `ωSup`, hence is ω-Scott-continuous. Absent from
     Mathlib (`grep -rn OrderIso Mathlib/Order/OmegaCompletePartialOrder.lean`
     is empty) and needed because the reflexive equivalence must be applied
     INSIDE a continuous map.
  2. **`lawvere_domainReflexive`** — Lawvere in the CCC of ω-CPOs: if
     `e : D ≃o (D →𝒄 D)` then every CONTINUOUS `g : D →𝒄 D` has a fixed point.
     The diagonal `d ↦ g (e d d)` is continuous (`ContinuousHom.Prod.apply` on
     the pair `(e d, d)`), so it is `e a` for some `a`, and `e a a` is fixed. This
     is `Function.exists_fixed_point_of_surjective` moved from `Type` to ω-CPOs,
     where the point-surjection is only onto the continuous maps.
  3. `unique_representation` — clause (ii) for any such `e`: `∃! d, e d = f`.
  4. **`dInf_forces`** — the headline as ONE statement, at the estate's own
     witness `Limit (canonical propPt)`: non-trivial, with `e : D ≃o (D →𝒄 D)`
     such that every continuous endomorphism has a fixed point, every continuous
     endomorphism is `e d` for exactly one `d`, and there is no surjection
     `D → (D → Prop)`.
  5. **`subsingleton_of_surjective_eval`** — the OTHER half of the obstruction,
     which the estate had recorded in prose and never proved: a point-surjective
     `eval : D → D → D` (this is `LawvereFixedPoint.SelfRepresentable D`
     unfolded; that root module is not importable from `paper_f`) forces `D` to
     be a subsingleton — because Lawvere gives every self-map a fixed point,
     and a two-element swap has none. So the set-theoretic Lawvere the estate
     has had since July was true of trivial domains only, and §2 is the version
     with content.

  WHAT THIS DOES NOT DO, AND WHAT IS THE AUTHOR'S. **The literal headline
  `D ≃ (D → D)` is refuted, not proved** — `isSetReflexive_iff` is the theorem
  — and whether L2's published statement is restated to the continuous function
  space is the reflexive-domain decision under `ASSUMPTIONS_LEDGER`'s DECISIONS
  NEEDED; this file proves the continuous reading and re-rates nothing. **Clause
  (iii) is Cantor for every type** (`Function.cantor_surjective`) and is stated
  here so the headline's three clauses all appear at the witness, but it is not
  *forced by* reflexivity in any sense the theorem carries: it holds for the
  empty type. **No naturality, canonicity or uniqueness of `e`** is claimed;
  `CanonicalTower`'s own header says the same of the bilimit.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import CanonicalTower

namespace DInfForces

open OmegaCompletePartialOrder CanonicalTower InverseLimitCPO

variable {D : Type*} [OmegaCompletePartialOrder D]

/-! ## 1. An order isomorphism of ω-CPOs is Scott-continuous -/

/-- An order isomorphism carries `ωSup` to `ωSup`. -/
theorem OrderIso.map_ωSup' {E : Type*} [OmegaCompletePartialOrder E] (e : D ≃o E)
    (c : Chain D) : e (ωSup c) = ωSup (c.map ⟨e, e.monotone⟩) := by
  apply le_antisymm
  · rw [← e.le_symm_apply]
    refine ωSup_le_iff.2 fun i => ?_
    rw [e.le_symm_apply]
    exact le_ωSup_of_le i le_rfl
  · refine ωSup_le_iff.2 fun i => ?_
    exact e.monotone (le_ωSup_of_le i le_rfl)

/-- **An order isomorphism between ω-CPOs is ω-Scott-continuous.** Not in
Mathlib: `OrderIso` does not occur in `Order/OmegaCompletePartialOrder.lean`. -/
theorem orderIso_ωScottContinuous {E : Type*} [OmegaCompletePartialOrder E]
    (e : D ≃o E) : ωScottContinuous e :=
  ωScottContinuous_iff_monotone_map_ωSup.2 ⟨e.monotone, fun c => OrderIso.map_ωSup' e c⟩

/-! ## 2. Lawvere in the CCC of ω-CPOs -/

/-- The diagonal `d ↦ (e d, d)` as a continuous map into the product. -/
noncomputable def diagPair (e : D ≃o (D →𝒄 D)) : D →𝒄 (D →𝒄 D) × D :=
  ContinuousHom.ofFun (fun d => ((e d : D →𝒄 D), d))
    (Prod.ωScottContinuous.prodMk (orderIso_ωScottContinuous e) ωScottContinuous.id)

/-- **LAWVERE, FOR CONTINUOUS ENDOMORPHISMS.** If `D` is reflexive in the
Scott sense, every continuous self-map has a fixed point. The witness is
`e a a`, where `e a` is the continuous map `d ↦ g (e d d)`. -/
theorem lawvere_domainReflexive (e : D ≃o (D →𝒄 D)) (g : D →𝒄 D) :
    ∃ x : D, g x = x := by
  let h : D →𝒄 D := g.comp (ContinuousHom.comp ContinuousHom.Prod.apply (diagPair e))
  obtain ⟨a, ha⟩ := e.surjective h
  refine ⟨e a a, ?_⟩
  have h1 : h a = g (e a a) := by
    simp [h, diagPair, ContinuousHom.comp_apply]
  calc g (e a a) = h a := h1.symm
    _ = e a a := by rw [ha]

/-- Clause (ii): every continuous endomorphism is `e d` for exactly one `d`. -/
theorem unique_representation (e : D ≃o (D →𝒄 D)) (f : D →𝒄 D) : ∃! d : D, e d = f :=
  ⟨e.symm f, e.apply_symm_apply f, fun _ hd => e.injective (hd.trans (e.apply_symm_apply f).symm)⟩

/-- Clause (iii) is Cantor, and holds for EVERY type — stated so that the three
clauses can be assembled at the witness, and named as what it is. -/
theorem no_surjection_to_powerset (X : Type*) :
    ¬ ∃ h : X → X → Prop, Function.Surjective h :=
  fun ⟨h, hs⟩ => Function.cantor_surjective h hs

/-! ## 3. The headline, as one statement, at the estate's witness -/

/-- **THE REFLEXIVE DOMAIN FORCES WHAT THE SPINE SAYS IT FORCES**, for the
continuous reading, at `Limit (canonical propPt)`: non-trivial, reflexive by an
order isomorphism, every continuous endomorphism has a fixed point and a unique
internal name, and there is no surjection onto the powerset. -/
theorem dInf_forces :
    ∃ (D : Type) (_ : OmegaCompletePartialOrder D), ¬ Subsingleton D ∧
      ∃ e : D ≃o (D →𝒄 D),
        (∀ g : D →𝒄 D, ∃ x : D, g x = x) ∧
        (∀ f : D →𝒄 D, ∃! d : D, e d = f) ∧
        ¬ ∃ h : D → D → Prop, Function.Surjective h := by
  obtain ⟨e⟩ := bilimit_orderIso propPt
  exact ⟨Limit (canonical propPt), inferInstance,
    not_subsingleton_limit propPt not_subsingleton_prop, e,
    lawvere_domainReflexive e, unique_representation e, no_surjection_to_powerset _⟩

/-! ## 4. And the set-theoretic Lawvere was vacuous, as a theorem -/

/-- **A point-surjective `eval : D → D → D` forces `D` to be a subsingleton.**
This is `SelfRepresentable D` (the root module `LawvereFixedPoint`) unfolded.
The estate's `subsingleton_of_setReflexive` has the EQUIVALENCE form; the
surjection form — the hypothesis the July Lawvere theorems actually take — was
recorded in prose and never proved. Lawvere itself proves it: every self-map
has a fixed point, and on two distinct points the swap has none. -/
theorem subsingleton_of_surjective_eval {X : Type*} (eval : X → X → X)
    (h : Function.Surjective eval) : Subsingleton X := by
  classical
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  obtain ⟨z, hz⟩ := Function.exists_fixed_point_of_surjective eval h
    (fun d => if d = x then y else x)
  by_cases hzx : z = x
  · subst hzx
    simp only [if_true] at hz
    exact hxy hz.symm
  · rw [if_neg hzx] at hz
    exact hzx hz.symm

/-- The two readings side by side: the Scott-reflexive witness is NOT a
subsingleton, so §2's fixed-point theorem has content there, where the
set-theoretic one (§4) cannot. -/
theorem dInf_not_subsingleton : ¬ Subsingleton (Limit (canonical propPt)) :=
  not_subsingleton_limit propPt not_subsingleton_prop

/-! ## 5. Review round 74 — the ways this could be hollow

**"§2 is Mathlib's theorem with a coercion."** The Mathlib theorem quantifies
over ALL maps `D → D → B` and needs the point-surjection onto all of `D → B`;
that hypothesis is inconsistent with non-triviality (§4). §2's hypothesis is a
surjection onto the CONTINUOUS maps only, so the diagonal `d ↦ g (e d d)` has
to be shown continuous before it can be hit — §1 and `diagPair` are that step,
and they are the whole difference between a theorem with models and one
without.

**"§1 must be in Mathlib."** Probed: no `OrderIso` in
`Order/OmegaCompletePartialOrder.lean`; `OrderIso.map_iSup` exists for complete
lattices, which an ω-CPO is not. Ten lines here.

**"§3 re-rates L2."** It does not. The headline's literal `D ≃ (D → D)` is
refuted by `isSetReflexive_iff`; §3 proves the continuous reading at the
witness. Whether the published headline is RESTATED to that reading is the
author's decision, filed under DECISIONS NEEDED, and the recompute of `SPINE.md`
will rate against whichever statement the author owns.

**"Clause (iii) is dressed up."** It is Cantor for every type and the docstring
says so. It is included because the headline lists three clauses and a reader
should find all three at the witness; it is NOT claimed to follow from
reflexivity.

**"§4 was already there."** The equivalence form was
(`ReflexiveDomainObstruction.subsingleton_of_setReflexive`). The surjection
form is the hypothesis `LawvereFixedPoint`'s theorems actually carry, and the
L1 audit found it stated in `TRUE_LEDGER` and `ASSUMPTIONS_LEDGER` prose and in
no Lean file; `grep -rn SelfRepresentable` returns only its own module. Now it
is a theorem.
-/

end DInfForces
