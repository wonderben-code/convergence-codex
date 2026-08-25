/-
  IsingWalkExpect.lean — the comparison model's magnetisation, evaluated.

  `IsingWalkIsChain` proved the box's walk model **is** a chain as an energy. That made the chain
  theorems applicable; this file applies them. The two sums over configurations — the partition
  function and the numerator — are carried across the same matching the energy was, and
  `IsingChainDecay.chain_expect` then computes the ratio.

  `box_walk_expect`: the magnetisation of the comparison model at the walk's starting site is
  **exactly** `tanh β ^ m` times the base model's correlation, where `m` is the walk's length.

  **THIS IS AN EQUALITY AND IT IS THE ARM'S ANSWER, NOT ITS SUCCESS.** `tanh β < 1` for every real
  `β`, so the right-hand side decays geometrically in the walk's length — and
  `IsingChainRouteCeiling.chain_route_insufficient` proves that a route decaying in `depth` cannot
  deliver the magnetisation bound this arm was opened for. **The arm therefore does not close the
  wall, and this file is where that becomes a computation rather than an expectation.** What it does
  give, through `IsingPathComparison.pathCoup_le_integral`, is a genuine lower bound on the box at
  every site — a weak one, decaying with distance to the boundary, but proved.

  THE BASE CORRELATION IS EVALUATED TOO, in the last section: a single site in a field has
  correlation `tanh` of that field, so `box_walk_expect_closed` reads
  **`tanh β ^ m * tanh (β * h)`** with nothing left symbolic.

  **THAT EVALUATION WAS FIRST RECORDED HERE AS "NOT ATTEMPTED" AND THE SENTENCE IS SUPERSEDED**
  (`ERRATUM 94`). It said the evaluation was a separate small statement whose cost was not claimed.
  It was small; naming a residue does not discharge it, and `PROOF_STRATEGY §7`'s second rule is to
  finish every unfinished chain. Nothing above depended on it then and nothing does now — the decay
  is settled by the `tanh β ^ m` factor alone — but the formula is now closed.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingWalkIsChain

namespace IsingWalkExpect

open Finset Real
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingPathComparison
open IsingBoxRegion IsingWalkOrder IsingChainIndex IsingChainClosedForm IsingWalkChainEnergy
open IsingChainDecay IsingPendantSite IsingGriffithsMono IsingWalkIsChain

variable {n : ℕ}

/-- Precomposing configurations with an equivalence of sites permutes the sum.

**THE REGION IS WRITTEN AS A PREDICATE AND NOT AS A `Finset` COERCION, AND THAT IS NOT COSMETIC.**
`{v // v ∈ walkSites γ m}` and `{v // Q v}` are the same type, but Lean equips them with *different*
`Fintype` instances — `Finset.Subtype.fintype` for the first, `Subtype.fintype` for the second — and
`IsingRegionSplit.partL` sums using the second. Stating this lemma over a bare `Finset` made every
later `rw` fail on an instance mismatch that no amount of `apply` or `convert` would see through.
Taking the predicate as a variable puts the instance under this lemma's own binder, where it agrees
with `partL`'s by construction. -/
theorem sum_over_region {Q : Site n → Prop} [DecidablePred Q] {A : Type*} [Fintype A]
    [DecidableEq A] (e : A ≃ {v // Q v}) (F : (A → Bool) → ℝ) :
    ∑ b : {v // Q v} → Bool, F (fun x => b (e x)) = ∑ a : A → Bool, F a :=
  Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
    (fun b => F (fun x => b (e x))) (fun a => F a) (fun _ => rfl)

/-- The chain's base model: a single site carrying the boundary field. -/
abbrev baseE (β h : ℝ) : (Fin 1 → Bool) → ℝ := fun τ => β * h * IsingTransfer2D.spin (τ 0)

theorem siteAt_zero_eq_lastSite (m : ℕ) : siteAt m 0 = lastSite (Fin 1) 0 m := by
  rw [siteAt, Equiv.symm_apply_eq, chainEquivFin_lastSite]

section
variable (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
  (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
  (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
  (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)

include hadj hinj hbnd hoff in
theorem partL_eq :
    IsingRegionSplit.partL (fun v => v ∈ walkSites γ m) (boxSet n)
        (pathCoup n β h (walkBonds γ m)) (Pin γ m)
      = basePart (chainE (baseE β h) β (0 : Fin 1) m) := by
  rw [IsingRegionSplit.partL, basePart,
      ← sum_over_region (Q := fun v => v ∈ walkSites γ m) (chainWalk γ m hinj)
        (fun σ => exp (chainE (baseE β h) β (0 : Fin 1) m σ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [eL_walk_eq_chainE β h γ m hadj hinj hbnd hoff a]

include hadj hinj hbnd hoff in
theorem numL_eq :
    IsingRegionSplit.numL (fun v => v ∈ walkSites γ m) (boxSet n)
        (pathCoup n β h (walkBonds γ m)) (Pin γ m) {γ 0}
      = baseNum (chainE (baseE β h) β (0 : Fin 1) m) (lastSite (Fin 1) 0 m) := by
  rw [IsingRegionSplit.numL, baseNum,
      ← sum_over_region (Q := fun v => v ∈ walkSites γ m) (chainWalk γ m hinj)
        (fun σ => IsingTransfer2D.spin (σ (lastSite (Fin 1) 0 m))
          * exp (chainE (baseE β h) β (0 : Fin 1) m σ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hg : IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ 0)
      = a (walkOrder γ m hinj 0) := glue_eq γ m hinj a 0
  rw [Finset.prod_singleton, hg, ← chainWalk_siteAt γ m hinj 0, siteAt_zero_eq_lastSite,
      eL_walk_eq_chainE β h γ m hadj hinj hbnd hoff a]

include hadj hinj hbnd hoff in
/-- **THE COMPARISON MODEL'S MAGNETISATION, EXACTLY.** `tanh β ^ m` times the base correlation.
An equality, not a bound — and since `tanh β < 1`, a **decaying** one. -/
theorem box_walk_expect :
    num (boxSet n) (pathCoup n β h (walkBonds γ m)) {γ 0}
        / part (boxSet n) (pathCoup n β h (walkBonds γ m))
      = tanh β ^ m * (baseNum (baseE β h) (0 : Fin 1)
          / basePart (baseE β h)) := by
  have hA : ∀ v ∈ ({γ 0} : Finset (Site n)), v ∈ walkSites γ m := by
    intro v hv
    rw [Finset.mem_singleton.mp hv]
    exact mem_walkSites γ m 0 (by omega)
  rw [IsingRegionSplit.expect_eq_left (boxSet n) (pathCoup n β h (walkBonds γ m)) (Pin γ m)
        (fun _ hi => hi) (fun i hi hz => (pathCoup_pure_of_live β h γ m i hz).resolve_left hi)
        {γ 0} hA,
      numL_eq β h γ m hadj hinj hbnd hoff, partL_eq β h γ m hadj hinj hbnd hoff, chain_expect]

end

/-! ## The base correlation, evaluated -/

theorem base_part_eq (c : ℝ) :
    basePart (fun τ : Fin 1 → Bool => c * IsingTransfer2D.spin (τ 0)) = exp c + exp (-c) := by
  rw [basePart, ← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm
      (fun b : Bool => exp (c * IsingTransfer2D.spin ((fun _ => b : Fin 1 → Bool) 0)))
      (fun τ : Fin 1 → Bool => exp (c * IsingTransfer2D.spin (τ 0))) (fun _ => rfl),
      Fintype.sum_bool]
  simp [IsingTransfer2D.spin]

theorem base_num_eq (c : ℝ) :
    baseNum (fun τ : Fin 1 → Bool => c * IsingTransfer2D.spin (τ 0)) (0 : Fin 1)
      = exp c - exp (-c) := by
  rw [baseNum, ← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool).symm
      (fun b : Bool => IsingTransfer2D.spin ((fun _ => b : Fin 1 → Bool) 0)
        * exp (c * IsingTransfer2D.spin ((fun _ => b : Fin 1 → Bool) 0)))
      (fun τ : Fin 1 → Bool => IsingTransfer2D.spin (τ 0)
        * exp (c * IsingTransfer2D.spin (τ 0))) (fun _ => rfl),
      Fintype.sum_bool]
  simp [IsingTransfer2D.spin]
  ring

/-- **THE BASE CORRELATION IS `tanh` OF THE FIELD.** A single site in a field: two configurations,
one computation. -/
theorem base_expect (c : ℝ) :
    baseNum (fun τ : Fin 1 → Bool => c * IsingTransfer2D.spin (τ 0)) (0 : Fin 1)
        / basePart (fun τ : Fin 1 → Bool => c * IsingTransfer2D.spin (τ 0)) = tanh c := by
  rw [base_num_eq, base_part_eq, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : (0 : ℝ) < exp c + exp (-c) := by positivity
  field_simp

section
variable (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
  (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
  (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
  (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)

include hadj hinj hbnd hoff in
/-- **THE COMPARISON MODEL'S MAGNETISATION IN CLOSED FORM: `tanh β ^ m * tanh (β * h)`.**
Every symbol on the right is elementary, and **every one of them is at most `1` in absolute value
while `tanh β` is strictly less than `1`** — so the whole thing decays geometrically in `m`, the
site's distance to the boundary. This is the arm's answer written out with nothing left symbolic. -/
theorem box_walk_expect_closed :
    num (boxSet n) (pathCoup n β h (walkBonds γ m)) {γ 0}
        / part (boxSet n) (pathCoup n β h (walkBonds γ m))
      = tanh β ^ m * tanh (β * h) := by
  rw [box_walk_expect β h γ m hadj hinj hbnd hoff, base_expect (β * h)]

include hadj hinj hbnd hoff in
/-- **THE ARM'S ACTUAL DELIVERABLE, AS A THEOREM RATHER THAN A SENTENCE.** Every record of this arm
has said in prose that it yields a genuine lower bound on the box; the review asked where that
theorem was, and it was nowhere. Here it is: at every site, the box's magnetisation is at least
`tanh β ^ m * tanh (β * h)`, where `m` is the length of any self-avoiding walk from the site to the
boundary.

**It is a true bound and a weak one**, decaying geometrically in `m` and so useless for the uniform
statement `MagnetisationBound` wants — which is the arm's answer, not a defect in this line. -/
theorem box_magnetisation_lower_bound (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    tanh β ^ m * tanh (β * h)
      ≤ ∫ σ, ∏ p ∈ ({γ 0} : Finset (Site n)),
          IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) := by
  rw [← box_walk_expect_closed β h γ m hadj hinj hbnd hoff]
  exact pathCoup_le_integral β h hβ hh (walkBonds γ m) {γ 0}

end

end IsingWalkExpect
