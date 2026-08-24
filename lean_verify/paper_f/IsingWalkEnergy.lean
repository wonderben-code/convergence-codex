/-
  IsingWalkEnergy.lean — the two idioms joined, and the walk's model carried across.

  WHY. This arm has been written in two notations that never met. The box side says `part S J` and
  `num S J A`: a model is a family of interaction terms, each a coupling and a set of sites. The
  chain side — `IsingPendantSite`, `IsingChainDecay`, and `chain_expect`, which is what the arm is
  aimed at — says `basePart E` and `baseNum E v₀`: a model is a function of the configuration.
  **Nothing in the estate related the two**, which was checked by grep before this file was written
  rather than recalled: `basePart` occurs in four files and `part` in none of them.

  * §1 `part_eq_basePart`, `num_eq_baseNum`, `expect_eq`: the bridge. It is short, and it is short
    because the two notations really do describe the same object — the interaction-term model's
    energy IS the configuration function. The only content is `Finset.prod_singleton`, and the
    restriction to a **single site** is not laziness: `num` was always stated for a `Finset` of
    sites and `baseNum` for one site, so the singleton case is exactly where they meet, and a
    product of two or more spins has no counterpart to be carried to.
  * §2 `box_expect_eq_walk_energy`: the box's path-comparison correlation at one walk site, written
    in the chain side's own notation. This is `IsingBoxRegion.box_expect_eq_walk` read through §1.

  WHAT REMAINS. `chain_expect` computes a correlation over `IsingChainDecay.chainSite`, whose sites
  are built by iterated `Option`. Reading the walk's model as one of those needs an equivalence
  between the walk's sites and that tower. Relating the two, and then exhibiting the walk's energy
  as a `chainE`, is not attempted here and its cost is not claimed (`ERRATUM 246`).

  **THE PARAGRAPH THAT STOOD HERE WAS WRONG AND IS QUOTED SO THE CORRECTION CAN BE CHECKED**
  (`ERRATUM 94`, `ERRATUM 258`). It said the next step was that *"the walk to visit `m + 1` distinct
  sites — and `IsingBoxWalk.exists_boundary_walk` does not say that … injectivity is not among its
  five clauses"*. **It is the fourth clause.** That theorem's docstring calls the walk
  *self-avoiding* in its first line and names clause four as "what makes it a path rather than a
  walk". The absence was asserted from memory against a statement written two units earlier and
  never re-read. `IsingWalkOrder` is the fold-back and it folds back by **using** the clause:
  `card_walkSites` counts the sites and `walkOrder` indexes them **in the walk's own order**, which
  is the object the chain actually needs and which a bare cardinality bijection would not give.

  **No wall moves. Nothing here is a bound on anything** — §2 is an identity between two
  correlations in the finite box, in a new notation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingBoxRegion
import IsingChainDecay

namespace IsingWalkEnergy

open Finset Real
open IsingTransfer2D IsingGriffithsMono IsingPendantSite
open IsingFiniteVolume IsingBoxInteraction IsingPathComparison IsingBoxRegion

/-! ## 1. The two idioms are the same object -/

variable {V : Type*} [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]

/-- The energy of an interaction-term model, read as a function of the configuration. -/
def energy (S : I → Finset V) (J : I → ℝ) (σ : V → Bool) : ℝ :=
  ∑ i : I, J i * ∏ v ∈ S i, IsingTransfer2D.spin (σ v)

theorem part_eq_basePart (S : I → Finset V) (J : I → ℝ) : part S J = basePart (energy S J) := rfl

theorem num_eq_baseNum (S : I → Finset V) (J : I → ℝ) (v₀ : V) :
    num S J {v₀} = baseNum (energy S J) v₀ :=
  Finset.sum_congr rfl fun σ _ => by simp only [Finset.prod_singleton, energy]

/-- **THE BRIDGE.** A one-site correlation is the same number in either notation. -/
theorem expect_eq (S : I → Finset V) (J : I → ℝ) (v₀ : V) :
    num S J {v₀} / part S J = baseNum (energy S J) v₀ / basePart (energy S J) := by
  rw [part_eq_basePart, num_eq_baseNum]

/-- **AND THE BRIDGE IMMEDIATELY PAYS FOR ITSELF.** `IsingChainDecay.abs_baseNum_div_le` says a
one-site correlation of a bare-energy model lies between `-1` and `1`. Read through §1 that becomes
a statement about **every interaction-term model in the estate** — any index type, any couplings,
any site sets — and nothing had said it. It is exactly the kind of fact whose absence is invisible
until a bound needs it: a correlation is an average of `±1`, so of course it lies in `[-1, 1]`, and
"of course" is not a proof. -/
theorem abs_expect_le_one (S : I → Finset V) (J : I → ℝ) (v₀ : V) :
    |num S J {v₀} / part S J| ≤ 1 := by
  rw [expect_eq]
  exact IsingChainDecay.abs_baseNum_div_le (energy S J) v₀

/-! ## 2. The walk's model, in the chain side's notation -/

variable {n : ℕ}

/-- **THE BOX'S COMPARISON CORRELATION AT A WALK SITE, WRITTEN THE WAY THE CHAIN THEOREMS ARE.**
`IsingBoxRegion.box_expect_eq_walk` read through §1. Both sides are still correlations in the finite
box and **nothing is estimated**; only the notation has changed, which is the point — the chain
results cannot be applied to something written the other way. -/
theorem box_expect_eq_walk_energy (β h : ℝ) (γ : ℕ → Site n) (m : ℕ) (p : Site n)
    (hp : p ∈ walkSites γ m) :
    num (boxSet n) (pathCoup n β h (walkBonds γ m)) {p}
        / part (boxSet n) (pathCoup n β h (walkBonds γ m))
      = baseNum (energy (boxSet n)
          (IsingRegionSplit.keep (fun i => ∀ v ∈ boxSet n i, v ∈ walkSites γ m)
            (pathCoup n β h (walkBonds γ m)))) p
        / basePart (energy (boxSet n)
          (IsingRegionSplit.keep (fun i => ∀ v ∈ boxSet n i, v ∈ walkSites γ m)
            (pathCoup n β h (walkBonds γ m)))) := by
  rw [box_expect_eq_walk β h γ m {p} (fun v hv => (Finset.mem_singleton.mp hv) ▸ hp),
      expect_eq]

end IsingWalkEnergy
