/-
  IsingBoxRegion.lean — the instantiation. The box's path-comparison model satisfies the region
  hypothesis, so **its correlations among the walk's sites are computed by the walk's own terms
  alone**, every other interaction in the box switched off.

  WHY THIS IS THE STEP THE RECORDS NAMED. `IsingRegionSplit` proved that deleting the interaction
  terms living entirely outside a region changes no correlation inside it. Every record since has
  said the same thing was left: name the walk's sites as the region and check the box's model
  against the hypothesis. That check is this file, and it is two facts.

  * **A walk's bond has both ends on the walk.** `walkBonds_ends_mem`. Immediate from the
    definition — a bond of `walkBonds γ m` is `(γ i, γ (i+1))` for some `i < m` — but it is the
    reason bonds are pure, and nothing had stated it.
  * **A field term touches one site, so it is pure whatever that site is.** No content at all, and
    it is half of the case split.

  **THE THIRD CASE IS WHY THE REGION THEOREM HAD TO BE WEAKENED FIRST.** A bond of the box that is
  *not* on the walk generally has one end on the walk and one off it — it straddles, and no purity
  argument will save it. It does not need saving: `pathCoup` gives it coupling `0`, and
  `IsingRegionSplit.expect_drop_outside_of_live` asks for purity **only of live terms**. Under the
  original statement this model failed the hypothesis outright.

  WHAT THIS IS AND IS NOT. The conclusion is an **identity between two correlations**, both in the
  finite box. It is not a bound, not a limit, and not a lower bound on anything: the right-hand
  side is a model whose terms are the walk's bonds and the fields at the walk's sites, and
  evaluating *it* — which is what `IsingChainDecay.chain_expect` would do — is not attempted here
  and its cost is not claimed (`ERRATUM 246`). **No wall moves.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingRegionSplit
import IsingPathComparison

namespace IsingBoxRegion

open Finset
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingPathComparison
open IsingGriffithsMono

variable {n : ℕ}

/-! ## 1. The sites a walk visits -/

/-- The sites a walk visits in its first `m` steps — its `m + 1` positions, not its `m` bonds. -/
def walkSites (γ : ℕ → Site n) (m : ℕ) : Finset (Site n) := (Finset.range (m + 1)).image γ

theorem mem_walkSites (γ : ℕ → Site n) (m : ℕ) (i : ℕ) (hi : i ≤ m) : γ i ∈ walkSites γ m :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- **A WALK'S BOND HAS BOTH ENDS ON THE WALK.** Immediate from the definition, and the reason the
bond terms are pure. Nothing had stated it. -/
theorem walkBonds_ends_mem (γ : ℕ → Site n) (m : ℕ) {p q : Site n}
    (hpq : (p, q) ∈ walkBonds γ m) : p ∈ walkSites γ m ∧ q ∈ walkSites γ m := by
  rw [walkBonds] at hpq
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hpq
  have him : i < m := Finset.mem_range.mp hi
  have hp : γ i = p := congrArg Prod.fst heq
  have hq : γ (i + 1) = q := congrArg Prod.snd heq
  exact ⟨hp ▸ mem_walkSites γ m i (by omega), hq ▸ mem_walkSites γ m (i + 1) (by omega)⟩

/-! ## 2. Every live term of the comparison model is pure -/

/-- **THE HYPOTHESIS, CHECKED.** A live term of the walk's comparison model either has all its
sites on the walk or none of them. Three cases and only two arguments: a live bond is one of the
walk's, so both ends are on it; a field term is a singleton, so it is pure either way. The third
case — a bond of the box that is not the walk's — really does straddle, and is excluded not by an
argument but because it is dead. -/
theorem pathCoup_pure_of_live (β h : ℝ) (γ : ℕ → Site n) (m : ℕ) (i : BoxIdx n)
    (hi : pathCoup n β h (walkBonds γ m) i ≠ 0) :
    (∀ v ∈ boxSet n i, v ∈ walkSites γ m) ∨ (∀ v ∈ boxSet n i, v ∉ walkSites γ m) := by
  rcases i with ⟨p, q⟩ | p
  · left
    by_cases hc : (p, q) ∈ walkBonds γ m ∧ adj p q
    · obtain ⟨hp, hq⟩ := walkBonds_ends_mem γ m hc.1
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact hp
      · exact (Finset.mem_singleton.mp hv') ▸ hq
    · exact absurd (by simp [pathCoup, hc]) hi
  · by_cases hp : p ∈ walkSites γ m
    · exact Or.inl fun v hv => (Finset.mem_singleton.mp hv) ▸ hp
    · exact Or.inr fun v hv => (Finset.mem_singleton.mp hv) ▸ hp

/-! ## 3. The instantiation -/

/-- **THE BOX'S COMPARISON MODEL IS COMPUTED BY THE WALK ALONE.** For any observable supported on
the walk's sites, the correlation in the model keeping the walk's bonds and the boundary field is
**equal** — not comparable, equal — to the correlation in the model that additionally switches off
every term not lying entirely on the walk. The whole of the box outside the walk, boundary fields
included, cancels.

This is an identity between two finite-box correlations. **It is not a bound and nothing is
estimated**; evaluating the right-hand side is the separate matter the records name. -/
theorem box_expect_eq_walk (β h : ℝ) (γ : ℕ → Site n) (m : ℕ) (A : Finset (Site n))
    (hA : ∀ v ∈ A, v ∈ walkSites γ m) :
    num (boxSet n) (pathCoup n β h (walkBonds γ m)) A
        / part (boxSet n) (pathCoup n β h (walkBonds γ m))
      = num (boxSet n)
          (IsingRegionSplit.keep (fun i => ∀ v ∈ boxSet n i, v ∈ walkSites γ m)
            (pathCoup n β h (walkBonds γ m))) A
        / part (boxSet n)
          (IsingRegionSplit.keep (fun i => ∀ v ∈ boxSet n i, v ∈ walkSites γ m)
            (pathCoup n β h (walkBonds γ m))) :=
  IsingRegionSplit.expect_drop_outside_of_live (boxSet n) (pathCoup n β h (walkBonds γ m))
    (pathCoup_pure_of_live β h γ m) A hA

end IsingBoxRegion
