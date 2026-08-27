import LatticeTruncatedExplicit
import LatticeSplitFourCheck
import LatticeFourPointClustering

/-!
# The four-point clustering estimate, re-derived through the general machinery

`LatticeTruncatedExplicit` ended with the constant `2` at four test functions and said plainly what
that did **not** amount to: its statement is about four **arbitrary** test functions, while
`LatticeFourPointClustering.connected_smeared_le` is about the pattern `(f, f, g, g)`, so **the
agreement of the two constants was something a reader checked by eye and not something the estate
proved.** This proves it.

The instantiation is `a = ![f, f, g, g]` and `S = {0, 1}`, and the three product identities it needs
already exist — `LatticeSplitFourCheck` built them for the exact-value check at the same instance.
**That is why this file is short, and it is worth saying**: the work was done two units before
anybody knew what it would be used for.

## What is proved

* **`connected_smeared_le_via_general`** — the general chain, at `![f, f, g, g]` and `S = {0, 1}`,
  bounds **exactly the quantity `connected_smeared_le` bounds** — `⟨f²g²⟩ − ⟨f²⟩⟨g²⟩` — by
  `2·(C²rᴺ/m²)²`. Same constant, same power of the decay rate; `C²` where that estimate has
  `‖f‖₁·‖g‖₁`, and **that substitution is now the entire difference between the two routes**;
* **`connected_smeared_le_via_general_abs`** — and the general route bounds the **modulus**, where
  `connected_smeared_le` bounds the value. At order four this wins nothing, because
  `LatticeIsserlisSmeared.connected_smeared` makes the quantity a square; it is recorded so that the
  two-sided form is not mistaken for an improvement.

## What this is NOT

**It is not a proof that the general route is as strong as the special one.** It is not: at
`‖f‖₁ ≠ ‖g‖₁` the special estimate is strictly better, because `‖f‖₁·‖g‖₁ < C²` for any common
bound `C`. What is proved is that the two bound the same quantity with the same constant and the
same rate, so **the only remaining difference is the one that has been named for three units.**

**And it is not OS4**, for the reason every file on this line carries: finite volume, and a constant
that grows faster than geometrically in the order.
-/

namespace LatticeFourPointViaGeneral

open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay
open LatticeIsserlisSmeared LatticeSplitFourCheck LatticeTruncatedExplicit

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The instantiation

Everything here is `truncated_abs_le_four` at `a = ![f, f, g, g]` and `S = {0, 1}`, with the three
hypotheses discharged by `fin_cases` and the two sides of the integral rewritten by
`LatticeSplitFourCheck`'s product identities. -/

/-- **THE GENERAL CHAIN, ON `connected_smeared_le`'s OWN QUANTITY.** Fifteen files from
`PairingSplit` bound `|⟨f²g²⟩ − ⟨f²⟩⟨g²⟩|` by `2·(C²rᴺ/m²)²`. -/
theorem connected_smeared_le_via_general_abs (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {N : ℕ} (f g : EuclideanSpace ℝ V) {C : ℝ} (hC0 : 0 ≤ C)
    (hf : ∑ p, |f.ofLp p| ≤ C) (hg : ∑ p, |g.ofLp p| ≤ C)
    (hsep : ∀ p q, f.ofLp p ≠ 0 → g.ofLp q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |(∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))|
      ≤ 2 * (C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 := by
  classical
  have hC : ∀ i : Fin 4, ∑ p, |((![f, f, g, g] i : EuclideanSpace ℝ V)).ofLp p| ≤ C := by
    intro i; fin_cases i <;> simpa using ‹_›
  have hsep' : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)), ∀ p q,
      ((![f, f, g, g] i : EuclideanSpace ℝ V)).ofLp p ≠ 0 →
      ((![f, f, g, g] j : EuclideanSpace ℝ V)).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q := by
    -- `simp_all` kills the branches the two memberships forbid and closes the four that survive
    -- with `hsep` itself; a trailing `exact hsep p q hp hq` was written first and the build
    -- reported it dead, so it was removed rather than left to look like part of the proof.
    intro i hi j hj p q hp hq
    fin_cases i <;> fin_cases j <;> simp_all
  have h := truncated_abs_le_four hm hΔ ![f, f, g, g] ({0, 1} : Finset (Fin 4)) (by decide)
    hC0 hC hsep'
  rw [show (fun ω => ∏ i : Fin 4, (inner ℝ (![f, f, g, g] i) ω : ℝ))
      = fun ω => (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_fin_four f f g g ω]; ring,
    show (fun ω => ∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] x) ω : ℝ)) = fun ω => (inner ℝ f ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_lower_two f f g g ω]; ring,
    show (fun ω => ∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] y) ω : ℝ)) = fun ω => (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_upper_two f f g g ω]; ring] at h
  exact h

/-- The same statement without the modulus, which is the shape
`LatticeFourPointClustering.connected_smeared_le` has, so that the two can be read side by side. -/
theorem connected_smeared_le_via_general (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {N : ℕ} (f g : EuclideanSpace ℝ V) {C : ℝ} (hC0 : 0 ≤ C)
    (hf : ∑ p, |f.ofLp p| ≤ C) (hg : ∑ p, |g.ofLp p| ≤ C)
    (hsep : ∀ p q, f.ofLp p ≠ 0 → g.ofLp q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      ≤ 2 * (C * C * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 :=
  (le_abs_self _).trans (connected_smeared_le_via_general_abs hm hΔ f g hC0 hf hg hsep)

end LatticeFourPointViaGeneral
