import LatticeTruncatedNorms

/-!
# Clustering with a tolerance instead of a rate, at every order

Every estimate on this line names a rate: `r^N` at a fixed graph. The statement an
infinite-volume argument needs is the other one — **a separation `N` produced from the degree
bound, the mass, an `ℓ¹` bound, the order and the tolerance, BEFORE the vertex type, the graph or
the test functions are mentioned** — because that is what says the rate does not degrade as the
graph grows.

`GreenClustering.exists_clustering_uniform` has that shape for the generating functional and
`LatticeFourPointClustering.exists_four_point_clustering_uniform` for four test functions. **This
has it at every order**, from `LatticeTruncatedSharp.truncated_abs_le_sq`.

## What is proved

* **`exists_truncated_clustering_uniform`** — for every `Δ`, `m ≠ 0`, `ℓ¹` bound `C`, order `k`
  and tolerance `ε > 0` there is an `N` such that on ANY finite graph of degree at most `Δ`, for
  ANY `k` test functions of `ℓ¹` norm at most `C` split into an even-sized near group whose
  support is `N` steps from the rest, the truncated correlation is at most `ε` in modulus;
* **`exists_four_point_clustering_uniform_two_ways`** — **the check.** The general statement at
  `k = 4`, `S = {0, 1}` and `a = ![f, f, g, g]` is
  `LatticeFourPointClustering.exists_four_point_clustering_uniform`, whose own proof goes through
  `GreenClustering.cross_abs_le` and no pairing at all. **A wrong quantifier order, a wrong split
  or a wrong instantiation would each break it**, and the `N` the general theorem produces is not
  the `N` that one produces.

## What is NOT here

**The limit itself.** This supplies the hypothesis a tightness argument consumes; it is not that
argument, and nothing here takes a limit of measures or mentions an infinite graph. OS4's two
remaining pieces are unchanged. **Not costed** (`ERRATUM 194`).

**And the constant is still super-geometric in `k`.** `N` depends on the order, and it must: the
number of crossing pairings grows faster than geometrically, so a tolerance held at order `k`
says nothing about order `k + 2`. Summing over orders is a cluster expansion and none of it is
here.
-/

namespace LatticeTruncatedUniform

open Equiv Function Involutions PairingSplit PairingCluster
open LatticeTruncatedSharp LatticeTruncatedDecay LatticeFourPointViaGeneral
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay LatticeIsserlisSmeared

universe u

/-! ## 1. The tolerance form -/

/-- **CLUSTERING WITH A TOLERANCE, AT EVERY ORDER.** `N` is produced from `Δ`, `m`, `C`, `k` and
`ε` alone. **The whole content is that the quantifiers come in that order**: the graph, the vertex
type and the test functions are all introduced after `N` is fixed. -/
theorem exists_truncated_clustering_uniform {m : ℝ} (hm : m ≠ 0) (Δ : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ (a : Fin k → EuclideanSpace ℝ W) (S : Finset (Fin k)),
        Even S.card → (∀ i, ∑ p, |(a i).ofLp p| ≤ C) →
        (∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
          ¬ H.Reachable p q ∨ N ≤ H.dist p q) →
        |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField H m)
            - (∫ ω, (∏ x : {x : Fin k // x ∈ S},
                (inner ℝ (a x) ω : ℝ)) ∂(gaussianField H m))
              * (∫ ω, (∏ y : {y : Fin k // y ∉ S},
                  (inner ℝ (a y) ω : ℝ)) ∂(gaussianField H m))|
          ≤ ε := by
  classical
  -- everything the bound carries except the separation, fixed before any graph exists
  set B : ℝ := (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
      * ((C * C) ^ 2 * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 2)) with hBdef
  -- `|B|` and not `B`, because `C` is a bare parameter: at `C < 0` the hypothesis below is
  -- unsatisfiable but `B` is still a real number, and `Real.sqrt` of a negative is `0`.
  have hden : (0 : ℝ) < |B| + 1 := by positivity
  set δ : ℝ := Real.sqrt (ε / (|B| + 1)) with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨N, hN⟩ := GreenDecay.exists_pow_lt hm Δ hδ
  refine ⟨N, fun W _ _ H _ hdeg a S hS hC hsep => ?_⟩
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by
    have := decayRate_nonneg Δ (m := m) hm
    positivity
  have hKδ : decayRate Δ m ^ N * (m ^ 2)⁻¹ < δ := hN N le_rfl
  -- the estimate this file exists to convert, at the `N` just chosen
  have hbound := truncated_abs_le_sq (G := H) (m := m) hm hdeg a S hS hC0 hC hsep
  refine hbound.trans ?_
  -- `P(k)·((C²K)²·(C²/m²)^(k/2−2)) = B·K²`, and `B·K² ≤ |B|·δ² = |B|·ε/(|B|+1) ≤ ε`
  set K : ℝ := decayRate Δ m ^ N * (m ^ 2)⁻¹ with hKdef
  have hrw : (Fintype.card ↑(perfectMatchings (Fin k)) : ℝ)
      * ((C * C * K) ^ 2 * (C * C * (m ^ 2)⁻¹) ^ (k / 2 - 2)) = B * K ^ 2 := by
    rw [hBdef]; ring
  rw [hrw]
  have hsq : K ^ 2 ≤ δ ^ 2 := by
    have := mul_self_le_mul_self hK0 hKδ.le
    simpa [sq] using this
  have hδsq : δ ^ 2 = ε / (|B| + 1) := by
    rw [hδdef]
    exact Real.sq_sqrt (by positivity)
  calc B * K ^ 2 ≤ |B| * K ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg K)
    _ ≤ |B| * δ ^ 2 := by exact mul_le_mul_of_nonneg_left hsq (abs_nonneg B)
    _ = |B| * (ε / (|B| + 1)) := by rw [hδsq]
    _ ≤ ε := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hden]
        nlinarith [abs_nonneg B, hε.le]

/-! ## 2. The check -/

/-- **THE CHECK.** The general statement at `k = 4`, `S = {0, 1}` and `a = ![f, f, g, g]` IS
`LatticeFourPointClustering.exists_four_point_clustering_uniform`, whose own proof goes through
`GreenClustering.cross_abs_le` and mentions no pairing. Kept on the estate's `_two_ways` pattern
(`LatticeFourPointExact.connected_smeared_two_ways` and
`LatticeTruncatedNorms.connected_smeared_le_two_ways`): the statement is that theorem's and the
route is not. -/
theorem exists_four_point_clustering_uniform_two_ways {m : ℝ} (hm : m ≠ 0) (Δ : ℕ) (C : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ f g : EuclideanSpace ℝ W,
        (∑ p, |f.ofLp p|) ≤ C → (∑ q, |g.ofLp q|) ≤ C →
        (∀ p q, f.ofLp p ≠ 0 → g.ofLp q ≠ 0 → ¬ H.Reachable p q ∨ N ≤ H.dist p q) →
          (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField H m))
              - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField H m))
                * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField H m))
            ≤ ε := by
  classical
  -- **WHY THE GENERAL THEOREM ASKS FOR `0 ≤ C` AND THIS ONE DOES NOT, AND IT IS NOT COSMETIC.**
  -- `N` has to be produced BEFORE any test function exists, so `0 ≤ C` cannot be derived there;
  -- and at `k = 0` the general statement quantifies over none at all, so nothing forces it. Here
  -- `C < 0` makes the hypothesis `∑ |f p| ≤ C` unsatisfiable — a sum of absolute values is
  -- non-negative — so the statement is vacuous and ANY `N` serves. That case is discharged first
  -- rather than assumed away, which is what keeps this statement identical to the estate's.
  by_cases hC0 : (0 : ℝ) ≤ C
  case neg =>
    exact ⟨0, fun W _ _ H _ hdeg f g hf hg hsep =>
      absurd (le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) hf) hC0⟩
  obtain ⟨N, hN⟩ := exists_truncated_clustering_uniform (m := m) (C := C) hm Δ hC0 4 hε
  refine ⟨N, fun W _ _ H _ hdeg f g hf hg hsep => ?_⟩
  have hmemS : ∀ i ∈ ({0, 1} : Finset (Fin 4)), i = 0 ∨ i = 1 := by decide
  have hmemT : ∀ i ∉ ({0, 1} : Finset (Fin 4)), i = 2 ∨ i = 3 := by decide
  have hC : ∀ i : Fin 4, ∑ p, |((![f, f, g, g] i : EuclideanSpace ℝ W)).ofLp p| ≤ C := by
    intro i; fin_cases i <;> assumption
  have hsep' : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)), ∀ p q,
      ((![f, f, g, g] i : EuclideanSpace ℝ W)).ofLp p ≠ 0 →
      ((![f, f, g, g] j : EuclideanSpace ℝ W)).ofLp q ≠ 0 →
      ¬ H.Reachable p q ∨ N ≤ H.dist p q := by
    intro i hi j hj p q hp hq
    rcases hmemS i hi with rfl | rfl <;> rcases hmemT j hj with rfl | rfl <;>
      exact hsep p q hp hq
  have h := hN W H hdeg ![f, f, g, g] ({0, 1} : Finset (Fin 4)) (by decide) hC hsep'
  rw [show (fun ω => ∏ i : Fin 4, (inner ℝ (![f, f, g, g] i) ω : ℝ))
      = fun ω => (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [LatticeSplitFourCheck.prod_fin_four f f g g ω]; ring,
    show (fun ω => ∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] x) ω : ℝ)) = fun ω => (inner ℝ f ω : ℝ) ^ 2 from
        funext fun ω => by rw [LatticeSplitFourCheck.prod_lower_two f f g g ω]; ring,
    show (fun ω => ∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] y) ω : ℝ)) = fun ω => (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [LatticeSplitFourCheck.prod_upper_two f f g g ω]; ring] at h
  exact (le_abs_self _).trans h

end LatticeTruncatedUniform
