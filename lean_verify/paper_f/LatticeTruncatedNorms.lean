import LatticeFourPointExact

/-!
# Two norms instead of one, and the last item on this line

Five records in a row have named the same remaining difference between the general clustering
estimate and `LatticeFourPointClustering.connected_smeared_le`: that one uses `‖f‖₁·‖g‖₁` where the
general route uses `C²` for a common `ℓ¹` bound on every test function. Each of them said closing it
meant *"carrying two norms separately through `PairingBound` and `PairingSharp`"*.

**THAT ESTIMATE OF THE WORK WAS WRONG, AND THE RECORD IS CORRECTED HERE RATHER THAN QUIETLY.**
`PairingBound` and `PairingSharp` never asked for one norm. They take `ε` — a bound on the
propagator ACROSS the split — and `M` — a bound on all of it — as **independent** parameters, and
they always did. The common `C` was introduced two files later, in `LatticeTruncatedDecay`'s
convenience composition, where one bound covering every test function was simply easier to state.
**Nothing in the combinatorial files needed changing, and this file changes none of them.**

## What is proved

* **`truncated_abs_le_two_norms`** — the decay bound with **one norm per side of the split**:
  `≤ count·((Cs·Ct·rᴺ/m²)²·((Cs+Ct)²/m²)^(k/2−2))`. The sum `Cs + Ct` appears only in the factor
  that bounds *every* pair including the same-side ones, and it is a sum rather than a maximum
  because that needs no case analysis and both are non-negative;
* **`truncated_abs_le_four_two_norms`** — at four test functions the second factor is an empty
  power, **so the uniform bound disappears entirely** and what is left is `2·(Cs·Ct·rᴺ/m²)²`;
* **`connected_smeared_le_two_ways`** — **the last item, closed.** At `![f, f, g, g]` and
  `S = {0, 1}` that reads `≤ 2·(‖f‖₁·‖g‖₁·rᴺ/m²)²`, which is
  `LatticeFourPointClustering.connected_smeared_le` **exactly** — same quantity, same constant,
  same rate, same norms. **The two statements are interchangeable and that was checked in both
  directions**: each theorem discharges the other's statement by `exact`, the only difference in
  the source text being `WithLp.ofLp`, which is the identity. **They are NOT byte-identical, and a
  first draft of this summary said they were** — the difference is one coercion, and a claim about
  source text has to be true of the source text. It is named on the estate's `_two_ways` pattern
  for the same reason `LatticeFourPointExact`'s twin is.

## What is NOT here

**The uniform factor does not disappear above order four.** At `k > 4` the exponent `k/2 − 2` is
positive and `(Cs + Ct)²` is still a common bound — a crude one, since it does not distinguish which
side a pair lies on. Splitting `M` into three cases by side would sharpen it and is **not done, not
costed** (`ERRATUM 194`). What can be said is that the CROSS factor, which carries all the decay,
is now exact at every order.

**And it is not OS4.** Finite volume, and a constant that grows faster than geometrically in the
order — unchanged by anything here.
-/

namespace LatticeTruncatedNorms

open Equiv Function Involutions PairingSplit PairingCluster
open LatticeTruncatedCount LatticeTruncatedDecay LatticeSplitFourCheck
open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. One norm per side -/

/-- **THE DECAY BOUND WITH TWO NORMS.** `Cs` bounds the test functions indexed by `S` and `Ct`
those outside it. The cross factor is `Cs·Ct` exactly; only the factor bounding every pair —
same-side ones included — needs something covering both. -/
theorem truncated_abs_le_two_norms (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) (hS : Even S.card)
    {Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hCs : ∀ i ∈ S, ∑ p, |(a i).ofLp p| ≤ Cs) (hCt : ∀ i ∉ S, ∑ p, |(a i).ofLp p| ≤ Ct)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ∀ p q, (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ((Finset.univ.filter
            (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)).card : ℝ)
        * ((Cs * Ct * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2
            * ((Cs + Ct) * (Cs + Ct) * (m ^ 2)⁻¹) ^ (k / 2 - 2)) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hr0 : (0 : ℝ) ≤ decayRate Δ m := decayRate_nonneg Δ hm
  have hK0 : (0 : ℝ) ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by positivity
  have hU0 : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hl1 : ∀ i, (0 : ℝ) ≤ ∑ p, |(a i).ofLp p| :=
    fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the only place the two bounds have to be merged: a factor covering SAME-side pairs too
  have hsum : ∀ i, ∑ p, |(a i).ofLp p| ≤ Cs + Ct := by
    intro i
    by_cases hi : i ∈ S
    · exact (hCs i hi).trans (by linarith)
    · exact (hCt i hi).trans (by linarith)
  refine abs_integral_prod_sub_mul_le_count hm a S hS (by positivity) ?_ ?_
  · intro i hi j hj
    refine (dotG_abs_le_of_sep hm hΔ (a i) (a j) (hsep i hi j hj)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hCs i hi) (hCt j hj) (hl1 j) hCs0) hK0
  · intro i j
    refine (dotG_abs_le hm hΔ (a i) (a j)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hsum i) (hsum j) (hl1 j) (by linarith)) hU0

/-! ## 2. At four test functions the common bound disappears -/

/-- **THE UNIFORM FACTOR IS AN EMPTY POWER AT ORDER FOUR.** `4/2 − 2 = 0`, so `Cs + Ct` never
appears, and `LatticeTruncatedCount.crossing_card_fin_four` supplies the `2`. -/
theorem truncated_abs_le_four_two_norms (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {N : ℕ} (a : Fin 4 → EuclideanSpace ℝ V) {Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hCs : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∑ p, |(a i).ofLp p| ≤ Cs)
    (hCt : ∀ i ∉ ({0, 1} : Finset (Fin 4)), ∑ p, |(a i).ofLp p| ≤ Ct)
    (hsep : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)), ∀ p q,
      (a i).ofLp p ≠ 0 → (a j).ofLp q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
            (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ 2 * (Cs * Ct * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 := by
  have h := truncated_abs_le_two_norms hm hΔ a ({0, 1} : Finset (Fin 4)) (by decide)
    hCs0 hCt0 hCs hCt hsep
  rwa [crossing_card_fin_four, show (4 : ℕ) / 2 - 2 = 0 from rfl, pow_zero, mul_one,
    show ((2 : ℕ) : ℝ) = 2 from by norm_num] at h

/-! ## 3. The last item, closed

`LatticeFourPointClustering.connected_smeared_le` bounds `⟨f²g²⟩ − ⟨f²⟩⟨g²⟩` by
`2·(‖f‖₁·‖g‖₁·rᴺ/m²)²`. So does this, through seventeen files. **The two are interchangeable, and
that was checked in both directions rather than asserted** — each discharges the other by `exact` —
which is why this one is named on the `_two_ways` pattern. -/

/-- **THE FOUR-POINT CLUSTERING ESTIMATE, THROUGH THE GENERAL MACHINERY.** Interchangeable with
`LatticeFourPointClustering.connected_smeared_le` — each discharges the other by `exact`, checked
in both directions; the source text differs only by `WithLp.ofLp`, which is the identity. Kept for
the same reason `LatticeFourPointExact.connected_smeared_two_ways` is: the route differs. **This is
the last of the three differences the records have been tracking — exponent, constant, norms — and
it closes here.** -/
theorem connected_smeared_le_two_ways (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f.ofLp p ≠ 0 → g.ofLp q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      ≤ 2 * ((∑ p, |f.ofLp p|) * (∑ q, |g.ofLp q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 := by
  classical
  have hl1 : ∀ h : EuclideanSpace ℝ V, (0 : ℝ) ≤ ∑ p, |h.ofLp p| :=
    fun h => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- The membership facts are settled by `decide` on their own, BEFORE any analytic goal is in
  -- sight. A first draft ran `fin_cases i <;> simp_all` on the combined goal and timed out at
  -- `whnf`: `simp_all` was unfolding the sums over `V` while trying to discharge `i ∈ {0, 1}`.
  -- Once the index is a literal, `![f, f, g, g] 0` IS `f` by `rfl` and nothing needs simplifying.
  have hmemS : ∀ i ∈ ({0, 1} : Finset (Fin 4)), i = 0 ∨ i = 1 := by decide
  have hmemT : ∀ i ∉ ({0, 1} : Finset (Fin 4)), i = 2 ∨ i = 3 := by decide
  have hCs : ∀ i ∈ ({0, 1} : Finset (Fin 4)),
      ∑ p, |((![f, f, g, g] i : EuclideanSpace ℝ V)).ofLp p| ≤ ∑ p, |f.ofLp p| := by
    intro i hi; rcases hmemS i hi with rfl | rfl <;> exact le_rfl
  have hCt : ∀ i ∉ ({0, 1} : Finset (Fin 4)),
      ∑ p, |((![f, f, g, g] i : EuclideanSpace ℝ V)).ofLp p| ≤ ∑ q, |g.ofLp q| := by
    intro i hi; rcases hmemT i hi with rfl | rfl <;> exact le_rfl
  have hsep' : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)), ∀ p q,
      ((![f, f, g, g] i : EuclideanSpace ℝ V)).ofLp p ≠ 0 →
      ((![f, f, g, g] j : EuclideanSpace ℝ V)).ofLp q ≠ 0 →
      ¬ G.Reachable p q ∨ N ≤ G.dist p q := by
    intro i hi j hj p q hp hq
    rcases hmemS i hi with rfl | rfl <;> rcases hmemT j hj with rfl | rfl <;>
      exact hsep p q hp hq
  have h := truncated_abs_le_four_two_norms hm hΔ ![f, f, g, g] (hl1 f) (hl1 g) hCs hCt hsep'
  rw [show (fun ω => ∏ i : Fin 4, (inner ℝ (![f, f, g, g] i) ω : ℝ))
      = fun ω => (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_fin_four f f g g ω]; ring,
    show (fun ω => ∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] x) ω : ℝ)) = fun ω => (inner ℝ f ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_lower_two f f g g ω]; ring,
    show (fun ω => ∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
        (inner ℝ (![f, f, g, g] y) ω : ℝ)) = fun ω => (inner ℝ g ω : ℝ) ^ 2 from
        funext fun ω => by rw [prod_upper_two f f g g ω]; ring] at h
  exact (le_abs_self _).trans h

end LatticeTruncatedNorms
