import GreenNormExact
import LatticeUniformPoincare

/-!
# The uniform Poincaré constant is attained at EVERY graph, not only at the edgeless one

`LatticeUniformPoincare.quadForm_green_le` is `w ⬝ᵥ G *ᵥ w ≤ m⁻² · ∑ⱼ wⱼ²`, with a constant that
names no graph, and its sharpness is recorded there in a carefully worded docstring:

> *"On the edgeless graph `quadForm_green_le` holds with equality, so **no bound of that shape valid
> on every graph** can have a constant below `m⁻²`."*

**THE WITNESS IS NOT SPECIAL AND THE RESTRICTION TO IT IS REMOVABLE.** `quadForm_green_bot` needs
`⊥` because it computes `green ⊥ m = m⁻² • 1` outright. But the constant vector is an eigenvector of
`green` at `m⁻²` on **every** finite graph — `GreenExpansion.green_mulVec_one`, because the graph
Laplacian kills constants — so the equality case is available everywhere:

* **`quadForm_green_one`** — `1 ⬝ᵥ (green K m) *ᵥ 1 = m⁻² · ∑ⱼ 1²`, at every graph `K`.
* **`le_of_quadForm_green_le`** — hence at **each fixed graph**, a bound of that shape forces
  `m⁻² ≤ c`. Not *"no constant below `m⁻²` works for all graphs"* but *"no constant below `m⁻²`
  works for this one"*.

`PROOF_STRATEGY` §7 rule 3: the hypothesis removed is the choice of witness graph.

## Why it was not seen before, which is worth one sentence

`quadForm_green_bot` is the older statement and it is not wrong; what it lacks is
`green_mulVec_one`, which sits in `GreenExpansion` — a file about reflection positivity, not about
Poincaré inequalities. **`ERRATUM 434` is the same fact arriving late in the operator-norm chain**:
the constant eigenvector is a one-line consequence of the Laplacian's definition, and this estate
has now failed to have it in front of it twice.

## What is NOT strengthened here, and it is the half a reader cares about

`LatticeUniformPoincare.poincare_uniform_sharp` — the sharpness of the **Poincaré inequality
itself**, for an observable against the measure — is still stated at `⊥` only. **The same argument
should generalise**: at an arbitrary graph the observable `ω ↦ ∑ⱼ ωⱼ` has variance
`1 ⬝ᵥ green *ᵥ 1 = m⁻²·|V|` and gradient sum `|V|`, so equality should hold there too.
**It is not attempted here, no cost is claimed for it** (`ERRATUM 246`) **and no estimate is
offered** (`ERRATUM 183`); this file strengthens the matrix step and says so, which is the
distinction `quadForm_green_bot`'s own docstring was written to protect.

**⚠ ATTEMPTED AND CLOSED IN THE NEXT UNIT; THE PARAGRAPH ABOVE IS KEPT AS WRITTEN** (`ERRATUM 94`,
2026-09-03). §2 below proves it: **`poincare_uniform_sharp_general`**, equality at an **arbitrary**
graph for the observable `ω ↦ ∑ⱼ ωⱼ`, so `poincare_uniform`'s constant cannot be lowered at any
FIXED graph either. `PROOF_STRATEGY` §6 question 3 — *if the unit you just finished was a `B`, retry
`B → C` before touching the queue* — and this is that retry, run immediately rather than queued.
**The estimate the paragraph declined to offer was never needed**: the two integrals are
`GraphLaplacian.twoPoint` summed twice and a constant, and the only new input is the row-sum fact
§1 already uses.

**No wall moves** and nothing consumes this: `LatticeUniformStein`'s chain uses the INEQUALITY, and
is indifferent to where it is attained.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenQuadFormSharp

open Matrix GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-- **THE EQUALITY CASE OF `quadForm_green_le`, AT EVERY GRAPH.** The constant vector is an
eigenvector of `green` at `m⁻²` on any finite graph, so the uniform bound is attained there. -/
theorem quadForm_green_one (hm : m ≠ 0) :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ green K m *ᵥ (fun _ : V => (1 : ℝ))
      = (m ^ 2)⁻¹ * ∑ _j : V, (1 : ℝ) ^ 2 := by
  rw [GreenExpansion.green_mulVec_one (G := K) hm]
  simp [dotProduct, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **AND SO THE CONSTANT CANNOT BE LOWERED AT ANY FIXED GRAPH.**
`LatticeUniformPoincare.quadForm_green_bot` gives this for the class, witnessed by `⊥`; here the
witness is the graph itself. -/
theorem le_of_quadForm_green_le [Nonempty V] (hm : m ≠ 0) {c : ℝ}
    (h : ∀ w : V → ℝ, w ⬝ᵥ green K m *ᵥ w ≤ c * ∑ j : V, w j ^ 2) : (m ^ 2)⁻¹ ≤ c := by
  classical
  have hcard : (0 : ℝ) < ∑ _j : V, (1 : ℝ) ^ 2 := by
    refine Finset.sum_pos (fun _ _ => by norm_num) ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  have hle := h (fun _ : V => (1 : ℝ))
  rw [quadForm_green_one K hm] at hle
  exact le_of_mul_le_mul_right (by simpa using hle) hcard

/-! ## 2. And the Poincaré inequality itself, at an arbitrary graph -/

open MeasureTheory

omit [DecidableEq V] in
/-- The derivative of `x ↦ ∑ⱼ xⱼ` in a direction is the direction's coordinate sum. The observable
is a continuous linear map, so `ContinuousLinearMap.fderiv` does the work, exactly as
`LatticeUniformPoincare.fderiv_coord` does for one coordinate.

*`DecidableEq V` is genuinely unused and is omitted, as it is there. `Fintype` is not: the sum in
the statement needs it.* -/
theorem fderiv_sum_coord (ω v : EuclideanSpace ℝ V) :
    fderiv ℝ (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω v = ∑ j : V, v j := by
  have h : (fun x : EuclideanSpace ℝ V => ∑ j : V, x j)
      = ⇑(∑ j : V, EuclideanSpace.proj (𝕜 := ℝ) j) := by
    ext x; simp
  rw [h, ContinuousLinearMap.fderiv]
  simp

/-- **THE SUMMED OBSERVABLE IS CENTRED**, at every graph and **at every mass, `0` included**.

*The first draft carried `hm : m ≠ 0` and the unused-variable linter reported it. The hypothesis is
genuinely not needed — `GraphLaplacian.integral_eval` and `memLp_eval` both hold at every `m` — so
it is dropped rather than kept for symmetry with its neighbours. Six linter reports in this family
have been genuine strengthenings and one was not (`LatticeUniformPoincare.fderiv_coord`); this one
was checked against the two cited statements rather than assumed.* -/
theorem integral_sum_eval :
    ∫ ω, (∑ j : V, ω j) ∂(gaussianField K m) = 0 := by
  rw [integral_finset_sum _ (fun j _ => (GraphLaplacian.memLp_eval K m j).integrable (by norm_num))]
  simp [GraphLaplacian.integral_eval]

/-- **ITS SECOND MOMENT IS `m⁻²·|V|`**, at every graph — every row of `green` sums to `m⁻²`
(`GreenExpansion.green_mulVec_one`), so the double sum of the covariance collapses. -/
theorem integral_sum_sq (hm : m ≠ 0) :
    ∫ ω, (∑ j : V, ω j) * (∑ j : V, ω j) ∂(gaussianField K m)
      = (m ^ 2)⁻¹ * (Fintype.card V : ℝ) := by
  have hint : ∀ p q : V, Integrable (fun ω : EuclideanSpace ℝ V => ω p * ω q)
      (gaussianField K m) :=
    fun p q => (GraphLaplacian.memLp_eval K m p).integrable_mul (GraphLaplacian.memLp_eval K m q)
  have hexp : ∀ ω : EuclideanSpace ℝ V,
      (∑ p : V, ω p) * (∑ q : V, ω q) = ∑ p : V, ∑ q : V, ω p * ω q :=
    fun ω => Finset.sum_mul_sum _ _ _ _
  have hrow : ∀ p : V, ∑ q : V, green K m p q = (m ^ 2)⁻¹ := by
    intro p
    have h := congrFun (GreenExpansion.green_mulVec_one (G := K) hm) p
    simpa [Matrix.mulVec, dotProduct] using h
  simp only [hexp]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun q _ => hint p q))]
  have hinner : ∀ p : V,
      ∫ ω, ∑ q : V, ω p * ω q ∂(gaussianField K m) = (m ^ 2)⁻¹ := by
    intro p
    rw [integral_finset_sum _ (fun q _ => hint p q)]
    simp only [GraphLaplacian.twoPoint K hm]
    exact hrow p
  simp [hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **THE POINCARÉ CONSTANT `m⁻²` IS ATTAINED AT EVERY GRAPH, NOT ONLY AT THE EDGELESS ONE.**
`LatticeUniformPoincare.poincare_uniform_sharp` exhibits equality on `⊥` with a single coordinate;
here the graph is arbitrary and the observable is `ω ↦ ∑ⱼ ωⱼ`, whose variance is `m⁻²·|V|` because
every row of `green` sums to `m⁻²` and whose `ℓ²` gradient sum is `|V|` at every point.

**So `poincare_uniform`'s constant cannot be lowered at any FIXED graph**, where the previous
statement said only that it cannot be lowered in a theorem quantified over graphs. -/
theorem poincare_uniform_sharp_general [Nonempty V] (hm : m ≠ 0) :
    (∫ ω, (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω
        * (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω ∂(gaussianField K m))
      - (∫ ω, (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω ∂(gaussianField K m)) ^ 2
      = (m ^ 2)⁻¹ * ∫ ω, ∑ i : V, (fderiv ℝ (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ^ 2 ∂(gaussianField K m) := by
  classical
  have hgrad : ∀ (ω : EuclideanSpace ℝ V) (i : V),
      (fderiv ℝ (fun x : EuclideanSpace ℝ V => ∑ j : V, x j) ω
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) ^ 2 = 1 := by
    intro ω i
    rw [fderiv_sum_coord]
    have : ∑ j : V, (WithLp.toLp 2 (Pi.single i (1 : ℝ)) : EuclideanSpace ℝ V) j = 1 := by
      simp [Pi.single_apply]
    rw [this]; norm_num
  simp only [hgrad]
  rw [integral_sum_eval K, integral_sum_sq K hm]
  simp

end GreenQuadFormSharp
