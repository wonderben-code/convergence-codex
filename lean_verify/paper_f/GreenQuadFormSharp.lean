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

end GreenQuadFormSharp
