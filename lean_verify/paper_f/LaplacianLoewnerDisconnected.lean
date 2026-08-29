import LaplacianLoewnerConverse
import LaplacianSharpDisconnected

/-!
# The Loewner characterisation with no connectivity hypothesis

`LaplacianLoewnerConverse` proved that a **connected** regular graph's constant `2Δ + m²` cannot be
lowered exactly when the graph is two-colourable, and named connectivity as a hypothesis it did not
remove. `LaplacianSharpDisconnected` then removed it at the level of a supplied vector: a regular
graph attains **iff some connected component is two-colourable**. **This file carries that through
to the Loewner order**, which is the language the rest of the estate states these results in.

> **`massive_le_smul_one_iff_exists_component_colorable`** — for a `Δ`-regular graph, connected or
> not, `∀ c, massive ≼ c·1 → 2Δ + m² ≤ c` **iff some connected component is two-colourable**.

**CONNECTIVITY ENTERED THE OLD ARGUMENT EXACTLY ONCE AND THE REPLACEMENT IS ONE LINE.** The strict
eigenvalue bound is got by contradiction: an eigenvalue equal to the constant gives an eigenvector
attaining the quadratic form, and something then forbids that. In the connected case the forbidding
was `LaplacianSharpEquality.colorable_two_of_quadForm_eq`; here it is
`LaplacianSharpDisconnected.exists_component_colorable_of_neg_adj`, which needs no connectivity at
all. Everything else — the passage from a strict eigenvalue bound to a strict Loewner bound — is
`LaplacianLoewnerConverse.exists_lt_massive_le_smul_one_of_eigenvalues_lt`, **factored out of that
file for this one rather than copied into it** (`ERRATUM 337`: the estate's recurring defect is
re-proving what it already has, and a shared proof is the structural answer).

**THE CONNECTED CASE IS RECOVERED FROM THIS ONE** (`ERRATUM 201`), through the same `induceUnivIso`
bridge `LaplacianSharpDisconnected` uses, so the generalisation is instantiated at the statement it
generalises rather than merely asserted to cover it.

## What this does NOT do

**It does not remove regularity**, which is the hypothesis every result in this chain still carries;
`RegularBipartiteSharp` has only the averaged statement without it.

**It does not identify the constant.** The `c` produced is the maximum of the eigenvalue list, and
no closed form is given for it at any graph — the same fence `LaplacianLoewnerConverse` carries,
unchanged.

**It does not settle a graph with no vertices.** `Nonempty V` is required, because the maximum of an
empty eigenvalue list is not a number; at `V` empty the Loewner statement is vacuous on both sides
and nothing here says so.

**This is a statement about a matrix.** No measure appears, nothing in the OS chain changes, and no
published tag is touched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianLoewnerDisconnected

open Matrix GraphLaplacian SimpleGraph LaplacianSharpEquality LaplacianSharpDisconnected
open LaplacianLoewnerConverse
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The strict eigenvalue bound, without connectivity -/

/-- **EVERY EIGENVALUE IS STRICTLY BELOW THE CONSTANT WHEN NO COMPONENT IS TWO-COLOURABLE.** The
connected version's one use of connectivity, replaced by the component characterisation. -/
theorem eigenvalues_massive_lt_of_no_component_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (m : ℝ) (hcol : ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2) (j : V) :
    (massive_isHermitian G m).eigenvalues j < 2 * (Δ : ℝ) + m ^ 2 := by
  refine lt_of_le_of_ne (eigenvalues_massive_le G hreg m j) fun heq => ?_
  set hH := massive_isHermitian G m with hHdef
  set b : EuclideanSpace ℝ V := hH.eigenvectorBasis j with hb
  have hnorm : inner ℝ b b = (1 : ℝ) := by
    have h1 : ‖b‖ = 1 := (hH.eigenvectorBasis).orthonormal.1 j
    have h2 := real_inner_self_eq_norm_sq b
    rw [h2, h1]; norm_num
  have hq : inner ℝ b (RayleighMatrix.mv (massive G m) b) = hH.eigenvalues j := by
    rw [RayleighMatrix.mv_eigenvectorBasis hH, real_inner_smul_right, hnorm, mul_one]
  rw [inner_mv_eq] at hq
  rw [inner_self_eq] at hnorm
  set w := WithLp.ofLp b with hw
  have hne : w ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp [dotProduct] at hnorm
  have hattain : w ⬝ᵥ (massive G m) *ᵥ w = (2 * (Δ : ℝ) + m ^ 2) * (w ⬝ᵥ w) := by
    rw [hq, heq, hnorm, mul_one]
  obtain ⟨C, hC⟩ := exists_component_colorable_of_neg_adj G hne
    ((massive_quadForm_eq_iff_neg_adj G hreg m w).mp hattain)
  exact hcol C hC

/-! ## 2. Hence the constant can be lowered, and the characterisation -/

/-- **THE CONSTANT CAN BE LOWERED WHENEVER NO COMPONENT IS TWO-COLOURABLE**, with no connectivity
hypothesis. -/
theorem exists_lt_massive_le_smul_one_of_no_component [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) (m : ℝ)
    (hcol : ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2) :
    ∃ c : ℝ, c < 2 * (Δ : ℝ) + m ^ 2 ∧ massive G m ≤ c • (1 : Matrix V V ℝ) :=
  exists_lt_massive_le_smul_one_of_eigenvalues_lt G m
    (fun j => eigenvalues_massive_lt_of_no_component_colorable G hreg m hcol j)

/-- **THE CHARACTERISATION IN THE LOEWNER ORDER, WITH NO CONNECTIVITY HYPOTHESIS.** The constant
`2Δ + m²` cannot be lowered exactly when some connected component is two-colourable. -/
theorem massive_le_smul_one_iff_exists_component_colorable [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) (m : ℝ) :
    (∀ c : ℝ, massive G m ≤ c • (1 : Matrix V V ℝ) → 2 * (Δ : ℝ) + m ^ 2 ≤ c)
      ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  constructor
  · intro hmin
    by_contra hcol
    obtain ⟨c, hlt, hle⟩ := exists_lt_massive_le_smul_one_of_no_component G hreg m
      (fun C hC => hcol ⟨C, hC⟩)
    exact absurd (hmin c hle) (not_le.mpr hlt)
  · rintro ⟨C, hC⟩ c hle
    obtain ⟨x, hx, hflip⟩ := exists_neg_adj_of_component_colorable G C hC
    have hattain : x ⬝ᵥ (massive G m) *ᵥ x = (2 * (Δ : ℝ) + m ^ 2) * (x ⬝ᵥ x) :=
      (massive_quadForm_eq_iff_neg_adj G hreg m x).mpr hflip
    have hxx : 0 < x ⬝ᵥ x := by
      obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
        by_contra hc
        exact hx (funext fun w => not_not.mp fun h => hc ⟨w, h⟩)
      refine Finset.sum_pos' (fun i _ => mul_self_nonneg (x i)) ⟨v, Finset.mem_univ v, ?_⟩
      exact mul_self_pos.mpr hv
    have hnn := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg x
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hnn
    have hone : x ⬝ᵥ (c • (1 : Matrix V V ℝ)) *ᵥ x = c * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hone, hattain] at hnn
    exact le_of_mul_le_mul_right hnn hxx

/-- **THE CONNECTED CASE IS RECOVERED FROM THIS ONE** (`ERRATUM 201`), through the same
`induceUnivIso` bridge `LaplacianSharpDisconnected` uses. -/
example [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hG : G.Connected) (m : ℝ) :
    (∀ c : ℝ, massive G m ≤ c • (1 : Matrix V V ℝ) → 2 * (Δ : ℝ) + m ^ 2 ≤ c)
      ↔ G.Colorable 2 := by
  rw [massive_le_smul_one_iff_exists_component_colorable G hreg m]
  constructor
  · rintro ⟨C, hc⟩
    have hsupp : C.supp = Set.univ := by
      obtain ⟨v₀, hv₀⟩ := C.exists_rep
      subst hv₀
      ext v
      simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
      exact SimpleGraph.ConnectedComponent.sound (hG.preconnected v v₀)
    rw [hsupp] at hc
    exact SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso G).symm.toHom hc
  · intro hc
    obtain ⟨v₀⟩ := ‹Nonempty V›
    exact ⟨G.connectedComponentMk v₀,
      SimpleGraph.Colorable.of_hom (SimpleGraph.Embedding.induce _).toHom hc⟩

end LaplacianLoewnerDisconnected
