import LaplacianSharpEquality

/-!
# The signless Laplacian `D + A`, and the degree bound's equality case with no regularity

Every sharpness result in this chain — `LaplacianSharpEquality`, `LaplacianSharpDisconnected`,
`LaplacianLoewnerDisconnected` — carries `IsRegularOfDegree` as a hypothesis, and each of them says
so in its own fence. **Regularity is used in exactly one place**: to collapse `Σᵢ deg(i)·xᵢ²` to
`Δ‖x‖²`. `LaplacianSharpEquality.sum_adj_add_sq_of_degree` is that identity before the collapse,
and this file is what it says when nothing is collapsed.

> **`dotProduct_signlessLap`** — for **any** finite graph,
> `xᵀ(D + A)x = ½ Σᵢ Σⱼ [i ∼ j] (xᵢ + xⱼ)²`.
>
> **`dotProduct_signlessLap_eq_zero_iff`** — so `xᵀ(D + A)x = 0` **iff `x` flips sign across every
> edge**, with no hypothesis on the graph whatever. That is the kernel of the signless Laplacian.
>
> **`quadForm_eq_iff_neg_adj_of_degree`** — and the degree bound's equality case in the same
> generality: `xᵀLx = 2·Σᵢ deg(i)·xᵢ²` **iff** `x` flips sign across every edge.

**`D + A` IS THE OBJECT THE WHOLE CHAIN HAS BEEN CIRCLING.** The Laplacian is `D − A`; its signless
twin is `D + A`, and the two quadratic forms are the two sums `Σ (xᵢ − xⱼ)²` and `Σ (xᵢ + xⱼ)²`.
Everything the earlier files proved about "the slack in the bound" is the second of these, and it is
a positive semidefinite form in its own right (`signlessLap_posSemidef`) whose kernel is exactly the
sign-flipping vectors. **The regular case is recovered below** (`ERRATUM 201`), so nothing that was
proved with regularity is lost or restated.

**ABSENT FROM MATHLIB, MEASURED RATHER THAN ASSERTED** (`ERRATUM 194`, and by shape rather than by
name per `ERRATUM 42`): `Combinatorics/SimpleGraph/LapMatrix.lean` defines `degMatrix`, `adjMatrix`
and `lapMatrix = degMatrix - adjMatrix`, and the sum `degMatrix + adjMatrix` occurs **nowhere** in
Mathlib v4.29.1 — grepping for the shape `degMatrix.*+.*adjMatrix` and for `signless` each returns
**0**. It occurs nowhere in `paper_f` either. **No difficulty is inferred from that**: it is a
three-line definition, and its absence is an absence.

## What this does NOT do

**It does not remove regularity from the Loewner statements**, and cannot as they stand. Without
regularity the bound `massive ≼ c·1` is not governed by a single constant — the degree-weighted sum
does not collapse — and `RegularBipartiteSharp` has only the averaged form for that reason. What
generalises is the EQUALITY CASE, not the ORDER statement, and the difference is exactly the
collapse.

**^ AND THAT PARAGRAPH IS NOW A THEOREM RATHER THAN AN ARGUMENT, 30 AUGUST.** It is kept as written
(`ERRATUM 94`) and it was right; what it lacked was a witness.
`LoewnerRegularityNecessary.regularity_necessary` refutes
`LaplacianLoewnerDisconnected.massive_le_smul_one_iff_exists_component_colorable` with
`IsRegularOfDegree` weakened to a degree **bound** — the only weakening under which the statement
still typechecks — on `PrismReflection.path3`, whose degrees are `1, 2, 1`. **The gap is exactly
`2Δ` minus the true spectral radius**: the claimed constant is `4 + m²` and `massive ≼ (3 + m²)·1`
holds, while the graph is two-colourable. So *"cannot as they stand"* is now known and not believed.

**It does not compute the spectrum of `D + A`.** Positive semidefiniteness and the kernel are
proved; nothing else about its eigenvalues is, here or anywhere in this estate.

**It is a statement about a matrix.** No measure appears, nothing in the OS chain changes, and no
published tag is touched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianSignless

open Matrix SimpleGraph LaplacianSharpEquality

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The signless Laplacian and its quadratic form -/

/-- **THE SIGNLESS LAPLACIAN `D + A`**, the Laplacian's twin with the sign of the adjacency term
reversed. Mathlib has `lapMatrix = degMatrix - adjMatrix` and not this. -/
noncomputable def signlessLap : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ

/-- **ITS QUADRATIC FORM IS THE SUM OF `(xᵢ + xⱼ)²` OVER ORDERED EDGES**, exactly as the Laplacian's
is the sum of `(xᵢ − xⱼ)²`. -/
theorem dotProduct_signlessLap (x : V → ℝ) :
    x ⬝ᵥ (signlessLap G) *ᵥ x
      = (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0) / 2 := by
  have hq : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x
      = (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
    rw [← Matrix.toLinearMap₂'_apply']
    exact G.lapMatrix_toLinearMap₂' ℝ x
  have hid := sum_adj_add_sq_of_degree G x
  have hlap : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x
      = (∑ i : V, (G.degree i : ℝ) * x i ^ 2) - x ⬝ᵥ (G.adjMatrix ℝ) *ᵥ x := by
    rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub,
      SimpleGraph.dotProduct_mulVec_degMatrix]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsl : x ⬝ᵥ (signlessLap G) *ᵥ x
      = (∑ i : V, (G.degree i : ℝ) * x i ^ 2) + x ⬝ᵥ (G.adjMatrix ℝ) *ᵥ x := by
    rw [signlessLap, Matrix.add_mulVec, dotProduct_add,
      SimpleGraph.dotProduct_mulVec_degMatrix]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsl]
  rw [hq] at hid hlap
  linarith

/-- **SO IT IS POSITIVE SEMIDEFINITE**, the twin of Mathlib's `posSemidef_lapMatrix`. -/
theorem dotProduct_signlessLap_nonneg (x : V → ℝ) : 0 ≤ x ⬝ᵥ (signlessLap G) *ᵥ x := by
  rw [dotProduct_signlessLap G x]
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) (by norm_num)
  by_cases h : G.Adj i j <;> simp [h, sq_nonneg]

/-! ## 2. Its kernel, with no hypothesis on the graph -/

/-- **THE KERNEL OF THE SIGNLESS LAPLACIAN IS THE SIGN-FLIPPING VECTORS**, for every finite graph:
no regularity, no connectivity, no two-colourability assumed. -/
theorem dotProduct_signlessLap_eq_zero_iff (x : V → ℝ) :
    x ⬝ᵥ (signlessLap G) *ᵥ x = 0 ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [dotProduct_signlessLap G x, div_eq_zero_iff]
  constructor
  · rintro (hzero | h2)
    · intro u v huv
      have hnn : ∀ i ∈ (Finset.univ : Finset V),
          0 ≤ ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0 :=
        fun i _ => Finset.sum_nonneg fun j _ => by
          by_cases h : G.Adj i j <;> simp [h, sq_nonneg]
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero u (Finset.mem_univ u)
      have hnn2 : ∀ j ∈ (Finset.univ : Finset V),
          0 ≤ (if G.Adj u j then (x u + x j) ^ 2 else 0) :=
        fun j _ => by by_cases h : G.Adj u j <;> simp [h, sq_nonneg]
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp h1 v (Finset.mem_univ v)
      rw [if_pos huv] at h3
      have h4 : x u + x v = 0 := by
        have := sq_eq_zero_iff.mp h3
        linarith
      linarith
    · exact absurd h2 (by norm_num)
  · intro hflip
    left
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases h : G.Adj i j
    · rw [if_pos h, hflip i j h]; ring
    · rw [if_neg h]

/-! ## 3. The degree bound's equality case in the same generality -/

/-- **THE EQUALITY CASE WITH NO REGULARITY.** `LaplacianSharpEquality.quadForm_eq_iff_neg_adj` with
`Δ‖x‖²` replaced by the degree-weighted sum it was a collapse of. -/
theorem quadForm_eq_iff_neg_adj_of_degree (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (∑ i : V, (G.degree i : ℝ) * x i ^ 2)
      ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [← dotProduct_signlessLap_eq_zero_iff G x, dotProduct_signlessLap G x,
    sum_adj_add_sq_of_degree G x]
  constructor <;> intro h <;> linarith

/-- **THE REGULAR CASE IS RECOVERED**, so nothing proved with regularity is restated or lost
(`ERRATUM 201`). -/
example {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x)
      ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [← quadForm_eq_iff_neg_adj_of_degree G x]
  have hdeg : (∑ i : V, (G.degree i : ℝ) * x i ^ 2) = (Δ : ℝ) * (x ⬝ᵥ x) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hreg i]; ring
  rw [hdeg]
  constructor <;> intro h <;> linarith

end LaplacianSignless
