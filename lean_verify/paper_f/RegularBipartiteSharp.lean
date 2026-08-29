import LaplacianBoundSharp

/-!
# Which regular graphs attain the degree bound: two-colourable ones do, and the cycle was a case

`LaplacianBoundSharp` proved `LaplacianDegreeBound`'s constant `2Δ + m²` is exactly right on the
**even** cycle, and `CycleSpectralBound` proved it is **not** attained on the odd one. The item
those two left open asks which regular graphs attain it, and observes what the pair suggests: the
even cycle is two-colourable and the odd cycle is not.

**One direction of that is this file, and it is four lines of arithmetic.** If `σ` is a `±1`
labelling that flips across every edge then, at every site,

```
(massive G m *ᵥ σ) v  =  (deg v + m²)·σ v  −  Σ_{u ∼ v} σ u  =  (2·deg v + m²)·σ v
```

because every neighbour's label is `−σ v`. **The even cycle's alternating vector is that labelling**
and nothing about cycles is used.

## What is proved

* `IsSignColouring`, and **`exists_signColouring_of_colorable`** — a graph Mathlib calls
  `Colorable 2` has one, so this is two-colourability in `±1` form and not a private notion;
* **`massive_mulVec_signColouring`** — the identity above, **with no regularity hypothesis**: the
  factor is the site's *own* degree;
* **`sum_le_of_massive_le_smul_one`** — hence, still without regularity, `massive ≼ c·1` forces
  `Σ_v (2·deg v + m²) ≤ c·|V|`. That is an **averaged** sharpness statement and it is the general
  form;
* **`massive_le_smul_one_iff_of_regular`** — and when the graph *is* `Δ`-regular the average
  collapses and the bound is an `iff`: `massive ≼ c·1` exactly when `2Δ + m² ≤ c`. The reverse
  half is `LaplacianDegreeBound.massive_le_smul_one` itself, so the two together say the constant
  is right and not merely safe;
* `alt_isSignColouring`, and the `example` below it — **`LaplacianBoundSharp`'s even-cycle `iff` is
  this at `Δ = 2`**, so the generalisation is instantiated at the statement it generalises
  (`ERRATUM 201`).

## What this is NOT

**It is not the characterisation.** What is proved is *two-colourable and regular ⟹ attained*. The
converse — attained ⟹ two-colourable — is **not proved here and not attempted**, and **nothing in
this estate proves it either: checked 2026-08-29**, no declaration in `paper_f` relates
two-colourability to an eigenvalue, to attainment, or to `massive`, and this file is the only one
mentioning `IsSignColouring`. The odd cycle is consistent with the converse (`CycleSpectralBound`)
and one family is not a proof.

**It says nothing about a graph that is two-colourable and not regular** beyond the averaged
statement, which is genuinely weaker: it bounds `c` below by the *average* of `2·deg + m²`, and
without regularity that is all the sign colouring gives.

**The estate's own lattice is not reached, and the missing step is one sentence.**
`TorusBipartite.torusGraph_colorable_two` proves the periodic lattice is two-colourable at even
side length **in every dimension**, so `exists_signColouring_of_colorable` applies to it directly.
What is missing is that `torusGraph d n` is `2d`-**regular**: the estate has
`TorusDecay.torusGraph_degree_le`, an inequality, and no equality. **That is recorded as its own
item and is not attempted here** (`ERRATUM 246`: no cost is claimed).

> **^ THE LAST SENTENCE IS FALSE AND WAS FALSE WHEN WRITTEN** (`ERRATUM 336`, 2026-08-29).
> Paragraph kept as written (`ERRATUM 94`). The estate has had the **equality** since
> `TorusEmbeddingAllDims.torusGraph_degree_eq`, with
> `RegularSelfEmbedding.torusGraph_isRegularOfDegree`
> packaging it as `IsRegularOfDegree (2*d)` — and `TorusRegular` is the instantiation, which needed
> no new graph theory at all. What produced the false clause was a probe truncated by `head -6`,
> read as though it were exhaustive; the erratum records that cause.

**`OS4` does not move, no measure is involved, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RegularBipartiteSharp

open Matrix GraphLaplacian SimpleGraph
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Sign colourings -/

/-- A `±1` labelling that flips across every edge — a proper two-colouring written additively. -/
def IsSignColouring (G : SimpleGraph V) (σ : V → ℝ) : Prop :=
  (∀ v, σ v = 1 ∨ σ v = -1) ∧ ∀ u v, G.Adj u v → σ u = - σ v

omit [Fintype V] [DecidableEq V] in
theorem exists_signColouring_of_colorable {G : SimpleGraph V} (h : G.Colorable 2) :
    ∃ σ : V → ℝ, IsSignColouring G σ := by
  classical
  obtain ⟨C⟩ := h
  have key : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  refine ⟨fun v => if C v = 0 then 1 else -1, fun v => ?_, fun u v huv => ?_⟩
  · by_cases hv : C v = 0 <;> simp [hv]
  · have hne : C u ≠ C v := C.valid huv
    by_cases hu : C u = 0
    · have hv : C v ≠ 0 := fun hv => hne (hu.trans hv.symm)
      simp [hu, hv]
    · have hv : C v = 0 := by
        by_contra hv
        exact hne ((key _ hu).trans (key _ hv).symm)
      simp [hu, hv]

/-! ## 2. The massive operator on a sign colouring -/

/-- **A SIGN COLOURING TURNS THE NEIGHBOUR SUM INTO A SECOND COPY OF THE DIAGONAL.** No
regularity is used: the factor is the site's own degree. -/
theorem massive_mulVec_signColouring (G : SimpleGraph V) [DecidableRel G.Adj] {σ : V → ℝ}
    (hσ : IsSignColouring G σ) (m : ℝ) (v : V) :
    (massive G m *ᵥ σ) v = (2 * (G.degree v : ℝ) + m ^ 2) * σ v := by
  classical
  have hterm : ∀ u ∈ G.neighborFinset v, σ u = - σ v := by
    intro u hu
    exact hσ.2 u v (((SimpleGraph.mem_neighborFinset _ _ _).mp hu).symm)
  have hsum : ∑ u ∈ G.neighborFinset v, σ u = (G.degree v : ℝ) * (- σ v) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [GraphGreenPositive.massive_mulVec_apply, hsum]
  ring

omit [DecidableEq V] in
theorem dotProduct_self_signColouring {G : SimpleGraph V} {σ : V → ℝ}
    (hσ : IsSignColouring G σ) : σ ⬝ᵥ σ = (Fintype.card V : ℝ) := by
  have hone : ∀ v : V, σ v * σ v = 1 := by
    intro v
    rcases hσ.1 v with h | h <;> rw [h] <;> norm_num
  rw [dotProduct]
  simp [hone]

/-! ## 3. The bound, without regularity -/

/-- **AN AVERAGED SHARPNESS STATEMENT.** -/
theorem sum_le_of_massive_le_smul_one (G : SimpleGraph V) [DecidableRel G.Adj] {σ : V → ℝ}
    (hσ : IsSignColouring G σ) (m c : ℝ)
    (h : massive G m ≤ c • (1 : Matrix V V ℝ)) :
    ∑ v : V, (2 * (G.degree v : ℝ) + m ^ 2) ≤ c * (Fintype.card V : ℝ) := by
  have hq := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg σ
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hq
  have h1 : σ ⬝ᵥ (massive G m *ᵥ σ) = ∑ v : V, (2 * (G.degree v : ℝ) + m ^ 2) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [massive_mulVec_signColouring G hσ m v]
    rcases hσ.1 v with hv | hv <;> rw [hv] <;> ring
  have h2 : σ ⬝ᵥ ((c • (1 : Matrix V V ℝ)) *ᵥ σ) = c * (Fintype.card V : ℝ) := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_self_signColouring hσ]
  rw [h1, h2] at hq
  exact hq

/-! ## 4. And with regularity, the exact constant -/

theorem le_of_massive_le_smul_one_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) {σ : V → ℝ} (hσ : IsSignColouring G σ) [Nonempty V]
    (m c : ℝ) (h : massive G m ≤ c • (1 : Matrix V V ℝ)) : 2 * (Δ : ℝ) + m ^ 2 ≤ c := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum := sum_le_of_massive_le_smul_one G hσ m c h
  rw [Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => by rw [hreg v]), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_comm ((Fintype.card V : ℝ))] at hsum
  exact le_of_mul_le_mul_right hsum hcard

/-- **THE CONSTANT `2Δ + m²` IS EXACTLY RIGHT ON EVERY REGULAR TWO-COLOURABLE GRAPH.** -/
theorem massive_le_smul_one_iff_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) {σ : V → ℝ} (hσ : IsSignColouring G σ) [Nonempty V]
    (m c : ℝ) :
    massive G m ≤ c • (1 : Matrix V V ℝ) ↔ 2 * (Δ : ℝ) + m ^ 2 ≤ c := by
  refine ⟨le_of_massive_le_smul_one_of_regular G hreg hσ m c, fun hc => ?_⟩
  have hbase := LaplacianDegreeBound.massive_le_smul_one G (fun p => le_of_eq (by rw [hreg p])) m
  refine le_trans hbase (Matrix.le_iff.mpr ?_)
  rw [← sub_smul]
  exact (Matrix.PosSemidef.one).smul (by linarith)

/-! ## 5. The even cycle is an instance -/

theorem alt_isSignColouring (M : ℕ) :
    IsSignColouring (cycleGraph (2 * M + 4)) (LaplacianBoundSharp.alt (2 * M + 4)) := by
  constructor
  · intro v
    rcases Nat.even_or_odd v.val with hv | hv
    · exact Or.inl (by rw [LaplacianBoundSharp.alt, hv.neg_one_pow])
    · exact Or.inr (by rw [LaplacianBoundSharp.alt, hv.neg_one_pow])
  · intro u v huv
    rw [cycleGraph_adj] at huv
    rcases huv with h | h
    · have hu : u = v + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 v)
      rw [hu, LaplacianBoundSharp.alt_add_one]
    · have hv : v = u + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 u)
      rw [hv, LaplacianBoundSharp.alt_add_one, neg_neg]

/-- `LaplacianBoundSharp.massive_cycle_le_smul_one_iff` is this at the even cycle, so the
generalisation is instantiated at the statement it generalises. -/
example (M : ℕ) (m c : ℝ) :
    massive (cycleGraph (2 * M + 4)) m
        ≤ c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ) ↔ 4 + m ^ 2 ≤ c := by
  have hreg : (cycleGraph (2 * M + 4)).IsRegularOfDegree 2 :=
    fun v => cycleGraph_degree_three_le
  have h := massive_le_smul_one_iff_of_regular (cycleGraph (2 * M + 4)) hreg
    (alt_isSignColouring M) m c
  norm_num at h
  exact h

end RegularBipartiteSharp
