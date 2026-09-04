import AdjNormRegular
import LaplacianNormLowerBound

/-!
# The adjacency norm is at least the square root of the degree, at every vertex of every graph

`AdjNormRegular` proves `‖G.adjMatrix ℝ‖ = Δ` and **needs the graph to be regular** to do it: the
lower half of that equality comes from the all-ones vector, which is an eigenvector only when every
degree agrees. Off that class the estate had **no lower bound of any kind** on the adjacency norm —
`SymmetricOpNorm` gives `‖A‖ ≤ Δ` and nothing gives anything from below.

**This file removes the hypothesis and pays for it in the constant** — which is a deepening in one
direction and a weakening in the other, and neither statement contains the other (`ERRATUM 337`:
both stay). At every vertex of every finite graph

```
Real.sqrt (G.degree v) ≤ ‖G.adjMatrix ℝ‖
```

**with no hypothesis of any kind**: no regularity, no connectivity, no mass, and not even a
positive degree — an isolated vertex is a triviality (`√0 = 0`, and a norm is nonnegative), not an
exception, and it is discharged inside the statement rather than fenced off in a caveat. Read at a
vertex of maximum degree and set beside `SymmetricOpNorm.norm_adjMatrix_le` this gives
`√Δ ≤ ‖A‖ ≤ Δ`, **the first two-sided bracket the estate has on this operator away from the regular
class** — where `AdjNormRegular` collapses it to an equality that this theorem, read on a regular
graph, is strictly weaker than.

The positive-degree form is kept as `sqrt_degree_le_norm_adjMatrix_of_pos`, because that is where
the work is: the hypothesis exists only to make the witness nonzero.

## The witness

`√(deg v)` at `v`, `1` at each neighbour of `v`, `0` elsewhere — the same star shape
`LaplacianDeltaPlusOne.starVec` uses for the Laplacian, with the signs dropped and the centre
rescaled. The rescaling is the whole content: the quadratic form of the adjacency matrix on this
vector is at least `2 · deg v · √(deg v)` while its square norm is exactly `2 · deg v`, and the two
`deg v` factors cancel. **All entries are nonnegative and all entries of `A` are nonnegative**, so
every term thrown away is thrown away for free, exactly as in the Laplacian case.

## Sharpness, stated at exactly the strength this estate has earned

`AdjNormRegular` states, and does not formalise, that `‖A‖ ≤ Δ` is loose off the regular class,
witnessed by the star `K_{1,n}`, whose adjacency eigenvalues are `±√n`. **The theorem below is
exactly the lower half of that example**: read at the centre it says `√n ≤ ‖A‖`.

**Whether it is ATTAINED there is classical and is not proved anywhere in this estate.** The
sharpness of `√(deg v)` rests entirely on the star's value `‖A‖ = √n`, and that value is prose in
three files and a theorem in none — so the honest statement is that *classically* no argument of
this shape can do better than the square root, and that this estate has **not** established it.
`ERRATUM 439`'s rule points the other way here and still applies: a sentence about what is
impossible is a claim about every route, and this file is not entitled to it. The item that would
settle it is on the watchlist, filed by this unit.

> ⚠ **2026-09-04, WITHIN THE DAY: SETTLED, AND BY MORE THAN THE PARAGRAPH ABOVE ASKED FOR**
> (`ERRATUM 94`; the paragraph is kept exactly as written, because it was right to refuse).
> `StarAdjNormExact.norm_adjMatrix_starGraph_eq` proves `‖A‖ = √(card V − 1)` on the star, so the
> constant IS attained — and `StarAdjNormExact.le_sqrt_of_universal_degree_bound` goes further:
> **no function of the degree alone beats the square root.** If `f (G.degree v) ≤ ‖G.adjMatrix ℝ‖`
> at every vertex of every finite graph then `f n ≤ √n` for every `n`.
> `StarAdjNormExact.sqrt_is_the_optimal_degree_bound` states attainment and optimality as one pair,
> because a sharpness claim is two statements and this estate has previously written one and
> implied the other. **What the paragraph above says about the ESTATE was true when written and has
> been false since that file landed**; what it says about method — that a claim of impossibility
> needs proof, not inheritance — is why the proof exists.

## What is NOT here

**Not the maximum.** The statement is per-vertex. `√Δ ≤ ‖A‖` for a maximum-degree vertex is the
same theorem read at that vertex, and no `Finset.sup'` wrapper is provided (`RayleighVariational`
has the pattern if one is ever wanted).

**Not the star's exact norm.** `‖A‖ = √n` on `K_{1,n}` needs the matching upper bound and a star
to state it about, and this file supplies neither — **no `K_{1,n}` is constructed anywhere in
`paper_f/`**, which was checked and not assumed. The route is visible: `A²` on a star is `diag(n)`
at the centre and the all-ones block on the leaves, so `‖A²‖ = n`, and for a real symmetric matrix
`‖A * A‖ = ‖A‖ ‖A‖` closes it. **The instrument was probed, not guessed** — Mathlib's
`Matrix.l2_opNorm_conjTranspose_mul_self` states exactly that at this pin, with no `CStarRing`
detour needed, and `SimpleGraph.transpose_adjMatrix` supplies the symmetry. **It is still not
attempted and not costed here** (`ERRATUM 246`): what is claimed is that the tool exists, not that
the theorem is cheap.

> ⚠ **2026-09-04: DONE, AND NONE OF THIS PARAGRAPH'S ROUTE WAS USED** (`ERRATUM 94`,
> **`ERRATUM 443`**, within the day). `StarAdjNormExact` forms no `A²`, computes no all-ones block
> and never invokes `l2_opNorm_conjTranspose_mul_self`. The star's quadratic form is
> `2·x c·∑_{v ≠ c} x v`; Cauchy–Schwarz and `2ab ≤ a² + b²` give `−√n • 1 ≼ A ≼ √n • 1` directly,
> and `SymmetricOpNorm.l2_opNorm_le_of_abs_le` — which already existed — converts that to the norm.
> **The paragraph is kept because the route it names is real and would also work.** What was wrong
> was the definite article.

**Not Perron–Frobenius.** `‖A‖ = Δ ⟹ regular` for connected graphs stays open exactly where
`AdjNormRegular` left it. A lower bound below `Δ` is not a converse.

**No wall moves.** `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjNormSqrtDegree

open Matrix Finset SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The witness -/

/-- `√(deg v)` at `v`, `1` at each neighbour of `v`, `0` elsewhere. -/
noncomputable def sqrtStar (v : V) : V → ℝ :=
  fun p => if p = v then Real.sqrt (G.degree v) else if G.Adj v p then 1 else 0

variable {G}

theorem sqrtStar_self (v : V) : sqrtStar G v v = Real.sqrt (G.degree v) := by simp [sqrtStar]

theorem sqrtStar_nbr {v u : V} (h : G.Adj v u) : sqrtStar G v u = 1 := by
  have hne : u ≠ v := (G.ne_of_adj h).symm
  simp [sqrtStar, hne, h]

theorem sqrtStar_nonneg (v : V) (p : V) : 0 ≤ sqrtStar G v p := by
  unfold sqrtStar
  split_ifs with h1 h2
  · exact Real.sqrt_nonneg _
  · exact zero_le_one
  · exact le_rfl

theorem sqrtStar_ne_zero {v : V} (hdeg : 1 ≤ G.degree v) : sqrtStar G v ≠ 0 := by
  intro h0
  have hv := congrFun h0 v
  rw [sqrtStar_self] at hv
  simp only [Pi.zero_apply] at hv
  have hpos : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast hdeg
  have hs : 0 < Real.sqrt (G.degree v) := Real.sqrt_pos.mpr hpos
  rw [hv] at hs
  exact lt_irrefl 0 hs

/-- **`x ⬝ᵥ x = 2 · deg v`.** One square `(√deg)² = deg` at the centre and `deg v` ones on the
neighbours. -/
theorem dotProduct_sqrtStar_self (v : V) :
    sqrtStar G v ⬝ᵥ sqrtStar G v = 2 * (G.degree v : ℝ) := by
  classical
  rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ v), sqrtStar_self]
  have hsq : Real.sqrt (G.degree v) * Real.sqrt (G.degree v) = (G.degree v : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hrest : ∑ p ∈ Finset.univ.erase v, sqrtStar G v p * sqrtStar G v p
      = ∑ p ∈ Finset.univ.erase v, (if G.Adj v p then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
    by_cases hadj : G.Adj v p
    · rw [sqrtStar_nbr hadj]; simp [hadj]
    · simp [sqrtStar, hpv, hadj]
  have hcount : ∑ p ∈ Finset.univ.erase v, (if G.Adj v p then (1 : ℝ) else 0)
      = ∑ p : V, (if G.Adj v p then (1 : ℝ) else 0) := by
    refine Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro p _ hp
    have hpv : p = v := by simpa [Finset.mem_erase] using hp
    subst hpv
    simp
  rw [hrest, hcount, ← G.degree_eq_sum_if_adj (R := ℝ) v, hsq]
  ring

/-! ## 2. Throwing terms away is free -/

/-- Every summand of `∑ p, x p * (A *ᵥ x) p` is nonnegative, because both factors are. -/
theorem quadForm_summand_nonneg (v : V) (p : V) :
    0 ≤ sqrtStar G v p * ((G.adjMatrix ℝ) *ᵥ sqrtStar G v) p := by
  refine mul_nonneg (sqrtStar_nonneg v p) ?_
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  exact Finset.sum_nonneg fun u _ => sqrtStar_nonneg v u

/-- **`2 · deg v · √(deg v) ≤ xᵀAx`.** The centre row contributes `√deg · deg` and each of the
`deg v` neighbour rows contributes at least `1 · √deg`, because the centre is one of that
neighbour's own neighbours and the rest of its row is nonnegative. -/
theorem le_quadForm_sqrtStar (v : V) :
    2 * (G.degree v : ℝ) * Real.sqrt (G.degree v)
      ≤ sqrtStar G v ⬝ᵥ (G.adjMatrix ℝ) *ᵥ sqrtStar G v := by
  classical
  set x := sqrtStar G v with hx
  set f : V → ℝ := fun p => x p * ((G.adjMatrix ℝ) *ᵥ x) p with hf
  have hfp : ∀ p : V, f p = x p * ((G.adjMatrix ℝ) *ᵥ x) p := fun _ => rfl
  have hq : x ⬝ᵥ (G.adjMatrix ℝ) *ᵥ x = ∑ p : V, f p := rfl
  have hnn : ∀ p : V, 0 ≤ f p := by
    intro p
    rw [hfp p, hx]
    exact quadForm_summand_nonneg v p
  -- the centre row
  have hcentre : f v = Real.sqrt (G.degree v) * (G.degree v : ℝ) := by
    have hrow : ((G.adjMatrix ℝ) *ᵥ x) v = (G.degree v : ℝ) := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      have hone : ∀ u ∈ G.neighborFinset v, x u = (1 : ℝ) := by
        intro u hu
        rw [hx]
        exact sqrtStar_nbr ((SimpleGraph.mem_neighborFinset _ _ _).mp hu)
      rw [Finset.sum_congr rfl hone, Finset.sum_const,
        SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
    have hxv : x v = Real.sqrt (G.degree v) := by rw [hx]; exact sqrtStar_self v
    rw [hfp v, hrow, hxv]
  -- each neighbour row
  have hnbr : ∀ u ∈ G.neighborFinset v, Real.sqrt (G.degree v) ≤ f u := by
    intro u hu
    have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    have hvu : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj.symm
    have hrow : Real.sqrt (G.degree v) ≤ ((G.adjMatrix ℝ) *ᵥ x) u := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      have hsingle : x v ≤ ∑ w ∈ G.neighborFinset u, x w := by
        refine Finset.single_le_sum (fun w _ => ?_) hvu
        rw [hx]; exact sqrtStar_nonneg v w
      have hxv : x v = Real.sqrt (G.degree v) := by rw [hx]; exact sqrtStar_self v
      rwa [hxv] at hsingle
    have hxu : x u = 1 := by rw [hx]; exact sqrtStar_nbr hadj
    rw [hfp u, hxu, one_mul]
    exact hrow
  have hnbrsum : (G.degree v : ℝ) * Real.sqrt (G.degree v)
      ≤ ∑ u ∈ G.neighborFinset v, f u := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hnbr)
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  -- the whole sum dominates the centre plus the neighbours
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    have h : G.Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj h).symm, Finset.mem_univ u⟩
  have hsplit : ∑ p : V, f p = f v + ∑ p ∈ Finset.univ.erase v, f p :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hrest : ∑ u ∈ G.neighborFinset v, f u ≤ ∑ p ∈ Finset.univ.erase v, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
  rw [hq, hsplit, hcentre]
  linarith

/-! ## 3. The bound -/

/-- **`√(deg v) ≤ ‖G.adjMatrix ℝ‖` AT EVERY VERTEX OF POSITIVE DEGREE OF EVERY FINITE GRAPH.**
The hypothesis is only there to make the witness nonzero, and `sqrt_degree_le_norm_adjMatrix`
removes it. -/
theorem sqrt_degree_le_norm_adjMatrix_of_pos (v : V) (hdeg : 1 ≤ G.degree v) :
    Real.sqrt (G.degree v) ≤ ‖G.adjMatrix ℝ‖ := by
  have hT : (G.adjMatrix ℝ)ᵀ = G.adjMatrix ℝ := G.transpose_adjMatrix (α := ℝ)
  refine LaplacianNormLowerBound.le_opNorm_of_le_quadForm hT (sqrtStar_ne_zero hdeg) ?_
  rw [dotProduct_sqrtStar_self]
  exact le_of_eq_of_le (by ring) (le_quadForm_sqrtStar (G := G) v)

/-- **`√(deg v) ≤ ‖G.adjMatrix ℝ‖` AT EVERY VERTEX OF EVERY FINITE GRAPH**, with no hypothesis of
any kind: no regularity, no connectivity, no mass, no positive degree. An isolated vertex is not an
exception but a triviality — `√0 = 0` and a norm is nonnegative — and saying that in the statement
rather than in a caveat is the point. Read at a vertex of maximum degree this is `√Δ ≤ ‖A‖`, which
with `SymmetricOpNorm.norm_adjMatrix_le` brackets the adjacency norm off the regular class for the
first time. -/
theorem sqrt_degree_le_norm_adjMatrix (v : V) :
    Real.sqrt (G.degree v) ≤ ‖G.adjMatrix ℝ‖ := by
  rcases Nat.eq_zero_or_pos (G.degree v) with h | h
  · rw [h]
    simp [norm_nonneg]
  · exact sqrt_degree_le_norm_adjMatrix_of_pos v h

/-- **The same in the form the degree bound is stated in**: the square of the norm is at least the
degree, which avoids the square root at the call site. Also hypothesis-free. -/
theorem degree_le_norm_adjMatrix_sq (v : V) :
    (G.degree v : ℝ) ≤ ‖G.adjMatrix ℝ‖ ^ 2 := by
  have h := sqrt_degree_le_norm_adjMatrix (G := G) v
  have hnn : (0 : ℝ) ≤ Real.sqrt (G.degree v) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (G.degree v) ^ 2 = (G.degree v : ℝ) :=
    Real.sq_sqrt (by positivity)
  nlinarith [h, hnn]

end AdjNormSqrtDegree
