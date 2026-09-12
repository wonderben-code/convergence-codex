import UnbalancedMultipartiteDiamond

/-!
# Algebraic multiplicity is geometric multiplicity — and one signless characteristic polynomial

**FOUR FILES OF THIS CHAIN LISTED THE SAME UNDONE ITEM.** `MultipartiteCharpoly` wrote the
multipartite Laplacian's polynomial as `X·(X − N)^{r−1}·∏ₙ(X − (N − n))^{kₙ(n−1)}` and said, in its
own list of what it had not checked, *no agreement of these exponents with
`Polynomial.rootMultiplicity`*; the three signless units since have repeated the clause about `Q`.
**It is one theorem for every real Hermitian matrix at once**, and this file is that theorem plus
its instances.

## The route, and it invokes nothing new

**Mathlib's** `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` already says the root multiset is
the image of the eigenvalue enumeration — it is **not restated here**, and `HermitianCharpoly`'s own
fence names it, which is where I should have looked first (`ERRATUM 510`). Counting `μ` in a mapped
multiset is counting the fibre over `μ`, and
`HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` identified that fibre's size with
the eigenspace's dimension several units ago. **So this theorem is two library facts composed**,
and the reason it took four fences to appear is that nobody put them side by side.

## What is proved

**`rootMultiplicity_charpoly`** — for every real Hermitian `A` and every real `μ`, the multiplicity
of `μ` as a root of `Matrix.charpoly A` **equals** `finrank` of its eigenspace.
**`rootMultiplicity_charpoly_lapMatrix`, `rootMultiplicity_charpoly_signlessLap`** — hence for both
graph matrices, on any finite simple graph, with no hypothesis beyond the graph.

**`rootMultiplicity_lapMatrix_multi_zero`, `_top`, `_size`** — hence the three exponents
`MultipartiteCharpoly` computed — `1` at `0`, `r − 1` at `N`, `kₙ(n − 1)` at `N − n` — **are** root
multiplicities, which is the clause that file left open.

**`rootMultiplicity_signless_diamond_two`, `_add_sqrt`, `_sub_sqrt`,
`image_eigenvalues_signless_diamond`, `charpoly_signless_diamond`** — and the previous unit's
spectrum becomes a polynomial:
`(signlessLap …).charpoly = (X − 2)²·(X − (3 + √5))·(X − (3 − √5))` at parts of sizes `1`, `1`
and `2`. That is the fence the previous unit wrote — *no characteristic polynomial, here or
anywhere for `Q` on this family* — closed at the one graph whose spectrum is known.

## What is NOT here

* **NO GENERAL CHARACTERISTIC POLYNOMIAL FOR `Q` ON THE FAMILY.** The product needs the eigenvalue
  set, which needs the secular roots, which at `r` parts is a polynomial of degree up to `r`.
  One graph is done because its secular equation is a quadratic. Not attempted (`ERRATUM 246`).
* **NOTHING ABOUT A NON-HERMITIAN MATRIX**, and the hypothesis is doing all the work: for a Jordan
  block the two multiplicities differ, so no version of this survives dropping it.
* **NOTHING OVER `ℂ`.** `Matrix.IsHermitian.charpoly_eq` is instantiated at `ℝ` only, as everywhere
  in this chain, and the complex case is not a corollary of what is written here.
* **NO STATEMENT ABOUT THE SUM OF THE MULTIPLICITIES** over all roots. It is the vertex count and
  the ingredients are here, but nothing below says so.
* **THE ROOT MULTISET IS NOT PROVED HERE.** It is `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`
  and it is Mathlib's; a draft of this file re-proved it before the name was grepped for, and the
  re-proof was deleted (`ERRATUM 510`).
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `Fintype` and `DecidableEq` on the index
type and `Matrix.IsHermitian A` for the general theorem; for the multipartite instances, the same
`∀ i, Nonempty (V i)`, `2 ≤ card ι`, `n ≠ 0` and `n ≠ N` the theorems they quote carry, and nothing
more; for the diamond, nothing beyond the concrete type. **No mass, no propagator, and no metric
anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HermitianRootMultiplicity

open Matrix Polynomial

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## 1. The roots of a real Hermitian matrix's characteristic polynomial -/

/-- **ALGEBRAIC MULTIPLICITY IS GEOMETRIC MULTIPLICITY**, for every real Hermitian matrix. -/
theorem rootMultiplicity_charpoly {A : Matrix m m ℝ} (hA : A.IsHermitian) (μ : ℝ) :
    Polynomial.rootMultiplicity μ A.charpoly
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  classical
  rw [← Polynomial.count_roots, hA.roots_charpoly_eq_eigenvalues, Multiset.count_map,
    HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA μ, Fintype.card_subtype]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, eq_comm]
  rfl

/-! ## 2. The two graph matrices -/

theorem rootMultiplicity_charpoly_lapMatrix (G : SimpleGraph m) [DecidableRel G.Adj] (μ : ℝ) :
    Polynomial.rootMultiplicity μ (G.lapMatrix ℝ).charpoly
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) :=
  rootMultiplicity_charpoly (FieldSimpleConverse.lapMatrix_isHermitian G) μ

theorem rootMultiplicity_charpoly_signlessLap (G : SimpleGraph m) [DecidableRel G.Adj] (μ : ℝ) :
    Polynomial.rootMultiplicity μ (LaplacianSignless.signlessLap G).charpoly
      = Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' (LaplacianSignless.signlessLap G) - μ • LinearMap.id)) :=
  rootMultiplicity_charpoly (LaplacianSignlessDefinite.signlessLap_isHermitian G) μ

/-! ## 3. The multipartite Laplacian's exponents are root multiplicities -/

section Multipartite

open SimpleGraph UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem rootMultiplicity_lapMatrix_multi_zero (hne : ∀ i, Nonempty (V i))
    (hι : 2 ≤ Fintype.card ι) :
    Polynomial.rootMultiplicity 0
        ((completeMultipartiteGraph V).lapMatrix ℝ).charpoly = 1 := by
  rw [rootMultiplicity_charpoly_lapMatrix, finrank_eigenspace_zero hne hι]

theorem rootMultiplicity_lapMatrix_multi_top (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    Polynomial.rootMultiplicity (Fintype.card (Σ i, V i) : ℝ)
        ((completeMultipartiteGraph V).lapMatrix ℝ).charpoly = Fintype.card ι - 1 := by
  rw [rootMultiplicity_charpoly_lapMatrix, finrank_eigenspace_top hne hι]

theorem rootMultiplicity_lapMatrix_multi_size {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    Polynomial.rootMultiplicity ((Fintype.card (Σ i, V i) : ℝ) - n)
        ((completeMultipartiteGraph V).lapMatrix ℝ).charpoly
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) := by
  rw [rootMultiplicity_charpoly_lapMatrix, finrank_eigenspace_size hn0 hnN]

end Multipartite

/-! ## 4. `Q`'s characteristic polynomial at the diamond -/

section Diamond

open SimpleGraph LaplacianSignless UnbalancedMultipartiteDiamond

theorem rootMultiplicity_signless_diamond_two :
    Polynomial.rootMultiplicity 2
        (signlessLap (completeMultipartiteGraph DiamondPart)).charpoly = 2 := by
  rw [rootMultiplicity_charpoly_signlessLap,
    UnbalancedMultipartiteSecular.finrank_signless_eigenspace_diamond]

theorem rootMultiplicity_signless_diamond_add_sqrt :
    Polynomial.rootMultiplicity (3 + Real.sqrt 5)
        (signlessLap (completeMultipartiteGraph DiamondPart)).charpoly = 1 := by
  rw [rootMultiplicity_charpoly_signlessLap, finrank_signless_diamond_add_sqrt]

theorem rootMultiplicity_signless_diamond_sub_sqrt :
    Polynomial.rootMultiplicity (3 - Real.sqrt 5)
        (signlessLap (completeMultipartiteGraph DiamondPart)).charpoly = 1 := by
  rw [rootMultiplicity_charpoly_signlessLap, finrank_signless_diamond_sub_sqrt]

theorem image_eigenvalues_signless_diamond :
    Finset.univ.image (LaplacianSignlessDefinite.signlessLap_isHermitian
        (completeMultipartiteGraph DiamondPart)).eigenvalues
      = {2, 3 + Real.sqrt 5, 3 - Real.sqrt 5} := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff, isEigenvalue_signless_diamond]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL AT `K₄` MINUS AN EDGE.** -/
theorem charpoly_signless_diamond :
    (signlessLap (completeMultipartiteGraph DiamondPart)).charpoly
      = (X - C (2 : ℝ)) ^ 2 * (X - C (3 + Real.sqrt 5)) * (X - C (3 - Real.sqrt 5)) := by
  have hb2 := two_lt_sqrt_five
  have hb3 := sqrt_five_lt_three
  have hA := LaplacianSignlessDefinite.signlessLap_isHermitian
    (completeMultipartiteGraph DiamondPart)
  have hne1 : (2 : ℝ) ∉ ({3 + Real.sqrt 5, 3 - Real.sqrt 5} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h) <;> linarith
  have hne2 : (3 : ℝ) + Real.sqrt 5 ∉ ({3 - Real.sqrt 5} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    intro h; linarith
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank hA, image_eigenvalues_signless_diamond,
    Finset.prod_insert hne1, Finset.prod_insert hne2, Finset.prod_singleton,
    UnbalancedMultipartiteSecular.finrank_signless_eigenspace_diamond,
    finrank_signless_diamond_add_sqrt, finrank_signless_diamond_sub_sqrt]
  ring

end Diamond

end HermitianRootMultiplicity
