import BoxGraph

/-!
# Every site of the `n^d` box has at most `2d` neighbours

`FieldThreshold`'s header names the fence its own threshold sits behind, and then names the one
ingredient the sharper estimate needs and the estate does not have:

> the energy comparison wants `isingH (flip S σ) ≤ isingH σ + c·|S|`, whose constant comes from a
> **degree bound on `adj`**, and **the estate has none** … That bound is itself a bounded build —
> the four neighbours are tagged by which coordinate moved and in which direction — and nothing
> here has tried it.

This is that build, and it comes out in **any** dimension rather than only in two, because
`BoxGraph.adj` is already stated in any dimension and nothing in the argument cares:

> **`card_adj_le`** — for every site `p` of the `n^d` box, at most `2d` sites are adjacent to it.
> **`boxGraph_degree_le`** — the same as a statement about `SimpleGraph.degree`.
> **`card_isingAdj_le_four`** — and hence at most `4` in the estate's own two-dimensional lattice.

## The proof is a covering, not a tagging

The sentence quoted above proposed *tagging* each neighbour by `(coordinate, direction)` and
arguing the tag is injective. That works, but it has to **extract** the coordinate from an
existential, which in Lean means finding it rather than being handed it. Turning the argument
around removes that step entirely: instead of mapping neighbours **into** a `2d`-element type,
map a `2d`-element type **onto** a set containing all the neighbours.

`stepSite p i b` moves coordinate `i` of `p` one step up or down, **clamped at the ends of the
box**. The clamping is not a correctness worry and the file does not need a lemma about it: the
image is only ever used as an over-count, so a clamped step landing on `p` itself, or on a site
that is not a neighbour, costs nothing. What is needed is the one direction that matters —
`adj_eq_stepSite`, every neighbour **is** some `stepSite` — and that is where the two cases of
`adj`'s disjunction are discharged.

So no injectivity, no choice, no decidable search: a subset inclusion and `Finset.card_image_le`.

## What this does NOT do

**It does not move the Peierls wall or the field threshold.** It supplies one arithmetic
ingredient that `FieldThreshold`'s sharper estimate would need; the estimate itself — the flip
energy comparison, the stratification by the number of wrong boundary spins, the binomial sum —
is **not attempted here**. `FieldThreshold.magnetisation_threshold` is unchanged and still
quadratic in the side.

**And the bound is not claimed sharp at the boundary.** `2d` is the interior degree; corner and
edge sites have fewer. Nothing below distinguishes them, because an upper bound is all the
consumer wants.
-/

namespace BoxDegree

open BoxGraph

set_option linter.style.openClassical false
open scoped Classical

variable {d n : ℕ}

/-! ## 1. One step along one coordinate -/

/-- **THE STEP MAP.** `stepSite p i b` moves coordinate `i` of `p` up (`b = true`) or down,
clamped inside the box. Clamping makes it total; it is used only to over-count, so a clamped step
that lands back on `p` — or on a non-neighbour — is harmless and no lemma below rules it out. -/
def stepSite (p : Site d n) (i : Fin d) (b : Bool) : Site d n :=
  Function.update p i
    (if b then ⟨min ((p i).val + 1) (n - 1), by have := (p i).isLt; omega⟩
     else ⟨(p i).val - 1, by have := (p i).isLt; omega⟩)

/-- **EVERY NEIGHBOUR IS A STEP.** This is the only direction the count needs, and it is where
`adj`'s disjunction is discharged: an upward step is clamped to itself because `(q i).val < n`
forces `(p i).val + 1 ≤ n − 1`, and a downward step is `Nat` subtraction of one from a positive
number. -/
theorem adj_eq_stepSite {p q : Site d n} (h : adj p q) :
    ∃ t : Fin d × Bool, q = stepSite p t.1 t.2 := by
  obtain ⟨i, hoff, hstep⟩ := h
  rcases hstep with hup | hdown
  · refine ⟨(i, true), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepSite, Function.update_self]
      refine Fin.ext ?_
      change (q j).val = min ((p j).val + 1) (n - 1)
      have h1 := (q j).isLt
      omega
    · simp only [stepSite, Function.update_of_ne hj]
      exact (hoff j hj).symm
  · refine ⟨(i, false), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepSite, Function.update_self]
      refine Fin.ext ?_
      change (q j).val = (p j).val - 1
      omega
    · simp only [stepSite, Function.update_of_ne hj]
      exact (hoff j hj).symm

/-! ## 2. The count -/

/-- **AT MOST `2d` NEIGHBOURS**, in every dimension and for every site, boundary sites included
(where the truth is smaller and this bound does not say so). -/
theorem card_adj_le (p : Site d n) :
    ((Finset.univ : Finset (Site d n)).filter (fun q => adj p q)).card ≤ 2 * d := by
  classical
  have hsub : (Finset.univ : Finset (Site d n)).filter (fun q => adj p q)
      ⊆ (Finset.univ : Finset (Fin d × Bool)).image (fun t => stepSite p t.1 t.2) := by
    intro q hq
    obtain ⟨t, ht⟩ := adj_eq_stepSite (Finset.mem_filter.mp hq).2
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht.symm⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Finset.card_univ, Fintype.card_prod, Nat.mul_comm]

/-- The same fact in the vocabulary of `SimpleGraph`, so a consumer working with `boxGraph` does
not have to unfold a filter. -/
theorem boxGraph_degree_le (p : Site d n) : (boxGraph d n).degree p ≤ 2 * d := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  exact card_adj_le p

/-! ## 3. And four, in the estate's own lattice

`BoxGraph` §3 already proves the `d = 2` adjacency is `IsingFiniteVolume.adj` transported along
`sitePair`. Transporting a cardinality along the same equivalence is all that is left. -/

/-- **AT MOST FOUR NEIGHBOURS IN THE TWO-DIMENSIONAL LATTICE**, stated against
`IsingFiniteVolume.adj` — the relation `isingH` is actually summed over. -/
theorem card_isingAdj_le_four {n : ℕ} (P : IsingFiniteVolume.Site n) :
    ((Finset.univ : Finset (IsingFiniteVolume.Site n)).filter
      (fun Q => IsingFiniteVolume.adj P Q)).card ≤ 4 := by
  classical
  set p : Site 2 n := (sitePair n).symm P with hp
  have hPp : sitePair n p = P := by rw [hp, Equiv.apply_symm_apply]
  have hcard : ((Finset.univ : Finset (Site 2 n)).filter (fun q => adj p q)).card
      = ((Finset.univ : Finset (IsingFiniteVolume.Site n)).filter
          (fun Q => IsingFiniteVolume.adj P Q)).card := by
    refine Finset.card_equiv (sitePair n) fun q => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [adj_two_iff, hPp]
  rw [← hcard]
  exact (card_adj_le p).trans (by norm_num)

end BoxDegree
