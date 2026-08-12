import BoxGraph

/-!
# Every site of the `n^d` box has at most `2d` neighbours

## Read the correction first: this file was written on a false premise

`FieldThreshold`'s header said, of the estimate that would sharpen its own threshold:

> the energy comparison wants `isingH (flip S σ) ≤ isingH σ + c·|S|`, whose constant comes from a
> **degree bound on `adj`**, and **the estate has none** … That bound is itself a bounded build
> … and nothing here has tried it.

**Both halves of that were false, and `ERRATUM 131` records how.** The estate has had the degree
bound since `PlusClassVanishes` — `card_adj_le_four` and `card_adj_le_four'`, both exactly the
`d = 2` statement — and has had the single-site energy comparison too,
`PlusClassVanishes.isingH_flipAt_le`, with the same constant `16`. The probe that produced the
word "none" was truncated: it scanned the first `20` of the `96` files that mention `adj`, and
`PlusClassVanishes` is the `74`th.

**What is left of this file after that correction is real, and it is a generalisation rather than
a first.** The pre-existing bound is `d = 2` only, and stated as a raw `Finset` cardinality:

> **`card_adj_le`** — for every site of the `n^d` box, at most `2d` sites are adjacent to it, in
> **every** dimension. That is queue item 4's shape exactly: one restrictive hypothesis — the
> dimension — removed from a result the estate already had.
> **`boxGraph_degree_le`** — and the same fact in the `SimpleGraph.degree` vocabulary, which the
> estate also did not have, so a consumer working with `boxGraph` need not unfold a filter.

**The `d = 2` corollary this file first carried has been deleted**, because it was a second copy
of `PlusClassVanishes.card_adj_le_four` under a new name, and duplicated declaration names are
already an open question for the author here.

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

**It does not move the Peierls wall or the field threshold**, and — now that the premise is
corrected — it does not supply a missing ingredient either, because the ingredient was not
missing. `FieldThreshold.magnetisation_threshold` is unchanged and still quadratic in the side,
and the remaining legs of the sharper estimate are **not attempted here**.

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

end BoxDegree
