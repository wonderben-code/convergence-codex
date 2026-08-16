import GreenDecay
import TorusReflection

/-!
# The same decay on the periodic box, which is the family the infinite-volume limit uses

`GreenDecay` proved that the propagator decays geometrically in the graph distance at a rate fixed
by a bound on the degrees, and drew the volume-uniform corollary **on the box**. The watchlist item
that wants a uniform bound is not about the box:

> ITEM: the infinite-volume limit along periodic boxes (W2's first leg)
> … **What does not exist is any statement relating different `n`**: no embedding of
> `torusGraph d n` into `torusGraph d (2n)`, **no uniform bound**, no notion of the limit measure's
> index set.
> WHAT WOULD BE NEEDED … (ii) … **uniform correlation bounds** plus a tightness argument, which is
> where the analysis lives.

So the corollary has to be on `torusGraph`, and the only thing standing between `GreenDecay` and
that was a degree bound, which no file had. **This supplies it and takes the corollary.**

## What is delivered

* `torusGraph_degree_le`: every site of `torusGraph d n` has at most `2d` neighbours, at every
  side length, `n = 1` and `n = 2` included (where the truth is smaller and this does not say so).
  Proved by the over-counting argument `BoxDegree` uses — exhibit a total step map and show every
  neighbour is in its image — with the clamped step replaced by the **cyclic** one.
* `torusGraph_green_abs_le`, `torusGraph_uniform`, `torusGraph_covariance_abs_le`: `GreenDecay`'s
  three conclusions, at `torusGraph d n`, with a rate depending on `d` and `m` and **not on `n`**.

## Exactly how far this moves the watchlist item, which is half of one clause of three

**It supplies the first half of clause (ii) and nothing else.** Clause (ii) reads *"uniform
correlation bounds **plus a tightness argument**, which is where the analysis lives"*, and the
second half is where the analysis lives, by the clause's own account. Not supplied here, and not
attempted:

* **the tightness argument** — nothing here is a statement about a sequence of measures;
* **clause (i)** — the item records that the torus covariances are **not** compatible, so there is
  no projective system, and a uniform bound does not create one;
* **clause (iii)** — the extension theorem, which `ERRATUM 100` and `ERRATUM 101` between them
  established is *absent* from Mathlib rather than merely unspecialised.

## Two amendments, 15 Aug 2026

**`torusGraph_uniform` is now an instance rather than a theorem of its own.** The distance at
which the propagator drops below `ε` depends on the degree bound, the mass and `ε` and on nothing
else, which this file demonstrated for the torus and `GreenDecay` demonstrated for the box, twice
over, with two proofs. `GreenDecay.exists_dist_uniform` now says it once for **every** finite
graph of bounded degree, with `N` produced before the graph is mentioned, and both family
versions are corollaries. Its separation hypothesis is `¬ Reachable ∨ N ≤ dist`, so this file's
statement inherits the weaker form.

**And the torus is now known to be connected, which the estate had never said.** `ERRATUM 165`
recorded a sentence about this file that could not be checked from inside the estate, because
`BoxGraph.boxGraph_connected` existed and no torus counterpart did. `torusGraph_connected` closes
that, in three lines and by the cheapest available route: **the box is a subgraph of the torus**
(`boxGraph_le_torusGraph`) — a box bond changes one coordinate by exactly one, which is `adjT`'s
first disjunct — so connectivity transports along `SimpleGraph.Connected.mono` and **the
wrap-around bonds the torus adds are never used**. The consequence, `torusGraph_reachable`,
settles what `165` left open: the generalised hypothesis's first disjunct is vacuous on this
family. That is not a defect of the generalisation, which buys everything on
`GreenClustering.cross_abs_le`'s arbitrary graphs; it is what *this* family gets, now said rather
than assumed.

**And "uniform correlation bounds" is read here as a bound on the two-point function, uniform in
`n`.** A first draft of this paragraph added that bounds on *higher* correlations would need the
Wick moment formula, which the estate does not have. **`GreenClustering`, written the same day,
makes that false as stated**: it bounds the whole generating functional's failure to factorise, for
all test functions at once, without Wick — so the higher orders are covered in that sense. What
remains true, and is the narrower claim this paragraph now makes, is that no *individual* higher
correlation is written down, because extraction is the Wick step. **The item stays open** on its
other clauses, and its trigger is unchanged.

*AMENDED 16 AUGUST 2026 (`ERRATUM 184`). The clause struck through above — "~~no individual
higher correlation is written down~~" — is **withdrawn**. **The diagnosis was right and the
verdict is now wrong.** Extracting one did mean differentiating under the integral, and the
identity that came out IS Wick's formula — `LatticeWickRecursion.wick_recursion` (`214454a`).
Individual higher correlations now exist **at every order** and, since
`LatticeHigherClustering` (`da0390a`), **they cluster**: in the pattern `(a, f^(n+1))` the
whole correlation decays geometrically, with nothing to subtract, and across components it is
exactly zero. **What is NOT withdrawn is everything else in this paragraph** — this file still
does not prove any of that, `OS4` is untouched, and the generating-functional route recorded
here remains what this file does.*


Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusDecay

open BoxGraph TorusReflection GraphLaplacian MeasureTheory ProbabilityTheory

set_option linter.style.openClassical false
open scoped Classical

variable {d n : ℕ} {m : ℝ}

/-! ## 1. One cyclic step along one coordinate

`BoxDegree.stepSite` clamps at the wall; here the step wraps. Both are total, and totality is the
only property the count needs — a step that lands on a non-neighbour, or back on `p`, only makes
the over-count larger.
-/

/-- **THE CYCLIC STEP MAP.** `stepT p i b` moves coordinate `i` of `p` one place forward
(`b = true`) or back around the circle `Fin n`. -/
def stepT (p : Site d n) (i : Fin d) (b : Bool) : Site d n :=
  Function.update p i
    (if b then ⟨if (p i).val + 1 = n then 0 else (p i).val + 1, by
        have := (p i).isLt; split <;> omega⟩
     else ⟨if (p i).val = 0 then n - 1 else (p i).val - 1, by
        have := (p i).isLt; split <;> omega⟩)

/-- **EVERY NEIGHBOUR IS A CYCLIC STEP.** The four disjuncts of `adjT` are the four cases, and the
two wrap-around ones are exactly what the clamped map could not produce. -/
theorem adjT_eq_stepT {p q : Site d n} (h : (torusGraph d n).Adj p q) :
    ∃ t : Fin d × Bool, q = stepT p t.1 t.2 := by
  obtain ⟨i, hoff, hne, hstep⟩ := h
  -- `n` is positive because `p i` inhabits `Fin n`
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (p i).isLt
  rcases hstep with hup | hdown | hzero | hwrap
  · -- `p i + 1 = q i`, an ordinary forward step
    refine ⟨(i, true), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepT, Function.update_self]
      refine Fin.ext ?_
      have hlt := (q j).isLt
      change (q j).val = if (p j).val + 1 = n then 0 else (p j).val + 1
      rw [if_neg (by omega)]
      omega
    · simp only [stepT, Function.update_of_ne hj]
      exact (hoff j hj).symm
  · -- `q i + 1 = p i`, an ordinary backward step
    refine ⟨(i, false), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepT, Function.update_self]
      refine Fin.ext ?_
      change (q j).val = if (p j).val = 0 then n - 1 else (p j).val - 1
      rw [if_neg (by omega)]
      omega
    · simp only [stepT, Function.update_of_ne hj]
      exact (hoff j hj).symm
  · -- `p i = 0` and `q i + 1 = n`: step back across the join
    refine ⟨(i, false), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepT, Function.update_self]
      refine Fin.ext ?_
      change (q j).val = if (p j).val = 0 then n - 1 else (p j).val - 1
      rw [if_pos hzero.1]
      omega
    · simp only [stepT, Function.update_of_ne hj]
      exact (hoff j hj).symm
  · -- `q i = 0` and `p i + 1 = n`: step forward across the join
    refine ⟨(i, true), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [stepT, Function.update_self]
      refine Fin.ext ?_
      change (q j).val = if (p j).val + 1 = n then 0 else (p j).val + 1
      rw [if_pos hwrap.2]
      omega
    · simp only [stepT, Function.update_of_ne hj]
      exact (hoff j hj).symm

/-! ## 2. The count -/

/-- **AT MOST `2d` NEIGHBOURS ON THE PERIODIC BOX**, in every dimension and at every side length.
At `n ≤ 2` the true degree is smaller — the two directions coincide — and this bound does not say
so, which is all the decay estimate needs. -/
theorem torusGraph_degree_le (p : Site d n) : (torusGraph d n).degree p ≤ 2 * d := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have hsub : (Finset.univ : Finset (Site d n)).filter (fun q => (torusGraph d n).Adj p q)
      ⊆ (Finset.univ : Finset (Fin d × Bool)).image (fun t => stepT p t.1 t.2) := by
    intro q hq
    obtain ⟨t, ht⟩ := adjT_eq_stepT (Finset.mem_filter.mp hq).2
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht.symm⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Finset.card_univ, Fintype.card_prod, Nat.mul_comm]

/-! ## 3. `GreenDecay` on the periodic box -/

/-- **THE DECAY RATE ON THE TORUS DOES NOT DEPEND ON THE SIDE LENGTH.** -/
theorem torusGraph_green_abs_le (d n : ℕ) (hm : m ≠ 0) (p q : Site d n) :
    |green (torusGraph d n) m p q|
      ≤ GreenDecay.decayRate (2 * d) m ^ ((torusGraph d n).dist p q) * (m ^ 2)⁻¹ :=
  GreenDecay.green_abs_le_pow_dist hm (fun v => torusGraph_degree_le v) p q

/-- **THE UNIFORM BOUND THE WATCHLIST ITEM ASKS FOR**, in the quantifier order that makes it
uniform: `N` is produced from `d`, `m` and `ε` before `n` is mentioned. Now an instance of
`GreenDecay.exists_dist_uniform`, which produces `N` before the *graph* is mentioned, so the
uniformity is no longer a property this family happens to have. -/
theorem torusGraph_uniform (d : ℕ) (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (p q : Site d n),
      (¬ (torusGraph d n).Reachable p q ∨ N ≤ (torusGraph d n).dist p q) →
      |green (torusGraph d n) m p q| < ε := by
  obtain ⟨N, hN⟩ := GreenDecay.exists_dist_uniform (m := m) hm (2 * d) hε
  exact ⟨N, fun n p q hpq =>
    hN (Site d n) (torusGraph d n) (fun v => torusGraph_degree_le v) p q hpq⟩

/-! ## 4. The torus is connected, which the estate had never said

`ERRATUM 165` recorded that a sentence about `torusGraph_uniform` could not be checked from
inside the estate, because `BoxGraph.boxGraph_connected` exists and **no torus counterpart did**.
It does now, and it costs three lines, because the box is a subgraph of the torus: a box bond
changes one coordinate by exactly one, and that is the first disjunct of `adjT`. The wrap-around
bonds the torus adds are not needed for connectivity and are not used here.
-/

/-- **THE BOX IS A SUBGRAPH OF THE TORUS.** Every non-wrapping bond is a torus bond. -/
theorem boxGraph_le_torusGraph (d n : ℕ) : boxGraph d n ≤ torusGraph d n := by
  rintro p q ⟨i, hj, hi⟩
  refine ⟨i, hj, ?_, ?_⟩
  · intro he
    rw [he] at hi
    rcases hi with h1 | h1 <;> omega
  · rcases hi with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

/-- **THE PERIODIC BOX IS CONNECTED IN EVERY DIMENSION AND AT EVERY POSITIVE SIDE LENGTH.** -/
theorem torusGraph_connected (d : ℕ) (hn : 0 < n) : (torusGraph d n).Connected :=
  SimpleGraph.Connected.mono (boxGraph_le_torusGraph d n) (BoxGraph.boxGraph_connected d hn)

/-- **AND THEREFORE THE FIRST DISJUNCT OF `torusGraph_uniform`'S HYPOTHESIS IS NEVER USED HERE.**
This settles what `ERRATUM 165` left open: generalising the separation hypothesis to cover
unreachable pairs buys nothing on the torus, because the torus has none. It is not a defect of
the generalisation — `GreenClustering.cross_abs_le` quantifies over arbitrary graphs and there it
buys everything — but it is what this family gets, and the estate can now say so instead of
assuming it. -/
theorem torusGraph_reachable (d : ℕ) (hn : 0 < n) (p q : Site d n) :
    (torusGraph d n).Reachable p q :=
  (torusGraph_connected d hn).preconnected p q

/-- **AND THE SAME ABOUT THE FIELD**: the two-point function of the Gaussian field on the periodic
box clusters exponentially, at a rate independent of the side length. -/
theorem torusGraph_covariance_abs_le (d n : ℕ) (hm : m ≠ 0) (p q : Site d n) :
    |cov[fun ω : EuclideanSpace ℝ (Site d n) => ω p,
        fun ω : EuclideanSpace ℝ (Site d n) => ω q; gaussianField (torusGraph d n) m]|
      ≤ GreenDecay.decayRate (2 * d) m ^ ((torusGraph d n).dist p q) * (m ^ 2)⁻¹ :=
  GreenDecay.covariance_abs_le hm (fun v => torusGraph_degree_le v) p q

end TorusDecay
