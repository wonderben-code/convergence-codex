import SignlessStarConverse

/-!
# And the other end: `topEigen = 2Δ` on a connected graph forces regularity

`SignlessStarConverse` classified the bracket's **lower** end — `topEigen = Δ + 1` exactly on the
stars — and fenced the other one in terms: *`topEigen = 2Δ` holds on every regular graph and the
converse there — does `2Δ` force regularity? — is **a different question and is not touched**.*
**This touches it, and the answer is yes.**

## What is proved

**`regular_of_topEigen_eq`** — **THE FILE'S THEOREM.** For a connected graph,

```
topEigen (signlessLap G) = 2Δ   →   G.IsRegularOfDegree Δ
```

and with `SignlessTopDegreeBounds.topEigen_regular` this is an iff, **`topEigen_eq_iff_regular`**.
So both ends of `Δ + 1 ≤ topEigen ≤ 2Δ` are now classified on connected graphs: the bottom is the
stars and the top is the regular graphs.

**AND OFF THOSE TWO CLASSES BOTH INEQUALITIES ARE STRICT** — `maxDegree_add_one_lt_of_not_star` and
`lt_two_maxDegree_of_not_regular`, one line each from the two biconditionals, and stated because
*classified at the ends* and *strict in between* are different sentences and only the second is
what a reader wants when the graph in front of them is neither.

## The argument, and why it is not the previous file's

**THE TWO ENDS ARE NOT SYMMETRIC AND NEEDED DIFFERENT PROOFS.** The lower end was settled without
ever mentioning an eigenvector: the bound came from a *test vector*, and equality collapsed a
sandwich whose two ends were the same number, so the slack in an inequality between explicit sums
went to zero. **Nothing like that is available here**, because the upper bound came from the other
side of the estate — `PerronBound.abs_le_of_rowSum_le`, every eigenvalue of a non-negative matrix
being under the largest row sum — and a row-sum bound has no test vector in it to squeeze.

So this proof takes the eigenvector, which the lower end did not need:

**`row_forces`** — at a vertex `i` where `x` attains the maximum of `|x|` and is positive there,
the row equation `deg(i)·x(i) + ∑_{w ∼ i} x(w) = 2Δ·x(i)` **forces both** `deg(i) = Δ` **and**
`x(w) = x(i)` at every neighbour. The first because the neighbour sum is at most `deg(i)·x(i)`, so
`2Δ ≤ 2·deg(i)`; the second because that inequality is then an equality, and a sum of non-negative
terms `x(i) − x(w)` that vanishes has every term zero.

**`regular_of_topEigen_eq`** — the second conclusion is what propagates. The set where `x` equals
its maximum is closed under adjacency — `row_forces` applied at each of its points — so
connectedness makes it everything (`TorusEmbeddingGeneral.mem_of_walk`), and then the first
conclusion holds at every vertex.

**THE SIGN IS HANDLED ONCE, AT THE TOP, AND NOT INSIDE THE INDUCTION.** An eigenvector need not be
positive and this file proves no Perron positivity — it does not need any. `|x|` attains a maximum
somewhere; replacing `x` by `−x` if necessary makes `x` positive there; and the lemma is stated
against that normalisation rather than against `|x(i)|`, which keeps every later step free of
absolute values.

## What is NOT here

* **NO PERRON POSITIVITY IS USED OR PROVED.** The estate has it —
  `PerronSimple.pos_of_nonneg_top_eigenvector`, which `SignlessPerronSimple` spends on exactly this
  family — and **this file does not call it**: the maximum of `|x|` is enough, and asking for less
  keeps the proof shorter than the tool it declined.
* **CONNECTEDNESS IS LOAD-BEARING, AND THE WITNESS IS ARITHMETIC RATHER THAN A THEOREM.** A
  triangle beside a single edge has `Δ = 2` and `topEigen = 4 = 2Δ` — the triangle's own top, the
  spectrum of a disjoint union being the union of the spectra — and is not regular. **Computed by
  hand and NOT formalised here**: this estate has no disjoint-union-of-graphs construction and no
  block-diagonal spectrum theorem, so the counterexample is a reason to keep the hypothesis and
  not an object in the library. The same caveat attaches to `SignlessStarConverse`'s star-beside-
  an-isolated-vertex, which is the identical remark at the other end and is equally unformalised.
* **NOTHING ABOUT WHICH INTERIOR VALUES ARE ATTAINED.** §3 says the inequalities are strict off
  the two classes; it does **not** say which numbers in `(Δ+1, 2Δ)` occur, for how many graphs, or
  whether they are dense in it. That is a different question and is not touched (`ERRATUM 246`).
* **STILL NO SECOND EIGENVALUE AND NO GAP**, six units running.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency, `Nonempty V`, and `G.Connected`. No colourability, no positivity, and no
`Nontrivial` — a one-vertex graph is `0`-regular and the statement is true of it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessRegularConverse

open Matrix Finset SimpleGraph LaplacianSignless RayleighVariational
open GraphIsoSignlessSpectrum

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. One row, at the maximum -/

/-- **THE ROW EQUATION AT A MAXIMUM FORCES THE DEGREE AND FLATTENS THE NEIGHBOURS.**
`hmax` says `x i` is the maximum of `|x|` and, being positive there, `x i` itself. -/
theorem row_forces {x : V → ℝ} {i : V} (hmax : ∀ u, |x u| ≤ x i) (hpos : 0 < x i)
    (heig : signlessLap G *ᵥ x = (2 * (G.maxDegree : ℝ)) • x) :
    G.degree i = G.maxDegree ∧ ∀ w, G.Adj i w → x w = x i := by
  classical
  have hcard : (G.neighborFinset i).card = G.degree i := G.card_neighborFinset_eq_degree i
  have hrow : (G.degree i : ℝ) * x i + ∑ w ∈ G.neighborFinset i, x w
      = 2 * (G.maxDegree : ℝ) * x i := by
    have := congrFun heig i
    rw [signlessLap_mulVec_apply i x] at this
    simpa using this
  -- each neighbour's value is at most `x i`
  have hle : ∀ w ∈ G.neighborFinset i, x w ≤ x i := fun w _ => (le_abs_self (x w)).trans (hmax w)
  have hsum_le : ∑ w ∈ G.neighborFinset i, x w ≤ (G.degree i : ℝ) * x i := by
    calc ∑ w ∈ G.neighborFinset i, x w
        ≤ ∑ _w ∈ G.neighborFinset i, x i := Finset.sum_le_sum hle
      _ = (G.degree i : ℝ) * x i := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- so `2Δ ≤ 2 · deg i`, and `deg i ≤ Δ` always
  have hdeg : G.degree i = G.maxDegree := by
    have hR : 2 * (G.maxDegree : ℝ) * x i ≤ 2 * (G.degree i : ℝ) * x i := by linarith
    have hcast : (G.maxDegree : ℝ) ≤ (G.degree i : ℝ) := by
      have h2 : (0 : ℝ) < 2 * x i := by linarith
      nlinarith [hR, hpos]
    have : G.maxDegree ≤ G.degree i := by exact_mod_cast hcast
    exact le_antisymm (G.degree_le_maxDegree i) this
  refine ⟨hdeg, ?_⟩
  -- with the degree pinned, the neighbour sum is exactly `deg i · x i`
  have hsum_eq : ∑ w ∈ G.neighborFinset i, x w = (G.degree i : ℝ) * x i := by
    rw [hdeg] at hrow ⊢
    linarith
  have hzero : ∑ w ∈ G.neighborFinset i, (x i - x w) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, hsum_eq]
    ring
  intro w hw
  have hmem : w ∈ G.neighborFinset i := (G.mem_neighborFinset i w).mpr hw
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u hu => sub_nonneg.mpr (hle u hu))).mp hzero w hmem
  linarith [this]

/-! ## 2. Connectedness spreads it -/

/-- **THE FILE'S THEOREM.** -/
theorem regular_of_topEigen_eq [Nonempty V] (hconn : G.Connected)
    (heq : topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      = 2 * (G.maxDegree : ℝ)) :
    G.IsRegularOfDegree G.maxDegree := by
  classical
  obtain ⟨x, hx0, hxeig⟩ :=
    OpNormTopEigenvalue.exists_eigenvector_sup'
      (LaplacianSignlessDefinite.signlessLap_isHermitian G)
  rw [show (Finset.univ.sup' Finset.univ_nonempty
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues)
      = topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) from rfl, heq] at hxeig
  -- a vertex where `|x|` is largest, and it is not zero there
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun u => |x u|) Finset.univ_nonempty
  have hipos : 0 < |x i| := by
    rcases Function.ne_iff.mp hx0 with ⟨u, hu⟩
    exact lt_of_lt_of_le (abs_pos.mpr hu) (hi u (Finset.mem_univ u))
  -- normalise the sign once, here
  set y : V → ℝ := if 0 < x i then x else -x with hy
  have hyeig : signlessLap G *ᵥ y = (2 * (G.maxDegree : ℝ)) • y := by
    by_cases h : 0 < x i
    · rw [hy, if_pos h]; exact hxeig
    · rw [hy, if_neg h, Matrix.mulVec_neg, hxeig, smul_neg]
  have hyabs : ∀ u, |y u| = |x u| := by
    intro u
    by_cases h : 0 < x i
    · rw [hy, if_pos h]
    · rw [hy, if_neg h]; exact abs_neg (x u)
  have hyi : y i = |x i| := by
    by_cases h : 0 < x i
    · rw [hy, if_pos h]; exact (abs_of_pos h).symm
    · rw [hy, if_neg h]
      have hneg : x i < 0 := by
        rcases lt_trichotomy (x i) 0 with h1 | h1 | h1
        · exact h1
        · rw [h1] at hipos; simp at hipos
        · exact absurd h1 h
      simp [abs_of_neg hneg]
  have hymax : ∀ u, |y u| ≤ y i := by intro u; rw [hyabs u, hyi]; exact hi u (Finset.mem_univ u)
  have hypos : 0 < y i := by rw [hyi]; exact hipos
  -- the level set of the maximum is closed under adjacency
  have hclosed : ∀ a b : V, y a = y i → G.Adj a b → y b = y i := by
    intro a b ha hab
    have hmaxa : ∀ u, |y u| ≤ y a := by intro u; rw [ha]; exact hymax u
    exact ha ▸ (row_forces G hmaxa (ha ▸ hypos) hyeig).2 b hab
  have hall : ∀ u : V, y u = y i := by
    intro u
    obtain ⟨p⟩ := hconn.preconnected i u
    exact TorusEmbeddingGeneral.mem_of_walk (S := {z | y z = y i})
      (fun a b ha hab => hclosed a b ha hab) p rfl
  -- so the degree is `Δ` everywhere
  intro u
  have hmaxu : ∀ v : V, |y v| ≤ y u := by intro v; rw [hall u]; exact hymax v
  exact (row_forces G hmaxu (by rw [hall u]; exact hypos) hyeig).1

/-- **AND THE UPPER END OF THE BRACKET IS ATTAINED EXACTLY ON THE REGULAR GRAPHS.** -/
theorem topEigen_eq_iff_regular [Nonempty V] (hconn : G.Connected) :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
        = 2 * (G.maxDegree : ℝ) ↔ G.IsRegularOfDegree G.maxDegree := by
  refine ⟨regular_of_topEigen_eq G hconn, fun hreg => ?_⟩
  exact SignlessTopDegreeBounds.topEigen_regular G hreg

/-! ## 3. So off the two classes both inequalities are strict -/

/-- **A CONNECTED GRAPH THAT IS NOT A STAR CLEARS `Δ + 1` STRICTLY.** -/
theorem maxDegree_add_one_lt_of_not_star [Nontrivial V] (hconn : G.Connected)
    (hΔ : 0 < G.maxDegree) (hns : ¬ ∃ v : V, G = StarAdjNormExact.starGraph v) :
    (G.maxDegree : ℝ) + 1
      < topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  refine lt_of_le_of_ne (SignlessMaxDegreeBound.maxDegree_add_one_le_topEigen G hΔ) ?_
  intro h
  exact hns ((SignlessStarConverse.topEigen_eq_iff_star G hconn).mp h.symm)

/-- **AND ONE THAT IS NOT REGULAR STAYS STRICTLY UNDER `2Δ`.** -/
theorem lt_two_maxDegree_of_not_regular [Nonempty V] (hconn : G.Connected)
    (hnr : ¬ G.IsRegularOfDegree G.maxDegree) :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      < 2 * (G.maxDegree : ℝ) := by
  refine lt_of_le_of_ne (SignlessTopDegreeBounds.topEigen_le_two_maxDegree G) ?_
  intro h
  exact hnr ((topEigen_eq_iff_regular G hconn).mp h)

end SignlessRegularConverse
