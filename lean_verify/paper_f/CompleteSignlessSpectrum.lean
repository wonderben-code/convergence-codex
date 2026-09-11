import SignlessBipartite

/-!
# The complete graph's two Laplacians, and the first non-bipartite family with a computed `Q`

**THIS FILE EXISTS BECAUSE THE PREVIOUS UNIT'S FENCE WAS WRONG** (`ERRATUM 506`).
`SignlessBipartite` closed the box's signless spectrum by conjugation and then fenced with *an odd
cycle's signless spectrum is still uncomputed*. **It is not**:
`SignlessCycleSpectrum.signless_eigenvalue_eq_real` gives `2 + 2cos(2πk/N)` on **every** cycle,
odd ones included, and the fence I was paraphrasing says so in its own words — *no eigenvalue of `Q`
is known at any graph that is not a cycle or a torus*. The real gap is the one that sentence names:
a graph that is **neither a cycle, nor a torus, nor two-colourable with a known Laplacian
spectrum**. This file supplies a family of them.

**THE COMPLETE GRAPH IS THAT FAMILY, AND THE ESTATE HAD NEVER MENTIONED IT** — counted, not
assumed: before this file, no file of `paper_f` contained the string `completeGraph` or `⊤` as a
graph. `K_n` is non-bipartite at three vertices and more, it is not a cycle beyond `n = 3`, and both
its Laplacians are two lines of arithmetic away.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED** (`ERRATUM 500`'s rule): everything, because the
graph is new here. The route is elementary and worth stating so nobody looks for more: on `K_n` the
neighbour sum is the total sum minus the vertex, and the degree is `n − 1` at every vertex, so
`Q = (n − 2)·I + J` and `L = n·I − J` with `J` the all-ones matrix. The constant vector and the
zero-sum vectors are then the whole story, and `Fintype.card` arithmetic over `ℝ` is the only thing
that needs care.

## What is proved

**`adjMatrix_top_mulVec`, `degMatrix_top_mulVec`** — the two matrices acting on a vector, from
Mathlib's `complete_graph_degree` and a `Finset.erase` of the neighbour sum.

**`signlessLap_top_mulVec`, `lapMatrix_top_mulVec`** — hence `(Q x) v = (n − 2)·x v + ∑ x` and
`(L x) v = n·x v − ∑ x`.

**`signlessLap_top_mulVec_const`** — **`Q` HAS EIGENVALUE `2n − 2` ON THE CONSTANT VECTOR**;
**`signlessLap_top_mulVec_of_sum_eq_zero`** — **AND `n − 2` ON EVERY ZERO-SUM VECTOR**. That is the
classical signless spectrum of `K_n`, and it is the second family in this estate after the cycle and
the torus — **the first that is not two-colourable**.

**`lapMatrix_top_mulVec_of_sum_eq_zero`** — and the Laplacian has eigenvalue `n` on the zero-sum
vectors, which with Mathlib's `lapMatrix_mulVec_const_eq_zero` is the classical `{0, n^(n−1)}`.
**Also new here**: this estate had the path, the cycle, the torus and the box, and not the complete
graph.

**`exists_ne_zero_sum_eq_zero`** — the zero-sum family is **inhabited** above one vertex, so the
`n − 2` eigenvalue is not a statement about nothing.

**`coloring_top_injective`, `not_colorable_two_of_three_le`** — a proper colouring of `K_n` is
injective, so `K_n` is **not two-colourable** at three vertices or more. That is what makes it a
witness for the gap rather than another instance of `SignlessBipartite`.

**`sum_eq_zero_of_signlessLap_top_mulVec_eq_zero`, `eq_zero_of_signlessLap_top_mulVec_eq_zero`,
`det_signlessLap_top_ne_zero`** — `Q` is **injective** on `K_n` for `n ≥ 3`: summing `Q x = 0` over
the vertices gives `(2n − 2)∑x = 0`, and then `(n − 2)x v = 0` pointwise.

**`charpoly_signlessLap_top_ne`** — **SO THE TWO CHARACTERISTIC POLYNOMIALS DIFFER ON `K_n`**, `n ≥
3`: the Laplacian is singular on any non-empty graph and `Q` is not. `SignlessBipartite`'s
equivalence is therefore **strictly** about two-colourable graphs, shown on a family rather than on
the single odd cycle that file used.

## What is NOT here

* **NO MULTIPLICITIES.** The eigenvalue `n − 2` is exhibited on the zero-sum subspace and **no
  dimension count is made**: that the subspace is `(n − 1)`-dimensional, and that the two
  eigenvalues therefore exhaust the spectrum, is standard and **not proved here**. Not attempted, no
  cost claimed (`ERRATUM 246`).
* **NO CHROMATIC NUMBER.** `not_colorable_two_of_three_le` is the one fact needed; that `K_n` has
  chromatic number `n` is not stated.
* **NOTHING ABOUT `K_n` AS A GRAPH BEYOND THIS.** Its automorphism group, its propagator, its OS
  properties, the estate's field machinery on it — all untouched. In particular **no `green`, no
  `massive`, no mass**: this file is about `Q` and `L` alone.
* **NOTHING FOR ANY OTHER NON-BIPARTITE GRAPH.** The paw, the wheel, a general graph with an odd
  cycle: nothing here reaches them, and the gap the previous unit's item names is narrowed by one
  family and not closed.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, and
nothing else — no graph argument, since the graph is `⊤`. The arithmetic hypotheses are explicit:
`2 ≤ Fintype.card V` for the zero-sum witness and the sum lemma, `3 ≤ Fintype.card V` for
injectivity, the non-colourability and the characteristic-polynomial statement.
`coloring_top_injective` takes no `Fintype` at all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CompleteSignlessSpectrum

open Matrix Finset SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The two matrices of the complete graph, acting on a vector -/

theorem adjMatrix_top_mulVec (x : V → ℝ) (v : V) :
    ((⊤ : SimpleGraph V).adjMatrix ℝ *ᵥ x) v = (∑ u, x u) - x v := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hnb : (⊤ : SimpleGraph V).neighborFinset v = Finset.univ.erase v := by
    ext u
    simp [SimpleGraph.mem_neighborFinset, Finset.mem_erase, ne_comm]
  rw [hnb, Finset.sum_erase_eq_sub (Finset.mem_univ v)]

theorem degMatrix_top_mulVec (x : V → ℝ) (v : V) :
    ((⊤ : SimpleGraph V).degMatrix ℝ *ᵥ x) v = ((Fintype.card V : ℝ) - 1) * x v := by
  classical
  have hd : (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 :=
    SimpleGraph.complete_graph_degree v
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal, hd]
  push_cast [Nat.cast_sub hcard]
  ring

theorem signlessLap_top_mulVec (x : V → ℝ) (v : V) :
    (signlessLap (⊤ : SimpleGraph V) *ᵥ x) v
      = ((Fintype.card V : ℝ) - 2) * x v + ∑ u, x u := by
  rw [signlessLap, Matrix.add_mulVec, Pi.add_apply, degMatrix_top_mulVec,
    adjMatrix_top_mulVec]
  ring

theorem lapMatrix_top_mulVec (x : V → ℝ) (v : V) :
    ((⊤ : SimpleGraph V).lapMatrix ℝ *ᵥ x) v = (Fintype.card V : ℝ) * x v - ∑ u, x u := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply, degMatrix_top_mulVec,
    adjMatrix_top_mulVec]
  ring

/-! ## 2. So the eigenvectors are the constant vector and the zero-sum vectors -/

theorem signlessLap_top_mulVec_const :
    signlessLap (⊤ : SimpleGraph V) *ᵥ (fun _ ↦ (1 : ℝ))
      = (2 * (Fintype.card V : ℝ) - 2) • (fun _ ↦ (1 : ℝ)) := by
  funext v
  rw [signlessLap_top_mulVec]
  simp
  ring

theorem signlessLap_top_mulVec_of_sum_eq_zero {x : V → ℝ} (h : ∑ u, x u = 0) :
    signlessLap (⊤ : SimpleGraph V) *ᵥ x = ((Fintype.card V : ℝ) - 2) • x := by
  funext v
  rw [signlessLap_top_mulVec, h]
  simp

theorem lapMatrix_top_mulVec_of_sum_eq_zero {x : V → ℝ} (h : ∑ u, x u = 0) :
    (⊤ : SimpleGraph V).lapMatrix ℝ *ᵥ x = (Fintype.card V : ℝ) • x := by
  funext v
  rw [lapMatrix_top_mulVec, h]
  simp

/-! ## 3. The complete graph is not two-colourable above two vertices -/

omit [Fintype V] [DecidableEq V] in
theorem coloring_top_injective {α : Type*} (C : (⊤ : SimpleGraph V).Coloring α) :
    Function.Injective C := by
  intro u v huv
  by_contra hne
  exact C.valid (by simpa [SimpleGraph.top_adj] using hne) huv

omit [DecidableEq V] in
theorem not_colorable_two_of_three_le (h : 3 ≤ Fintype.card V) :
    ¬ (⊤ : SimpleGraph V).Colorable 2 := by
  intro hcol
  obtain ⟨C⟩ := hcol
  have hle := Fintype.card_le_of_injective _ (coloring_top_injective C)
  simp at hle
  omega

omit [DecidableEq V] in
/-- **AND THE ZERO-SUM EIGENVECTORS EXIST**, so the `card V − 2` eigenvalue is not a statement
about an empty family: on two vertices or more, `e_i − e_j` is one. -/
theorem exists_ne_zero_sum_eq_zero (h2 : 2 ≤ Fintype.card V) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ u, x u = 0 := by
  classical
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
  refine ⟨fun u ↦ (if u = i then 1 else 0) - (if u = j then 1 else 0), ?_, ?_⟩
  · intro h0
    have h := congrFun h0 i
    simp only [Pi.zero_apply, if_pos, if_neg hij, sub_zero] at h
    exact one_ne_zero h
  · rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i (fun _ ↦ (1:ℝ)),
      Finset.sum_ite_eq' Finset.univ j (fun _ ↦ (1:ℝ))]
    simp

/-! ## 4. And the two spectra differ on the complete graph, as they must -/

theorem sum_eq_zero_of_signlessLap_top_mulVec_eq_zero (h2 : 2 ≤ Fintype.card V)
    {x : V → ℝ} (hx : signlessLap (⊤ : SimpleGraph V) *ᵥ x = 0) : ∑ u, x u = 0 := by
  have hsum : ∑ v, (signlessLap (⊤ : SimpleGraph V) *ᵥ x) v = 0 := by
    simp [hx]
  rw [Finset.sum_congr rfl fun v _ ↦ signlessLap_top_mulVec x v] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hne : (2 * (Fintype.card V : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h2
    nlinarith
  have hfac : (2 * (Fintype.card V : ℝ) - 2) * ∑ u, x u = 0 := by linarith [hsum]
  exact (mul_eq_zero.mp hfac).resolve_left hne

theorem eq_zero_of_signlessLap_top_mulVec_eq_zero (h3 : 3 ≤ Fintype.card V)
    {x : V → ℝ} (hx : signlessLap (⊤ : SimpleGraph V) *ᵥ x = 0) : x = 0 := by
  have hsum := sum_eq_zero_of_signlessLap_top_mulVec_eq_zero (by omega) hx
  funext v
  have hv : ((Fintype.card V : ℝ) - 2) * x v + ∑ u, x u = 0 := by
    rw [← signlessLap_top_mulVec x v, hx]
    simp
  rw [hsum, add_zero] at hv
  have hne : ((Fintype.card V : ℝ) - 2) ≠ 0 := by
    have : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
    nlinarith
  simpa using (mul_eq_zero.mp hv).resolve_left hne

theorem det_signlessLap_top_ne_zero (h3 : 3 ≤ Fintype.card V) :
    (signlessLap (⊤ : SimpleGraph V)).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hx0 (eq_zero_of_signlessLap_top_mulVec_eq_zero h3 hx)

theorem charpoly_signlessLap_top_ne (h3 : 3 ≤ Fintype.card V) :
    (signlessLap (⊤ : SimpleGraph V)).charpoly
      ≠ ((⊤ : SimpleGraph V).lapMatrix ℝ).charpoly := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  intro hpoly
  have hdet : (signlessLap (⊤ : SimpleGraph V)).det
      = ((⊤ : SimpleGraph V).lapMatrix ℝ).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hpoly]
  rw [SignlessBipartite.det_lapMatrix_eq_zero] at hdet
  exact det_signlessLap_top_ne_zero h3 hdet

end CompleteSignlessSpectrum
