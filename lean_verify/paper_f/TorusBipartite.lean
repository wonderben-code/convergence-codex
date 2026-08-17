import TorusCycleTheory

/-!
# Bipartite in every dimension — `d = 1` was the route's restriction, not the fact's

`TorusCycleTheory.torusGraph_one_chromaticNumber_even` proves the periodic lattice is
two-colourable at even side length, **at `d = 1` only**, and says so. The reason for the
restriction is honest and is recorded there: the proof goes through
`TorusCycleGraph.torusGraph_one_iso` into Mathlib's `cycleGraph`, and **`torusGraph d n` at
`d ≥ 2` is a product of cycles, not a cycle.**

**That is a restriction on the route, and the fact does not have it.** Colour a site by the
parity of the sum of its coordinates. An edge of `torusGraph d n` changes exactly one coordinate,
by `±1` or across the wrap — and at **even** `n` the wrap changes `0` to `n − 1`, which is odd, so
the parity flips in every case. No cycle, no isomorphism, no `d = 1`.

This is the same shape as `TorusEmbeddingAllDims`: a `d = 1` written into a header because the
tool reached for was one-dimensional. `ERRATUM 194` is about exactly that habit, and this is the
second time in this chain it has cost a dimension.

## What is proved

* **`adjT_val_parity_ne`** — at even `n`, adjacent coordinates on the circle have opposite
  parity. **This is where `Even n` enters and it is the only place**: the wrap disjuncts of
  `adjT` compare `0` with `n − 1`.
* **`sum_parity_ne_of_adj`** — hence **no edge of `torusGraph d n` joins two sites whose
  coordinate sums have the same parity**, in every dimension. The `d = 1` case is
  `TorusCycleTheory.torusGraph_one_adj_parity_ne`.
* **`siteParity`**, **`torusColoring`** — the colour of a site, and the two-colouring as data,
  valued in `Fin 2`. The leaf is `siteParity` rather than `parity` because `SpinDetOne.parity`
  already exists; `ERRATUM 193` recorded what leaf collisions cost this estate and the `28
  duplicated declaration names` decision item is live.
* **`torusGraph_colorable_two`**, **`torusGraph_chromaticNumber_even`** — the periodic lattice is
  **two-colourable, and needs two colours, at every even side `≥ 2` and in every dimension `≥ 1`.**
* The `example` at the end re-derives `TorusCycleTheory`'s `d = 1` theorem from this one,
  **so the two routes agree by kernel rather than by resemblance** — and the older route uses
  `cycleGraph` while this one does not, so they share no lemma.

## What this is NOT

**Odd `n` at `d ≥ 2` is not settled here and is not claimed.** At `d = 1`,
`TorusCycleTheory.torusGraph_one_chromaticNumber_odd` gives `3`. The parity argument fails at odd
`n` for the right reason — the wrap changes `0` to `n − 1`, which is *even* — but a failed
argument is not a lower bound, and nothing here says what the chromatic number is.

**`Even n` is doing work, and the `d = 1` odd theorem is the witness** that it cannot simply be
dropped.

**THE PARITY COINCIDENCE IS STILL A COINCIDENCE.** `TorusReflection.reflectionPositive_torus`
requires `Even n`; so does this. **Nothing here says the second is why the first holds**, nothing
in the estate connects them, and `TorusCycleTheory` recorded that in capitals for the same reason.
Generalising the colouring to every `d` makes the agreement *look* stronger and **is not
evidence**.

**`OS4` does not move**, nothing here touches `gaussianField`, no reflection positivity is used or
affected, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusBipartite

open TorusReflection BoxGraph SimpleGraph

variable {d n : ℕ}

/-! ## 1. On the circle, at even side, adjacency flips parity -/

/-- **WHERE `Even n` ENTERS, AND THE ONLY PLACE IT DOES.** Two adjacent coordinates on the circle
`Fin n` have opposite parity when `n` is even.

The ordinary disjuncts of `adjT` are `b = a ± 1` and flip parity at every `n`. The two **wrap**
disjuncts compare `0` with `n − 1`, and that flips parity exactly when `n` is even. -/
theorem adjT_val_parity_ne (hn : Even n) {a b : Fin n} (h : adjT a b) :
    a.val % 2 ≠ b.val % 2 := by
  obtain ⟨-, hcase⟩ := h
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨k, hk⟩ := hn
  rcases hcase with h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-! ## 2. Hence the coordinate-sum parity, in every dimension -/

/-- The parity of the sum of a site's coordinates — the two-colouring, before it is bundled. -/
def siteParity (p : Site d n) : ℕ := (∑ i, (p i).val) % 2

/-- **NO EDGE JOINS TWO SITES OF THE SAME COORDINATE-SUM PARITY**, at even side length and in
**every** dimension.

An edge changes exactly one coordinate, so the sum splits as *that coordinate* plus *a rest that
does not move*, and §1 flips the first. -/
theorem sum_parity_ne_of_adj (hn : Even n) {p q : Site d n}
    (h : (torusGraph d n).Adj p q) : siteParity p ≠ siteParity q := by
  classical
  obtain ⟨i, hoff, hne, hcase⟩ := h
  have hsplit : ∀ r : Site d n, ∑ j, (r j).val
      = (r i).val + ∑ j ∈ Finset.univ.erase i, (r j).val :=
    fun r => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hrest : ∑ j ∈ Finset.univ.erase i, (p j).val
      = ∑ j ∈ Finset.univ.erase i, (q j).val :=
    Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
  have hpar := adjT_val_parity_ne hn (a := p i) (b := q i) ⟨hne, hcase⟩
  unfold siteParity
  rw [hsplit p, hsplit q, hrest]
  omega

/-! ## 3. The colouring, and the chromatic number -/

/-- The two-colouring as **data**: a site's colour is the parity of its coordinate sum. -/
def torusColoring (hn : Even n) : (torusGraph d n).Coloring (Fin 2) :=
  Coloring.mk (fun p => ⟨siteParity p, Nat.mod_lt _ (by norm_num)⟩) <| by
    intro p q hadj
    have hne := sum_parity_ne_of_adj hn hadj
    simpa [Fin.ext_iff] using hne

/-- **THE PERIODIC LATTICE IS TWO-COLOURABLE AT EVEN SIDE, IN EVERY DIMENSION.** -/
theorem torusGraph_colorable_two (hn : Even n) : (torusGraph d n).Colorable 2 := by
  simpa using (torusColoring (d := d) hn).colorable

/-- An edge exists once there is an axis to move along and a place to move to. Needed for the
lower bound: a graph with no edges is one-colourable. -/
theorem exists_adj (hd : 1 ≤ d) (hn : 2 ≤ n) :
    ∃ p q : Site d n, (torusGraph d n).Adj p q := by
  classical
  have hd0 : (0 : ℕ) < d := hd
  obtain ⟨z, hz⟩ : ∃ z : Fin n, z.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o : Fin n, o.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  refine ⟨fun _ => z, fun j => if j = ⟨0, hd0⟩ then o else z, ⟨0, hd0⟩, ?_, ?_, ?_⟩
  · intro j hj
    simp [if_neg hj]
  · simp [Fin.ext_iff, hz, ho]
  · exact Or.inl (by simp [hz, ho])

/-- **AND IT NEEDS TWO COLOURS**, so the chromatic number is exactly `2`, at every even side
`≥ 2` and every dimension `≥ 1`. -/
theorem torusGraph_chromaticNumber_even (hd : 1 ≤ d) (h2 : 2 ≤ n) (hn : Even n) :
    (torusGraph d n).chromaticNumber = 2 := by
  refine le_antisymm (torusGraph_colorable_two hn).chromaticNumber_le ?_
  obtain ⟨p, q, hpq⟩ := exists_adj (d := d) (n := n) hd h2
  exact two_le_chromaticNumber_of_adj hpq

/-! ## 4. The two routes agree, checked by the kernel -/

/-- **`TorusCycleTheory`'S `d = 1` THEOREM IS THIS ONE AT `d = 1`.**

The two proofs share no lemma: that one transports Mathlib's `chromaticNumber_cycleGraph_of_even`
along `torusGraph_one_iso`; this one counts coordinate parities and never mentions `cycleGraph`.
**A fact reached twice by arguments with nothing in common is a fact whose proof one need not read
to believe** — the estate's own standard, from `LorentzProperTopological`. -/
example (n : ℕ) (h2 : 2 ≤ n) (hn : Even n) :
    (torusGraph 1 n).chromaticNumber = 2 :=
  torusGraph_chromaticNumber_even (d := 1) le_rfl h2 hn

end TorusBipartite
