/-
  IsingContourCocycle.lean — contours are exactly the cocycles, and the
  reindexing buys less than it looks.

  WHY. Two consecutive units closed by naming the same gap.
  `IsingContourInvariant` reindexed the Peierls sum onto `realisedContours`
  and proved nothing whatever about that set; `IsingContourClosed` proved
  one necessary condition and said in its header that the converse "is where
  the remaining work is". **This project's ERRATUM 53 is exactly that
  pattern — a caveat repeated by two files in a row — and the standing
  response is to attack it rather than let a third file repeat it.**

  WHAT THIS FILE PROVES:
  1. **`IsCocycle`** — a bond set every closed walk crosses evenly, and
     `pathParity`, the configuration it induces: the spin at `p` is the
     parity of the crossings along a walk from the origin to `p`.
     `pathParity_well_defined` is the content — two walks differ by a closed
     walk, which crosses evenly, so the choice of walk does not matter.
  2. **`contour_pathParity`** — that configuration has exactly the given
     bond set as its contour.
  3. **`realised_iff_cocycle`** — **CONTOURS ARE EXACTLY THE COCYCLES.**
     With `IsingContourClosed.cocycle_of_realised` this closes the
     characterisation both ways, and `realisedContours` stops being an
     opaque image.
  4. **`card_realisedContours`** — `2 · #realisedContours = 2^(n²)`, and
     **this is the honest half of the file.** The reindexing of
     `IsingContourInvariant` halves the Peierls sum and does nothing else:
     the number of contours is still exponential in the AREA of the box.
     **`card_realisedContours_unbounded`** puts the consequence beyond
     argument — the contour count exceeds any fixed `C` at some box size —
     so that "the sum has been reindexed" cannot be read as progress on
     bounding it. (What that theorem states is exactly the count being
     unbounded. It says nothing about `β` or about weights, and no such
     statement is made here.)

  WHAT THIS DOES NOT DO. It characterises the set of contours; it does not
  count the subset that matters. Peierls needs the number of contours of
  LENGTH `L` that SURROUND a fixed site, and neither "length `L`" as a
  filtered count nor "surrounds" as a predicate exists here. There is no
  circuit decomposition, no dual lattice, no `3^{|γ|}`.
  **`IsingBoundaryField.MagnetisationBound` is untouched.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourClosed

namespace IsingContourCocycle

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourInvariant IsingContourClosed

variable {n : ℕ}

/-! ## 1. Cocycles, and the configuration a cocycle induces -/

/-- A bond set crossed an even number of times by every closed walk. -/
def IsCocycle (γ : Finset (Sym2 (Site n))) : Prop :=
  ∀ (u : Site n) (w : (latticeGraph n).Walk u u), Even (crossings γ w)

/-- The origin of the box. -/
def origin (hn : 0 < n) : Site n := (⟨0, hn⟩, ⟨0, hn⟩)

/-- Some walk from the origin to `p`. Noncomputable by necessity: the box is
    connected, and connectedness gives existence, not a choice. -/
noncomputable def toOrigin (hn : 0 < n) (p : Site n) :
    (latticeGraph n).Walk (origin hn) p :=
  ((latticeGraph_connected hn).preconnected (origin hn) p).some

/-- **The configuration a cocycle induces**: the spin at `p` is the parity of
    the number of crossings along a walk from the origin. -/
noncomputable def pathParity (hn : 0 < n) (γ : Finset (Sym2 (Site n))) :
    Config n :=
  fun p => decide (Even (crossings γ (toOrigin hn p)))

/-- **THE WELL-DEFINEDNESS.** Any two walks with the same endpoints cross a
    cocycle with the same parity — because their difference is a closed
    walk. This is the only real content in §1, and it is where `IsCocycle`
    is used. -/
theorem pathParity_well_defined (hn : 0 < n) {γ : Finset (Sym2 (Site n))}
    (hγ : IsCocycle γ) {p : Site n}
    (w₁ w₂ : (latticeGraph n).Walk (origin hn) p) :
    (Even (crossings γ w₁) ↔ Even (crossings γ w₂)) := by
  have hclosed : Even (crossings γ (w₁.append w₂.reverse)) :=
    hγ _ (w₁.append w₂.reverse)
  have hsplit : crossings γ (w₁.append w₂.reverse)
      = crossings γ w₁ + crossings γ w₂ := by
    unfold crossings
    rw [SimpleGraph.Walk.edges_append, List.countP_append,
      SimpleGraph.Walk.edges_reverse, List.countP_reverse]
  rw [hsplit, Nat.even_add] at hclosed
  exact hclosed

/-- The induced spin at `p`, read off any walk you like. -/
theorem pathParity_apply (hn : 0 < n) {γ : Finset (Sym2 (Site n))}
    (hγ : IsCocycle γ) (p : Site n) (w : (latticeGraph n).Walk (origin hn) p) :
    pathParity hn γ p = decide (Even (crossings γ w)) := by
  unfold pathParity
  exact decide_eq_decide.mpr (pathParity_well_defined hn hγ _ w)

/-! ## 2. The induced configuration has the given contour -/

/-- Extending a walk by one bond flips the crossing parity exactly when that
    bond lies in the set. -/
theorem pathParity_step (hn : 0 < n) {γ : Finset (Sym2 (Site n))}
    (hγ : IsCocycle γ) {p q : Site n} (h : adj p q) :
    (pathParity hn γ p ≠ pathParity hn γ q) ↔ s(p, q) ∈ γ := by
  have hpq : (latticeGraph n).Adj p q := h
  set w : (latticeGraph n).Walk (origin hn) q :=
    (toOrigin hn p).append (SimpleGraph.Walk.cons hpq SimpleGraph.Walk.nil) with hwdef
  have hcount : crossings γ w
      = crossings γ (toOrigin hn p) + (if s(p, q) ∈ γ then 1 else 0) := by
    rw [hwdef]
    unfold crossings
    rw [SimpleGraph.Walk.edges_append, List.countP_append]
    congr 1
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.countP_cons, List.countP_nil, Nat.zero_add]
    by_cases hm : s(p, q) ∈ γ <;> simp [hm]
  rw [pathParity_apply hn hγ q w, pathParity_apply hn hγ p (toOrigin hn p),
    ne_eq, decide_eq_decide, hcount]
  by_cases hm : s(p, q) ∈ γ
  · rw [if_pos hm]
    refine iff_of_true ?_ hm
    rcases Nat.even_or_odd (crossings γ (toOrigin hn p)) with he | ho
    · simp [he, Nat.even_add_one]
    · simp [Nat.not_even_iff_odd.mpr ho, Nat.even_add_one]
  · simp [hm]

/-- **The cocycle is recovered as a contour.** -/
theorem contour_pathParity (hn : 0 < n) {γ : Finset (Sym2 (Site n))}
    (hγ : IsCocycle γ) (hsub : ∀ e ∈ γ, ∃ p q : Site n, e = s(p, q) ∧ adj p q) :
    contour (pathParity hn γ) = γ := by
  ext e
  constructor
  · induction e using Sym2.ind with
    | _ p q =>
      intro he
      obtain ⟨hadj, hne⟩ := (mem_contour _ p q).mp he
      exact (pathParity_step hn hγ hadj).mp hne
  · intro he
    obtain ⟨p, q, rfl, hadj⟩ := hsub e he
    exact (mem_contour _ p q).mpr ⟨hadj, (pathParity_step hn hγ hadj).mpr he⟩

/-! ## 3. Contours are exactly the cocycles

The `hsub` hypothesis above is not decoration: a cocycle could contain a
`Sym2` that is not a lattice bond at all, and no configuration's contour
ever does. So the characterisation is against bond sets, which is what
`realisedContours` consists of.
-/

/-- Every realised contour consists of actual bonds. -/
theorem realised_sub {γ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ realisedContours n) : ∀ e ∈ γ, ∃ p q : Site n, e = s(p, q) ∧ adj p q := by
  simp only [realisedContours] at hγ
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hγ
  intro e he
  induction e using Sym2.ind with
  | _ p q => exact ⟨p, q, rfl, ((mem_contour σ p q).mp he).1⟩

/-- **CONTOURS ARE EXACTLY THE COCYCLES.** A set of lattice bonds occurs as
    the contour of some configuration precisely when every closed walk
    crosses it an even number of times. The forward direction is
    `IsingContourClosed.cocycle_of_realised`; §1–§2 give the converse. -/
theorem realised_iff_cocycle (hn : 0 < n) (γ : Finset (Sym2 (Site n)))
    (hsub : ∀ e ∈ γ, ∃ p q : Site n, e = s(p, q) ∧ adj p q) :
    γ ∈ realisedContours n ↔ IsCocycle γ := by
  constructor
  · intro hγ u w
    exact cocycle_of_realised hγ w
  · intro hγ
    simp only [realisedContours]
    exact Finset.mem_image.mpr ⟨pathParity hn γ, Finset.mem_univ _,
      contour_pathParity hn hγ hsub⟩

/-! ## 4. How many contours there are, and why that is bad news

This section exists to stop the reindexing being over-read. It is the
honest half of the file.
-/

/-- `2 · #realisedContours = 2^(n²)`. Immediate from
    `IsingContourInvariant.card_fiber`. -/
theorem card_realisedContours (hn : 0 < n) :
    2 * (realisedContours n).card = 2 ^ (n * n) := by
  classical
  have h := Finset.card_eq_sum_card_image (contour (n := n)) Finset.univ
  rw [Finset.card_univ, card_config] at h
  have hall : ∑ b ∈ Finset.image (contour (n := n)) Finset.univ,
      (Finset.univ.filter (fun τ : Config n => contour τ = b)).card
      = ∑ _b ∈ Finset.image (contour (n := n)) Finset.univ, 2 := by
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hb
    exact card_fiber hn σ
  rw [hall, Finset.sum_const, smul_eq_mul] at h
  simp only [realisedContours]
  omega

/-- **THE CONTOUR COUNT IS UNBOUNDED**, so the reindexing bounds nothing on
    its own. By `card_realisedContours` the number of contours is
    `2^(n²−1)`, exponential in the AREA of the box, and this says it
    therefore exceeds any fixed `C` at some box size.

    Peierls escapes this by never summing over all contours: it sums over
    contours of a given LENGTH that SURROUND a fixed site, and bounds THAT
    count by `3^{|γ|}`. Neither notion exists in this estate. **This theorem
    is here so that "the sum has been reindexed" is not mistaken for
    progress on the bound** — and note it is a statement about the COUNT
    only; nothing here bounds, or fails to bound, any weighted sum. -/
theorem card_realisedContours_unbounded (C : ℕ) :
    ∃ m : ℕ, 0 < m ∧ C < (realisedContours m).card := by
  refine ⟨C + 1, Nat.succ_pos C, ?_⟩
  have h := card_realisedContours (n := C + 1) (Nat.succ_pos C)
  have h1 : C < 2 ^ C := Nat.lt_two_pow_self
  have h2 : 2 ^ (C + 1) ≤ 2 ^ ((C + 1) * (C + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : 2 * C < 2 ^ (C + 1) := by rw [pow_succ]; omega
  omega

/-! ## 5. Review round 69 — the ways this could be hollow

**"`pathParity` could be ill-defined and the file not notice."** It is
noncomputable by construction — `toOrigin` picks a walk out of a
`Reachable`, which is a `Nonempty` and carries no canonical choice — so
`pathParity` literally depends on that pick until
`pathParity_well_defined` says it does not. That theorem is the only place
`IsCocycle` is used in §1–§2, which is the right shape: the hypothesis buys
exactly the independence and nothing else. `pathParity_apply` is the usable
form, and every later proof goes through it rather than through the chosen
walk.

**"The `hsub` hypothesis could be hiding a gap."** It is real and it is
stated rather than assumed away. A `Finset (Sym2 (Site n))` can contain
pairs that are not lattice bonds; such a set can vacuously satisfy
`IsCocycle` while no configuration's contour contains it. `realised_sub`
shows every realised contour satisfies `hsub`, so the biconditional is
exactly right on the sets it is about.

**"§3 could be circular."** The forward direction is imported
(`cocycle_of_realised`, proved in the previous file from a walk induction).
The converse is proved here by construction and uses none of it. The two
halves have disjoint proofs.

**"§4 could be padding."** It is the opposite: it is the section that stops
this staircase being over-read. Three units in a row have made the Peierls
sum look closer — a weight identity, a reindexing, a characterisation — and
`card_realisedContours_unbounded` is the statement that the set they reindex
onto grows without bound, so none of them bounds anything. It is proved
rather than remarked for the reason ERRATUM 58 gives.

*And the draft of this file gave ERRATUM 58 its fifth consecutive instance.*
The theorem was renamed late, and the header went on describing it as
"bounding the sum by (number of contours) × (largest weight) gives a bound
that grows with the box" — a claim about a WEIGHTED sum, when what is proved
is a claim about a COUNT. Both the stale name and the widened claim are
corrected above. The interesting part is that this one arrived by a route
none of the previous four used: not a sentence written too boldly, but a
sentence left behind by a rename.

**"This could be claimed as the entropy half."** The entropy half is a
count, and this file counts the wrong thing: all contours, rather than
contours of length `L` surrounding a site. Neither "length `L`" as a
filtered count nor "surrounds" as a predicate exists anywhere in the estate.
`MagnetisationBound` is untouched.
-/

end IsingContourCocycle
