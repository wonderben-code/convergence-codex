/-
  IsingContourClosed.lean — contours are closed, said without a dual lattice.

  WHY. `WALLS.md` costs W3's remaining work as the `3^{|γ|}` count, and puts
  "contours as geometric objects" in the same voluminous basket. But a large
  part of what "contour" MEANS geometrically is one sentence: **a contour is
  closed** — it has no loose ends. The textbook says this in the dual
  lattice ("every dual vertex has even degree, so the contour decomposes
  into circuits") and the estate has no dual lattice and no plan to build
  one.

  **The primal form of the same fact needs no dual lattice at all**, and it
  is a walk induction: every cycle of the box crosses the contour an even
  number of times. That is what this file proves.

  WHAT THIS FILE PROVES:
  1. **`crossings`** — how many edges of a walk lie in a given bond set.
  2. **`even_crossings_iff`** — **along ANY walk from `u` to `v`, the number
     of contour crossings is even exactly when `σ u = σ v`.** Exact parity.
     This strictly strengthens
     `IsingContourSeparation.exists_broken_of_walk`, which said only "at
     least one", and that theorem is re-derived from it in §3.
  3. **`even_crossings_closed`** — hence **every closed walk crosses the
     contour an even number of times: the contour is CLOSED.**
  4. **`cocycle_of_realised`** — so every realised contour satisfies the
     cocycle condition. That is **the first constraint of any kind on
     `IsingContourInvariant.realisedContours`**, the set whose size is the
     entropy question.

  WHAT THIS DOES NOT DO. **The converse is not attempted and is where the
  work is.** That every cocycle is realised requires building a
  configuration by path-following and proving the result independent of the
  path; without it `realisedContours` is CONSTRAINED, not characterised, and
  no upper bound on its size follows. There is also no decomposition into
  circuits as objects — "crosses every cycle evenly" is the content of
  closedness, but a `Finset` of edges with that property has not been cut
  into a list of loops here. No dual lattice, no `3^{|γ|}`,
  `IsingBoundaryField.MagnetisationBound` untouched.

  AMENDED 2026-08-10. **The cutting into a list of loops now EXISTS as a
  general theorem** (`CycleDecomposition.exists_cycle_decomposition`), and
  the sentence above should not be read as saying it is unavailable. What it
  needs is EVEN DEGREES, and the cocycle property proved in this file is not
  that: `ContourCircuits.not_evenDegrees_brokenGraph_sigmaOdd` exhibits a
  configuration whose broken-bond graph has a site of degree one. **The gap
  between "crosses every cycle evenly" and "every vertex has even degree" is
  exactly planar duality**, and it is the piece this estate does not have.
  The header's caution — that calling this "contours are circuits" would be
  wrong — stands unchanged and is if anything now sharper.

  AMENDED 2026-08-28, AND THIS TIME IT IS THE CONVERSE. The paragraph above
  says **"the converse is not attempted and is where the work is"**, and
  draws a consequence: *"without it `realisedContours` is CONSTRAINED, not
  characterised, and no upper bound on its size follows."* **The converse was
  attempted and it is proved**, in `IsingContourCocycle`, which imports this
  file and cites `cocycle_of_realised` as the other half — and this header
  said nothing about it until today. `realised_iff_cocycle` is
  `γ ∈ realisedContours n ↔ IsCocycle γ`, for `0 < n` and for `γ` whose edges
  are edges of the site graph, **and it is proved by exactly the route this
  paragraph predicted**: a configuration built by path-following, `pathParity`.
  So `realisedContours` IS characterised, and the consequence clause above is
  now false rather than merely dated.

  **The size clause is closed too, and closed against the Peierls argument
  rather than for it.** `IsingContourCocycle.card_realisedContours` gives
  `2 · #realisedContours n = 2^(n·n)` — an exact count, not a bound — and
  `card_realisedContours_unbounded` puts the consequence beyond argument.
  That file's own header calls this "the honest half": the number of contours
  is still exponential in the AREA of the box, so what the characterisation
  bought is a true count and **not** the entropy estimate Peierls needs.

  The first sentence — *"the converse is not attempted"* — was true of THIS
  file when written and stays true of this file; it is kept (`ERRATUM 94`) as
  the record of what was open. What is corrected is the reader's route: there
  was none, and the closing file is one import away.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourInvariant

namespace IsingContourClosed

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation
open IsingContourInvariant

/-! ## 1. Counting crossings

Stated for an arbitrary bond set rather than for `contour σ`, because §4
needs it applied to a set that is only later identified as a contour.
-/

/-- How many edges of a walk lie in the bond set `γ`. -/
def crossings {n : ℕ} (γ : Finset (Sym2 (Site n))) {u v : Site n}
    (w : (latticeGraph n).Walk u v) : ℕ :=
  w.edges.countP (fun e => decide (e ∈ γ))

@[simp] theorem crossings_nil {n : ℕ} (γ : Finset (Sym2 (Site n))) (u : Site n) :
    crossings γ (SimpleGraph.Walk.nil : (latticeGraph n).Walk u u) = 0 := rfl

theorem crossings_cons {n : ℕ} (γ : Finset (Sym2 (Site n))) {u v w : Site n}
    (h : (latticeGraph n).Adj u v) (p : (latticeGraph n).Walk v w) :
    crossings γ (SimpleGraph.Walk.cons h p)
      = (if s(u, v) ∈ γ then 1 else 0) + crossings γ p := by
  unfold crossings
  rw [SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases hm : s(u, v) ∈ γ <;> simp [hm, Nat.add_comm]

/-! ## 2. Exact parity along a walk

The whole file is this induction. The `cons` step is a Boolean fact: if the
first bond is broken the endpoints of that bond disagree, so adding it flips
both the parity and the agreement, and the equivalence is preserved.
-/

/-- **THE PARITY THEOREM.** Along any walk in the box, the number of contour
    crossings is even exactly when the two endpoints carry the same spin. -/
theorem even_crossings_iff {n : ℕ} (σ : Config n) {u v : Site n}
    (w : (latticeGraph n).Walk u v) :
    Even (crossings (contour σ) w) ↔ σ u = σ v := by
  induction w with
  | nil => simp
  | @cons a b c h p ih =>
    rw [crossings_cons]
    by_cases hb : s(a, b) ∈ contour σ
    · have hne : σ a ≠ σ b := ((mem_contour σ a b).mp hb).2
      rw [if_pos hb, Nat.add_comm 1, Nat.even_add_one, ih]
      cases hsa : σ a <;> cases hsb : σ b <;> cases hsc : σ c <;> simp_all
    · have heq : σ a = σ b := by
        by_contra hne
        exact hb ((mem_contour σ a b).mpr ⟨h, hne⟩)
      rw [if_neg hb, Nat.zero_add, ih, heq]

/-! ## 3. Closedness, and the old separation theorem as a corollary -/

/-- **THE CONTOUR IS CLOSED.** Every closed walk in the box crosses it an
    even number of times. This is the primal form of "every dual vertex has
    even degree" — the statement that a contour has no loose ends — and it
    is proved without a dual lattice existing anywhere in the estate. -/
theorem even_crossings_closed {n : ℕ} (σ : Config n) {u : Site n}
    (w : (latticeGraph n).Walk u u) : Even (crossings (contour σ) w) :=
  (even_crossings_iff σ w).mpr rfl

/-- `IsingContourSeparation.exists_broken_of_walk` re-derived from the exact
    parity: a walk between disagreeing sites has an ODD number of crossings,
    so in particular a nonzero number. The earlier theorem is the weaker
    half of this one, and re-deriving it is the check that §2 really does
    subsume it. -/
theorem exists_broken_of_walk' {n : ℕ} (σ : Config n) {u v : Site n}
    (w : (latticeGraph n).Walk u v) (hne : σ u ≠ σ v) :
    ∃ e ∈ w.edges, e ∈ contour σ := by
  classical
  have hodd : ¬ Even (crossings (contour σ) w) := fun hev =>
    hne ((even_crossings_iff σ w).mp hev)
  have hpos : 0 < crossings (contour σ) w := by
    rcases Nat.eq_zero_or_pos (crossings (contour σ) w) with h0 | hp
    · exact absurd (h0 ▸ (⟨0, rfl⟩ : Even 0)) hodd
    · exact hp
  obtain ⟨e, he, hce⟩ := List.countP_pos_iff.mp hpos
  exact ⟨e, he, by simpa using hce⟩

/-- **Non-vacuity, as a theorem rather than as a remark.** On the
    chessboard every bond is broken, so the one-edge walk across any bond
    has exactly ONE crossing — odd. §2's odd case is occupied. -/
theorem crossings_chess_bond {n : ℕ} {p q : Site n} (h : adj p q) :
    crossings (contour (chess n))
        (SimpleGraph.Walk.cons (show (latticeGraph n).Adj p q from h)
          SimpleGraph.Walk.nil) = 1 := by
  rw [crossings_cons, crossings_nil, Nat.add_zero, if_pos (mem_contour_chess h)]

/-! ## 4. The first constraint on the realised contours

`IsingContourInvariant` reindexed the Peierls sum onto `realisedContours`
and proved nothing whatever about that set. Here is the first thing known
about it, and it is the classical one.
-/

/-- **EVERY REALISED CONTOUR IS A COCYCLE.** A bond set that occurs as the
    contour of some configuration is crossed an even number of times by
    every cycle of the box.

    This is a NECESSARY condition. The converse — that every cocycle is
    realised — is not proved here and is where the remaining work is; see
    the header. -/
theorem cocycle_of_realised {n : ℕ} {γ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ realisedContours n) {u : Site n} (w : (latticeGraph n).Walk u u) :
    Even (crossings γ w) := by
  simp only [realisedContours] at hγ
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hγ
  exact even_crossings_closed σ w

/-! ## 5. Review round 68 — the ways this could be hollow

**"The parity theorem could be vacuously true because no walk has an odd
count."** The draft of this paragraph answered that with an argument — "any
single bond of the chessboard is a one-edge walk with count 1" — which is a
count asserted in prose beside theorems, for the fourth unit running.
`crossings_chess_bond` is now that sentence as a theorem: on the chessboard
the one-edge walk across any bond has crossing number exactly `1`. The odd
case is occupied, and `exists_broken_of_walk'` is the general form of it.

**"§3 could be circular — re-deriving a theorem this file imports."** The
direction matters and it is the honest way round.
`IsingContourSeparation.exists_broken_of_walk` is imported but is NOT used
in this file's proofs; §2 is proved from scratch by induction, and §3
re-derives the imported statement from it. That is the check that §2
subsumes the earlier theorem rather than merely resembling it. Both remain
in the estate because the earlier one is what the earlier file's downstream
results are stated against.

**"'Contours are closed' could be overclaiming for an evenness statement."**
This is the claim worth testing hardest, and the header is deliberately
narrow. What is proved is the cocycle property: every cycle crosses the
contour evenly. That is the CONTENT of closedness — it is exactly what "no
loose ends" means, and it is the property the dual-lattice argument extracts
from "every dual vertex has even degree". What is NOT proved is the
DECOMPOSITION: a `Finset` of bonds with the cocycle property has not been
cut into an explicit list of circuits, and Peierls counts circuits. Calling
this "contours are closed" is accurate; calling it "contours are circuits"
would not be, and the file does not.

**"§4 could suggest `realisedContours` is now characterised."** It is not,
and the header says which half is missing. `cocycle_of_realised` is one
inclusion. The converse needs a configuration built by path-following, with
well-definedness from the cocycle condition, and until that exists no upper
bound on `#realisedContours` follows from anything here — which is the
quantity the entropy half is about. `MagnetisationBound` is untouched.
-/

end IsingContourClosed
