/-
  BoxGraph.lean — the d-dimensional box, and the field theory in the
  dimension the physics actually names.

  WHY. `PROOF_STRATEGY` §3: "B IS A RUNG, NOT A LANDING. The moment B lands,
  immediately re-attempt B → C." `GraphLaplacian` was a B: it took the W1
  covariance layer off the square box and put it over an arbitrary finite
  simple graph. **The C that B was for is `d = 4`**, which is what `WALLS.md`
  W1 and W2 both want and what no object in this estate had ever been.

  WHAT THIS FILE PROVES:
  1. **`boxGraph d n`** — the `n^d` box in ANY dimension, free boundary, as a
     `SimpleGraph` on `Fin d → Fin n`, with `boxGraph_connected`. The
     connectivity is the only real proof here: a descent on `∑ i, (p i).val`,
     stepping one coordinate down at a time to the origin.
  2. **`boxGraph_two_iso`** — **the `d = 2` case IS the estate's box.** A
     graph isomorphism `boxGraph 2 n ≃g IsingContourSeparation.latticeGraph n`,
     which is the check that this is a generalisation and not a lookalike.
     Without it a reader has only the name to go on.
  3. **§4: the four-dimensional field.** `lap4`, `massive4`, `green4`,
     `field4`, and `twoPoint4` — **the two-point function of a Gaussian field
     on a four-dimensional lattice equals the four-dimensional massive Green
     function.** Every one is `GraphLaplacian`'s theorem at `boxGraph 4 n`;
     the point is that they now have a subject.

  WHAT THIS DOES NOT DO, and it is the whole of W1. **No reflection
  positivity, and in four dimensions not even a reflection.**
  `LatticeReflection.refl` is `Fin.rev` on the first component of a PAIR, so
  the existing Lean object does not apply here; **the analogue on
  `Fin d → Fin n` is easy to write and this file does not write it** — a
  statement about what was done, not about difficulty. So the
  four-dimensional field exists and is Gaussian and has the right
  covariance, and **nothing about Osterwalder–Schrader is closer than it
  was.** Getting the dimension right was never the difficulty; it was a
  mismatch between what the estate had built and what its own wall document
  said it needed.

  Nor is there any continuum limit, any lattice spacing, or any relation
  between `n` and a physical volume. `d = 4` here is four coordinates, not
  spacetime.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphLaplacian

namespace BoxGraph

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d n : ℕ}

/-! ## 1. The box in any dimension -/

/-- A site of the `n^d` box: one `Fin n` coordinate per dimension. -/
abbrev Site (d n : ℕ) := Fin d → Fin n

/-- Nearest-neighbour adjacency, FREE boundary: the sites agree in every
    coordinate but one, and differ by a single step there. At `d = 2` this
    is `IsingFiniteVolume.adj`; §3 proves it. -/
def adj (p q : Site d n) : Prop :=
  ∃ i : Fin d, (∀ j, j ≠ i → p j = q j) ∧
    ((p i).val + 1 = (q i).val ∨ (q i).val + 1 = (p i).val)

instance (p q : Site d n) : Decidable (adj p q) := by
  unfold adj; infer_instance

theorem adj_symm (p q : Site d n) : adj p q ↔ adj q p := by
  constructor <;> rintro ⟨i, h1, h2⟩ <;>
    exact ⟨i, fun j hj => (h1 j hj).symm, h2.symm⟩

theorem adj_irrefl (p : Site d n) : ¬ adj p p := by
  rintro ⟨i, -, h | h⟩ <;> omega

/-- **THE d-DIMENSIONAL BOX.** -/
def boxGraph (d n : ℕ) : SimpleGraph (Site d n) where
  Adj p q := adj p q
  symm := fun p q h => (adj_symm p q).mp h
  loopless := ⟨fun p h => adj_irrefl p h⟩

@[simp] theorem boxGraph_adj (p q : Site d n) :
    (boxGraph d n).Adj p q ↔ adj p q := Iff.rfl

instance : DecidableRel (boxGraph d n).Adj := fun p q =>
  inferInstanceAs (Decidable (adj p q))

/-! ## 2. Connectivity

The only genuine proof in the file. Walk each coordinate down to zero, one
step at a time; the sum of the coordinates strictly decreases, so the descent
terminates at the origin.
-/

/-- The origin of the box. -/
def zeroSite (d : ℕ) (hn : 0 < n) : Site d n := fun _ => ⟨0, hn⟩

private theorem eq_zeroSite (hn : 0 < n) {p : Site d n}
    (h : ∑ i, (p i).val = 0) : p = zeroSite d hn := by
  funext i
  exact Fin.ext (Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i))

private theorem val_update (p : Site d n) (i : Fin d) (v : Fin n) :
    (fun j => ((Function.update p i v) j).val)
      = Function.update (fun j => (p j).val) i v.val := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- Stepping one coordinate down by one is a bond. -/
private theorem adj_pred {p : Site d n} {i : Fin d} {v : Fin n}
    (hv : v.val + 1 = (p i).val) : adj (Function.update p i v) p := by
  refine ⟨i, fun j hj => ?_, Or.inl ?_⟩
  · simp [Function.update_of_ne hj]
  · simpa using hv

/-- And it strictly decreases the coordinate sum. -/
private theorem sum_update_succ {p : Site d n} {i : Fin d} {v : Fin n}
    (hv : v.val + 1 = (p i).val) :
    (∑ j, ((Function.update p i v) j).val) + 1 = ∑ j, (p j).val := by
  have hsplit : (p i).val + ∑ j ∈ Finset.univ.erase i, (p j).val
      = ∑ j, (p j).val :=
    Finset.add_sum_erase Finset.univ (fun j => (p j).val) (Finset.mem_univ i)
  rw [val_update, Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  omega

private theorem reachable_zeroSite (hn : 0 < n) :
    ∀ (k : ℕ) (p : Site d n), (∑ i, (p i).val) ≤ k →
      (boxGraph d n).Reachable (zeroSite d hn) p := by
  intro k
  induction k with
  | zero =>
      intro p hp
      rw [eq_zeroSite hn (Nat.le_zero.mp hp)]
  | succ k ih =>
      intro p hp
      by_cases h0 : ∑ i, (p i).val = 0
      · rw [eq_zeroSite hn h0]
      · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
        have hlt : (p i).val - 1 < n :=
          lt_of_le_of_lt (Nat.sub_le _ _) (p i).isLt
        set v : Fin n := ⟨(p i).val - 1, hlt⟩ with hvdef
        have hv : v.val + 1 = (p i).val := by
          simp only [hvdef]
          omega
        have hsum := sum_update_succ (p := p) (i := i) hv
        exact (ih (Function.update p i v) (by omega)).trans
          (SimpleGraph.Adj.reachable (G := boxGraph d n) (adj_pred hv))

/-- **THE BOX IS CONNECTED IN EVERY DIMENSION.** This is what
    `GraphLaplacian.lapMatrix_mulVec_eq_zero_iff_const` consumes, and it is
    the only hypothesis the general theory needs that a graph does not carry
    for free. -/
theorem boxGraph_connected (d : ℕ) (hn : 0 < n) : (boxGraph d n).Connected := by
  haveI : Nonempty (Site d n) := ⟨zeroSite d hn⟩
  refine ⟨fun p q => ?_⟩
  exact (reachable_zeroSite hn _ p le_rfl).symm.trans
    (reachable_zeroSite hn _ q le_rfl)

/-! ## 3. The two-dimensional case is the estate's box

A generalisation that cannot be checked against the thing it generalises is
a name, not a theorem. `finTwoArrowEquiv` identifies the vertex types and
the adjacencies correspond — coordinate `0` of `boxGraph 2 n` is the first
component of `IsingFiniteVolume.Site n`, coordinate `1` the second, and the
two disjuncts of `IsingFiniteVolume.adj` are the two values of the index
`i`.
-/

/-- The vertex types agree — Mathlib's own identification of `Fin 2 → α`
    with `α × α`, not one written here to make a proof go. -/
def sitePair (n : ℕ) : Site 2 n ≃ IsingFiniteVolume.Site n :=
  finTwoArrowEquiv (Fin n)

open IsingFiniteVolume in
theorem adj_two_iff (p q : Site 2 n) :
    adj p q ↔ IsingFiniteVolume.adj (sitePair n p) (sitePair n q) := by
  constructor
  · rintro ⟨i, h1, h2⟩
    fin_cases i
    · exact Or.inr ⟨h1 1 (by decide), h2⟩
    · exact Or.inl ⟨h1 0 (by decide), h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨1, fun j hj => by fin_cases j; exacts [h1, absurd rfl hj], h2⟩
    · exact ⟨0, fun j hj => by fin_cases j; exacts [absurd rfl hj, h1], h2⟩

/-- **`boxGraph 2 n` IS `latticeGraph n`**, as graphs. -/
def boxGraph_two_iso (n : ℕ) :
    boxGraph 2 n ≃g IsingContourSeparation.latticeGraph n where
  toEquiv := sitePair n
  map_rel_iff' := (adj_two_iff _ _).symm

/-! ## 4. The four-dimensional field

Nothing below is proved here: every one is `GraphLaplacian`'s theorem at
`boxGraph 4 n`. They are named because a theorem with no subject is not a
theorem anybody can find, and because until now this estate had no
four-dimensional lattice object at all.
-/

/-- The four-dimensional lattice Laplacian. -/
noncomputable abbrev lap4 (n : ℕ) : Matrix (Site 4 n) (Site 4 n) ℝ :=
  (boxGraph 4 n).lapMatrix ℝ

/-- `−Δ + m²` in four dimensions. -/
noncomputable abbrev massive4 (n : ℕ) (m : ℝ) : Matrix (Site 4 n) (Site 4 n) ℝ :=
  GraphLaplacian.massive (boxGraph 4 n) m

/-- **THE FOUR-DIMENSIONAL MASSIVE GREEN FUNCTION.** -/
noncomputable abbrev green4 (n : ℕ) (m : ℝ) : Matrix (Site 4 n) (Site 4 n) ℝ :=
  GraphLaplacian.green (boxGraph 4 n) m

/-- **THE FOUR-DIMENSIONAL LATTICE GAUSSIAN FIELD.** -/
noncomputable abbrev field4 (n : ℕ) (m : ℝ) : Measure (EuclideanSpace ℝ (Site 4 n)) :=
  GraphLaplacian.gaussianField (boxGraph 4 n) m

theorem massive4_posDef (n : ℕ) {m : ℝ} (hm : m ≠ 0) : (massive4 n m).PosDef :=
  GraphLaplacian.massive_posDef _ hm

theorem green4_posDef (n : ℕ) {m : ℝ} (hm : m ≠ 0) : (green4 n m).PosDef :=
  GraphLaplacian.green_posDef _ hm

theorem lap4_posSemidef (n : ℕ) : (lap4 n).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix ℝ _

/-- The zero mode in four dimensions: the kernel is the constants, which is
    where `boxGraph_connected` is spent. -/
theorem lap4_mulVec_eq_zero_iff_const {n : ℕ} (hn : 0 < n) (x : Site 4 n → ℝ) :
    lap4 n *ᵥ x = 0 ↔ ∃ c : ℝ, x = fun _ => c :=
  GraphLaplacian.lapMatrix_mulVec_eq_zero_iff_const _ (boxGraph_connected 4 hn) x

/-- **THE FOUR-DIMENSIONAL TWO-POINT FUNCTION IS THE FOUR-DIMENSIONAL GREEN
    FUNCTION.** -/
theorem twoPoint4 (n : ℕ) {m : ℝ} (hm : m ≠ 0) (p q : Site 4 n) :
    ∫ ω, ω p * ω q ∂(field4 n m) = green4 n m p q :=
  GraphLaplacian.twoPoint _ hm p q

theorem twoPoint4_diag_pos (n : ℕ) {m : ℝ} (hm : m ≠ 0) (p : Site 4 n) :
    0 < ∫ ω, ω p * ω p ∂(field4 n m) :=
  GraphLaplacian.twoPoint_diag_pos _ hm p

/-- A numeric anchor, so the object is pinned rather than merely typed: the
    `2^4` box has `16` sites, every site has degree `4` (one neighbour per
    coordinate, since the side is 2), so `16 · 4 / 2 = 32` edges and a trace
    of `64` ordered bonds. A wrong adjacency — periodic boundaries, say, or a
    diagonal coupling — gives a different number. -/
theorem trace_lap4_two : Matrix.trace (lap4 2) = 2 * ((boxGraph 4 2).edgeFinset.card : ℝ) :=
  GraphLaplacian.trace_lapMatrix _

theorem card_edgeFinset_four_two : (boxGraph 4 2).edgeFinset.card = 32 := by decide

theorem trace_lap4_two_eq : Matrix.trace (lap4 2) = 64 := by
  rw [trace_lap4_two, card_edgeFinset_four_two]
  norm_num

/-! ## 5. Review round 76 — the ways this could be hollow

**"§4 could be a rename."** It is, and the header says so in the section
heading itself: every theorem in §4 is `GraphLaplacian`'s at
`boxGraph 4 n`, discharged by one application. **What is NOT a rename is §1
and §2**, because none of §4 could be stated before them — the general
theory needs a graph, and the only lattice graph in the estate was
two-dimensional. `boxGraph_connected` is the one hypothesis the general
theory cannot supply for itself, and it is a real induction.

**"The `d = 4` claim could be decoration."** The test is whether a reader
could have obtained `twoPoint4` yesterday, and they could not: there was no
four-dimensional lattice object of any kind in this estate. **The test it
FAILS is whether that matters to the wall**, and it does not. See below.

**"`boxGraph 2 n ≃g latticeGraph n` could be doing violence to one side."**
It is a `RelIso`, so adjacency is preserved in both directions, and the
underlying map is `piFinTwoEquiv` — the library's own identification, and it is in the ROOT
namespace: this line said `Equiv.piFinTwoEquiv`, which does not exist (`ERRATUM 224`), and the
wrong spelling is kept beside the right one —
not one written here to make the proof go. `adj_two_iff` is proved by case
analysis on the index, and the correspondence is exactly the expected one:
index `1` is `IsingFiniteVolume.adj`'s first disjunct (`p.1 = q.1`, second
coordinate steps), index `0` is its second. **Had the estate's `adj` used a
different convention the `fin_cases` would have produced two unprovable
goals rather than a silently different graph.**

**"This could be presented as progress on W1."** It is not, and the
distinction is sharp enough to state. W1's failing step is reflection
positivity of the massive Green function. To state it one needs a reflection;
`LatticeReflection.refl` is `Fin.rev` on the first component of a PAIR, **so
the existing object does not apply to `Fin d → Fin n`, this file does not
import `LatticeReflection`, and it does not build the replacement.** The
replacement is not hard — reverse one coordinate with `Function.update` —
and implying otherwise would be the mirror image of the mistake
`LatticeField` §3 already recorded once, where "done and waiting" concealed
a missing object. **The honest form is that it is unwritten, and that
writing it would not touch the positivity.** So the four-
dimensional theory currently has strictly less structure attached to it than
the two-dimensional one, not more. What changed is the carrier. W1's
mathematics is untouched, and the honest summary is that the estate had been
proving `d = 2` theorems while its own wall document asked for `d = 4`, and
that mismatch — not the difficulty — is what this closes.

**"`card_edgeFinset_four_two = 32` could be wrong and `decide` could be
hiding it."** `decide` is a kernel computation over a 16-vertex graph, so it
is not hiding anything, but the number is worth a hand check: `2^4 = 16`
sites, every coordinate has exactly one neighbour in a box of side 2, so
every site has degree 4 and there are `16 · 4 / 2 = 32` edges. Periodic
boundaries at side 2 would double-count each pair and are excluded by
construction. The trace is `2 · 32 = 64` ordered bonds.

**And the draft of the line above got that wrong, which is worth recording.**
It said the trace was `32` — confusing the edge count with the degree sum —
in a docstring, in the theorem statement, and nowhere else, because this same
paragraph was written at the same time and had it right. **The kernel caught
it, and only because the number happened to sit in a theorem rather than only
in prose.** ERRATUM 58 is about numbers in summary sentences that no theorem
supports; the practical corollary is visible here: **put the number in a
theorem and the compiler becomes the reviewer.** `trace_lap4_two_eq` is now
`64`.
-/

end BoxGraph
