/-
  IsingContourSeparation.lean — the contour separates, and the ground states
  are exactly the two constant configurations.

  WHY THIS FILE EXISTS, and it is a test rather than a plan.
  `IsingContourEnergy.lean` claims — in its header, in its `TRUE_LEDGER` row
  and in the `WALLS.md` W3 amendment — that building the contour as a
  `SimpleGraph` rather than as a bespoke `Finset` means "Mathlib's `Walk` /
  `Subgraph` / `ConnectedComponent` API now applies to the contour, which is
  the API the geometric half will need". **That is a prediction about future
  work, made by the party who benefits from it being believed.** ERRATUM 48
  says the check for a "this makes X possible" claim is to attempt X. This
  file is the attempt. The verdict, including the part of the claim that did
  NOT hold, is in §6.

  WHAT THIS FILE PROVES:
  1. **`latticeGraph`** — the box itself as a `SimpleGraph`, and
     `agreeGraph`, the bonds that are not broken. `latticeGraph_eq_sup` and
     `agree_disjoint_broken`: the box splits into agreeing and broken bonds,
     disjointly, so the contour is not an auxiliary set but exactly the half
     of the lattice the configuration breaks.
  2. **`agree_const`** — spin is constant along any walk in `agreeGraph`.
  3. **`exists_broken_of_walk`** — **THE SEPARATION THEOREM.** Every path in
     the box between two sites that disagree contains a contour edge. In
     Peierls language: you cannot get from the `+` region to the `−` region
     without crossing the contour. No dual lattice is needed to say it.
  4. **`latticeGraph_connected`** — the box is connected for `n ≥ 1`.
  5. **`contour_eq_empty_iff`** — the contour is empty exactly when the
     configuration is constant. This is where 3 and 4 meet.
  6. **`isingH_eq_ground_iff_const`** — **THE GROUND STATES ARE EXACTLY THE
     TWO CONSTANT CONFIGURATIONS.** The estate characterised the ground
     states nowhere. `IsingContourEnergy.isingH_eq_ground_iff` got as far as
     "the minimisers are the contour-free configurations" without knowing
     which configurations those are; this says which, and
     `isingH_allFalse_eq_allTrue` confirms the easy direction by direct
     computation rather than through the characterisation.
  7. **`card_ground_states`** — and there are exactly two of them, out of
     the `2^(n²)` configurations counted by `card_config`.

  WHAT THIS DOES NOT DO. **It does not organise the contour into circuits**,
  which is the actual content of the geometric half. There is no dual
  lattice, no planar duality, no proof that the broken bonds around a
  minority region form a closed loop, and no `3^{|γ|}` entropy count.
  Separation is necessary for Peierls and nowhere near sufficient: Peierls
  has to ENUMERATE the contours surrounding a site, and enumerating needs
  the circuit structure this file does not build.
  **`IsingBoundaryField.MagnetisationBound` is still not proved.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourEnergy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace IsingContourSeparation

open IsingFiniteVolume IsingContourEnergy

/-! ## 1. The box, and the bonds that are not broken -/

/-- The box itself as a `SimpleGraph`: sites joined by lattice bonds. -/
def latticeGraph (n : ℕ) : SimpleGraph (Site n) where
  Adj p q := adj p q
  symm := fun p q h => (adj_symm p q).mp h
  loopless := ⟨fun p h => adj_irrefl p h⟩

@[simp] theorem latticeGraph_adj {n : ℕ} (p q : Site n) :
    (latticeGraph n).Adj p q ↔ adj p q := Iff.rfl

instance instDecidableLatticeAdj {n : ℕ} : DecidableRel (latticeGraph n).Adj :=
  fun p q => inferInstanceAs (Decidable (adj p q))

/-- The bonds a configuration does NOT break. The `p ≠ q` clause is what
    makes this a `SimpleGraph`; it costs nothing, because `adj_irrefl` says
    no site is adjacent to itself anyway. -/
def agreeGraph {n : ℕ} (σ : Config n) : SimpleGraph (Site n) where
  Adj p q := adj p q ∧ p ≠ q ∧ σ p = σ q
  symm := by
    intro p q h
    exact ⟨(adj_symm p q).mp h.1, Ne.symm h.2.1, h.2.2.symm⟩
  loopless := ⟨fun _ h => h.2.1 rfl⟩

@[simp] theorem agreeGraph_adj {n : ℕ} (σ : Config n) (p q : Site n) :
    (agreeGraph σ).Adj p q ↔ (adj p q ∧ p ≠ q ∧ σ p = σ q) := Iff.rfl

/-- **The box splits into agreeing bonds and broken bonds.** So the contour
    is not an auxiliary set: it is exactly the half of the lattice that the
    configuration breaks. -/
theorem latticeGraph_eq_sup {n : ℕ} (σ : Config n) :
    latticeGraph n = agreeGraph σ ⊔ brokenGraph σ := by
  ext p q
  simp only [latticeGraph_adj, SimpleGraph.sup_adj, agreeGraph_adj, brokenGraph_adj]
  constructor
  · intro h
    by_cases hs : σ p = σ q
    · exact Or.inl ⟨h, fun hpq => adj_irrefl p (hpq ▸ h), hs⟩
    · exact Or.inr ⟨h, hs⟩
  · rintro (⟨h, -, -⟩ | ⟨h, -⟩) <;> exact h

/-- And the two halves are disjoint — no bond is both. -/
theorem agree_disjoint_broken {n : ℕ} (σ : Config n) (p q : Site n) :
    ¬ ((agreeGraph σ).Adj p q ∧ (brokenGraph σ).Adj p q) := by
  rintro ⟨⟨-, -, hs⟩, ⟨-, hn⟩⟩
  exact hn hs

/-! ## 2. Spin is constant along agreement walks

The first place the graph API has to earn its keep. This is a statement
about paths, `Walk` is an inductive type, and the proof is one line per
constructor with no bespoke path machinery at all.
-/

/-- Spin is constant along any walk that never crosses a broken bond. -/
theorem agree_const {n : ℕ} (σ : Config n) {p q : Site n}
    (w : (agreeGraph σ).Walk p q) : σ p = σ q := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact h.2.2.trans ih

theorem agree_const_of_reachable {n : ℕ} (σ : Config n) {p q : Site n}
    (h : (agreeGraph σ).Reachable p q) : σ p = σ q := by
  obtain ⟨w⟩ := h
  exact agree_const σ w

/-! ## 3. Separation

The statement Peierls actually uses, said without a dual lattice: you cannot
walk from a `+` site to a `−` site without crossing the contour.
-/

/-- **THE SEPARATION THEOREM.** Every path in the box between two sites
    whose spins disagree contains an edge of the contour. -/
theorem exists_broken_of_walk {n : ℕ} (σ : Config n) {p q : Site n}
    (w : (latticeGraph n).Walk p q) :
    σ p ≠ σ q → ∃ e ∈ w.edges, e ∈ contour σ := by
  induction w with
  | nil => intro hne; exact absurd rfl hne
  | @cons u v r h w ih =>
    intro hne
    by_cases hs : σ u = σ v
    · obtain ⟨e, he, hce⟩ := ih (fun hc => hne (hs.trans hc))
      exact ⟨e, by simp [he], hce⟩
    · exact ⟨s(u, v), by simp, (mem_contour σ u v).mpr ⟨h, hs⟩⟩

/-- Contrapositive, in the form §5 uses: with no contour to cross,
    reachability in the box already forces agreement. -/
theorem eq_of_reachable_of_contour_empty {n : ℕ} (σ : Config n)
    (h : contour σ = ∅) {p q : Site n} (hr : (latticeGraph n).Reachable p q) :
    σ p = σ q := by
  by_contra hne
  obtain ⟨w⟩ := hr
  obtain ⟨e, -, hce⟩ := exists_broken_of_walk σ w hne
  rw [h] at hce
  exact absurd hce (Finset.notMem_empty e)

/-! ## 4. The box is connected

The one step where the graph API does NOT do the work. Connectivity of
`Fin n × Fin n` under nearest-neighbour adjacency is `Fin` arithmetic, and
it is done here the obvious way: walk the second coordinate down to zero,
then the first.
-/

/-- Walk the second coordinate down to zero. -/
theorem reachable_snd_zero {n : ℕ} (hn : 0 < n) (a : Fin n) :
    ∀ (j : ℕ) (hj : j < n),
      (latticeGraph n).Reachable (a, ⟨j, hj⟩) (a, ⟨0, hn⟩) := by
  intro j
  induction j with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    intro hj
    have hm : m < n := by omega
    have hadj : (latticeGraph n).Adj (a, (⟨m + 1, hj⟩ : Fin n)) (a, (⟨m, hm⟩ : Fin n)) :=
      Or.inl ⟨rfl, Or.inr rfl⟩
    exact hadj.reachable.trans (ih hm)

/-- Then walk the first coordinate down to zero. -/
theorem reachable_fst_zero {n : ℕ} (hn : 0 < n) :
    ∀ (i : ℕ) (hi : i < n),
      (latticeGraph n).Reachable ((⟨i, hi⟩ : Fin n), (⟨0, hn⟩ : Fin n))
        (⟨0, hn⟩, ⟨0, hn⟩) := by
  intro i
  induction i with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    intro hi
    have hm : m < n := by omega
    have hadj : (latticeGraph n).Adj
        ((⟨m + 1, hi⟩ : Fin n), (⟨0, hn⟩ : Fin n))
        ((⟨m, hm⟩ : Fin n), (⟨0, hn⟩ : Fin n)) :=
      Or.inr ⟨rfl, Or.inr rfl⟩
    exact hadj.reachable.trans (ih hm)

theorem reachable_origin {n : ℕ} (hn : 0 < n) (p : Site n) :
    (latticeGraph n).Reachable p (⟨0, hn⟩, ⟨0, hn⟩) := by
  have h1 : (latticeGraph n).Reachable p (p.1, ⟨0, hn⟩) := by
    have h := reachable_snd_zero hn p.1 p.2.val p.2.isLt
    simpa using h
  have h2 : (latticeGraph n).Reachable (p.1, (⟨0, hn⟩ : Fin n)) (⟨0, hn⟩, ⟨0, hn⟩) := by
    have h := reachable_fst_zero hn p.1.val p.1.isLt
    simpa using h
  exact h1.trans h2

/-- **The box is connected** for every `n ≥ 1`. -/
theorem latticeGraph_connected {n : ℕ} (hn : 0 < n) : (latticeGraph n).Connected := by
  haveI : Nonempty (Site n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  refine ⟨fun p q => ?_⟩
  exact (reachable_origin hn p).trans (reachable_origin hn q).symm

/-! ## 5. The contour is empty exactly on the constants -/

/-- **No contour iff constant.** Separation gives one direction, and it is
    the direction that needs the box to be connected — on a disconnected
    lattice a configuration could be constant on each piece and differ
    between them, with no bond broken. -/
theorem contour_eq_empty_iff {n : ℕ} (hn : 0 < n) (σ : Config n) :
    contour σ = ∅ ↔ ∀ p q : Site n, σ p = σ q := by
  constructor
  · intro h p q
    exact eq_of_reachable_of_contour_empty σ h
      ((latticeGraph_connected hn).preconnected p q)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    refine Sym2.ind (fun p q => ?_)
    rw [mem_contour]
    rintro ⟨-, hne⟩
    exact hne (h p q)

theorem const_iff_eq {n : ℕ} (hn : 0 < n) (σ : Config n) :
    (∀ p q : Site n, σ p = σ q) ↔ (σ = fun _ => true) ∨ (σ = fun _ => false) := by
  constructor
  · intro h
    cases hb : σ (⟨0, hn⟩, ⟨0, hn⟩) with
    | true => exact Or.inl (funext fun p => (h p _).trans hb)
    | false => exact Or.inr (funext fun p => (h p _).trans hb)
  · rintro (rfl | rfl) <;> intro p q <;> rfl

/-! ## 6. The ground states, and the verdict on the claim this file tests -/

/-- The all-down configuration has the same energy as the all-up one, by the
    same direct computation as `isingH_allTrue_eq` — every bond contributes
    `(-1)·(-1) = 1`. Stated separately so the easy half of the theorem below
    is confirmed by computation and not only by the characterisation. -/
theorem isingH_allFalse_eq (n : ℕ) :
    isingH n (fun _ => false) = -(bondCount n : ℝ) := by
  have hp : ∀ p q : Site n,
      (if adj p q then spin ((fun _ : Site n => false) p)
          * spin ((fun _ : Site n => false) q) else 0)
        = (if adj p q then (1:ℝ) else 0) := by
    intro p q
    by_cases hadj : adj p q
    · rw [if_pos hadj, if_pos hadj]; norm_num [spin]
    · rw [if_neg hadj, if_neg hadj]
  rw [isingH]
  simp_rw [hp]
  rw [sum_bond_eq]

theorem isingH_allFalse_eq_allTrue (n : ℕ) :
    isingH n (fun _ => false) = isingH n (fun _ => true) := by
  rw [isingH_allFalse_eq, isingH_allTrue_eq]

/-- **THE GROUND STATES ARE EXACTLY THE TWO CONSTANT CONFIGURATIONS.**
    `IsingContourEnergy.isingH_eq_ground_iff` said the minimisers are the
    contour-free configurations without saying which those are; §5 says
    which. The estate had no characterisation of the ground states.

    Note this is the ZERO-FIELD statement, and it is why
    `IsingBoundaryField` needs its field: without one the two constants are
    exactly tied, which `isingH_allFalse_eq_allTrue` confirms directly. -/
theorem isingH_eq_ground_iff_const {n : ℕ} (hn : 0 < n) (σ : Config n) :
    isingH n σ = isingH n (fun _ => true)
      ↔ (σ = fun _ => true) ∨ (σ = fun _ => false) := by
  rw [isingH_eq_ground_iff, contour_eq_empty_iff hn, const_iff_eq hn]

/-- The same thing as a minimisation statement. -/
theorem isingH_lt_of_not_const {n : ℕ} (hn : 0 < n) (σ : Config n)
    (h : σ ≠ fun _ => true) (h' : σ ≠ fun _ => false) :
    isingH n (fun _ => true) < isingH n σ := by
  rcases lt_or_eq_of_le (isingH_ground_le σ) with hlt | heq
  · exact hlt
  · exact absurd ((isingH_eq_ground_iff_const hn σ).mp heq.symm) (by tauto)

theorem allTrue_ne_allFalse {n : ℕ} (hn : 0 < n) :
    (fun _ : Site n => true) ≠ (fun _ => false) := by
  intro h
  exact Bool.noConfusion (congrFun h (⟨0, hn⟩, ⟨0, hn⟩))

theorem card_config (n : ℕ) : Fintype.card (Config n) = 2 ^ (n * n) := by
  simp [Config, Site]

/-- **EXACTLY TWO GROUND STATES, at every box size**, out of the
    `2^(n²)` configurations counted by `card_config`. The count is stated as
    a theorem rather than as a remark, because an "exactly" in a docstring is
    a claim like any other. -/
theorem card_ground_states {n : ℕ} (hn : 0 < n) :
    (Finset.univ.filter
        (fun σ : Config n => isingH n σ = isingH n (fun _ => true))).card = 2 := by
  classical
  have hset : (Finset.univ.filter
      (fun σ : Config n => isingH n σ = isingH n (fun _ => true)))
      = {(fun _ => true), (fun _ => false)} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact isingH_eq_ground_iff_const hn σ
  rw [hset, Finset.card_insert_of_notMem (by simpa using allTrue_ne_allFalse hn),
    Finset.card_singleton]

/-! ### Review round 65 — and the verdict on the claim this file was written to test

**THE CLAIM WAS PARTLY RIGHT, AND THE PART THAT WAS WRONG IS WORTH SAYING.**
`IsingContourEnergy` predicted that Mathlib's `Walk` / `Subgraph` /
`ConnectedComponent` API "is the API the geometric half will need".

*What held.* §2 and §3 are exactly what the claim promised. `agree_const` is
an induction over `Walk` with one line per constructor; `exists_broken_of_walk`
is the same shape, and `Walk.edges` gave the conclusion its natural form
("some edge of this path is in the contour") with no work. Neither would have
been available against a bespoke `Finset` of ordered pairs — there would have
been no `Walk` to induct on, and a path type would have had to be defined
first. **On §2–§3 the graph earned its keep.**

*What did not.* §4 is the load-bearing step of this file — separation is
vacuous on a disconnected box — and **the graph API contributes nothing to
it.** `latticeGraph_connected` is `Fin` arithmetic, done by walking each
coordinate down to zero, and would have looked the same in any formulation.
So the honest form of the claim is narrower than what was written: the graph
API carries reasoning ALONG contours and does nothing for facts about the
LATTICE, which have to be proved by hand.

*And the specific names were half wrong.* The prediction listed `Walk`,
`Subgraph` and `ConnectedComponent`. **`Walk` is used and is the whole of
§2–§3. `Subgraph` and `ConnectedComponent` are used nowhere in this file.**
What actually carried the rest were `Reachable` and `Connected`, neither of
which the prediction named. A guess at which three names would matter, made
before writing any of it, got one of three — which is about what a guess
deserves, and is worth recording next to the part that came out right.

*Neither `WALLS.md` nor the ledger row is softened.* The prediction was made
about the geometric half and one stair of it now exists, which is evidence
for it. This paragraph narrows it with the specific thing that did not
transfer.

**"Separation could be vacuous."** It is not: `mem_contour_chess` (previous
file) gives a configuration breaking every bond, and §6 shows the contour is
empty for exactly two configurations out of `2^(n²)`, so both ends are
occupied. §4 is what stops the theorem from being empty in the other
direction — on a disconnected lattice, two sites in different pieces could
disagree with no bond broken, and the statement would be false rather than
merely weak.

**"§6 could be circular."** The forward direction runs §3 → §4 → §5 → §6 and
uses `isingH_eq_ground_iff`, which is genuinely upstream. The backward
direction — that both constants really are ground states — is not taken from
the characterisation at all: `isingH_allFalse_eq` computes the all-down
energy directly from `spin`, the same way `isingH_allTrue_eq` does, and gets
the same `-bondCount`. So the two halves are independent.

**"This could be claimed as progress toward the magnetisation bound."** It is
one necessary ingredient and not a step toward the count. Peierls needs to
ENUMERATE contours around a site; enumeration needs circuits; circuits need
the dual lattice, and none of that is here. `MagnetisationBound` is exactly
as unproved as it was.
-/

end IsingContourSeparation
