/-
  IsingContourInvariant.lean — the contour is a complete invariant of the
  configuration up to the global flip, and therefore the Peierls sum can be
  reindexed.

  WHY. The Gibbs unit ends by saying what it does not give: Peierls needs a
  SUM over contours, not a maximum over configurations. **A Peierls
  argument's very first move is to stop summing over configurations and
  start summing over contours**, and that move is a counting fact, not a
  geometric one. This file makes it.

  WHAT THIS FILE PROVES:
  1. **`const_of_adj_const`** — a function constant across every bond is
     constant. This GENERALISES
     `IsingContourSeparation.eq_of_reachable_of_contour_empty`, which is the
     same statement for the single case `f = σ`. The general form arrived
     one unit later than the special one, which is worth noticing: the
     special case was written with the general proof already in hand.
  2. **`contour_flip`** — flipping every spin leaves the contour alone.
  3. **`contour_eq_iff`** — **THE CONTOUR IS A COMPLETE INVARIANT UP TO THE
     FLIP.** Two configurations break exactly the same bonds iff they are
     equal or exactly opposite. The argument is one line of mathematics:
     `σ p == τ p` is unchanged across every bond, so §1 makes it constant.
  4. **`card_fiber`** — hence every realised contour comes from exactly two
     configurations, and **`sum_over_contours`**: summing anything at all
     over the `2^(n²)` configurations equals twice summing it over the
     contours that actually occur. **That is the reindexing.**
  5. **`gibbs_sum_over_contours`** — the same statement for the Gibbs
     weights, which is the form a Peierls estimate consumes.

  WHAT THIS DOES NOT DO. It reindexes the sum; it does not BOUND it. Peierls
  needs to know how many realised contours of a given length pass through a
  fixed site — the `3^{|γ|}` count — and that is pure lattice geometry:
  circuits, the dual lattice, and the surgery this file has none of. The
  set `realisedContours` here is defined as the image of `contour` and
  nothing is proved about its size. **`IsingBoundaryField.MagnetisationBound`
  is untouched.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourGibbs

namespace IsingContourInvariant

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation MeasureTheory

/-! ## 1. Constant across every bond means constant

`IsingContourSeparation` proved this for the configuration itself, on the
way to `contour_eq_empty_iff`. Nothing in that proof used the fact that the
function was a `Config`, and §3 below needs it for a different function, so
here it is with the hypothesis removed.
-/

/-- A function constant across every lattice bond is constant on the box. -/
theorem const_of_adj_const {n : ℕ} (hn : 0 < n) {α : Type*} (f : Site n → α)
    (h : ∀ p q, adj p q → f p = f q) (p q : Site n) : f p = f q := by
  have key : ∀ {u v : Site n}, (latticeGraph n).Walk u v → f u = f v := by
    intro u v w
    induction w with
    | nil => rfl
    | cons hadj _ ih => exact (h _ _ hadj).trans ih
  obtain ⟨w⟩ := (latticeGraph_connected hn).preconnected p q
  exact key w

/-! ## 2. The flip does not move the contour -/

theorem contour_flip {n : ℕ} (σ : Config n) :
    contour (IsingFiniteVolume.flip σ) = contour σ := by
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    rw [mem_contour, mem_contour]
    cases hsp : σ p <;> cases hsq : σ q <;> simp_all [IsingFiniteVolume.flip]

/-! ## 3. The contour determines the configuration up to the flip -/

/-- **THE CONTOUR IS A COMPLETE INVARIANT, UP TO THE GLOBAL FLIP.** Two
    configurations break exactly the same bonds precisely when they are
    equal or exactly opposite.

    Both hypotheses earn their place: the box must be connected (`hn`), or
    the two pieces could be flipped independently and the fibre would be
    larger. -/
theorem contour_eq_iff {n : ℕ} (hn : 0 < n) (σ τ : Config n) :
    contour τ = contour σ ↔ (τ = σ ∨ τ = IsingFiniteVolume.flip σ) := by
  constructor
  · intro h
    have hbond : ∀ p q : Site n, adj p q → (σ p == τ p) = (σ q == τ q) := by
      intro p q hpq
      have hmem : s(p, q) ∈ contour τ ↔ s(p, q) ∈ contour σ := by rw [h]
      rw [mem_contour, mem_contour] at hmem
      have hiff : (τ p ≠ τ q) ↔ (σ p ≠ σ q) :=
        ⟨fun hne => (hmem.mp ⟨hpq, hne⟩).2, fun hne => (hmem.mpr ⟨hpq, hne⟩).2⟩
      cases hsp : σ p <;> cases hsq : σ q <;> cases htp : τ p <;> cases htq : τ q <;>
        simp_all
    have hconst := const_of_adj_const hn (fun p => (σ p == τ p)) hbond
    rcases h0 : (σ (⟨0, hn⟩, ⟨0, hn⟩) == τ (⟨0, hn⟩, ⟨0, hn⟩)) with _ | _
    · right
      funext p
      have hp : (σ p == τ p) = false := (hconst p _).trans h0
      cases hsp : σ p <;> cases htp : τ p <;> simp_all [IsingFiniteVolume.flip]
    · left
      funext p
      have hp : (σ p == τ p) = true := (hconst p _).trans h0
      exact (beq_iff_eq.mp hp).symm
  · rintro (rfl | rfl)
    · rfl
    · exact contour_flip σ

/-! ## 4. The reindexing -/

/-- The contours that actually occur. Nothing is proved here about how many
    there are — that is the entropy half, and it is not in this file. -/
def realisedContours (n : ℕ) : Finset (Finset (Sym2 (Site n))) :=
  Finset.image contour (Finset.univ : Finset (Config n))

/-- **Every realised contour comes from exactly two configurations** — a
    configuration and its flip. `IsingFiniteVolume.flip_ne` is what makes
    this `2` and not `1`. -/
theorem card_fiber {n : ℕ} (hn : 0 < n) (σ : Config n) :
    (Finset.univ.filter (fun τ : Config n => contour τ = contour σ)).card = 2 := by
  classical
  have hset : Finset.univ.filter (fun τ : Config n => contour τ = contour σ)
      = {σ, IsingFiniteVolume.flip σ} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact contour_eq_iff hn σ τ
  rw [hset, Finset.card_insert_of_notMem (by simpa using (flip_ne n hn σ).symm),
    Finset.card_singleton]

/-- **THE PEIERLS REINDEXING.** Summing any quantity over all `2^(n²)`
    configurations is exactly twice summing it over the contours that occur.
    This is a Peierls argument's first move, and it is the whole payoff of
    §3.

    It BOUNDS nothing: `realisedContours` is just the image, and how big it
    is — the `3^{|γ|}` question — is untouched. -/
theorem sum_over_contours {n : ℕ} (hn : 0 < n) {M : Type*} [AddCommMonoid M]
    (f : Finset (Sym2 (Site n)) → M) :
    ∑ σ : Config n, f (contour σ) = 2 • ∑ γ ∈ realisedContours n, f γ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (t := realisedContours n) (g := contour)
    (fun σ _ => Finset.mem_image_of_mem contour (Finset.mem_univ σ)) f,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  simp only [realisedContours] at hγ
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hγ
  rw [Finset.sum_const, card_fiber hn σ]

/-- The same statement for the Boltzmann weights: the partition function is
    twice a sum over realised contours of the Peierls factor. This is the
    form a Peierls estimate consumes. -/
theorem gibbs_sum_over_contours {n : ℕ} (hn : 0 < n) (β : ℝ) :
    ∑ σ : Config n, Real.exp (-β * isingH n σ)
      = 2 • ∑ γ ∈ realisedContours n,
          Real.exp (-(4 * β) * (γ.card : ℝ)) * Real.exp (-β * isingH n (fun _ => true)) := by
  rw [← sum_over_contours hn
    (fun γ => Real.exp (-(4 * β) * (γ.card : ℝ))
      * Real.exp (-β * isingH n (fun _ => true)))]
  exact Finset.sum_congr rfl fun σ _ => IsingContourGibbs.peierls_weight n β σ

/-! ## 5. Review round 67 — the ways this could be hollow

**"`contour_eq_iff` could be false at the edges."** The two hypotheses are
exactly the two ways it could fail and both are present. Connectivity
(`hn`): on a disconnected box each component could be flipped
independently, the fibre would be `2^(components)` and §4 would be wrong.
Non-degeneracy: the fibre is `{σ, flip σ}` and has TWO elements only because
`IsingFiniteVolume.flip_ne` says the flip moves every configuration, which
itself needs `n ≥ 1`. Take either away and `card_fiber` is false, not merely
unproved.

**"§1 could be a copy of what `IsingContourSeparation` already had."** It is
the same argument with a hypothesis removed, and the header says so rather
than presenting it as new. What is worth recording is the direction of the
mistake: the special case was written first, one unit ago, by an author who
already had the general proof in hand and did not notice. That is the
cheapest kind of missed generalisation and it is invisible unless a later
unit happens to need the general form.

**"The reindexing could be vacuous — maybe `realisedContours` is
everything."** It is not, and the file does not need it to be: `2 •` is the
content, and `card_config = 2^(n²)` against a fibre of size `2` means the
image has exactly `2^(n²−1)` elements. But note what is NOT claimed —
nothing here says which `Finset`s of bonds are realised, and that
characterisation (a bond set is realised iff every cycle of the lattice
crosses it evenly) is the dual-lattice statement this file does not prove.

**"This could be presented as the entropy half."** It is not the entropy
half; it is the reindexing that lets one begin. Peierls needs a BOUND on how
many realised contours of length `L` surround a given site, which is the
`3^{|γ|}` count, and that is geometry: circuits, planar duality, surgery.
None of it is here, and `MagnetisationBound` is exactly as unproved as it
was three units ago.
-/

end IsingContourInvariant
