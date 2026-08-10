/-
  ReachIsCoupling.lean — the converse's two hypotheses are one hypothesis.

  WHY. `ReachCriterion` proves that a nonpositive coupling plus a reach that
  stays inside the region forces a null direction, and its header presents
  those as two independent conditions — "**the converse, with its two
  hypotheses named**". It then draws a contrast from that separation:
  "*strictness is a fact about the geometry of the reach, not about the size
  of the coupling*". **Both readings are wrong in the same way.**

  **`ReachInside` IS a statement about the coupling, and the strongest one
  available: the coupling vanishes identically.** The proof is three lines and
  needs nothing that was not already in the file. Feed the reach condition the
  indicator of a single site and it says a matrix entry is zero. The entries it
  kills are exactly the entries the coupling form is built from, because for
  `q` in the half the mirror image `θ q` is neither in the half nor on the
  mirror — the one place the three-way splitting is doing real work. So the
  reach hypothesis implies the coupling hypothesis, and implies far more than
  nonpositivity: it implies equality with zero.

  **AND THE CONVERSE HOLDS TOO**, which is what makes this an identification
  rather than a redundancy. A coupling form that vanishes identically has a
  vanishing matrix, by polarisation — the form is symmetric, which needs the
  reflection-invariance of the operator and is not free — and every site
  outside the half and off the mirror is the image of a site in the half, so
  the killed entries are exactly the reach condition's. Hence

      **`ReachInside G m H Mir  ↔  ∀ w, crossForm G m θ H w = 0`.**

  **WHAT THAT DOES TO THE FOUR THEOREMS.** THREE of `ReachCriterion`'s four
  signatures carry `hcross` — counted, not recalled — and none of them needs
  it; the fourth, `exists_null_direction_box_odd'`, supplies it internally and
  need not. §4 restates the two substantive ones without it. Nothing gets weaker and one hypothesis disappears from each.
  More usefully, the contrapositive becomes a sentence about the object the
  wall is actually about: **strictness forces the coupling to be nonzero.**
  Not "the reach escapes" — that was the same fact wearing a geometric
  disguise, and the disguise made the criterion look like new information when
  it was a restatement.

  **HOW MUCH THIS COSTS THE CONVERSE.** It is honest to say: quite a lot, and
  the file says it here rather than in a footnote. `ReachCriterion` reads as
  though it covers a range of graphs with small couplings. It covers the
  graphs with NO coupling — where **no edge joins the half to its mirror
  image**, so the mirror layer separates them completely. That is a real class:
  every odd box is in it (`crossForm_odd_eq_zero`), and so is the estate's own
  `def` at odd side, which is the two-dimensional box transported.

  **THE TORUS IS NOT IN IT, AT ANY SIDE LENGTH**, and §3 explains a fact the
  estate had recorded without a reason. `TorusAnySide.torus_cross_diag_any`
  says the torus coupling is DIAGONAL, not zero — the wrap-around edge joins
  the bottom layer to its own mirror however long the side is. So
  `ReachCriterion` never applied to the torus, and `OddNotStrictInstances` had
  to build a separate construction on a smaller half. **That was not an
  oversight in either file; it is forced, and §3 is why.**

  WHAT THIS FILE PROVES:
  1. **`massive_eq_zero_of_reach`** — the reach condition, read as a statement
     about matrix entries rather than about vectors. The indicator trick, once.
  2. **`crossForm_symm_matrix`** — the coupling's matrix is symmetric:
     `massive p (θ q) = massive q (θ p)`. Needs both the reflection-invariance
     of the operator and its own symmetry, and it is the step polarisation
     cannot do without.
  3. **`crossForm_eq_zero_of_reach`** — reach implies the coupling vanishes,
     for EVERY `w`, with no hypothesis on the coupling.
     `ReachCriterion.crossForm_eq_zero_of_reach` is the same conclusion for one
     `w` from two hypotheses; this replaces it.
  4. **`reach_of_crossForm_eq_zero`** — and back, by polarisation.
  5. **`reachInside_iff_crossForm_eq_zero`** — **the identification.**
  6. **`not_strict_of_reach`**, **`reach_escapes_of_strict`** — the two
     substantive theorems of `ReachCriterion` with `hcross` deleted.
  7. **`crossForm_ne_zero_of_strict`** — the contrapositive said about the
     coupling: **if the reflected form is strict then the coupling is not
     identically zero.** The sentence the wall should carry.

  WHAT THIS DOES NOT DO.
  * **It does not touch `MirrorStrict`'s sufficient direction.** That needs the
    coupling negative definite on the strict half, which is a condition on a
    nonzero coupling and is untouched by an identification about the zero one.
  * **It does not make the criterion a biconditional.** Strict implies nonzero
    coupling; nonzero coupling does not imply strict, and box side four is the
    counterexample `ReachCriterion` already recorded. The gap is exactly where
    it was. **AMENDED 2026-08-10, SAME DAY (ERRATUM 76): A BICONDITIONAL DOES EXIST**, and this sentence generalised from the failure of one candidate to the non-existence of any. `StrictBiconditional.strict_iff_not_supportedIsotropic`: the form is strict exactly when no nonzero vector on the half is both killed by the coupling and kept inside the region by the massive operator. It comes from negating `NullSpace.reflectedForm_eq_zero_iff_massive`, which was proved the same day facing the other way. **What stays true is the narrower claim** — touching and reach are two different conditions and neither is the negation of the other, so THAT pair is not an equivalence.
  * **It does not widen the class.** Removing a hypothesis that was implied
    removes no restriction — the theorems always applied exactly here. What
    changes is what the statements say, not what they cover, and pretending
    otherwise would be the overclaim this campaign keeps catching.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import NullSpace

namespace ReachIsCoupling

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection ReachCriterion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The reach condition is about matrix entries

`ReachInside` quantifies over vectors. Every such condition is really a
condition on entries, and the indicator of a single site extracts them.
-/

/-- The reach condition, read off one entry at a time. -/
theorem massive_eq_zero_of_reach (hreach : ReachInside G m H Mir)
    {q : V} (hq : q ∈ H) {p : V} (hpH : p ∉ H) (hpM : p ∉ Mir) :
    GraphLaplacian.massive G m p q = 0 := by
  classical
  have hv : ∀ r, r ∉ H → (if r = q then (1 : ℝ) else 0) = 0 := by
    intro r hr
    exact if_neg fun hc => hr (by rw [hc]; exact hq)
  have := hreach (fun r => if r = q then (1 : ℝ) else 0) hv p hpH hpM
  simpa [Matrix.mulVec, dotProduct] using this

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **THE MIRROR IMAGE OF A SITE OF THE HALF IS OUTSIDE BOTH.** It is not in
    the half (that is the splitting) and not on the mirror (a fixed point of an
    involution whose image is fixed is itself fixed). The second half is where
    `Mir` earns its definition as *precisely* the fixed set. -/
theorem image_notMem_both (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    {q : V} (hq : q ∈ H) : θ q ∉ H ∧ θ q ∉ Mir := by
  refine ⟨hM.notMem_of_mem hq, fun hc => hM.disj q hq ?_⟩
  have hfix : θ (θ q) = θ q := (hM.fixed (θ q)).mp hc
  rw [h.invol q] at hfix
  exact (hM.fixed q).mpr hfix.symm

/-! ## 2. The coupling's matrix is symmetric

Polarisation needs this and it is not free: it consumes the reflection
invariance of the operator as well as the operator's own symmetry.
-/

/-- The coupling's matrix is symmetric. -/
theorem crossForm_symm_matrix (h : IsRefl G θ) (m : ℝ) (p q : V) :
    GraphLaplacian.massive G m p (θ q) = GraphLaplacian.massive G m q (θ p) := by
  have hinv : ∀ x y, GraphLaplacian.massive G m (θ x) (θ y)
      = GraphLaplacian.massive G m x y :=
    fun x y => congrFun (congrFun (h.massive m) x) y
  have hsym : ∀ x y, GraphLaplacian.massive G m x y = GraphLaplacian.massive G m y x :=
    fun x y => congrFun (congrFun (GraphLaplacian.massive_isSymm (G := G) m).eq y) x
  calc GraphLaplacian.massive G m p (θ q)
      = GraphLaplacian.massive G m (θ p) (θ (θ q)) := (hinv p (θ q)).symm
    _ = GraphLaplacian.massive G m (θ p) q := by rw [h.invol q]
    _ = GraphLaplacian.massive G m q (θ p) := hsym _ _

/-! ## 3. The identification -/

/-- **REACH INSIDE IMPLIES THE COUPLING VANISHES**, for every `w`, with no
    hypothesis on the coupling. `ReachCriterion.crossForm_eq_zero_of_reach`
    derives the same conclusion for a single `w` from `hcross` and `hreach`
    together; this needs only `hreach` and gives it for all of them. -/
theorem crossForm_eq_zero_of_reach (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hreach : ReachInside G m H Mir) (w : V → ℝ) :
    crossForm G m θ H w = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨hqH, hqM⟩ := image_notMem_both hM h hq
  have hzero : GraphLaplacian.massive G m (θ q) p = 0 :=
    massive_eq_zero_of_reach hreach hp hqH hqM
  have hsym : GraphLaplacian.massive G m p (θ q)
      = GraphLaplacian.massive G m (θ q) p :=
    congrFun (congrFun (GraphLaplacian.massive_isSymm (G := G) m).eq (θ q)) p
  rw [hsym, hzero, mul_zero]

/-- **AND BACK.** A coupling form vanishing identically has a vanishing matrix
    (polarisation, using §2), and every site outside the half and off the
    mirror is the image of a site of the half, so the entries killed are
    exactly the reach condition's. -/
theorem reach_of_crossForm_eq_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w = 0) :
    ReachInside G m H Mir := by
  classical
  -- the diagonal, from a single indicator
  have hdiag : ∀ r ∈ H, GraphLaplacian.massive G m r (θ r) = 0 := by
    intro r hr
    have := hcross (fun x => if x = r then (1 : ℝ) else 0)
    rw [crossForm, Finset.sum_eq_single_of_mem r hr] at this
    · rw [Finset.sum_eq_single_of_mem r hr] at this
      · simpa using this
      · intro b _ hbr; simp [hbr]
    · intro b hb hbr
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [hbr]
  -- the off-diagonal, from the indicator of a pair
  have hoff : ∀ r ∈ H, ∀ t ∈ H, GraphLaplacian.massive G m r (θ t) = 0 := by
    intro r hr t ht
    by_cases hrt : r = t
    · subst hrt; exact hdiag r hr
    have hpair := hcross (fun x => if x = r ∨ x = t then (1 : ℝ) else 0)
    have hexp : crossForm G m θ H (fun x => if x = r ∨ x = t then (1 : ℝ) else 0)
        = GraphLaplacian.massive G m r (θ r) + GraphLaplacian.massive G m r (θ t)
          + (GraphLaplacian.massive G m t (θ r) + GraphLaplacian.massive G m t (θ t)) := by
      rw [crossForm]
      rw [Finset.sum_eq_add_of_mem r t hr ht hrt ?_]
      · congr 1
        · rw [Finset.sum_eq_add_of_mem r t hr ht hrt ?_]
          · simp [hrt, Ne.symm hrt]
          · intro b _ hb
            simp [hb.1, hb.2]
        · rw [Finset.sum_eq_add_of_mem r t hr ht hrt ?_]
          · simp [hrt, Ne.symm hrt]
          · intro b _ hb
            simp [hb.1, hb.2]
      · intro b hb hbne
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [hbne.1, hbne.2]
    rw [hexp, hdiag r hr, hdiag t ht, crossForm_symm_matrix h m t r] at hpair
    linarith
  -- and that is exactly the reach condition
  intro v hvsupp p hpH hpM
  have hp' : θ p ∈ H := hM.mem_of_notMem hpH hpM
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ H
  · have : GraphLaplacian.massive G m p q = 0 := by
      have h1 : GraphLaplacian.massive G m q (θ (θ p)) = 0 := hoff q hq (θ p) hp'
      rw [h.invol p] at h1
      have h2 : GraphLaplacian.massive G m p q = GraphLaplacian.massive G m q p :=
        congrFun (congrFun (GraphLaplacian.massive_isSymm (G := G) m).eq q) p
      rw [h2, h1]
    rw [this, zero_mul]
  · rw [hvsupp q hq, mul_zero]

/-- **THE IDENTIFICATION.** The reach condition and the vanishing of the
    coupling are the same hypothesis. -/
theorem reachInside_iff_crossForm_eq_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) :
    ReachInside G m H Mir ↔ ∀ w : V → ℝ, crossForm G m θ H w = 0 :=
  ⟨fun hr w => crossForm_eq_zero_of_reach hM h hr w, reach_of_crossForm_eq_zero hM h⟩

/-! ## 4. `ReachCriterion` without `hcross`

Nothing here is stronger than what that file proves. What changes is that the
hypothesis it named second is deleted, because §3 supplies it.
-/

/-- **THE CONVERSE, WITH ONE HYPOTHESIS.** `ReachCriterion.not_strict_of_reach`
    with `hcross` removed. -/
theorem not_strict_of_reach (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hreach : ReachInside G m H Mir) {p₀ : V} (hp₀ : p₀ ∈ H) :
    ∃ c : V → ℝ, c ≠ 0 ∧ (∀ p, p ∉ H → p ∉ Mir → c p = 0) ∧
      GraphReflection.reflectedForm G m θ c = 0 :=
  ReachCriterion.not_strict_of_reach hM h hm
    (fun w => le_of_eq (crossForm_eq_zero_of_reach hM h hreach w)) hreach hp₀

/-- **THE CONTRAPOSITIVE, WITH ONE HYPOTHESIS.** -/
theorem reach_escapes_of_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {p₀ : V} (hp₀ : p₀ ∈ H)
    (hstrict : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < GraphReflection.reflectedForm G m θ c) :
    ¬ ReachInside G m H Mir := by
  intro hreach
  obtain ⟨c, hc0, hcsupp, hcform⟩ := not_strict_of_reach hM h hm hreach hp₀
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-- **THE SENTENCE THE WALL SHOULD CARRY.** Strictness forces the coupling to
    be nonzero. `ReachCriterion` says this as "the operator must reach out of
    the region"; §3 says those are the same statement, and this is the one
    phrased in terms of the object the rest of the wall is about. -/
theorem crossForm_ne_zero_of_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {p₀ : V} (hp₀ : p₀ ∈ H)
    (hstrict : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < GraphReflection.reflectedForm G m θ c) :
    ¬ (∀ w : V → ℝ, crossForm G m θ H w = 0) := by
  intro hzero
  exact reach_escapes_of_strict hM h hm hp₀ hstrict
    ((reachInside_iff_crossForm_eq_zero hM h).mpr hzero)

/-! ## 5. Review — the ways this could be hollow

**"Is removing an implied hypothesis a result?"** On its own, barely — it is
bookkeeping, and the header says so. The result is the EQUIVALENCE, and what
it costs the reading of `ReachCriterion`. That file presents reach-inside as a
geometric condition standing apart from the coupling, and draws a moral from
the separation: *strictness is about the geometry of the reach, not the size
of the coupling*. §3 says the separation does not exist. The moral was drawn
from an artefact of phrasing.

**"Does anything the estate proved become false?"** No. Every theorem in
`ReachCriterion` is true as stated; a redundant hypothesis makes a theorem
weaker, never wrong, and the odd-box instantiation supplies both hypotheses
honestly. What changes is the prose, and `ReachCriterion`'s header is amended
in place rather than rewritten.

**"Is the converse direction (§3, second half) real work or padding?"**
Real, and it is where the only interesting step is. Polarisation needs the
coupling's matrix to be symmetric, and that is not automatic — it consumes
`IsRefl.massive`, the reflection-invariance of the operator, and then the
operator's own symmetry. Without §2 the pair-indicator computation gives
`massive r (θ t) + massive t (θ r) = 0`, which is not enough. **A file that
had only proved the forward direction would have found a redundancy; proving
both is what turns it into an identification.**

**"Does this narrow what the wall covers?"** It narrows what the wall's PROSE
suggested, not what its theorems cover — those covered exactly this all along.
The honest statement is in the header: `ReachCriterion` applies to graphs in
which no edge joins the half to its mirror image. Every odd box is such a
graph and the torus is not — checked against `torus_cross_diag_any` rather
than assumed, after a draft of this file claimed the odd torus qualified. **It
does not, and the reason is the wrap-around edge that made the torus need its
own construction in the first place.** So the class is one class, not a
spectrum of small couplings, and the estate's split between box and torus
turns out to be exactly the boundary of it.

**"Then is the converse still worth having?"** Yes, and for the reason §3
makes visible rather than despite it. `reflectionPositive_mirror` needs the
coupling only nonpositive; degeneracy needs it exactly zero. **The gap between
those two conditions is the whole of the strictness question**, and naming the
zero end precisely is what lets `MirrorStrict`'s negative-definite end be
recognised as the other extreme rather than as an unrelated criterion.
-/

end ReachIsCoupling
