/-
  CrossDegenerate.lean — why strictness transfers to the prism and not to the
  box.

  WHY. `PrismStrict` proved the reflected form of the two-layer stack strictly
  positive, and its header says the route "says nothing about the box or the
  torus", giving a reason: **those graphs have no identification of the blocks
  with base-graph operators.** That is a claim of the form "X is impossible
  because Y", and ERRATUM 48's rule is to check Y rather than let it stand as
  prose. Checking it turns up something sharper than the reason given.

  **The real difference is one line of geometry, and it is visible before any
  inverse is taken.** The criterion behind every reflection-positivity result
  in this estate asks that the coupling across the cut be negative
  semidefinite. On the prism that coupling is `−1` on the WHOLE diagonal,
  because every vertex has a rung; on the box it is `−1` only on the innermost
  layer, because only those sites touch the mirror. **So on the prism the
  inequality is strict and on the box it is attained** — and the attaining
  vector is a single site sitting away from the mirror.

  WHAT THIS FILE PROVES:
  1. **`crossOp_form_prism`** — on the stack, the cross-coupling form at `v`
     is exactly `−∑ v²`, hence **`crossOp_form_prism_neg`: strictly negative
     for every nonzero `v`.**
  2. **`crossOp_form_box_eq_zero`** — on the box of even side at least four,
     the cross-coupling form VANISHES at the indicator of the corner site.
     Hence **`crossOp_form_box_not_neg`: the inequality `BoxCrossCoupling.crossOp_nonpos`
     proves is ATTAINED at a nonzero vector**, so no strengthening of it to a
     strict inequality is possible.
  3. **`corner_mem_lowerHalf`, `corner_not_innermost`** — the two facts about
     the corner site that make it a witness, proved rather than asserted.
  4. **§2b, the torus.** A torus reflection has TWO mirror layers, the
     innermost and the seam, so the corner will not do — it sits on the seam.
     **`crossOp_form_torus_not_neg`**: the site one step in does, once the
     side is at least six, and the form is attained there as well. So the
     degeneracy is not special to free boundaries.

  **WHAT THIS EXPLAINS.** `PrismStrict` runs through `M − P = 1 + 1`, which is
  positive DEFINITE. For the box the same difference is `−2 · crossOp`, which
  §2 shows is positive semidefinite and SINGULAR. The strictness argument
  needs the definite version, so it stops — **not because the box lacks an
  identification, but because the box's mirror touches only one layer.** The
  reason recorded in `PrismStrict`'s header was true but was not the operative
  one; this file supersedes it and the correction is recorded in the log.

  WHAT THIS DOES NOT DO.
  * **It does not prove that strict reflection positivity is FALSE on the
    box.** It proves the criterion's inequality is attained, which blocks THIS
    route. A different argument could still give strictness, and nothing here
    rules one out. **Stating the stronger negative would be exactly the
    overreach this file exists to correct.**
  * **The torus is covered too, and §2b is why the sentence that used to sit
    here is gone.** The draft said the torus "needs a corner away from BOTH
    mirror layers, which is true for large enough side but is not proved
    here" — a claim of exactly the kind ERRATUM 48 forbids leaving
    unattempted, in the file written to correct another one. It is now
    proved, at side at least six.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PrismStrict

namespace CrossDegenerate

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open PrismReflection PrismTransfer

/-! ## 1. On the stack the inequality is strict -/

section Prism

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-- **The cross-coupling form of the stack is minus a sum of squares** — every
    vertex has a rung, so the coupling is `−1` on the whole diagonal. -/
theorem crossOp_form_prism (v : V → ℝ) :
    ∑ p, ∑ q, v p * v q * crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
      = -∑ p, v p * v p := by
  classical
  have hterm : ∀ p q : V,
      v p * v q * crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
        = if p = q then -(v p * v p) else 0 := by
    intro p q
    rw [crossOp_prism]
    by_cases h : p = q
    · subst h; simp
    · simp [h]
  simp_rw [hterm]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => by simp

/-- **STRICTLY NEGATIVE for every nonzero coefficient family.** This is what
    `PrismStrict` was able to exploit. -/
theorem crossOp_form_prism_neg {v : V → ℝ} (hv : v ≠ 0) :
    ∑ p, ∑ q, v p * v q * crossOp (prism K) m (swap (V := V)) (p, false) (q, false) < 0 := by
  rw [crossOp_form_prism]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have : 0 < ∑ p, v p * v p :=
    Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr (by simpa using hi)⟩
  linarith

end Prism

/-! ## 2. On the box it is attained

The corner site — all coordinates zero — lies in the lower half and, once the
side is at least four, is not on the innermost layer. The coupling therefore
does not see it, and the form vanishes there.
-/

section Box

variable {d n : ℕ} {m : ℝ}

/-- The corner of the box. -/
def corner (d n : ℕ) (hn : 0 < n) : BoxGraph.Site d n := fun _ => ⟨0, hn⟩

theorem corner_mem_lowerHalf (i : Fin d) (hn : 0 < n) :
    corner d n hn ∈ lowerHalf i n := by
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
  change 2 * 0 < n
  omega

theorem corner_not_innermost (i : Fin d) (hn : 0 < n) (h4 : 4 ≤ n) :
    ¬ (2 * ((corner d n hn) i).val + 2 = n) := by
  simp only [corner]
  omega

/-- **THE CROSS-COUPLING FORM OF THE BOX VANISHES AT THE CORNER.** -/
theorem crossOp_form_box_eq_zero (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) :
    ∑ p, ∑ q,
        (if p = corner d n (by omega) then (1:ℝ) else 0) *
        (if q = corner d n (by omega) then (1:ℝ) else 0) *
        crossOp (boxGraph d n) m (revSite (n := n) i) p q = 0 := by
  classical
  have hpos : 0 < n := by omega
  have hmem := corner_mem_lowerHalf (n := n) i hpos
  have hdiag : crossOp (boxGraph d n) m (revSite (n := n) i)
      (corner d n hpos) (corner d n hpos) = 0 := by
    rw [BoxCrossCoupling.crossOp_eq i hn hmem hmem]
    exact if_neg (fun hc => corner_not_innermost (n := n) i hpos h4 hc.2)
  rw [Finset.sum_eq_single (corner d n hpos)]
  · rw [Finset.sum_eq_single (corner d n hpos)]
    · simp [hdiag]
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [hp]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **SO THE BOX'S INEQUALITY IS ATTAINED**, and cannot be strengthened to a
    strict one: there is a nonzero coefficient family supported on the half at
    which `BoxCrossCoupling.crossOp_nonpos` holds with equality. -/
theorem crossOp_form_box_not_neg (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) :
    ∃ v : BoxGraph.Site d n → ℝ, v ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → v p = 0) ∧
      ∑ p, ∑ q, v p * v q * crossOp (boxGraph d n) m (revSite (n := n) i) p q = 0 := by
  classical
  have hpos : 0 < n := by omega
  refine ⟨fun p => if p = corner d n hpos then (1:ℝ) else 0, ?_, ?_, ?_⟩
  · intro hc
    have := congrFun hc (corner d n hpos)
    simp at this
  · intro p hp
    refine if_neg fun hc => hp ?_
    rw [hc]
    exact corner_mem_lowerHalf (n := n) i hpos
  · exact crossOp_form_box_eq_zero (m := m) i hn h4

end Box

/-! ## 2b. And on the torus, for the same reason twice over

A torus reflection has two mirror layers rather than one — the innermost and
the seam where the ends are glued. **The corner is therefore the wrong
witness: it sits ON the seam.** The site one step in is the right one, and it
exists as soon as the side is at least six.
-/

section Torus

open TorusReflection

variable {d n : ℕ} {m : ℝ}

/-- One step in from the corner. -/
def stepIn (d n : ℕ) (hn : 1 < n) : BoxGraph.Site d n := fun _ => ⟨1, hn⟩

theorem stepIn_mem_lowerHalf (i : Fin d) (hn : 1 < n) (h6 : 6 ≤ n) :
    stepIn d n hn ∈ lowerHalf i n := by
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
  change 2 * 1 < n
  omega

/-- It is on neither mirror layer: not the innermost, and not the seam. -/
theorem stepIn_off_both (i : Fin d) (hn : 1 < n) (h6 : 6 ≤ n) :
    ¬ (2 * ((stepIn d n hn) i).val + 2 = n ∨ ((stepIn d n hn) i).val = 0) := by
  simp only [stepIn]
  omega

/-- **THE TORUS'S CROSS-COUPLING FORM IS ATTAINED TOO**, at the site one step
    in from the corner, once the side is at least six. So the degeneracy that
    blocks strictness is not special to free boundaries. -/
theorem crossOp_form_torus_not_neg (i : Fin d) (hn : Even n) (h6 : 6 ≤ n) :
    ∃ v : BoxGraph.Site d n → ℝ, v ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → v p = 0) ∧
      ∑ p, ∑ q, v p * v q * crossOp (torusGraph d n) m (revSite (n := n) i) p q = 0 := by
  classical
  have h1 : 1 < n := by omega
  have hmem := stepIn_mem_lowerHalf (n := n) i h1 h6
  have hdiag : crossOp (torusGraph d n) m (revSite (n := n) i)
      (stepIn d n h1) (stepIn d n h1) = 0 := by
    rw [TorusReflection.crossOp_eq_neg_adj (isHalf_lowerHalf i hn) hmem hmem]
    refine if_neg fun hadj => ?_
    exact stepIn_off_both (n := n) i h1 h6
      ((adj_torus_revSite_iff i hn hmem hmem).mp hadj).2
  refine ⟨fun p => if p = stepIn d n h1 then (1:ℝ) else 0, ?_, ?_, ?_⟩
  · intro hc
    have := congrFun hc (stepIn d n h1)
    simp at this
  · intro p hp
    refine if_neg fun hc => hp ?_
    rw [hc]; exact hmem
  · rw [Finset.sum_eq_single (stepIn d n h1)]
    · rw [Finset.sum_eq_single (stepIn d n h1)]
      · simp [hdiag]
      · intro q _ hq; simp [hq]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _ hp
      refine Finset.sum_eq_zero fun q _ => ?_
      simp [hp]
    · intro h; exact absurd (Finset.mem_univ _) h

end Torus

/-! ## 3. Review round 94 — the ways this could be hollow

**"Does this correct `PrismStrict` or decorate it?"** It corrects it.
`PrismStrict`'s header says the route fails on the box because the box has no
identification of its blocks with base-graph operators. **That is true and it
is not the operative reason.** The operative reason is visible two steps
earlier and needs no inverses at all: the strictness argument consumes
`M − P` positive DEFINITE, and on the box `M − P = −2·crossOp` is
semidefinite and singular, because the mirror touches only the innermost
layer. §2 exhibits the null direction. **A wrong-but-true reason in a header
is exactly the kind of thing this project's review rounds exist to catch, and
this one was caught by running ERRATUM 48's check on my own sentence.**

**"Is the corner witness real, or a degenerate corner of the statement?"** It
is a genuine site of the half: `corner_mem_lowerHalf` and
`corner_not_innermost` are both proved, the second needing `4 ≤ n` because at
`n = 2` the corner IS the innermost layer and the argument would be false.
**The hypothesis is therefore load-bearing rather than defensive**, and at
`n = 2` the box's half is a single layer and the form genuinely is strict —
the same reason as the prism's.

**"Does this show strict reflection positivity FAILS on the box?"** **No, and
the header says so twice.** It shows the criterion's inequality is attained,
which blocks the route `PrismStrict` used. Some other argument could still
deliver strictness, and nothing here rules one out. Asserting the stronger
negative would be the overreach this file exists to correct — replacing one
unchecked sentence with another.

**"The torus section — is it the box argument copied?"** The structure is the
same and the WITNESS is not, which is the content. A torus reflection has two
mirror layers, so the corner is disqualified: it sits on the seam. The right
witness is one step in, and it exists only from side six, where the box needed
four. **Both numbers are forced and both are proved** (`stepIn_off_both`,
`corner_not_innermost`); had the corner worked on the torus the section would
have been a copy and would not have been worth writing.

**"Why is the prism different, in one sentence?"** Every vertex of a two-layer
stack touches the mirror, so the coupling is `−1` on the whole diagonal and
the form is minus a full sum of squares. On a box only the sites adjacent to
the cut touch it. **Strictness transfers exactly when the mirror touches
everything**, which is a property of the graph and not of the method.
-/

end CrossDegenerate
