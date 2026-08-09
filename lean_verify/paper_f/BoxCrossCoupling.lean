/-
  BoxCrossCoupling.lean — R3: what the coupling across the cut actually is.

  WHY. `WALLS.md` W1 records the ladder as R1a done, R1b mostly done, R2
  done, **R3 open and now the whole mathematics**, R4 open. R3 is the sign of
  the cross-coupling `B`, and the same document has been calling it "free for
  even `n`" on the grounds that `B` *should* be a diagonal indicator there.
  **"Should be" is not a theorem**, and the previous unit's own log entry says
  so. This computes it.

  WHAT THIS FILE PROVES, for the `d`-dimensional box of EVEN side, the
  reflection `revSite i`, and the half `lowerHalf i n`:
  1. **`adj_revSite_iff`** — a site of the lower half is adjacent to the
     mirror of a lower-half site **exactly when the two are the same site and
     it lies on the innermost layer**, `2·pᵢ + 2 = n`. Everything else about
     the geometry follows from this one characterisation, and it is where the
     `Fin` arithmetic lives.
  2. **`crossOp_eq`** — hence, on the half,
     `B p q = if p = q ∧ 2·pᵢ + 2 = n then −1 else 0`. **The cross-coupling
     is minus a diagonal indicator of the innermost layer**, exactly as the
     wall document guessed, and the mass term contributes nothing because a
     site of the half is never its own mirror.
  3. **`crossOp_nonpos`** — **R3.** For every coefficient vector supported on
     the half, `∑ v p · v q · B p q ≤ 0`, since the sum collapses to
     `−∑ (v p)²` over the innermost layer. **`exists_innermost`** shows that
     layer is inhabited on every even box of side at least two, so the
     inequality is not vacuous.

  A SIGN, PINNED. `UNLOCK_WATCHLIST`'s ladder states R3 as "`B` is PSD",
  writing the operator as `[[A, −B], [−B, A]]`. The estate's `crossOp` is the
  MATRIX ENTRY, so `crossOp = −B_ladder` and the fact needed here is
  `crossOp ≼ 0`. Both conventions are consistent and the two are negatives of
  each other; **the reason to say so is that R4 is an inequality and a
  convention mismatch there would flip it.**

  WHAT THIS DOES NOT DO. **This is not reflection positivity and R4 is not
  here.** R4 needs `A ± B` inverted AS OPERATORS ON THE HALF — the residue of
  R1b, which needs the subtype `↥H` — and then R2 applied to
  `A + B ≼ A − B`. **Neither step is in this file**, and nothing here
  mentions an inverse, `MatrixLoewner`, or `ReflectionPositive`. R3 is one
  rung.

  Nor does it say anything about odd `n`: `GraphHalfSpace.not_isHalf_of_odd`
  says there is no half to speak of there, so the question does not arise in
  this form.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphHalfSpace

namespace BoxCrossCoupling

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph

variable {d n : ℕ} {m : ℝ}

/-! ## 1. Who is adjacent to whom across the cut

The one place with arithmetic. A lower-half site and the mirror of a
lower-half site can only differ in the reflected coordinate — everywhere else
the mirror changes nothing, and the two halves are separated in coordinate
`i`. Once the differing coordinate is `i`, being one step apart forces both
sites onto the innermost layer.
-/

private theorem mem_lowerHalf_iff (i : Fin d) (p : Site d n) :
    p ∈ lowerHalf i n ↔ 2 * (p i).val < n := by
  simp [lowerHalf]

/-- The mirror of a lower-half site is never in the lower half — which is
    `IsHalf` specialised, recorded here in the arithmetic form the proofs
    below use. -/
private theorem rev_notMem (i : Fin d) (hn : Even n) {q : Site d n}
    (hq : 2 * (q i).val < n) :
    n ≤ 2 * ((revSite (n := n) i q) i).val := by
  obtain ⟨t, ht⟩ := hn
  rw [revSite_apply_self]
  have hrev : (Fin.rev (q i)).val = n - ((q i).val + 1) := Fin.val_rev (q i)
  have hlt : (q i).val < n := (q i).isLt
  omega

/-- **THE CROSS-CUT ADJACENCY, EXACTLY.** -/
theorem adj_revSite_iff (i : Fin d) (hn : Even n) {p q : Site d n}
    (hp : p ∈ lowerHalf i n) (hq : q ∈ lowerHalf i n) :
    BoxGraph.adj p (revSite (n := n) i q) ↔ (p = q ∧ 2 * (p i).val + 2 = n) := by
  rw [mem_lowerHalf_iff] at hp hq
  obtain ⟨t, ht⟩ := hn
  constructor
  · rintro ⟨k, h1, h2⟩
    -- the differing coordinate must be `i`
    have hki : k = i := by
      by_contra hk
      have hcoord : p i = (revSite (n := n) i q) i := h1 i (Ne.symm hk)
      have hup := rev_notMem i ⟨t, ht⟩ hq
      rw [← hcoord] at hup
      omega
    subst hki
    -- at `i`, one step apart, both halves below the midline
    rw [revSite_apply_self] at h2
    have hrev : (Fin.rev (q k)).val = n - ((q k).val + 1) := Fin.val_rev (q k)
    have hlt : (q k).val < n := (q k).isLt
    have hplt : (p k).val < n := (p k).isLt
    have hpk : (p k).val = (q k).val := by omega
    refine ⟨?_, by omega⟩
    funext j
    by_cases hj : j = k
    · subst hj; exact Fin.ext hpk
    · have := h1 j hj
      rwa [revSite_apply_ne hj] at this
  · rintro ⟨rfl, hlayer⟩
    refine ⟨i, fun j hj => ?_, Or.inl ?_⟩
    · rw [revSite_apply_ne hj]
    · rw [revSite_apply_self]
      have hrev : (Fin.rev (p i)).val = n - ((p i).val + 1) := Fin.val_rev (p i)
      have hlt : (p i).val < n := (p i).isLt
      omega

/-! ## 2. The cross-coupling is minus a diagonal indicator -/

/-- On the half, the mass term of `massive` never contributes to `B`,
    because a site of the half is never its own mirror. -/
private theorem ne_rev (i : Fin d) (hn : Even n) {p q : Site d n}
    (hp : p ∈ lowerHalf i n) (hq : q ∈ lowerHalf i n) :
    p ≠ revSite (n := n) i q := by
  rw [mem_lowerHalf_iff] at hp
  intro hc
  have hup := rev_notMem i hn ((mem_lowerHalf_iff i q).mp hq)
  rw [← hc] at hup
  omega

/-- **R3's OBJECT.** On the half the coupling across the cut is `−1` on the
    innermost layer's diagonal and `0` everywhere else. -/
theorem crossOp_eq (i : Fin d) (hn : Even n) {p q : Site d n}
    (hp : p ∈ lowerHalf i n) (hq : q ∈ lowerHalf i n) :
    crossOp (boxGraph d n) m (revSite (n := n) i) p q
      = if p = q ∧ 2 * (p i).val + 2 = n then -1 else 0 := by
  classical
  have hne : p ≠ revSite (n := n) i q := ne_rev i hn hp hq
  simp only [crossOp, Matrix.of_apply, GraphLaplacian.massive, Matrix.add_apply,
    Matrix.diagonal_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix,
    Matrix.of_apply, if_neg hne]
  by_cases hcase : p = q ∧ 2 * (p i).val + 2 = n
  · rw [if_pos hcase]
    have hadj : BoxGraph.adj p (revSite (n := n) i q) :=
      (adj_revSite_iff i hn hp hq).mpr hcase
    simp [hadj]
  · rw [if_neg hcase]
    have hadj : ¬ BoxGraph.adj p (revSite (n := n) i q) := fun hc =>
      hcase ((adj_revSite_iff i hn hp hq).mp hc)
    simp [hadj]

/-! ## 3. R3 -/

/-- **R3: THE COUPLING ACROSS THE CUT IS NEGATIVE SEMIDEFINITE ON THE HALF.**
    The double sum collapses to minus a sum of squares over the innermost
    layer.

    Read against `UNLOCK_WATCHLIST`'s ladder, which writes the operator as
    `[[A, −B], [−B, A]]` and asks for `B` PSD: `crossOp` is the matrix entry,
    so `crossOp = −B_ladder` and this is that statement. -/
theorem crossOp_nonpos (i : Fin d) (hn : Even n) {v : Site d n → ℝ}
    (hv : ∀ p, p ∉ lowerHalf i n → v p = 0) :
    ∑ p, ∑ q, v p * v q * crossOp (boxGraph d n) m (revSite (n := n) i) p q ≤ 0 := by
  classical
  have hstep : ∀ p q : Site d n,
      v p * v q * crossOp (boxGraph d n) m (revSite (n := n) i) p q
        = if p = q ∧ 2 * (p i).val + 2 = n then -(v p * v p) else 0 := by
    intro p q
    by_cases hp : p ∈ lowerHalf i n
    · by_cases hq : q ∈ lowerHalf i n
      · rw [crossOp_eq i hn hp hq]
        by_cases hcase : p = q ∧ 2 * (p i).val + 2 = n
        · rw [if_pos hcase, if_pos hcase, hcase.1]; ring
        · rw [if_neg hcase, if_neg hcase]; ring
      · rw [hv q hq]
        have hcase : ¬ (p = q ∧ 2 * (p i).val + 2 = n) := by
          rintro ⟨rfl, -⟩; exact hq hp
        rw [if_neg hcase]; ring
    · rw [hv p hp]
      split_ifs <;> ring
  calc ∑ p, ∑ q, v p * v q * crossOp (boxGraph d n) m (revSite (n := n) i) p q
      = ∑ p, ∑ q, if p = q ∧ 2 * (p i).val + 2 = n then -(v p * v p) else 0 :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hstep p q
    _ ≤ 0 := by
        refine Finset.sum_nonpos fun p _ => Finset.sum_nonpos fun q _ => ?_
        split_ifs
        · nlinarith [sq_nonneg (v p)]
        · exact le_rfl

/-- **The innermost layer is inhabited on every even box of side ≥ 2**, so
    §3's inequality is not vacuously about an empty sum. Proved rather than
    remarked, because §4 asserts it. -/
theorem exists_innermost (i : Fin d) {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) :
    ∃ p : Site d n, p ∈ lowerHalf i n ∧ 2 * (p i).val + 2 = n := by
  obtain ⟨t, ht⟩ := hn
  refine ⟨fun _ => ⟨t - 1, by omega⟩, ?_, ?_⟩
  · rw [mem_lowerHalf_iff]
    show 2 * (t - 1) < n
    omega
  · show 2 * (t - 1) + 2 = n
    omega

/-! ## 4. Review round 82 — the ways this could be hollow

**"The wall document already said `B` was a diagonal indicator."** It said it
*should* be, as a parenthetical justifying the phrase "free for even `n`",
and the previous unit's log entry flagged that as exactly the kind of
sentence this project keeps correcting. **The guess was right**, which is
worth recording — a prediction confirmed is a result, and had it been wrong
the ladder would have needed rebuilding rather than climbing. What was NOT
in the guess is the reason the mass term drops out: a site of the half is
never its own mirror (`ne_rev`), which is where `IsHalf`'s content is spent.

**"§1 could be doing less than it looks."** It is the whole geometry, and
both directions are used: `mpr` in `crossOp_eq`'s positive case, `mp` in its
negative case. The forward direction is where the arithmetic is — a
lower-half site and an upper-half site cannot agree in the reflected
coordinate, which forces the differing coordinate to be `i`, and then being
one step apart with both coordinates below the midline forces both onto the
innermost layer and forces the sites equal. **Nothing here is `decide` or a
special case of `n`.**

**"`crossOp_nonpos` could be vacuous."** It is not, and the draft of this
paragraph ASSERTED that rather than proving it. `exists_innermost` is the
theorem: on every even box of side at least two the innermost layer is
inhabited, so the collapsed sum has real terms and the inequality is not
`0 ≤ 0` by default. It IS an inequality
rather than an equality on purpose — the sum is `−∑(v p)²` over that layer,
which is strictly negative for any `v` nonzero there, and stating it as `≤ 0`
is what R4 will consume.

**"So is the wall about to fall?"** No, and the header says which two steps
are missing. R4 needs `A ± B` inverted **as operators on the half**, which is
R1b's recorded residue and needs the subtype `↥H`; only then does R2 apply,
to `A + B ≼ A − B`. **Nothing in this file mentions an inverse,
`MatrixLoewner`, or `ReflectionPositive`**, and no theorem here is about a
half rather than about a matrix entry. Three rungs of four are done or nearly
so, and the fourth is assembly that has a named prerequisite.
-/

end BoxCrossCoupling
