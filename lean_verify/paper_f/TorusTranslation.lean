/-
  TorusTranslation.lean — discharging yesterday's promise: an automorphism that
  is not a reflection.

  WHY. `FieldAutInvariance` proved the Gaussian field invariant under every
  graph automorphism and dropped the involutivity hypothesis every earlier file
  on this wall carries. Its own header recorded the weakness plainly: **the
  estate constructs no non-involutive automorphism, so nothing exercises the
  weakening.** The watchlist item says the same and names the discharge — *a
  torus translation is the cheap one* — as its REVISIT WHEN. This is that
  trigger, fired by the file that set it.

  **A HYPOTHESIS WEAKENED WITH NO CASE TO SHOW FOR IT IS A PROMISE.** It was
  recorded as a promise in three registers rather than as a result, and the
  honest way to close it is to build the case, not to reword the claim.

  **WHY THE TORUS AND NOT THE BOX.** The box has free boundary: it has no
  wrap-around bonds, so a translation carrying a site past the end has no edge
  to land on. The torus has exactly those bonds, and translation along any
  coordinate is an automorphism of it. That asymmetry is the reason the estate
  had only reflections — reflections are the box's symmetries, and the box came
  first. **No claim is made here about which translations fail on the box**;
  the point is only that the torus is where the construction lives, and
  nothing below mentions `boxGraph`.

  **THE ONE PIECE OF MATHEMATICS.** `adjT`, the circle adjacency, is written
  with `.val` arithmetic and four explicit wrap-around cases, which is the right
  shape for deciding it and the wrong shape for proving anything invariant.
  §1 replaces it with **`adjT_iff_succ`**: `a` and `b` are adjacent on the
  circle exactly when they are distinct and one is the other's successor in
  `Fin n`. Once adjacency is stated with `+ 1` rather than with `.val + 1` and
  a wrap case, translation invariance is `add_right_cancel` and nothing else.
  **The wrap-around cases in the original definition ARE the successor map; the
  case split was hiding the group structure.**

  WHAT THIS FILE PROVES:
  1. **`adjT_iff_succ`** — the circle adjacency as a statement about `Fin n`'s
     group structure. Four `.val` cases in, one disjunction out.
  2. **`shift`** — translation of one coordinate, as a `Site d n ≃ Site d n`.
  3. **`isGraphAut_shift`** — **it is an automorphism of the torus**, at every
     side length, every dimension and every shift. (`NeZero n` is required, as
     it must be: a shift amount is an element of `Fin n`, so at `n = 0` there
     is nothing to shift by.)
  4. **`shift_ne_involutive`** — **and it is NOT an involution**, exhibited at
     `d = 1`, `n = 3`, `k = 1`. This is the whole point of the file: without it
     the generality of `FieldAutInvariance` is untested, and with it there is a
     case that no theorem on this wall before yesterday could have covered.
     **That every earlier symmetry was an involution is structural, not
     incidental**: `GraphReflection.IsRefl` has `invol` as a FIELD, so no
     non-involutive map could be handed to any of this wall's machinery, and
     every instance in the estate discharges it with `revSite_involutive` or
     `refl_involutive`.
  5. **`gaussianField_map_shift`** — **the Gaussian field on the torus is
     translation invariant**, as an equality of measures.

  WHAT THIS DOES NOT DO.
  * **It is still not OS3.** Translations of a finite torus are a finite group,
    not the Euclidean group, and the caveat `FieldAutInvariance` carries is
    unchanged by having one more example inside it. **A second family of
    symmetries is not progress towards Euclidean invariance**, and saying it
    were would be the overclaim that file was careful to avoid.
  * **No coordinate permutations.** The box and torus are also symmetric under
    permuting the `d` axes, which is a third family and is not built here.
    Nothing needs it; it is named so the omission is a record.
  * **Nothing about the reflected form.** Translations do not fix a half, so
    they say nothing about reflection positivity, and no attempt is made to
    connect the two.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import FieldAutInvariance

namespace TorusTranslation

open Finset BoxGraph TorusReflection FieldAutInvariance

/-! ## 1. The circle adjacency is about the successor map

`adjT a b` is `a ≠ b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ (a.val = 0 ∧
b.val + 1 = n) ∨ (b.val = 0 ∧ a.val + 1 = n))`. The last two cases are the
wrap-around, and they are exactly what `Fin n`'s `+ 1` does at the top.
-/

variable {n : ℕ} [NeZero n]

/-- **THE CIRCLE ADJACENCY, WITHOUT THE CASE SPLIT.** Adjacent on the circle
    means distinct and one step apart, where "one step" is `Fin n` addition —
    so the wrap-around is not a special case, it is what addition does. -/
theorem adjT_iff_succ (a b : Fin n) :
    adjT a b ↔ a ≠ b ∧ (b = a + 1 ∨ a = b + 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsucc : ∀ x : Fin n, (x + 1).val = (x.val + 1) % n := by
    intro x
    simp [Fin.add_def]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with h | h | ⟨h0, hb⟩ | ⟨h0, ha⟩
    · left
      refine Fin.ext ?_
      rw [hsucc, Nat.mod_eq_of_lt (h ▸ b.isLt)]
      exact h.symm
    · right
      refine Fin.ext ?_
      rw [hsucc, Nat.mod_eq_of_lt (h ▸ a.isLt)]
      exact h.symm
    · right
      refine Fin.ext ?_
      rw [hsucc, hb, Nat.mod_self, h0]
    · left
      refine Fin.ext ?_
      rw [hsucc, ha, Nat.mod_self, h0]
  · rintro ⟨hne, h | h⟩
    · refine ⟨hne, ?_⟩
      have hb := congrArg Fin.val h
      rw [hsucc] at hb
      rcases Nat.lt_or_ge (a.val + 1) n with hlt | hge
      · left; rw [hb, Nat.mod_eq_of_lt hlt]
      · have : a.val + 1 = n := by omega
        right; right; right
        exact ⟨by rw [hb, this, Nat.mod_self], this⟩
    · refine ⟨hne, ?_⟩
      have ha := congrArg Fin.val h
      rw [hsucc] at ha
      rcases Nat.lt_or_ge (b.val + 1) n with hlt | hge
      · right; left; rw [ha, Nat.mod_eq_of_lt hlt]
      · have : b.val + 1 = n := by omega
        right; right; left
        exact ⟨by rw [ha, this, Nat.mod_self], this⟩

/-- Translation invariance of the circle adjacency. Immediate from §1: the
    condition is two equations in `Fin n` and adding `k` to both sides of each
    changes nothing. -/
theorem adjT_add_right (a b k : Fin n) : adjT (a + k) (b + k) ↔ adjT a b := by
  rw [adjT_iff_succ, adjT_iff_succ]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨fun hc => hne (by rw [hc]), ?_⟩
    rcases h with h | h
    · left
      have hb : b + k = a + 1 + k := by rw [h]; exact (add_right_comm a 1 k).symm
      exact add_right_cancel hb
    · right
      have ha : a + k = b + 1 + k := by rw [h]; exact (add_right_comm b 1 k).symm
      exact add_right_cancel ha
  · rintro ⟨hne, h⟩
    refine ⟨fun hc => hne (add_right_cancel hc), ?_⟩
    rcases h with h | h
    · left; rw [h]; exact add_right_comm a 1 k
    · right; rw [h]; exact add_right_comm b 1 k

/-! ## 2. Translation of one coordinate -/

variable {d : ℕ}

/-- Translate coordinate `i` by `k`, leaving the others alone. -/
def shift (i : Fin d) (k : Fin n) : Site d n ≃ Site d n where
  toFun p := fun j => if j = i then p j + k else p j
  invFun p := fun j => if j = i then p j - k else p j
  left_inv p := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  right_inv p := by
    funext j
    by_cases hj : j = i <;> simp [hj]

theorem shift_apply_self (i : Fin d) (k : Fin n) (p : Site d n) :
    shift i k p i = p i + k := if_pos rfl

theorem shift_apply_ne {i j : Fin d} (hj : j ≠ i) (k : Fin n) (p : Site d n) :
    shift i k p j = p j := if_neg hj

/-! ## 3. It is an automorphism, and it is not a reflection -/

/-- **TRANSLATION IS AN AUTOMORPHISM OF THE TORUS**, at every side length,
    every dimension and every shift. -/
theorem isGraphAut_shift (i : Fin d) (k : Fin n) :
    IsGraphAut (torusGraph d n) (shift i k) := by
  intro p q
  simp only [torusGraph_adj, torusAdj]
  constructor
  · rintro ⟨i', hsame, hstep⟩
    refine ⟨i', fun j hj => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        have := hsame j hj
        rw [shift_apply_self, shift_apply_self] at this
        exact add_right_cancel this
      · have := hsame j hj
        rwa [shift_apply_ne hji, shift_apply_ne hji] at this
    · by_cases hi' : i' = i
      · subst hi'
        rw [shift_apply_self, shift_apply_self] at hstep
        exact (adjT_add_right _ _ _).mp hstep
      · rwa [shift_apply_ne hi', shift_apply_ne hi'] at hstep
  · rintro ⟨i', hsame, hstep⟩
    refine ⟨i', fun j hj => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        rw [shift_apply_self, shift_apply_self, hsame j hj]
      · rw [shift_apply_ne hji, shift_apply_ne hji]
        exact hsame j hj
    · by_cases hi' : i' = i
      · subst hi'
        rw [shift_apply_self, shift_apply_self]
        exact (adjT_add_right _ _ _).mpr hstep
      · rw [shift_apply_ne hi', shift_apply_ne hi']
        exact hstep

/-- **AND IT IS NOT AN INVOLUTION.** At `d = 1`, `n = 3`, shifting by one and
    shifting again lands two steps along, not back. **This is the point of the
    file**: every automorphism the estate had before was its own inverse, so
    `FieldAutInvariance`'s dropped hypothesis had nothing to prove itself
    against. -/
theorem shift_ne_involutive :
    ¬ Function.Involutive (shift (n := 3) (d := 1) 0 1) := by
  intro h
  have := congrFun (h (fun _ => (0 : Fin 3))) 0
  rw [shift_apply_self, shift_apply_self] at this
  simp at this

/-! ## 4. The field is translation invariant -/

/-- **THE GAUSSIAN FIELD ON THE TORUS IS TRANSLATION INVARIANT**, as an
    equality of measures. `FieldAutInvariance.gaussianField_map_perm` at an
    automorphism that is not a reflection — the instantiation that file could
    not supply. -/
theorem gaussianField_map_shift (i : Fin d) (k : Fin n) {m : ℝ} (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (torusGraph d n) m).map (permField (shift i k))
      = GraphLaplacian.gaussianField (torusGraph d n) m :=
  gaussianField_map_perm (isGraphAut_shift i k) hm

/-! ## 5. Review — the ways this could be hollow

**"Is building an example a unit, or is it bookkeeping?"** It is the discharge
of a promise that was written down as a promise, in three registers, one day
earlier. And the promise was not idle: **`IsRefl` carries involutivity as a
structure FIELD**, so before `FieldAutInvariance` no non-involutive map could
even be supplied to this wall's machinery. The gap was structural, which is
why nothing had ever exercised it. `FieldAutInvariance` weakened a hypothesis
and said in its own header
that nothing in the estate exercised the weakening; a claim in that state is
not wrong, but it is untested, and an untested generalisation is the thing this
project has spent the week learning to distrust. **§3's non-involutivity is the
smallest object that turns it from untested into tested**, and it is two lines.

**"Is `adjT_iff_succ` needed, or is it decoration?"** Needed. Translation
invariance stated against the original definition means pushing `+ k` through
four `.val` cases with a modulus, and `omega` does not see modular arithmetic.
Restating adjacency as "one is the other's successor in `Fin n`" makes the
proof `add_right_cancel`. **The wrap-around cases in `adjT` are the successor
map written out**, and the case split was hiding the group structure that makes
the theorem true.

**"Does the torus really have this symmetry at every side?"** Yes, and the
proof takes no hypothesis on `n` beyond `NeZero`. At `n = 1` and `n = 2` the
graph is degenerate — no edges, and a single edge, respectively — and
translation is still an automorphism of it, vacuously at one and by swapping at
two. Nothing is excluded and nothing needed to be.

**"Does this bring OS3 any closer?"** No, and the header says so. The
translations of a finite torus form a finite group; OS3 is about a continuous
one. **Two families of symmetries instead of one is not a step towards the
Euclidean group**, and the honest description of this file is that it makes
yesterday's theorem non-vacuous, not that it advances an axiom.

**"What is still missing from the symmetry picture?"** The permutations of the
`d` coordinate axes, which are automorphisms of both the box and the torus and
are built nowhere. Nothing in the estate consumes them, so they are recorded as
absent rather than added for completeness.
-/

end TorusTranslation
