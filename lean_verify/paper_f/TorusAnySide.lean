/-
  TorusAnySide.lean — the torus at every side length, and the answer to a
  question three entries have called untraced.

  WHY. Every unit since the odd box has ended by saying the torus is
  "untraced — it builds its own reflection and computes its own
  cross-coupling, and `torus_two_eq_box` may genuinely need the parity."
  **That was an honest placeholder and it was also a guess.** This file
  traces it. The answer is that the parity is removable, and the reason is
  not the box's reason, which is why guessing would have been wrong in both
  directions.

  **WHAT IS DIFFERENT ABOUT THE TORUS.** On the box at odd side the mirror
  layer sits between the halves and NO edge crosses the cut, so the
  cross-coupling is identically zero (`BoxOddReflection.crossForm_odd_eq_zero`).
  **On the torus that is false**, and obviously so once stated: the torus has
  a second cut, the wrap-around, and the sites at coordinate `0` are adjacent
  to the sites at coordinate `n-1` no matter what the parity is. So an edge
  does cross, at every side length.

  **WHY IT DOES NOT MATTER.** The surviving edges join a site to its OWN
  mirror and to nothing else, so the cross-coupling is diagonal with
  nonpositive entries — which is what the criterion consumes. The box at even
  side has the same shape for the same reason at the midline; the torus has
  it at the wrap-around instead, and at even side it has both.
  `GraphMirrorReflection.crossForm_nonpos_of_cross_diag` is the criterion,
  stated for a mirror half rather than a half, and added when this file
  needed it.

  WHAT THIS FILE PROVES, all with no parity hypothesis:
  1. **`torus_cross_diag_any`** — on the torus, at EVERY side length, a site
     strictly below the midline is adjacent to the mirror of a site strictly
     below the midline only when the two are equal. The arithmetic runs over
     all four torus adjacency cases and each one either forces equality or is
     impossible; **the even-side innermost case and the wrap-around case both
     survive, and both force equality**, which is the content.
  2. **`reflectionPositive_torus_any`** — reflection positivity on the torus
     at every side length, over `lowerHalf`.
  3. **`reflectionPositive_torus_compl_any`**,
     **`reflectionPositive_torus_either_any`** — the other side, by the same
     inclusion `BoxOddComplement` used, which is a statement about finite
     sets and does not know which graph it is for.
  4. **`os2_torus_any`**, **`os2_exponential_torus_any`** — measure-level and
     exponential OS2 on the torus, either side, any side length, any
     dimension.
  5. **`os2_torus_four_any`** — and in four dimensions.

  WHAT THIS DOES NOT DO.
  * **It does not touch `torus_two_eq_box`.** That lemma identifies the
    two-site torus with the box and is not on the path; the guess that it
    might be the obstruction was wrong, and it is left exactly as it was.
  * **No strictness on the torus.** `TorusNotStrict` still carries `Even n`
    and `4 ≤ n`, and at odd side the picture should change rather than
    transfer.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxOddComplement
import TorusReflection

namespace TorusAnySide

open Finset BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection TorusReflection BoxOddReflection LatticeReflectionPositive
open scoped ComplexOrder

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The cross-coupling is diagonal, at every side length

Four adjacency cases in the reflected coordinate. Writing `a` for the site's
coordinate and `c` for its partner's mirror, the hypotheses give `a < c`, so
`c + 1 = a` and `c = 0 ∧ a = n-1` are impossible outright. The two that
survive are `a + 1 = c`, which forces `n = 2a + 2` and pins the partner —
this is the even-side innermost layer — and `a = 0 ∧ c = n-1`, which is the
wrap-around and pins the partner too. **Both force equality, which is all the
criterion wants.**
-/

theorem torus_cross_diag_any (i : Fin d) (n : ℕ) :
    ∀ p ∈ strictLower i n, ∀ q ∈ strictLower i n,
      (torusGraph d n).Adj p (GraphReflection.revSite (n := n) i q) → p = q := by
  classical
  intro p hp q hq hadj
  rw [mem_strictLower] at hp hq
  have hplt := (p i).isLt
  have hqlt := (q i).isLt
  obtain ⟨k, h1, h2⟩ := hadj
  have hrev : ∀ j, (GraphReflection.revSite (n := n) i q) j
      = if j = i then Fin.rev (q i) else q j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [GraphReflection.revSite_apply_ne hj, hj]
  have hrevval : (Fin.rev (q i)).val = n - ((q i).val + 1) := Fin.val_rev (q i)
  -- the step must be in the reflected coordinate: elsewhere the coordinates agree
  have hki : k = i := by
    by_contra hk
    have hco : p i = (GraphReflection.revSite (n := n) i q) i := h1 i (Ne.symm hk)
    rw [hrev i, if_pos rfl] at hco
    have : (p i).val = n - ((q i).val + 1) := by rw [hco, hrevval]
    omega
  subst hki
  rw [hrev k, if_pos rfl] at h2
  -- in that coordinate the two values are separated, so only two cases survive
  have hpk : (p k).val = (q k).val := by
    obtain ⟨-, h2⟩ := h2
    rw [hrevval] at h2
    rcases h2 with h | h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  funext j
  by_cases hj : j = k
  · subst hj; exact Fin.ext hpk
  · have := h1 j hj
    rw [hrev j, if_neg hj] at this
    exact this

/-! ## 2. Reflection positivity on the torus, both sides, any side length -/

/-- **REFLECTION POSITIVITY ON THE TORUS, ANY SIDE LENGTH.**
    `TorusReflection.reflectionPositive_torus` with `Even n` deleted. -/
theorem reflectionPositive_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (torusGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) := by
  intro c hc
  refine GraphMirrorReflection.reflectionPositive_mirror
    (isMirrorHalf_strictLower i n) (isRefl_torus i) hm
    (fun w => GraphMirrorReflection.crossForm_nonpos_of_cross_diag
      (isMirrorHalf_strictLower i n) (torus_cross_diag_any i n) w) (c := c) ?_
  intro p hpH hpM
  refine hc p ?_
  rw [lowerHalf_eq_union]
  simp only [Finset.mem_union]
  tauto

/-- **THE OTHER SIDE.** The inclusion is `BoxOddComplement.compl_subset_image`,
    which is a statement about finite sets and does not know which graph it is
    being used for — so it transfers to the torus unchanged. -/
theorem reflectionPositive_torus_compl_any (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (torusGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n)ᶜ :=
  ReflectionPositive.mono (BoxOddComplement.compl_subset_image i n)
    (ReflectionPositive.mirror (isRefl_torus i) (reflectionPositive_torus_any i n hm))

/-- **EITHER SIDE, ANY SIDE LENGTH.** -/
theorem reflectionPositive_torus_either_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ) :
    GraphReflection.ReflectionPositive (torusGraph d n) m
      (GraphReflection.revSite (n := n) i) half := by
  rcases hs with h | h
  · exact ReflectionPositive.mono h (reflectionPositive_torus_any i n hm)
  · exact ReflectionPositive.mono h (reflectionPositive_torus_compl_any i n hm)

/-! ## 3. The measure on the torus, both sides, any side length -/

/-- **MEASURE-LEVEL OS2 ON THE TORUS, EITHER SIDE, ANY SIDE LENGTH.** -/
theorem os2_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(GraphLaplacian.gaussianField (torusGraph d n) m) :=
  GraphOS2.os2_measure_level _ hm (reflectionPositive_torus_either_any i n hm hs) hc

/-- **AND IN FOUR DIMENSIONS.** -/
theorem os2_torus_four_any (i : Fin 4) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site 4 n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ)
    {c : BoxGraph.Site 4 n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(GraphLaplacian.gaussianField (torusGraph 4 n) m) :=
  os2_torus_any i n hm hs hc

/-- **AND ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_torus_any (i : Fin d) (n : ℕ) (hm : m ≠ 0)
    {half : Finset (BoxGraph.Site d n)}
    (hs : half ⊆ lowerHalf i n ∨ half ⊆ (lowerHalf i n)ᶜ)
    {M : ℕ} (t : Fin M → BoxGraph.Site d n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(GraphLaplacian.gaussianField (torusGraph d n) m) :=
  GraphOS2Exponential.os2_exponential m hm (isRefl_torus i)
    (reflectionPositive_torus_either_any i n hm hs) t ht c

/-! ## 4. Review — the ways this could be hollow

**"Three entries called this untraced. Was that caution or laziness?"** It
was honest at the time — I had not looked — but the accompanying GUESS was
wrong, and that is the part worth recording. The guess named
`torus_two_eq_box` as the likely obstruction. That lemma is not on the path
and was never touched. **A placeholder that says "untraced" is fine; a
placeholder that says "untraced, and probably X" spends credibility on a
coin flip**, and this one lost.

**"Is the torus really not zero-coupled at odd side?"** Really not, and it is
not subtle: a torus has a second cut. The sites at coordinate `0` are
adjacent to the sites at coordinate `n-1` at every side length, so an edge
crosses the reflected cut no matter the parity. **The box's odd-side argument
does not transfer at all**; what transfers is the even-side box's argument,
which is the one about diagonal coupling.

**"Then why is it still positive?"** Because the surviving edges join a site
to its own mirror and to nothing else. §1 checks that over all four torus
adjacency cases rather than over the two the even-side proof needed, and two
of the four survive: the innermost layer at even side, and the wrap-around at
every side. Both force equality. **The criterion never asked for zero, only
for diagonal.**

**"Did the general criterion have to be weakened to make this work?"**
`crossForm_nonpos_of_cross_diag` is `TorusReflection.crossOp_nonpos_of_cross_diag`
with `IsHalf` replaced by `IsMirrorHalf`, which is strictly more general —
the old one is the empty-mirror case. The conclusion is unchanged. Nothing
was weakened; the hypothesis was.

**"What is left with `Even n` on this wall now?"** `isHalf_lowerHalf` and
`BoxCrossCoupling`, permanently and correctly, because they are ABOUT
fixed-point-free reflections. And the three strictness files. **AMENDED
2026-08-10: this paragraph predicted "more directions should be null, not
fewer" at odd side, and measurement refutes the simple form of that
(ERRATUM 72)** — at odd side three the form is nondegenerate on the strict
half and every null direction must charge the mirror; from odd side five it
is degenerate on the strict half already. The watchlist carries the measured
structure; predictions like the one deleted here are what ERRATUM 72 is
about. **Nothing on the positivity side of
this wall carries a parity hypothesis any more** — box, lattice, both
coordinate cuts, both sides, torus, measure level and exponential algebra.
-/

end TorusAnySide
