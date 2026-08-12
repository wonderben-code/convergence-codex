import PrismStrict
import CrossBlockStructure

/-!
# The prism is the fourth family, and its strictness has two independent proofs

`CrossBlockStructure` §8 reduced strictness of the reflected form to a question with no vectors in
it — **`strict_iff_cut_perfect`: strict exactly when every half-site is joined to its own mirror and
to no other half-site's.** §§9–11 instantiated that on the torus, the box and the estate's own
lattice `def`, and stopped there, recording that those three were all it had attempted.

The prism is a fourth, and it is the cheapest of them: the cut of a two-layer stack is a perfect
matching by inspection of `PrismReflection.prismAdj`, because the only edge leaving a layer is the
vertical one. So `prism_cut_perfect`, and then strictness follows from the criterion with no
analysis at all.

## Why it is worth doing rather than noting

**`PrismStrict.reflectionPositive_prism_strict` already proves the prism strict, by a completely
different argument**: `PrismGreen` inverts the two blocks, `PrismReflectedForm` turns the reflected
form into a difference of two base-graph Green functions at masses `m` and `√(m²+2)`, and
`PrismStrict` shows that difference positive definite. Not a cut in sight.

`prism_strict_two_routes` derives **`PrismStrict`'s exact statement** from the criterion, so the two
are the same theorem with two proofs rather than two theorems that look alike. The estate has no
second reader; agreement between arguments that share nothing is the check available instead, and
`AdjSqForcesRegular` §8 did the same thing for `crossGraph` in the previous unit.

## What is not claimed

**No new case is decided.** The prism was already known strict. What is new is that a fourth family
is now an instance of the one criterion, and that the criterion's prediction was checked against a
Green-function computation rather than against itself.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PrismCutPerfect

open PrismReflection GraphReflection GraphMirrorReflection CrossBlockStructure

variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable {m : ℝ}

/-! ## 1. The cut of a two-layer stack is a perfect matching -/

omit [DecidableRel K.Adj] in
/-- **THE ONLY EDGE LEAVING A LAYER IS THE VERTICAL ONE.** Written as the criterion wants it: for
half-sites `s` and `q`, `s` is joined to `q`'s mirror exactly when `s = q`. -/
theorem prism_cut_perfect (s : V × Bool) (hs : s ∈ lower V) (q : V × Bool) (hq : q ∈ lower V) :
    (prism K).Adj s (swap (V := V) q) ↔ s = q := by
  obtain ⟨sv, sb⟩ := s
  obtain ⟨qv, qb⟩ := q
  simp only [mem_lower] at hs hq
  subst hs
  subst hq
  simp [prism, prismAdj, swap_apply, Prod.ext_iff]

omit [DecidableRel K.Adj] in
/-- A perfect matching is a block cut, so the criterion's standing hypothesis is free here. -/
theorem isCrossBlock_prism : IsCrossBlock (prism K) (swap (V := V)) (lower V) :=
  isCrossBlock_of_cross_diag fun p hp q hq hadj => (prism_cut_perfect K p hp q hq).mp hadj

/-! ## 2. Strictness, from the criterion -/

/-- **THE PRISM IS STRICT, BY THE CRITERION.** No Green function, no block inverse, no positive
definite difference — the cut is a perfect matching and `CrossBlockStructure` §8 does the rest. -/
theorem prism_strict_of_criterion (hm : m ≠ 0) :
    ∀ c : V × Bool → ℝ, c ≠ 0 → (∀ p, p ∉ lower V → p ∉ (∅ : Finset (V × Bool)) → c p = 0) →
      0 < GraphReflection.reflectedForm (prism K) m (swap (V := V)) c :=
  (strict_iff_cut_perfect (isMirrorHalf_of_isHalf (isHalf_lower (V := V)))
    (isRefl_swap K) hm (isCrossBlock_prism K)).mpr
    fun s hs q hq => prism_cut_perfect K s hs q hq

/-! ## 3. And it is `PrismStrict`'s theorem, not merely a theorem like it -/

open PrismGreen in
/-- The extension of a nonzero function on the half is a nonzero function on the whole graph. -/
theorem ext_ne_zero {v : V → ℝ} (hv : v ≠ 0) :
    GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x)) ≠ 0 := by
  intro h
  refine hv (funext fun x => ?_)
  have hmem : ((x, false) : V × Bool) ∈ lower V := by simp
  have := congrFun h (x, false)
  rwa [GraphReflectionPositive.ext, dif_pos hmem, show
    lowerEquiv V ⟨(x, false), hmem⟩ = x from rfl] at this

open PrismGreen in
/-- **THE SAME STATEMENT `PrismStrict` PROVES, DERIVED FROM THE CUT.** Two arguments sharing nothing
but the graph: this one reads the adjacency relation, `PrismStrict.reflectionPositive_prism_strict`
inverts two blocks and shows a difference of Green functions positive definite. -/
theorem prism_strict_via_cut (hm : m ≠ 0) {v : V → ℝ} (hv : v ≠ 0) :
    0 < GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x))) :=
  prism_strict_of_criterion K hm _ (ext_ne_zero hv)
    fun _ hp _ => GraphReflectionPositive.ext_notMem _ hp

open PrismGreen in
/-- **AND THE TWO AGREE**, stated so the agreement is a theorem rather than an observation. -/
theorem prism_strict_two_routes (hm : m ≠ 0) {v : V → ℝ} (hv : v ≠ 0) :
    (0 < GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x))))
      ∧ (0 < GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x)))) :=
  ⟨prism_strict_via_cut K hm hv, PrismStrict.reflectionPositive_prism_strict K hm hv⟩

end PrismCutPerfect
