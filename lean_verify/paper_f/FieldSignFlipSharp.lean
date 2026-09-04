import FieldSignFlip
import GraphGreenPositive

/-!
# Which sign flips are symmetries: exactly the ones on unions of components

`FieldSignFlip` proved that `signFlip s` preserves the propagator's quadratic form **if** `s` is a
union of connected components, and left the converse unasked. **It holds, and the reason is one
biconditional the estate already had**: `GreenDisconnected.green_pos_iff_reachable` — the propagator
is strictly positive exactly between vertices joined by a path.

`PROOF_STRATEGY` §7 rule 3, applied to the previous unit rather than to an older one: the
restriction removed is the one-sidedness of its hypothesis.

## The witness is the all-ones configuration

Write `ε v = ±1` for the sign `signFlip s` applies at `v`. On the all-ones vector the form becomes
`∑_{u,v} ε u · ε v · green u v` against `∑_{u,v} green u v`, and the two differ term by term by
`green u v · (1 − ε u ε v)` — **zero when `u` and `v` are on the same side of `s`, and
`2 · green u v` when they are not.** Every term is `≥ 0` because `green` has no negative
entries, and the term at a split reachable pair is **strictly** positive, so one split pair
makes the two sums differ.

**No basis vectors and no `Pi.single` arithmetic**: the all-ones vector makes the whole computation
a comparison of two double sums with the same index set.

## What is proved

**`not_preservesQuadForm_of_split`** — if `p ∈ s`, `q ∉ s` and `G.Reachable p q`, then `signFlip s`
does not preserve the form.

**`preservesQuadForm_signFlip_iff`** — **so `signFlip s` preserves the form if and only if `s` is a
union of connected components**, at every finite graph and every `m ≠ 0`. `FieldSignFlip` had one
direction; this is the characterisation.

**`preservesQuadForm_signFlip_iff_of_preconnected`** — on a connected graph the sign flips that
preserve the form are exactly the two trivial ones, `s = ∅` and `s = univ`. That upgrades
`FieldSignFlip.closed_iff_of_preconnected` from *"the closed sets are `∅` and `univ`"* to *"and
nothing else in this family preserves the form"*.

## What is NOT here

**No new symmetry.** This unit adds no invariant isometry; it says exactly which members of one
family are invariant.

**The open statement, named as a statement** (`ERRATUM 453`): *there is an invariant isometry of
`green` on a connected graph outside the permutations, the signs and their composites.* One route to
it — not the only one — is a rotation inside a degenerate eigenspace, and
`CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` shows the connected cycle **has** a
two-dimensional eigenspace, so what is missing is the rotation and not the degeneracy. **Not
attempted, no cost claimed** (`ERRATUM 246`).

> ⚠ **THE STATEMENT IS PROVED, TWO UNITS LATER, AND THIS PARAGRAPH IS KEPT AS WRITTEN**
> (`ERRATUM 94`, **`ERRATUM 454`**, 2026-09-04). `FieldHouseholder` exhibits the isometry on
> **every** finite graph with `3 ≤ |V|`: the Householder reflection through the all-ones line. **It
> uses no degenerate eigenspace** — a reflection needs a one-dimensional one, and `green`'s
> all-ones eigenvector supplies it on every graph. The sentence above is right that the rotation
> would work, and wrong to leave the impression that *"what is missing is the rotation"* was the
> whole of what was missing.

**Nothing about other diagonal maps.** Only `±1` per coordinate is an isometry; other scalings are
not, and are not discussed.

**Not a statement about the measure's full symmetry group.** `PreservesQuadForm` is sufficient for
invariance (`FieldIsometryInvariance.gaussianField_map_isometry`); this file does not ask whether it
is necessary, and nothing here rules out an invariant map that moves the form.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldSignFlipSharp

open Matrix GraphLaplacian FieldIsometryInvariance FieldSignFlip

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A split component is detected, at the all-ones configuration -/

/-- The value of `signFlip s` on the all-ones vector: `−1` inside `s` and `1` outside. -/
theorem signFlip_one_apply (s : Finset V) (v : V) :
    signFlip s (WithLp.toLp 2 (fun _ : V => (1 : ℝ)) : EuclideanSpace ℝ V) v
      = if v ∈ s then -1 else 1 := by
  rw [signFlip_apply]

/-- Every term of the flipped form is at most the corresponding unflipped term, because `green` has
no negative entries and the sign product is `±1`. -/
theorem signFlip_term_le (hm : m ≠ 0) (s : Finset V) (a b : V) :
    (signFlip s (WithLp.toLp 2 (fun _ : V => (1 : ℝ)) : EuclideanSpace ℝ V)) a *
        (green G m a b *
          (signFlip s (WithLp.toLp 2 (fun _ : V => (1 : ℝ)) : EuclideanSpace ℝ V)) b)
      ≤ green G m a b := by
  have hnn := GraphGreenPositive.green_nonneg G hm a b
  rw [signFlip_one_apply, signFlip_one_apply]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [ha, hb] <;> linarith

/-- **A SIGN FLIP THAT SPLITS A COMPONENT DOES NOT PRESERVE THE FORM.** -/
theorem not_preservesQuadForm_of_split (hm : m ≠ 0) {s : Finset V} {p q : V}
    (hp : p ∈ s) (hq : q ∉ s) (hpq : G.Reachable p q) :
    ¬ PreservesQuadForm G m (signFlip s) := by
  classical
  intro hpres
  set u : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ)) with hu
  have h := hpres u
  rw [signFlip_symm] at h
  have hone : ∀ v : V, u v = 1 := fun v => rfl
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at h
  have hgpos : 0 < green G m p q := (GreenDisconnected.green_pos_iff_reachable G hm p q).mpr hpq
  have hlt : ∑ a : V, ∑ b : V, (signFlip s u) a * (green G m a b * (signFlip s u) b)
      < ∑ a : V, ∑ b : V, u a * (green G m a b * u b) := by
    refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
    · simpa [hone] using signFlip_term_le hm s a b
    · refine Finset.sum_lt_sum (fun b _ => ?_) ⟨q, Finset.mem_univ q, ?_⟩
      · simpa [hone] using signFlip_term_le hm s p b
      · rw [signFlip_one_apply, signFlip_one_apply, if_pos hp, if_neg hq]
        simp only [hone, mul_one]
        linarith
  exact absurd h (ne_of_lt hlt)

/-! ## 2. The characterisation -/

/-- **`signFlip s` PRESERVES THE FORM IF AND ONLY IF `s` IS A UNION OF CONNECTED COMPONENTS.** -/
theorem preservesQuadForm_signFlip_iff (hm : m ≠ 0) (s : Finset V) :
    PreservesQuadForm G m (signFlip s) ↔ IsComponentClosed G s := by
  refine ⟨fun hpres p q hpq => ?_, preservesQuadForm_signFlip hm⟩
  by_cases hp : p ∈ s
  · refine ⟨fun _ => ?_, fun _ => hp⟩
    by_contra hq
    exact not_preservesQuadForm_of_split hm hp hq hpq hpres
  · refine ⟨fun h => absurd h hp, fun hq => ?_⟩
    exact absurd hpres (not_preservesQuadForm_of_split hm hq hp hpq.symm)

/-- **AND ON A CONNECTED GRAPH ONLY THE TWO TRIVIAL FLIPS SURVIVE** — the identity and the global
sign flip. `FieldSignFlip.closed_iff_of_preconnected` gave the closed sets; this says nothing else
in the family preserves the form. -/
theorem preservesQuadForm_signFlip_iff_of_preconnected (hG : G.Preconnected) (hm : m ≠ 0)
    (s : Finset V) :
    PreservesQuadForm G m (signFlip s) ↔ (s = ∅ ∨ s = Finset.univ) := by
  rw [preservesQuadForm_signFlip_iff hm]
  refine ⟨closed_iff_of_preconnected hG, fun hs p q _ => ?_⟩
  rcases hs with rfl | rfl
  · simp
  · simp

end FieldSignFlipSharp
