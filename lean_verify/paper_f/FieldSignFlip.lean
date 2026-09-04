import FieldIsometryInvariance
import GreenDisconnected

/-!
# A symmetry of the field that is neither a relabelling nor the global sign flip

`FieldIsometryInvariance` proved that any linear isometry preserving the propagator's quadratic form
is a symmetry of the Gaussian field, and closed with a fence: it exhibits **no** such isometry
outside permutations, signs and their composites, and names what would be needed. **This file
exhibits one**, and it needs no eigenspace machinery at all.

`PROOF_STRATEGY` §6 question 3 — *if the unit you just finished was a `B`, retry `B → C` right now*
— taken literally again. The general theorem was the `B`.

## The idea, in one sentence

`GreenDisconnected.green_eq_zero_of_not_reachable` says the propagator vanishes between vertices
with no path between them, so **flipping the sign of the field on one connected component and
leaving it alone on the others changes no term of the quadratic form.**

## What is proved

**`signFlip s`** — negate the coordinates in `s`, as a linear isometry
(`LinearIsometryEquiv.piLpCongrRight`, one `neg` or `refl` per vertex). It is its own inverse.

**`preservesQuadForm_signFlip`** — if `s` is a **union of connected components**
(`∀ p q, G.Reachable p q → (p ∈ s ↔ q ∈ s)`) then `signFlip s` preserves the form, so
**`gaussianField_map_signFlip`**: the field is invariant under it.

**`signFlip_ne_permField`** (`s` nonempty) and **`signFlip_ne_negPermField`** (`s ≠ univ`) — it is
`permField ψ` for **no** `ψ`, and `(permField ψ).trans (neg)` for **no** `ψ`. So on any graph with a
proper nonempty union of components this is a symmetry outside both of the estate's families and
outside the composites `FieldIsometryInvariance` added.

**`exists_new_symmetry_of_not_reachable`** — and such an `s` exists exactly when the graph is
disconnected: `{v | G.Reachable p v}` is closed by transitivity, contains `p`, and misses any `q`
unreachable from `p`.

**`closed_iff_of_preconnected`** — the converse. On a preconnected graph the only closed sets are
`∅` and `univ`, whose sign flips are the identity and the global one. **So this construction gives
something new exactly when the graph is disconnected**, which is the honest scope of it.

## What is NOT here

**No symmetry on a connected graph.** `closed_iff_of_preconnected` proves this construction cannot
give one, and the box and the torus are connected. The eigenspace route
`FieldIsometryInvariance` named — a rotation inside a degenerate eigenspace of `green` — is still
**not attempted**, and it is the one that could reach a connected graph. **No cost is claimed**
(`ERRATUM 246`).

**No claim that these generate anything.** The invariant isometries form a group
(`FieldIsometryInvariance.quadForm_preserving_comp`); nothing here computes it or bounds it.

**Not OS3 and not any OS axiom**, for the reason `FieldIsometryInvariance` gives: a wider shadow is
not a smaller gap.

**Physically this is not a surprise, and that is the point.** On a disconnected graph the field
restricted to each component is an independent Gaussian field — `LatticeFieldFactorises` proves the
independence — so flipping one component's sign obviously leaves the law alone. **What was missing
was a statement**, and the estate's two symmetry theorems could not supply one because a partial
sign flip is neither of them.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldSignFlip

open Matrix GraphLaplacian MeasureTheory FieldAutInvariance FieldIsometryInvariance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The map -/

/-- **NEGATE THE COORDINATES IN `s`**, as a linear isometry of `EuclideanSpace ℝ V`. -/
noncomputable def signFlip (s : Finset V) : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun v => if v ∈ s then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem signFlip_apply (s : Finset V) (x : EuclideanSpace ℝ V) (v : V) :
    signFlip s x v = if v ∈ s then -(x v) else x v := by
  rw [signFlip, LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases hv : v ∈ s <;> simp [hv]

/-- It is an involution. -/
theorem signFlip_involutive (s : Finset V) (x : EuclideanSpace ℝ V) :
    signFlip s (signFlip s x) = x := by
  ext v
  rw [signFlip_apply, signFlip_apply]
  by_cases hv : v ∈ s <;> simp [hv]

/-- So the inverse that `FieldIsometryInvariance.PreservesQuadForm` quantifies over is the
map itself. -/
@[simp] theorem signFlip_symm (s : Finset V) : (signFlip s).symm = signFlip s := by
  refine LinearIsometryEquiv.ext fun x => ?_
  apply (signFlip s).injective
  rw [LinearIsometryEquiv.apply_symm_apply, signFlip_involutive]

/-! ## 2. It preserves the form when `s` is a union of components -/

/-- A set closed under reachability: a union of connected components. -/
def IsComponentClosed (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ p q : V, G.Reachable p q → (p ∈ s ↔ q ∈ s)

/-- **FLIPPING THE SIGN ON A UNION OF COMPONENTS PRESERVES THE PROPAGATOR'S QUADRATIC FORM.**
Every term with `p` and `q` in different components is killed by
`GreenDisconnected.green_eq_zero_of_not_reachable`; every surviving term has both signs equal. -/
theorem preservesQuadForm_signFlip (hm : m ≠ 0) {s : Finset V} (hs : IsComponentClosed G s) :
    PreservesQuadForm G m (signFlip s) := by
  intro t
  rw [signFlip_symm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  by_cases hpq : G.Reachable p q
  · have hiff := hs p q hpq
    by_cases hp : p ∈ s
    · have hq : q ∈ s := hiff.mp hp
      simp only [signFlip_apply, if_pos hp, if_pos hq]
      ring
    · have hq : q ∉ s := fun h => hp (hiff.mpr h)
      simp only [signFlip_apply, if_neg hp, if_neg hq]
  · rw [GreenDisconnected.green_eq_zero_of_not_reachable G hm hpq]
    ring

/-- **AND SO THE FIELD IS INVARIANT UNDER IT.** -/
theorem gaussianField_map_signFlip (hm : m ≠ 0) {s : Finset V} (hs : IsComponentClosed G s) :
    (gaussianField G m).map (signFlip s) = gaussianField G m :=
  gaussianField_map_isometry hm (preservesQuadForm_signFlip hm hs)

/-! ## 3. It is in neither family -/

omit [DecidableRel G.Adj] in
/-- **NOT A RELABELLING**, for any `ψ` whatever: at a flipped vertex it puts `−1` on the diagonal
and a permutation puts `0` or `1`. -/
theorem signFlip_ne_permField {s : Finset V} (hs : s.Nonempty) (ψ : V ≃ V) :
    signFlip s ≠ permField ψ := by
  obtain ⟨p, hp⟩ := hs
  intro hcontra
  have h := DFunLike.congr_fun hcontra
    (WithLp.toLp 2 (Pi.single p (1 : ℝ)) : EuclideanSpace ℝ V)
  have hval := congrFun (congrArg (fun x : EuclideanSpace ℝ V => WithLp.ofLp x) h) p
  dsimp only at hval
  rw [signFlip_apply, if_pos hp, permField_apply] at hval
  simp only [Pi.single_eq_same] at hval
  by_cases hψ : ψ.symm p = p
  · rw [hψ, Pi.single_eq_same] at hval; norm_num at hval
  · rw [Pi.single_eq_of_ne hψ] at hval; norm_num at hval

omit [DecidableRel G.Adj] in
/-- **AND NOT A RELABELLING COMPOSED WITH THE GLOBAL SIGN FLIP**, for any `ψ`: at an unflipped
vertex it puts `1` where that map puts `0` or `−1`. -/
theorem signFlip_ne_negPermField {s : Finset V} (hs : s ≠ Finset.univ) (ψ : V ≃ V) :
    signFlip s ≠ (permField ψ).trans (LinearIsometryEquiv.neg ℝ) := by
  obtain ⟨q, hq⟩ : ∃ q : V, q ∉ s := by
    by_contra hall
    exact hs (Finset.eq_univ_of_forall (by simpa using hall))
  intro hcontra
  have h := DFunLike.congr_fun hcontra
    (WithLp.toLp 2 (Pi.single q (1 : ℝ)) : EuclideanSpace ℝ V)
  have hright : ((permField ψ).trans (LinearIsometryEquiv.neg ℝ))
      (WithLp.toLp 2 (Pi.single q (1 : ℝ)) : EuclideanSpace ℝ V)
      = -(permField ψ (WithLp.toLp 2 (Pi.single q (1 : ℝ)) : EuclideanSpace ℝ V)) := rfl
  rw [hright] at h
  have hval := congrFun (congrArg (fun x : EuclideanSpace ℝ V => WithLp.ofLp x) h) q
  dsimp only at hval
  rw [signFlip_apply, if_neg hq] at hval
  rw [WithLp.ofLp_neg, Pi.neg_apply, permField_apply] at hval
  simp only [Pi.single_eq_same] at hval
  by_cases hψ : ψ.symm q = q
  · rw [hψ, Pi.single_eq_same] at hval; norm_num at hval
  · rw [Pi.single_eq_of_ne hψ] at hval; norm_num at hval

/-! ## 4. Exactly when it gives something new -/

/-- **A DISCONNECTED GRAPH HAS ONE.** The component of `p` is closed, contains `p`, and misses any
`q` unreachable from it. -/
theorem exists_new_symmetry_of_not_reachable (hm : m ≠ 0) {p q : V} (hpq : ¬ G.Reachable p q) :
    ∃ s : Finset V, IsComponentClosed G s ∧ s.Nonempty ∧ s ≠ Finset.univ ∧
      (gaussianField G m).map (signFlip s) = gaussianField G m := by
  classical
  refine ⟨Finset.univ.filter fun v => G.Reachable p v, ?_, ⟨p, by simp⟩, ?_, ?_⟩
  · intro u v huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans huv, fun h => h.trans huv.symm⟩
  · intro hall
    have : q ∈ Finset.univ.filter fun v => G.Reachable p v := by rw [hall]; exact Finset.mem_univ q
    simp only [Finset.mem_filter] at this
    exact hpq this.2
  · refine gaussianField_map_signFlip hm ?_
    intro u v huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans huv, fun h => h.trans huv.symm⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **AND A CONNECTED GRAPH HAS NONE OF THIS SHAPE.** On a preconnected graph the only closed sets
are `∅` and `univ`, so `signFlip` gives the identity and the global sign flip and nothing else.
This is what makes §3's two theorems a statement about disconnected graphs. -/
theorem closed_iff_of_preconnected (hG : G.Preconnected) {s : Finset V}
    (hs : IsComponentClosed G s) : s = ∅ ∨ s = Finset.univ := by
  classical
  by_cases hne : s = ∅
  · exact Or.inl hne
  · refine Or.inr (Finset.eq_univ_of_forall fun v => ?_)
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact (hs p v (hG p v)).mp hp

end FieldSignFlip
