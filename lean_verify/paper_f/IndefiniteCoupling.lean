import StrictBiconditional

/-!
# The coupling hypothesis is not free, and here is the graph that breaks it

Every reflection-positivity result on this wall carries the same hypothesis: that the
cross-coupling form is nowhere positive,

  `hcross : ∀ w, crossForm G m θ H w ≤ 0`.

**Four files assume it and none exhibits a graph that fails it.** The only route to it in the
estate is `GraphMirrorReflection.crossForm_nonpos_of_cross_diag`, which asks that cross-cut
adjacency be *diagonal* — `p, q ∈ H` and `G.Adj p (θ q)` force `p = q` — and every lattice in the
estate satisfies that, so the hypothesis has always been discharged and never tested.

`StrictBiconditional` §3b removed `hcross` from the forward half of its biconditional, on the
grounds that the resulting statements *"survive exactly where §3 does not: an indefinite
coupling"*. **That claim was about a regime nothing in the estate inhabited.** A generalisation
into an empty regime proves nothing — which is `DualGraph` §8's standard, stated there as *"a
conditional theorem whose hypothesis nothing satisfies proves nothing"* — so this file inhabits it.

> **`crossForm_pos`** — for the four-vertex graph below, the half `{0, 1}` and the reflection
> `p ↦ p + 2`, the cross-coupling is **`+2` at an explicit vector**. Hence
> **`not_hcross`**: the standing hypothesis is FALSE here.

## Why it takes four vertices and two edges, and why no lattice does this

`crossForm G m θ H w = ∑_{p ∈ H} ∑_{q ∈ H} w p · w q · massive p (θ q)`, and off the diagonal
`massive p (θ q)` is `−1` across an edge and `0` otherwise. So every term with `p = q` contributes
`−(w p)² ≤ 0` and can never break the hypothesis. **The sign can only turn on a term with
`p ≠ q`** — two *different* sites of the half, adjacent across the cut — and then
`w p · w q · (−1)` is positive whenever `w p` and `w q` have opposite signs.

That is exactly the configuration `crossForm_nonpos_of_cross_diag` excludes, and it is exactly
what a lattice reflection cannot produce: a site's mirror image sits directly across the cut from
it, so the only cross-cut edge at `p` runs to `θ p` and the coupling is diagonal. **The hypothesis
is free on every lattice for a structural reason, and this graph is not a lattice.**

The graph is the perfect matching `0 – 3`, `1 – 2` on `Fin 4`; the reflection is `p ↦ p + 2`,
which swaps `0 ↔ 2` and `1 ↔ 3` and carries each edge to the other; the half is `{0, 1}` and the
mirror is empty. Site `0` is joined to `3 = θ 1` and site `1` to `2 = θ 0` — each half-site is
adjacent to the *other* one's mirror image, which is the whole of the construction.

## What this does and does not settle

**It makes §3b's generality real rather than notional**: `not_strict_of_supportedIsotropic` is a
statement about graphs, and there is now a graph in the estate where it applies and
`strict_iff_not_supportedIsotropic` cannot be stated at all.

**It does not exhibit a supported isotropic vector here**, so it does not decide whether *this*
graph is strict, and it makes no claim either way — deciding it means deciding whether such a
vector exists, which is a computation this file does not do. **NOT ATTEMPTED**, in the sense
`ERRATUM 71` addendum 3 fixes: nothing was tried.

**And it does not weaken anything.** No existing theorem loses a hypothesis and no lattice result
is touched; what changes is that a hypothesis assumed four times is now known to be a real
restriction rather than a formality.
-/

namespace IndefiniteCoupling

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace GraphMirrorReflection

/-! ## 1. The graph, the reflection, the half -/

/-- The perfect matching `0 – 3`, `1 – 2` on four vertices. Written as *the labels sum to three*
so that adjacency, symmetry and looplessness are all one arithmetic fact. -/
def crossGraph : SimpleGraph (Fin 4) where
  Adj p q := p.val + q.val = 3 ∧ p ≠ q
  symm := by
    rintro p q ⟨hs, hne⟩
    exact ⟨by omega, hne.symm⟩
  loopless := ⟨fun p h => h.2 rfl⟩

instance : DecidableRel crossGraph.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val + q.val = 3 ∧ p ≠ q))

/-- The reflection: add two, which swaps `0 ↔ 2` and `1 ↔ 3`. -/
def rho : Fin 4 ≃ Fin 4 := Equiv.addRight 2

@[simp] theorem rho_apply (p : Fin 4) : rho p = p + 2 := rfl

/-- The half: the two vertices the reflection moves onto the other pair. -/
def Hh : Finset (Fin 4) := {0, 1}

/-- **THE REFLECTION IS A GRAPH AUTOMORPHISM AND AN INVOLUTION.** It carries each edge to the
other one: `{0,3} ↦ {2,1}` and `{1,2} ↦ {3,0}`. -/
theorem isRefl_rho : GraphReflection.IsRefl crossGraph rho where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

/-- **AND `{0,1}` IS A MIRROR HALF WITH AN EMPTY MIRROR**, because `p ↦ p + 2` has no fixed
point on `Fin 4`. -/
theorem isMirrorHalf_Hh : IsMirrorHalf rho Hh (∅ : Finset (Fin 4)) where
  fixed := by decide
  disj := by decide
  split := by decide

/-! ## 2. The coupling is positive at an explicit vector -/

/-- The test vector: `+1` at site `0`, `−1` at site `1`, zero elsewhere. The opposite signs are
the point — with equal signs the same graph gives `−2`. -/
def wpos : Fin 4 → ℝ := ![1, -1, 0, 0]

/-- **THE CROSS-COUPLING IS `+2` HERE.** Only the two off-diagonal terms survive: site `0` is
adjacent to `3 = rho 1` and site `1` to `2 = rho 0`, each contributing `−(w 0)(w 1) = +1`, while
both diagonal terms vanish because `0` is not adjacent to `2` nor `1` to `3`. -/
theorem crossForm_pos (m : ℝ) : crossForm crossGraph m rho Hh wpos = 2 := by
  classical
  -- the four entries, each off the diagonal, so the mass never enters
  have e01 : GraphLaplacian.massive crossGraph m 0 (rho 1) = -1 := by
    rw [show rho 1 = (3 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((0 : Fin 4) = 3) by decide,
      show crossGraph.Adj 0 3 by decide]
  have e10 : GraphLaplacian.massive crossGraph m 1 (rho 0) = -1 := by
    rw [show rho 0 = (2 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((1 : Fin 4) = 2) by decide,
      show crossGraph.Adj 1 2 by decide]
  have e00 : GraphLaplacian.massive crossGraph m 0 (rho 0) = 0 := by
    rw [show rho 0 = (2 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((0 : Fin 4) = 2) by decide,
      show ¬ crossGraph.Adj 0 2 by decide]
  have e11 : GraphLaplacian.massive crossGraph m 1 (rho 1) = 0 := by
    rw [show rho 1 = (3 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((1 : Fin 4) = 3) by decide,
      show ¬ crossGraph.Adj 1 3 by decide]
  have hsum : ∀ f : Fin 4 → ℝ, ∑ p ∈ Hh, f p = f 0 + f 1 := by
    intro f; simp [Hh]
  rw [crossForm, hsum (fun p => ∑ q ∈ Hh, wpos p * wpos q * _)]
  rw [hsum (fun q => wpos 0 * wpos q * GraphLaplacian.massive crossGraph m 0 (rho q)),
    hsum (fun q => wpos 1 * wpos q * GraphLaplacian.massive crossGraph m 1 (rho q)),
    e00, e01, e10, e11]
  norm_num [wpos]

/-- **SO THE STANDING HYPOTHESIS IS FALSE ON THIS GRAPH.** The first configuration in the estate
that fails it. -/
theorem not_hcross (m : ℝ) : ¬ ∀ w : Fin 4 → ℝ, crossForm crossGraph m rho Hh w ≤ 0 := by
  intro hall
  have := hall wpos
  rw [crossForm_pos m] at this
  linarith

/-! ## 3. What that does to the two theorems -/

/-- **`strict_iff_not_supportedIsotropic` CANNOT BE APPLIED HERE**, and this says so as a theorem
rather than as a remark: its coupling hypothesis is exactly what §2 refutes. -/
theorem biconditional_hypothesis_fails (m : ℝ) :
    ¬ ∀ w : Fin 4 → ℝ, crossForm crossGraph m rho Hh w ≤ 0 :=
  not_hcross m

/-- **AND §3b STILL APPLIES**, which is the point of the file: `not_strict_of_supportedIsotropic`
asks for `IsMirrorHalf`, `IsRefl` and `m ≠ 0`, all of which hold here, and asks nothing about the
coupling. Stated as the instantiated implication rather than proved vacuously — no supported
isotropic vector is exhibited for this graph, and none is claimed. -/
theorem section3b_applies {m : ℝ} (hm : m ≠ 0)
    (hiso : StrictBiconditional.SupportedIsotropic crossGraph m rho Hh ∅) :
    ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm crossGraph m rho c) :=
  StrictBiconditional.not_strict_of_supportedIsotropic isMirrorHalf_Hh isRefl_rho hm hiso

end IndefiniteCoupling
