import CrossBlockStructure
import TorusBipGraphSame
import TorusCycleGraph

/-!
# Carrying the reflection and the half across the isomorphism

`TorusBipGraphSame` proved `torusGraph 1 4 ≃g IndefiniteCoupling.bipGraph` and said, in capitals,
that it **does not** transport reflection positivity, because those results are about a graph
*together with* a reflection `θ` and a half `H`. **This is that step**, and the payoff is not
reflection positivity — the estate has that on both sides already — but its **failure of
strictness**.

`LatticeReflectionPositive.reflectionPositive_congr` already transports the *positive* statement.
**Strictness was not transported**, and strictness is where the four-vertex graph has the
interesting answer: `CrossBlockStructure.bipGraph_not_strict` says reflection positivity on `K₂,₂`
is degenerate at every nonzero mass.

## What is proved

* **`reflectedForm_congr`** — the reflected form itself transports, which
  `LatticeReflectionPositive.sum_green_congr` had in unpackaged form.
* **`strict_congr`** and **`strict_congr_iff`** — **strictness transports**, in both directions,
  along a bijection intertwining the two reflections, with the half and the mirror carried by
  `Finset.map`.
* **`torusFourEquiv`** and **`torusFourEquiv_eq`** — the relabelling as a *computable* equivalence,
  checked by the kernel to be the underlying map of `TorusBipGraphSame.torusFour_iso_bipGraph`.
* **`isRefl_torusRho`, `isMirrorHalf_torusHalf`, `torusHalf_card`** — the transported reflection is
  a reflection, the transported half is a half, and it has two sites. **Without these the headline
  would not be about reflection positivity.**
* **`torusFour_reflectionPositive`** — reflection positivity **holds** there, so the next line is a
  degeneracy rather than an absence.
* **`torusFour_not_strict`** — **strict reflection positivity fails on the one-dimensional periodic
  lattice at side four**, under the carried-across reflection.
* **`strict_depends_on_reflection`** — **and it holds there under the lattice's own reflection**, so
  strictness is a property of the *pair*, not of the graph.
* **`strict_depends_on_the_half`** — and §7 pins down *which* part of the pair: the two reflections
  are **conjugate by a rotation** (`rot_intertwines`), so **the half is the variable**. Same graph,
  same reflection, same mass: strict on a contiguous half, degenerate on an antipodal one.

## And the reason that last one is sharp is not the reason first written here

**The first draft of this header said the estate's non-strictness on the periodic lattice "began at
six" and that side four was simply below the threshold. That is wrong, and the truth is better.**
`MirrorStrict.reflectionPositive_torus_four_strict` proves the periodic lattice at side four **IS
strict**, in every dimension, at every nonzero mass — under `revSite i` with `lowerHalf i 4`.

So this file is not filling a gap below a threshold. **It is showing that there is no threshold to
fill, because strictness is not a property of the graph at all.** `strict_depends_on_reflection`
puts the two side by side: same graph, same side length, same mass, **strict under one reflection
and degenerate under another**. §5 confirms by `decide` that the two reflections and the two halves
really are different objects, so the pair is not a contradiction.

## The apparent conflict, named before a reader finds it

`CrossBlockStructure.torus_strict_iff_le_four_lowerHalf` is a **biconditional at every side and in
every dimension**: the periodic lattice is strict **iff `n ≤ 4`**. Read by its name alone that
contradicts `torusFour_not_strict`. It does not, and the reason is written into the name:
**`_lowerHalf`**. The biconditional quantifies over families supported in `lowerHalf i n`, against
`revSite i`, and says nothing about any other reflection. **This file is what makes that suffix
load-bearing rather than descriptive.**

## A recorded claim this refutes

`CrossBlockStructure`'s closure of the `K₂,₂` strictness item says the result is *"the estate's
first non-strictness on a graph outside the lattice families"*. **`torusGraph 1 4 ≃g bipGraph` makes
that false**: the graph is the one-dimensional periodic lattice at side four. Struck in place there
rather than rewritten, per `ERRATUM 94`. **What survives is the other half of the same sentence** —
that the mechanism is a block of size two rather than the off-innermost-layer construction — and
that is untouched.

## What this is NOT

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed. Non-strictness is
a statement about *degeneracy* of an inequality the estate already knows holds; it neither adds nor
removes reflection positivity anywhere.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectedFormCongr

open SimpleGraph GraphReflection GraphLaplacian

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]

/-! ## 1. The reflected form transports -/

/-- **THE REFLECTED FORM TRANSPORTS**, provided the bijection intertwines the two reflections.
`LatticeReflectionPositive.sum_green_congr` is this with the sums written out. -/
theorem reflectedForm_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    {θ : V ≃ V} {θ' : W ≃ W} (hθ : ∀ p, e (θ p) = θ' (e p)) (m : ℝ) (c : W → ℝ) :
    reflectedForm G' m θ' c = reflectedForm G m θ (fun p => c (e p)) :=
  LatticeReflectionPositive.sum_green_congr e he hθ m c

/-! ## 2. And so does strictness -/

/-- **STRICTNESS TRANSPORTS.** If the reflected form is positive on every nonzero family supported
in `H` (off the mirror), the same holds on the far side for `H.map e`.

The reverse is `strict_congr_iff` below, obtained by running this one at `e.symm`. -/
theorem strict_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    {θ : V ≃ V} {θ' : W ≃ W} (hθ : ∀ p, e (θ p) = θ' (e p)) (m : ℝ) (H Mir : Finset V)
    (hst : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < reflectedForm G m θ c) :
    ∀ c : W → ℝ, c ≠ 0 → (∀ w, w ∉ H.map e.toEmbedding → w ∉ Mir.map e.toEmbedding → c w = 0) →
      0 < reflectedForm G' m θ' c := by
  intro c hc hsupp
  rw [reflectedForm_congr e he hθ]
  refine hst (fun p => c (e p)) (fun h0 => hc ?_) (fun p hp hpm => ?_)
  · funext w
    simpa using congrFun h0 (e.symm w)
  · refine hsupp (e p) (fun hmem => hp ?_) (fun hmem => hpm ?_) <;>
    · obtain ⟨k, hk, hke⟩ := Finset.mem_map.mp hmem
      rwa [e.injective hke] at hk

/-- **AND IT IS AN EQUIVALENCE.** The reverse direction is this same theorem run at `e.symm`, with
the adjacency and intertwining hypotheses transported and the half carried back by
`Finset.map_map`.

The first version of this file proved only the direction its application needed and said so. It
needed nothing else. -/
theorem strict_congr_iff (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    {θ : V ≃ V} {θ' : W ≃ W} (hθ : ∀ p, e (θ p) = θ' (e p)) (m : ℝ) (H Mir : Finset V) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) → 0 < reflectedForm G m θ c)
      ↔ (∀ c : W → ℝ, c ≠ 0 →
          (∀ w, w ∉ H.map e.toEmbedding → w ∉ Mir.map e.toEmbedding → c w = 0) →
          0 < reflectedForm G' m θ' c) := by
  have hback : ∀ X : Finset V, (X.map e.toEmbedding).map e.symm.toEmbedding = X := by
    intro X
    rw [Finset.map_map]
    simp
  refine ⟨strict_congr e he hθ m H Mir, fun hst => ?_⟩
  have he' : ∀ p q, G.Adj (e.symm p) (e.symm q) ↔ G'.Adj p q := by
    intro p q
    simpa using (he (e.symm p) (e.symm q)).symm
  have hθ' : ∀ p, e.symm (θ' p) = θ (e.symm p) := by
    intro p
    have h := hθ (e.symm p)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h, Equiv.symm_apply_apply]
  have := strict_congr e.symm he' hθ' m (H.map e.toEmbedding) (Mir.map e.toEmbedding) hst
  rwa [hback H, hback Mir] at this

/-! ## 3. The relabelling, computably -/

/-- The `Site 1 4 ≃ Fin 4` collapse followed by the transposition `1 ↔ 2`.

`TorusBipGraphSame.torusFour_iso_bipGraph` is built from `Equiv.ofBijective` and is therefore
`noncomputable`; nothing about it reduces. This is the same map written so that `decide` can see
it, and `torusFourEquiv_eq` checks by kernel that they agree. -/
def torusFourEquiv : BoxGraph.Site 1 4 ≃ Fin 4 :=
  (TorusCycleGraph.siteEquiv 4).trans (Equiv.swap 1 2)

/-- **THE COMPUTABLE COPY IS THE PREVIOUS UNIT'S ISOMORPHISM**, checked rather than assumed. -/
theorem torusFourEquiv_eq :
    ⇑torusFourEquiv = ⇑TorusBipGraphSame.torusFour_iso_bipGraph.toEquiv := by
  funext p
  revert p
  decide

/-- Adjacency corresponds, which is `TorusBipGraphSame.isGraphEmbedding_relabel` in both
directions — free here because the equivalence is computable. -/
theorem torusFourEquiv_adj (p q : BoxGraph.Site 1 4) :
    IndefiniteCoupling.bipGraph.Adj (torusFourEquiv p) (torusFourEquiv q)
      ↔ (TorusReflection.torusGraph 1 4).Adj p q := by
  revert p q
  decide

/-! ## 4. The transported reflection and half, and the conclusion -/

/-- `IndefiniteCoupling.rho` pulled back to the lattice. -/
def torusRho : BoxGraph.Site 1 4 ≃ BoxGraph.Site 1 4 :=
  torusFourEquiv.trans (IndefiniteCoupling.rho.trans torusFourEquiv.symm)

/-- `IndefiniteCoupling.Hh` pulled back to the lattice. -/
def torusHalf : Finset (BoxGraph.Site 1 4) :=
  IndefiniteCoupling.Hh.map torusFourEquiv.symm.toEmbedding

theorem torusRho_intertwines (p : BoxGraph.Site 1 4) :
    torusFourEquiv (torusRho p) = IndefiniteCoupling.rho (torusFourEquiv p) := by
  revert p
  decide

theorem torusHalf_map : torusHalf.map torusFourEquiv.toEmbedding = IndefiniteCoupling.Hh := by
  decide

/-- **AND IT IS A GENUINE REFLECTION OF THE LATTICE**, not an arbitrary permutation. Without this
the theorem below would not be a statement about reflection positivity at all. -/
theorem isRefl_torusRho : IsRefl (TorusReflection.torusGraph 1 4) torusRho where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

/-- **AND `torusHalf` IS A GENUINE HALF FOR IT**, with empty mirror. -/
theorem isMirrorHalf_torusHalf :
    GraphMirrorReflection.IsMirrorHalf torusRho torusHalf (∅ : Finset (BoxGraph.Site 1 4)) where
  fixed := by intro p; revert p; decide
  disj := by intro p; revert p; decide
  split := by intro p; revert p; decide

/-- **NON-VACUITY**: the half has two sites, so the theorem below is not a statement about an empty
support. Checked rather than assumed. -/
theorem torusHalf_card : torusHalf.card = 2 := by decide

/-- **AND REFLECTION POSITIVITY ITSELF HOLDS THERE**, transported by
`LatticeReflectionPositive.reflectionPositive_congr` from
`AdjSqForcesRegular.bipGraph_reflectionPositive_clean`. **This is what makes the failure below a
DEGENERACY rather than an absence**: the inequality holds, and it is not strict. -/
theorem torusFour_reflectionPositive {m : ℝ} (hm : m ≠ 0) :
    ReflectionPositive (TorusReflection.torusGraph 1 4) m torusRho torusHalf := by
  refine (LatticeReflectionPositive.reflectionPositive_congr torusFourEquiv torusFourEquiv_adj
    torusRho_intertwines m torusHalf).mpr ?_
  rw [torusHalf_map]
  exact AdjSqForcesRegular.bipGraph_reflectionPositive_clean hm

/-- **STRICT REFLECTION POSITIVITY FAILS ON THE ONE-DIMENSIONAL PERIODIC LATTICE AT SIDE FOUR**,
under the reflection and half carried across from `IndefiniteCoupling.bipGraph`.

`TorusNotStrict.not_strict_torus` needs `Even n` and `6 ≤ n`; this is `n = 4`. -/
theorem torusFour_not_strict (m : ℝ) (hm : m ≠ 0) :
    ¬ ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
        (∀ p, p ∉ torusHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
        0 < reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c := by
  intro hst
  refine CrossBlockStructure.bipGraph_not_strict m hm ?_
  have h := strict_congr torusFourEquiv torusFourEquiv_adj torusRho_intertwines m torusHalf ∅ hst
  rw [torusHalf_map] at h
  simpa using h

/-- **STRICTNESS IS NOT A PROPERTY OF THE GRAPH.** One graph, one side length, one mass, two
reflections — and the two answers differ.

`MirrorStrict.reflectionPositive_torus_four_strict` gives the left half: the periodic lattice at
side four is strict under `revSite 0` with `lowerHalf 0 4`. `torusFour_not_strict` gives the right:
it is degenerate under the reflection carried across from `IndefiniteCoupling.bipGraph`. §5 checks
that these really are two different reflections and two different halves, so the conjunction is a
statement about reflections rather than a contradiction. -/
theorem strict_depends_on_reflection (m : ℝ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf (d := 1) (n := 4) 0 → c p = 0) →
        0 < reflectedForm (TorusReflection.torusGraph 1 4) m
              (GraphReflection.revSite (d := 1) (n := 4) 0) c)
      ∧ ¬ ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
          (∀ p, p ∉ torusHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
          0 < reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c :=
  ⟨fun _ hc0 hcs => MirrorStrict.reflectionPositive_torus_four_strict 0 hm hc0 hcs,
    torusFour_not_strict m hm⟩

/-! ## 5. Is it the lattice's own reflection? Decided, not argued -/

/-- **IT IS NOT `GraphReflection.revSite 0`.** The lattice's own reflection at side four sends
`0 ↦ 3` and `1 ↦ 2`; the one carried across from `bipGraph` sends `0 ↦ 1` and `2 ↦ 3`. Both are
reflections of the same four-cycle through opposite edge midpoints, rotated by one step — but they
are **different maps**, and §4's theorem is about the second.

**So the two results do not collide.** `MirrorStrict.reflectionPositive_torus_four_strict` is about
`revSite 0` and `lowerHalf 0 4`; `torusFour_not_strict` is about `torusRho` and `torusHalf`; and
these theorems say those are different. **Without them `strict_depends_on_reflection` would read as
a contradiction rather than as a finding.** -/
theorem torusRho_ne_revSite : torusRho ≠ GraphReflection.revSite (d := 1) (n := 4) 0 := by
  intro h
  have : torusRho (fun _ => 0) = GraphReflection.revSite (d := 1) (n := 4) 0 (fun _ => 0) := by
    rw [h]
  revert this
  decide

/-- **AND THE HALF IS NOT `lowerHalf` EITHER.** -/
theorem torusHalf_ne_lowerHalf :
    torusHalf ≠ GraphHalfSpace.lowerHalf (d := 1) (n := 4) 0 := by decide

/-! ## 7. The operative difference is the HALF, not the reflection

`strict_depends_on_reflection` above is true and **its name is imprecise**, which the kernel says
rather than a reader having to notice. `revSite 0` is `(0 3)(1 2)` and `torusRho` is `(0 1)(2 3)`:
**both are edge reflections of the same four-cycle, conjugate by one step of rotation.** What
differs is the half — `lowerHalf 0 4` is `{0,1}`, a contiguous side, and `torusHalf` is `{0,2}`,
an antipodal pair. So the sharp statement fixes the reflection and moves the half.
-/

/-- One step of rotation of the four-cycle. -/
def rot : BoxGraph.Site 1 4 ≃ BoxGraph.Site 1 4 :=
  (TorusCycleGraph.siteEquiv 4).trans
    ((Equiv.addRight (1 : Fin 4)).trans (TorusCycleGraph.siteEquiv 4).symm)

theorem rot_adj (p q : BoxGraph.Site 1 4) :
    (TorusReflection.torusGraph 1 4).Adj (rot p) (rot q)
      ↔ (TorusReflection.torusGraph 1 4).Adj p q := by
  revert p q
  decide

/-- **THE TWO REFLECTIONS ARE CONJUGATE**, by that rotation. This is what makes the section
heading true rather than a guess. -/
theorem rot_intertwines (p : BoxGraph.Site 1 4) :
    rot (GraphReflection.revSite (d := 1) (n := 4) 0 p) = torusRho (rot p) := by
  revert p
  decide

/-- The contiguous half, carried along the rotation: `{1,2}`. -/
def rotHalf : Finset (BoxGraph.Site 1 4) :=
  (GraphHalfSpace.lowerHalf (d := 1) (n := 4) 0).map rot.toEmbedding

/-- **AND IT IS NOT `torusHalf`.** `{1,2}` against `{0,2}` — a side of the cycle against an
antipodal pair. **This is the whole difference between the two answers.** -/
theorem rotHalf_ne_torusHalf : rotHalf ≠ torusHalf := by decide

/-- The lattice at side four is strict under `torusRho` **on the rotated contiguous half**,
transported from `MirrorStrict.reflectionPositive_torus_four_strict` by `strict_congr_iff`. -/
theorem torusFour_strict_rotHalf (m : ℝ) (hm : m ≠ 0) :
    ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
      (∀ p, p ∉ rotHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
      0 < reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c := by
  have h := (strict_congr_iff rot rot_adj rot_intertwines m
      (GraphHalfSpace.lowerHalf (d := 1) (n := 4) 0) ∅).mp
    (fun c hc0 hcs => MirrorStrict.reflectionPositive_torus_four_strict 0 hm hc0
      (fun p hp => hcs p hp (by simp)))
  simpa [rotHalf] using h

/-- **ONE GRAPH, ONE REFLECTION, ONE MASS — AND THE HALF DECIDES.**

Under `torusRho`: **strict** on the contiguous half `rotHalf = {1,2}`, **degenerate** on the
antipodal half `torusHalf = {0,2}`. `rotHalf_ne_torusHalf` is what stops this being a
contradiction, and `rot_intertwines` is what shows the reflection is not the variable. -/
theorem strict_depends_on_the_half (m : ℝ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
        (∀ p, p ∉ rotHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
        0 < reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c)
      ∧ ¬ ∀ c : BoxGraph.Site 1 4 → ℝ, c ≠ 0 →
          (∀ p, p ∉ torusHalf → p ∉ (∅ : Finset (BoxGraph.Site 1 4)) → c p = 0) →
          0 < reflectedForm (TorusReflection.torusGraph 1 4) m torusRho c :=
  ⟨torusFour_strict_rotHalf m hm, torusFour_not_strict m hm⟩

end ReflectedFormCongr
