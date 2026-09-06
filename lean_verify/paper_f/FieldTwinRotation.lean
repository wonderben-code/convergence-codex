import LaplacianTwoClasses

/-!
# The twin chain pays out on the field: a tree with infinitely many symmetries

Five units have been about graphs and Laplacians, with the Gaussian field appearing only in the
equivalence that let them be stated. This carries them back. Two twin pairs of the same degree give
two independent eigenvectors of the **propagator**, and the estate's rotation machinery turns those
into a circle of symmetries of the measure.

**The instance is a tree.** Counted before the sentence was written (`ERRATUM 450`), and the first
draft of it was wrong: the graphs this estate had shown to carry a rotation are the **cycle**
(`FieldCycleRotation`), the **torus** (`FieldTorusRotation`), the **box** (`FieldBoxRotation`,
`FieldRotationCount`) — and **every disconnected graph**
(`FieldRotationInstance.exists_rotation_symmetry_of_not_reachable`), which the draft had forgotten.
`FieldTwinSpectrum.twinGraph` is an eight-vertex **connected** graph that is none of those: a
**tree**, whose two pendant pairs are enough.

## What is proved

**`massive_mulVec_of_lapMatrix_mulVec`** — an eigenvector of the Laplacian at `ν` is one of
`massive` at `ν + m²`, through `FieldLaplacianSimple.toLin'_massive`.

**`green_mulVec_twinDiff`** — so the difference of two twins is an eigenvector of the
**propagator**, at `(deg u + m²)⁻¹`. The eigenvalue is non-zero because the degree is a natural
number and `m² > 0`, which is the only place the mass hypothesis is used.

**`twinDiff_not_smul`** — a difference from a disjoint pair is not a multiple of another, read off
the value at one vertex; **it takes no `x ≠ y`**, the linter having said so. The companion fact
that a difference is non-zero was written here too and **deleted**: `CutTwins.twinDiff_ne_zero` is
the same theorem with the same proof, found by `newnames_scan` — the **fourth** time in this run
that a collision has shown two parts of the estate holding one object (`ERRATUM 465`).

**`infinite_symmetryMatrices_of_twin_pairs`, `exists_rotation_symmetry_of_twin_pairs`** — so a graph
with two twin pairs of the same degree has **infinitely many** symmetry matrices, and carries a
**genuine rotation** of the Gaussian field: an orthogonal matrix, not the identity, whose isometry
leaves the measure invariant.

**`infinite_symmetryMatrices_twinGraph`** — **and a tree carries one.**

## What is NOT here

**NO GROUP, NO COUNT, NO STRUCTURE.** `Set.Infinite` is what is proved. **The symmetry group of a
degenerate propagator is not described** — the shape it should have, `∏ᵢ O(dᵢ)` over the
eigenvalue multiplicities, is on `UNLOCK_WATCHLIST` and nothing here approaches it.

**THE ROTATION IS NOT EXHIBITED.** `exists_rotation_symmetry_of_twin_pairs` is an existence
statement produced by the estate's Gram–Schmidt route at `(c, s) = (0, 1)`; **no matrix is written
down** and no order or angle is computed.

**NOTHING NEW ABOUT THE MACHINERY.** `FieldRotationCount` and `FieldEigenGramSchmidt` do all the
work; the only new content is the **input**, which is that twins supply the eigenpair. **The
composition is the unit**, and it is small.

**THE TREE IS NOT CLAIMED TO BE THE FIRST OR THE SMALLEST ANYWHERE.** It is the first **connected
non-lattice** graph in **this estate**, which is a statement about this estate and was got by
counting the files that state a rotation for a named graph — cycle, torus, box, and every
disconnected graph. **A disconnected graph is neither connected nor a lattice**, so the qualifier is
doing real work and is not decoration.

**NO WALL MOVES**, and in particular this says nothing about `OS1`: a symmetry of the **measure**
under an orthogonal matrix is not a Euclidean symmetry of anything, which `FieldTorusRotation`
already fenced.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **every statement in §§1 and 3 takes
`m ≠ 0`** and it is load-bearing in exactly one place — `m² > 0` is what keeps the propagator's
eigenvalue away from zero. §2 takes no mass, no graph and no `≠` at all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldTwinRotation

open SimpleGraph Matrix GraphLaplacian FieldRotationCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. From the Laplacian to the propagator -/

theorem massive_mulVec_of_lapMatrix_mulVec {x : V → ℝ} {ν : ℝ}
    (h : G.lapMatrix ℝ *ᵥ x = ν • x) : massive G m *ᵥ x = (ν + m ^ 2) • x := by
  have h1 := congrArg (fun L : (V → ℝ) →ₗ[ℝ] (V → ℝ) => L x)
    (FieldLaplacianSimple.toLin'_massive (G := G) m)
  simp only [Matrix.toLin'_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h1
  rw [h1, h, add_smul]

theorem green_mulVec_twinDiff (hm : m ≠ 0) {u v : V} (huv : u ≠ v)
    (hnb : G.neighborFinset u = G.neighborFinset v) :
    green G m *ᵥ CutTwins.twinDiff u v
      = ((G.degree u : ℝ) + m ^ 2)⁻¹ • CutTwins.twinDiff u v := by
  have hpos : (0 : ℝ) < (G.degree u : ℝ) + m ^ 2 := by
    have := pow_two_pos_of_ne_zero hm
    positivity
  exact FieldSignReflection.green_mulVec_of_massive_mulVec hm hpos.ne'
    (massive_mulVec_of_lapMatrix_mulVec (LaplacianTwins.lapMatrix_mulVec_twinDiff huv hnb))

/-! ## 2. Two twin pairs give two independent eigenvectors of the propagator -/

omit [Fintype V] [DecidableRel G.Adj] in
theorem twinDiff_not_smul {u v x y : V} (hxu : x ≠ u) (hxv : x ≠ v) :
    ∀ c : ℝ, CutTwins.twinDiff x y ≠ c • CutTwins.twinDiff u v := by
  intro c hc
  have h := congrFun hc x
  simp [CutTwins.twinDiff, hxu, hxv] at h

/-! ## 3. So the field has infinitely many symmetries, and a genuine rotation -/

/-- **A GRAPH WITH TWO TWIN PAIRS OF THE SAME DEGREE HAS INFINITELY MANY FIELD SYMMETRIES.** -/
theorem infinite_symmetryMatrices_of_twin_pairs (hm : m ≠ 0) {u v x y : V}
    (huv : u ≠ v) (hxy : x ≠ y)
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (hxu : x ≠ u) (hxv : x ≠ v) : (symmetryMatrices G m).Infinite := by
  have h2 := green_mulVec_twinDiff hm hxy hnb2
  rw [hdeg] at h2
  exact infinite_symmetryMatrices_of_independent_eigenpair hm
    (FieldCycleRotation.dotProduct_self_ne_zero CutTwins.twinDiff_ne_zero)
    (twinDiff_not_smul hxu hxv) (green_mulVec_twinDiff hm huv hnb1) h2

/-- **AND A GENUINE ROTATION OF THE GAUSSIAN FIELD**: an orthogonal matrix, not the identity,
whose isometry leaves the measure invariant. -/
theorem exists_rotation_symmetry_of_twin_pairs (hm : m ≠ 0) {u v x y : V}
    (huv : u ≠ v) (hxy : x ≠ y)
    (hnb1 : G.neighborFinset u = G.neighborFinset v)
    (hnb2 : G.neighborFinset x = G.neighborFinset y) (hdeg : G.degree x = G.degree u)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    ∃ (R : Matrix V V ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (FieldOrthIsometry.orthIsometry h) (gaussianField G m)
        = gaussianField G m := by
  have h2 := green_mulVec_twinDiff hm hxy hnb2
  rw [hdeg] at h2
  refine FieldEigenGramSchmidt.exists_rotation_symmetry_of_independent_eigenpair hm
    (FieldCycleRotation.dotProduct_self_ne_zero CutTwins.twinDiff_ne_zero)
    (twinDiff_not_smul hxu hxv) (green_mulVec_twinDiff hm huv hnb1) h2
    (c := 0) (s := 1) (by norm_num) one_ne_zero

/-! ## 4. So a tree can carry one -/

/-- **THE GAUSSIAN FIELD ON A TREE CAN HAVE INFINITELY MANY SYMMETRIES.**
`FieldTwinSpectrum.twinGraph` is a tree; its pendant pairs `{0, 1}` and `{3, 4}` are twins of
degree one. Every earlier **connected** graph carrying a rotation in this estate was a cycle, a
torus or a box; the disconnected case is
`FieldRotationInstance.exists_rotation_symmetry_of_not_reachable`. -/
theorem infinite_symmetryMatrices_twinGraph {mass : ℝ} (hmass : mass ≠ 0) :
    (symmetryMatrices FieldTwinSpectrum.twinGraph mass).Infinite :=
  infinite_symmetryMatrices_of_twin_pairs (u := 0) (v := 1) (x := 3) (y := 4) hmass
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end FieldTwinRotation
