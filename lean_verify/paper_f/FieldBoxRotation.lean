import FieldCycleRotation
import BoxEigenspaceDimension
import BoxLapMultiplicity

/-!
# A rotation of the field on the BOX — the graph the OS programme uses

`FieldCycleRotation` put a rotation on the connected cycle and named two compositions it did not
make. **This is one of them**, and it is the one that matters: `boxGraph d n` at `d = 4` is the
finite volume every reflection-positivity result in this estate is stated on.

**The degeneracy is free on a box of dimension at least two.**
`BoxLapMultiplicity.boxLapEig_comp_perm` says permuting the axes does not move the eigenvalue, so a
frequency with two **different** coordinates and its swap are two distinct points of one fibre;
`BoxEigenspaceDimension.finrank_eigenspace_massive_box` turns a fibre of size at least two into an
eigenspace of dimension at least two; and `FieldEigenGramSchmidt` turns that into a rotation.

`PROOF_STRATEGY` §6 question 1 — *what did the last unit unlock* — answered by the general lemma it
left behind: `FieldCycleRotation.exists_independent_of_two_le_finrank` mentions no graph.

## What is proved

**`boxLapEig_nonneg`** — the free-boundary Laplacian's eigenvalues are `≥ 0`, one `Real.cos_le_one`
per axis, so the massive eigenvalue is `≥ mass²` and away from zero.

**`two_le_finrank_eigenspace_box`** — at a frequency with two distinct coordinates the massive
eigenspace has dimension at least two, the second point being the frequency with those coordinates
swapped.

**`exists_independent_eigenpair_box`** — hence two independent eigenvectors of `green` there.

**`exists_rotation_symmetry_box`** — **so `boxGraph d n` carries a genuine rotation of the Gaussian
field, at `m ≠ 0`**, whenever some frequency has two distinct coordinates: an orthogonal matrix,
not the identity, commuting with the propagator, whose isometry leaves the measure invariant.
**The mass hypothesis is part of the claim** — at `m = 0` the field is a point mass that every
isometry preserves, on every graph and in every dimension (`FieldMassNecessity`, `ERRATUM 455`).

**`exists_rotation_symmetry_box_of_two_le`** — and that hypothesis is met at every `2 ≤ d` and
`2 ≤ n`, which includes `d = 4`.

## What is NOT here

**No wall moves, and the box being the physical volume does not change that.** `W1`'s open part is
`OS0` and `OS4`, and `OS1` in its continuum sense. A finite-volume symmetry group that is larger
than anyone had shown is **a wider shadow of an axiom, not a smaller gap in it** — the sentence
`FieldAutInvariance`'s header puts in capitals, which every file in this chain repeats and which is
worth repeating hardest here, where the graph is the one the physics uses.

**Nothing about the torus at `d > 1`**, the other composition `FieldCycleRotation` named: its
degeneracies are `TorusFibreOrbitPartition`'s orbits and that route is still not taken. **Not
attempted, no cost claimed** (`ERRATUM 246`).

**No description of the commutant**, and no count of the rotations.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldBoxRotation

open Matrix GraphLaplacian SimpleGraph BoxGraph BoxLapSpectrum BoxEigenspaceDimension
open FieldOrthIsometry FieldEigenGramSchmidt FieldCycleRotation FieldSignReflection
open PathLapSpectrum

/-! ## 1. The eigenvalue is away from zero -/

theorem boxLapEig_nonneg (d n : ℕ) (k : Fin d → ℕ) : 0 ≤ boxLapEig d n k := by
  rw [boxLapEig]
  refine Finset.sum_nonneg fun i _ => ?_
  have := Real.cos_le_one (2 * half n (k i))
  linarith

/-! ## 2. Two distinct coordinates give a two-dimensional eigenspace -/

/-- **A FREQUENCY WITH TWO DIFFERENT COORDINATES SHARES ITS EIGENVALUE WITH ITS SWAP.** -/
theorem two_le_finrank_eigenspace_box (d m : ℕ) (mass : ℝ) (k : Site d (m + 1)) {i j : Fin d}
    (hk : k i ≠ k j) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (boxGraph d (m + 1)) mass)
        - (boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_massive_box]
  have hswap : (fun a => ((k ∘ Equiv.swap i j) a).val)
      = (fun a => (k a).val) ∘ Equiv.swap i j := rfl
  have hmem : boxLapEig d (m + 1) (fun a => ((k ∘ Equiv.swap i j) a).val) + mass ^ 2
      = boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2 := by
    rw [hswap, BoxLapMultiplicity.boxLapEig_comp_perm]
  have hne : (k ∘ Equiv.swap i j) ≠ k := by
    intro hcontra
    have := congrFun hcontra i
    simp only [Function.comp_apply, Equiv.swap_apply_left] at this
    exact hk this.symm
  have : Nontrivial {l : Site d (m + 1) //
      boxLapEig d (m + 1) (fun a => (l a).val) + mass ^ 2
        = boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2} :=
    ⟨⟨⟨k, rfl⟩, ⟨k ∘ Equiv.swap i j, hmem⟩, by simpa using fun h => hne h.symm⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr this

/-! ## 3. So the box carries a rotation -/

/-- **TWO INDEPENDENT EIGENVECTORS OF THE PROPAGATOR ON THE BOX.** -/
theorem exists_independent_eigenpair_box (d m : ℕ) {mass : ℝ} (hmass : mass ≠ 0)
    (k : Site d (m + 1)) {i j : Fin d} (hk : k i ≠ k j) :
    ∃ u v : Site d (m + 1) → ℝ, u ⬝ᵥ u ≠ 0 ∧ (∀ c : ℝ, v ≠ c • u) ∧
      green (boxGraph d (m + 1)) mass *ᵥ u
        = (boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2)⁻¹ • u ∧
      green (boxGraph d (m + 1)) mass *ᵥ v
        = (boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2)⁻¹ • v := by
  obtain ⟨u, huW, v, hvW, hu0, hind⟩ :=
    exists_independent_of_two_le_finrank (two_le_finrank_eigenspace_box d m mass k hk)
  have hmu : boxLapEig d (m + 1) (fun a => (k a).val) + mass ^ 2 ≠ 0 := by
    have h1 := boxLapEig_nonneg d (m + 1) (fun a => (k a).val)
    have h2 : (0 : ℝ) < mass ^ 2 := by positivity
    linarith
  refine ⟨u, v, dotProduct_self_ne_zero hu0, hind, ?_, ?_⟩
  · exact green_mulVec_of_massive_mulVec hmass hmu ((mem_eigenspace_iff_mulVec _ _ _).mp huW)
  · exact green_mulVec_of_massive_mulVec hmass hmu ((mem_eigenspace_iff_mulVec _ _ _).mp hvW)

/-- **THE BOX CARRIES A GENUINE ROTATION OF THE GAUSSIAN FIELD** whenever some frequency has two
distinct coordinates. -/
theorem exists_rotation_symmetry_box (d m : ℕ) {mass : ℝ} (hmass : mass ≠ 0)
    (k : Site d (m + 1)) {i j : Fin d} (hk : k i ≠ k j)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h) (gaussianField (boxGraph d (m + 1)) mass)
        = gaussianField (boxGraph d (m + 1)) mass := by
  obtain ⟨u, v, hu0, hind, hu, hv⟩ := exists_independent_eigenpair_box d m hmass k hk
  exact exists_rotation_symmetry_of_independent_eigenpair hmass hu0 hind hu hv hcs hs

/-- **AND THE HYPOTHESIS IS MET AT EVERY `2 ≤ d` AND EVERY SIDE LENGTH `≥ 2`**, which includes the
physical `d = 4`. -/
theorem exists_rotation_symmetry_box_of_two_le {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) {mass : ℝ}
    (hmass : mass ≠ 0) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix (Site d (m + 1)) (Site d (m + 1)) ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h) (gaussianField (boxGraph d (m + 1)) mass)
        = gaussianField (boxGraph d (m + 1)) mass := by
  classical
  set i : Fin d := ⟨0, by omega⟩ with hi
  set j : Fin d := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [hi, hj])
  set a0 : Fin (m + 1) := ⟨0, by omega⟩ with ha0
  set a1 : Fin (m + 1) := ⟨1, by omega⟩ with ha1
  set k : Site d (m + 1) := fun b => if b = i then a0 else a1 with hk
  have hki : k i = a0 := by simp [hk]
  have hkj : k j = a1 := by simp [hk, hij.symm]
  have hne : k i ≠ k j := by
    rw [hki, hkj]
    intro h
    exact absurd (congrArg Fin.val h) (by simp [ha0, ha1])
  exact exists_rotation_symmetry_box d m hmass k hne hcs hs


end FieldBoxRotation
