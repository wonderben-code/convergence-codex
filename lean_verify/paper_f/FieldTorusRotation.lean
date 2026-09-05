import FieldRotationCount
import TorusEigenspaceLowerBound

/-!
# The torus in EVERY dimension, and the fence seven files carried

**Since `FieldCycleRotation` on 5 September, every file of this chain has ended with the same
sentence**: *not the torus in dimension `d > 1`; the higher-dimensional fibres are
`TorusFibreOrbitPartition`'s orbits and that composition is not made.* **Nine files carry it** — a
count, not an impression (`ERRATUM 450`), and the first draft of this paragraph said *seven*. **This
is the composition**, and it turned out to need no orbit bookkeeping at all.

**`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank` had already done the hard part**,
and **with no hypotheses**: the eigenspace of `νR k` on `torusGraph d (N+3)` has dimension at least
`2 ^ |interiorAxes k| · multinomial`. To get a degeneracy of two, all that is needed is **one
frequency with one interior axis**, and the all-ones frequency has every axis interior on every
torus, because a side length of at least three makes `2 · 1 ≠ N + 3`. The rest is
`FieldCycleRotation`'s argument unchanged.

**So the fence was not describing a difficulty.** It named the route it could see —
`TorusFibreOrbitPartition`'s orbits — and the estate's own bound had made that route unnecessary.
**That bound was added on 2026-08-31, five days before the fence was first written** — read from
`git log --diff-filter=A`, not recalled. `ERRATUM 458` is the entry; it is `ERRATUM 454`'s pattern
with the longest run yet, and the aggravation that the tool was already in the building.

## What is proved

**`oneFreq`, `interiorAxes_oneFreq`** — the all-ones frequency, and that every axis is interior for
it. One `omega` per axis: `0 < 1` and `2 · 1 ≠ N + 3`.

**`two_le_finrank_eigenspace_torus`** — hence `2 ≤ dim` of the `νR`-eigenspace at that frequency, on
**every** torus of dimension at least one, by `two_pow_mul_multinomial_le_finrank` against
`Nat.multinomial_pos`.

**`exists_independent_eigenpair_torus`** — two independent eigenvectors of `green`, through
`FieldCycleRotation.exists_independent_of_two_le_finrank` and
`FieldSignReflection.green_mulVec_of_massive_mulVec`, with `MassiveTorusSpectrum.sq_le_nuR` keeping
the eigenvalue away from zero.

**`exists_rotation_symmetry_torus`** — **so the torus carries a genuine rotation of the Gaussian
field at `m ≠ 0`, in every dimension `d ≥ 1`**: an orthogonal matrix, not the identity, commuting
with the propagator, whose isometry leaves the measure invariant.

**`infinite_symmetryMatrices_torus`** — and, through `FieldRotationCount`, **its symmetry group is
infinite**, in every dimension.

## What is NOT here

**NO EXACT COUNT ON THE TORUS**, and no analogue of `FieldLineCount`. The count here is
`Set.Infinite`, exactly as for the box in `d ≥ 2`. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**NOTHING ABOUT SIDE LENGTHS BELOW THREE.** `torusGraph d (N+3)` is the estate's torus and the
interior-axis argument uses `N + 3 ≥ 3` directly; sides one and two are not covered and are not
this estate's object.

**NO DESCRIPTION OF THE TORUS EIGENSPACES.** `two_pow_mul_multinomial_le_finrank` is a lower bound,
`TorusRealMultiplicity.finrank_eigenspace_massive_real` is the exact fibre count, and **this file
uses only the bound** — it says nothing about which frequencies share an eigenvalue.

**Only isometries**, inherited from `FieldInvarianceCommutes`.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A rotation
of the field on a torus in finite volume is a wider shadow of an axiom, not a smaller gap in it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`exists_independent_eigenpair_torus`, `exists_rotation_symmetry_torus` and
`infinite_symmetryMatrices_torus`; it is **not** taken by `oneFreq`, `interiorAxes_oneFreq` or
`two_le_finrank_eigenspace_torus`, which are about `massive` and hold at every mass. `1 ≤ d` is
taken by everything except `oneFreq` and `interiorAxes_oneFreq`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldTorusRotation

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection MassiveTorusSpectrum
open TorusReflectionCount TorusEigenspaceLowerBound
open FieldOrthIsometry FieldEigenGramSchmidt FieldCycleRotation FieldSignReflection
open FieldRotationCount

/-! ## 1. The all-ones frequency has every axis interior -/

/-- The frequency that is `1` along every axis. -/
def oneFreq (d N : ℕ) : Site d (N + 3) := fun _ => ⟨1, by omega⟩

theorem interiorAxes_oneFreq (d N : ℕ) : interiorAxes (oneFreq d N) = Finset.univ := by
  ext i
  simp only [mem_interiorAxes, Finset.mem_univ, iff_true, oneFreq]
  omega

/-! ## 2. So every torus has a degenerate eigenvalue -/

/-- **THE DEGENERACY, ON EVERY TORUS OF DIMENSION AT LEAST ONE**, from the estate's own
hypothesis-free lower bound. -/
theorem two_le_finrank_eigenspace_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (m : ℝ) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m)
        - (nuR N m (oneFreq d N)) • LinearMap.id)) := by
  classical
  have hbound := two_pow_mul_multinomial_le_finrank (d := d) N m (oneFreq d N)
  rw [interiorAxes_oneFreq, Finset.card_univ, Fintype.card_fin] at hbound
  refine le_trans ?_ hbound
  have hpow : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  exact le_trans hpow (Nat.le_mul_of_pos_right _ (Nat.multinomial_pos _ _))

/-! ## 3. Hence a rotation, in every dimension -/

/-- **TWO INDEPENDENT EIGENVECTORS OF THE PROPAGATOR ON THE TORUS**, in every dimension. -/
theorem exists_independent_eigenpair_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) {m : ℝ} (hm : m ≠ 0) :
    ∃ u v : Site d (N + 3) → ℝ, u ⬝ᵥ u ≠ 0 ∧ (∀ c : ℝ, v ≠ c • u) ∧
      green (torusGraph d (N + 3)) m *ᵥ u = (nuR N m (oneFreq d N))⁻¹ • u ∧
      green (torusGraph d (N + 3)) m *ᵥ v = (nuR N m (oneFreq d N))⁻¹ • v := by
  obtain ⟨u, huW, v, hvW, hu0, hind⟩ :=
    exists_independent_of_two_le_finrank (two_le_finrank_eigenspace_torus hd N m)
  have hnu : nuR N m (oneFreq d N) ≠ 0 := by
    have hle := sq_le_nuR N m (oneFreq d N)
    have hpos : (0 : ℝ) < m ^ 2 := by positivity
    linarith
  refine ⟨u, v, dotProduct_self_ne_zero hu0, hind, ?_, ?_⟩
  · exact green_mulVec_of_massive_mulVec hm hnu ((mem_eigenspace_iff_mulVec _ _ _).mp huW)
  · exact green_mulVec_of_massive_mulVec hm hnu ((mem_eigenspace_iff_mulVec _ _ _).mp hvW)

/-- **THE TORUS CARRIES A GENUINE ROTATION OF THE GAUSSIAN FIELD, IN EVERY DIMENSION `d ≥ 1`.** -/
theorem exists_rotation_symmetry_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) {m : ℝ} (hm : m ≠ 0)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix (Site d (N + 3)) (Site d (N + 3)) ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (orthIsometry h) (gaussianField (torusGraph d (N + 3)) m)
        = gaussianField (torusGraph d (N + 3)) m := by
  obtain ⟨u, v, hu0, hind, hu, hv⟩ := exists_independent_eigenpair_torus hd N hm
  exact exists_rotation_symmetry_of_independent_eigenpair hm hu0 hind hu hv hcs hs

/-- **AND ITS SYMMETRY GROUP IS INFINITE.** -/
theorem infinite_symmetryMatrices_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) {m : ℝ} (hm : m ≠ 0) :
    (symmetryMatrices (torusGraph d (N + 3)) m).Infinite := by
  obtain ⟨u, v, hu0, hind, hu, hv⟩ := exists_independent_eigenpair_torus hd N hm
  exact infinite_symmetryMatrices_of_independent_eigenpair hm hu0 hind hu hv

end FieldTorusRotation
