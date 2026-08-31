import TorusReflectionMultiplicity

/-!
# `2^s`: the degeneracy grows with the number of interior axes

`TorusReflectionMultiplicity` proved that mirroring **one** axis leaves the eigenvalue alone, hence
that every interior eigenvalue is degenerate in every dimension, and drew its own fence:

> **This is a lower bound and only a lower bound.** A frequency with `s` interior axes has `2^s`
> reflections and they are all distinct, so the true bound is `2^s`; **that is not proved below**,
> because it needs the map from subsets of axes to frequencies exhibited and shown injective.

`PROOF_STRATEGY` §3 again: the fence was a scoping decision and the map is the whole of the work.

> **`reflectAxes`** — mirror every axis in a `Finset`, the others untouched. The one-axis version is
> its singleton case in spirit, though the two are kept separate: `reflectAxis` uses
> `Function.update` and is the shape a caller with one axis wants.
>
> **`nuR_reflectAxes`** — `νR` is unchanged, term by term, on
> `TorusReflectionMultiplicity.cos_mirror_eq` — the one analytic fact, extracted there for exactly
> this reuse.
>
> **`interiorAxes`** — the axes that are neither at rest nor halfway, as a `Finset`.
>
> **`reflectAxes_injOn`** — distinct subsets of the interior axes give distinct frequencies. This is
> where interiority is used and it is used exactly once: at an axis in one subset and not the other,
> the two frequencies would have to satisfy `n − kᵢ = kᵢ`.
>
> **`pow_two_le_finrank_eigenspace`** — hence `2^s ≤ dim`, with `s` the number of interior axes, in
> every dimension and at every side length at least three.

## What is NOT here

**It is still not an upper bound**, and that is unchanged from the previous unit and is the fence
that matters. Whether two frequencies that are **not** reflections of one another can share an
eigenvalue at `d ≥ 2` is exactly the question the ring's biconditional settles in one dimension, and
**nothing settles it in any other**.

**^ SOMETHING SETTLES IT NOW, 2026-08-31, AND THE ANSWER IS YES; THE SENTENCE IS KEPT**
(`ERRATUM 94`, `ERRATUM 371`). `TorusNonReflectionCollision` proves `νR` invariant under permuting
the axes — one reindexing of a finite sum — so at `d = 2` and side at least four `(1, 2)` and
`(2, 1)` collide with `(2, 1)` outside every `reflectAxes S`; and at side `12` the pair `(2, 3)`,
`(0, 4)` collides outside the signed permutations entirely. **The `2^s` below is unaffected**: it
was a lower bound and it stays one, and what this closes is the question of whether it could ever
have been sharp above one dimension. It could not. **No upper bound is proved at `d ≥ 2` and none
is estimated** (`ERRATUM 246`). At `d = 1` the bound here is `2^1 = 2` at an interior frequency
and `CycleMultiplicityCount` shows that is exact; **no such statement is available above one
dimension**, and none is guessed at (`ERRATUM 194`, `ERRATUM 246`).

**No eigenvectors.** Dimensions and not bases, as throughout the chain.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusReflectionCount

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusReflectionMultiplicity

variable {d : ℕ}

/-- **MIRROR EVERY AXIS IN `S`.** -/
def reflectAxes {N : ℕ} (S : Finset (Fin d)) (k : Site d (N + 3)) : Site d (N + 3) :=
  fun j => if j ∈ S then ⟨(N + 3 - (k j).val) % (N + 3), Nat.mod_lt _ (by omega)⟩ else k j

theorem reflectAxes_val_of_mem {N : ℕ} {S : Finset (Fin d)} {k : Site d (N + 3)} {j : Fin d}
    (hj : j ∈ S) : ((reflectAxes S k) j).val = (N + 3 - (k j).val) % (N + 3) := by
  simp [reflectAxes, hj]

theorem reflectAxes_of_not_mem {N : ℕ} {S : Finset (Fin d)} {k : Site d (N + 3)} {j : Fin d}
    (hj : j ∉ S) : (reflectAxes S k) j = k j := by
  simp [reflectAxes, hj]

/-- **MIRRORING ANY SET OF AXES LEAVES THE EIGENVALUE ALONE.** Term by term, on the single analytic
fact `cos_mirror_eq`. -/
theorem nuR_reflectAxes (N : ℕ) (m : ℝ) (S : Finset (Fin d)) (k : Site d (N + 3)) :
    nuR N m (reflectAxes S k) = nuR N m k := by
  have hterm : ∀ j : Fin d,
      2 * Real.cos (2 * Real.pi * ((reflectAxes S k) j).val / ((N : ℝ) + 3))
        = 2 * Real.cos (2 * Real.pi * (k j).val / ((N : ℝ) + 3)) := by
    intro j
    by_cases hj : j ∈ S
    · rw [reflectAxes_val_of_mem hj, cos_mirror_eq]
    · rw [reflectAxes_of_not_mem hj]
  rw [nuR, nuR, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j]

/-- **THE AXES THAT ARE NEITHER AT REST NOR HALFWAY.** -/
noncomputable def interiorAxes {N : ℕ} (k : Site d (N + 3)) : Finset (Fin d) :=
  open scoped Classical in
  Finset.univ.filter fun i => 0 < (k i).val ∧ 2 * (k i).val ≠ N + 3

theorem mem_interiorAxes {N : ℕ} {k : Site d (N + 3)} {i : Fin d} :
    i ∈ interiorAxes k ↔ 0 < (k i).val ∧ 2 * (k i).val ≠ N + 3 := by
  classical
  simp [interiorAxes]

/-- **DISTINCT SUBSETS OF THE INTERIOR AXES GIVE DISTINCT FREQUENCIES.** Interiority is used here
and only here: at an axis in one subset and not the other, equality would force `n − kᵢ = kᵢ`. -/
theorem reflectAxes_injOn {N : ℕ} (k : Site d (N + 3)) :
    Set.InjOn (fun S : Finset (Fin d) => reflectAxes S k)
      ((interiorAxes k).powerset : Set (Finset (Fin d))) := by
  intro S hS T hT hST
  have hSsub : S ⊆ interiorAxes k := Finset.mem_powerset.1 (by simpa using hS)
  have hTsub : T ⊆ interiorAxes k := Finset.mem_powerset.1 (by simpa using hT)
  have hST' : reflectAxes S k = reflectAxes T k := hST
  have hcoord : ∀ i : Fin d, (reflectAxes S k) i = (reflectAxes T k) i :=
    fun i => congrFun hST' i
  ext i
  have hlt := (k i).isLt
  constructor
  · intro hi
    by_contra hiT
    have hint := mem_interiorAxes.1 (hSsub hi)
    have h1 : ((reflectAxes S k) i).val = (N + 3 - (k i).val) % (N + 3) :=
      reflectAxes_val_of_mem hi
    have h2 : (reflectAxes T k) i = k i := reflectAxes_of_not_mem hiT
    rw [hcoord i, h2, Nat.mod_eq_of_lt (by omega)] at h1
    omega
  · intro hiT
    by_contra hi
    have hint := mem_interiorAxes.1 (hTsub hiT)
    have h1 : ((reflectAxes T k) i).val = (N + 3 - (k i).val) % (N + 3) :=
      reflectAxes_val_of_mem hiT
    have h2 : (reflectAxes S k) i = k i := reflectAxes_of_not_mem hi
    rw [← hcoord i, h2, Nat.mod_eq_of_lt (by omega)] at h1
    omega

/-- **SO THE DEGENERACY IS AT LEAST `2^s`**, with `s` the number of interior axes — in every
dimension and at every side length at least three. -/
theorem pow_two_le_finrank_eigenspace (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    2 ^ (interiorAxes k).card ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_massive_real N m (nuR N m k)]
  have hcard : Nat.card {k' : Site d (N + 3) // nuR N m k' = nuR N m k}
      = (Finset.univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  have himg : ((interiorAxes k).powerset.image fun S => reflectAxes S k)
      ⊆ Finset.univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k := by
    intro x hx
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact nuR_reflectAxes N m S k
  have hcount : ((interiorAxes k).powerset.image fun S => reflectAxes S k).card
      = 2 ^ (interiorAxes k).card := by
    rw [Finset.card_image_of_injOn (reflectAxes_injOn k), Finset.card_powerset]
  calc 2 ^ (interiorAxes k).card
      = ((interiorAxes k).powerset.image fun S => reflectAxes S k).card := hcount.symm
    _ ≤ (Finset.univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k).card :=
        Finset.card_le_card himg

end TorusReflectionCount
