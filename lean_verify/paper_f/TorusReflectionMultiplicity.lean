import CycleMultiplicityCount

/-!
# Every interior eigenvalue is degenerate, in every dimension

`CycleMultiplicity` and `CycleMultiplicityCount` settled the ring completely and left the same fence
twice over:

> **One dimension only.** At `d ≥ 2` the question is which multisets of `d` cosines have equal sums,
> which is a genuinely different problem — reflections in each axis independently are *some* of the
> collisions and **nothing here says they are all of them**.

That sentence names a positive fact and declines to prove it. **The positive fact is proved here**:
reflecting a single axis leaves the eigenvalue alone, in every dimension, so **every interior
eigenvalue of the massive Laplacian on the periodic lattice is degenerate.** What stays open is the
converse — whether reflections are *all* the collisions — and that is untouched.

> **`reflectAxis`** — mirror one coordinate, `kᵢ ↦ n − kᵢ` reduced mod `n`, leaving the others. The
> reduction is what makes it total, exactly as in `CycleMultiplicityCount.mirrorFreq`.
>
> **`nuR_reflectAxis`** — `νR` is unchanged. Each axis contributes its own cosine and only the
> mirrored one moves, by the same cosine identity the ring used.
>
> **`two_le_finrank_eigenspace_of_interior`** — so if **any** axis of `k` is interior — not `0`, not
> the halfway frequency — the real eigenspace at `νR k` has dimension **at least two**, in every
> dimension and at every side length at least three.

## What is NOT here

**This is a lower bound and only a lower bound.** At `d ≥ 2` a frequency with `s` interior axes has
`2^s` reflections and they are all distinct, so the true bound is `2^s`; **that is not proved
below**, because it needs the map from subsets of axes to frequencies exhibited and shown injective,
and the theorem below uses one axis. **No cost is claimed** (`ERRATUM 246`).

**And it is not an upper bound at all.** Whether two frequencies that are *not* reflections of one
another can share an eigenvalue at `d ≥ 2` is exactly the question the ring's biconditional answered
in one dimension, and **nothing here answers it in any other**. That is the real content of the
fence this file narrows, and it survives.

**No eigenvectors.** As throughout the chain, dimensions and not bases.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusReflectionMultiplicity

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity CycleMultiplicity

variable {d : ℕ}

/-- **MIRROR ONE AXIS.** `kᵢ ↦ n − kᵢ` reduced mod `n`, the other coordinates untouched. The
reduction makes the map total and fixes `0`, which is right — `0` is its own reflection. -/
def reflectAxis {N : ℕ} (i : Fin d) (k : Site d (N + 3)) : Site d (N + 3) :=
  Function.update k i ⟨(N + 3 - (k i).val) % (N + 3), Nat.mod_lt _ (by omega)⟩

@[simp] theorem reflectAxis_apply_ne {N : ℕ} (i : Fin d) (k : Site d (N + 3)) {j : Fin d}
    (hj : j ≠ i) : (reflectAxis i k) j = k j :=
  Function.update_of_ne hj _ _

theorem reflectAxis_val {N : ℕ} (i : Fin d) (k : Site d (N + 3)) :
    ((reflectAxis i k) i).val = (N + 3 - (k i).val) % (N + 3) := by
  rw [reflectAxis, Function.update_self]

/-- **THE MIRRORED COORDINATE HAS THE SAME COSINE.** The one analytic fact behind every reflection
statement in this chain, extracted so the multi-axis version does not repeat it (`ERRATUM 337`). -/
theorem cos_mirror_eq (N : ℕ) (a : Fin (N + 3)) :
    Real.cos (2 * Real.pi * (((N + 3 - a.val) % (N + 3) : ℕ) : ℝ) / ((N : ℝ) + 3))
      = Real.cos (2 * Real.pi * a.val / ((N : ℝ) + 3)) := by
  have hn : 0 < N + 3 := by omega
  have hcast : ((N : ℝ) + 3) = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hlt : (N + 3 - a.val) % (N + 3) < N + 3 := Nat.mod_lt _ hn
  have hkey : Real.cos (2 * Real.pi * (((N + 3 - a.val) % (N + 3) : ℕ) : ℝ) / ((N + 3 : ℕ) : ℝ))
      = Real.cos (2 * Real.pi * a.val / ((N + 3 : ℕ) : ℝ)) := by
    refine (cos_angle_eq_iff hn hlt a.isLt).2 ?_
    rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · left
      rw [h0]
      simp
    · right
      rw [Nat.mod_eq_of_lt (by omega)]
      have := a.isLt
      omega
  rw [← hcast] at hkey
  exact hkey

/-- **REFLECTING AN AXIS DOES NOT MOVE THE EIGENVALUE.** Every axis contributes its own cosine and
only the mirrored one changes; the ring's identity says that cosine is the same. -/
theorem nuR_reflectAxis (N : ℕ) (m : ℝ) (i : Fin d) (k : Site d (N + 3)) :
    nuR N m (reflectAxis i k) = nuR N m k := by
  have hn : 0 < N + 3 := by omega
  have hcast : ((N : ℝ) + 3) = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hterm : ∀ j : Fin d,
      2 * Real.cos (2 * Real.pi * ((reflectAxis i k) j).val / ((N : ℝ) + 3))
        = 2 * Real.cos (2 * Real.pi * (k j).val / ((N : ℝ) + 3)) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [reflectAxis_val, cos_mirror_eq]
    · rw [reflectAxis_apply_ne i k hj]
  rw [nuR, nuR, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j]

/-- At an interior axis the reflection really moves the frequency. -/
theorem ne_reflectAxis {N : ℕ} (i : Fin d) (k : Site d (N + 3))
    (hk0 : 0 < (k i).val) (hkhalf : 2 * (k i).val ≠ N + 3) : reflectAxis i k ≠ k := by
  intro h
  have h2 := congrArg (fun j : Site d (N + 3) => (j i).val) h
  simp only at h2
  rw [reflectAxis_val, Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- **SO EVERY INTERIOR EIGENVALUE IS DEGENERATE, IN EVERY DIMENSION.** If any one axis of `k` is
neither `0` nor the halfway frequency, the real eigenspace at `νR k` is at least two dimensional. -/
theorem two_le_finrank_eigenspace_of_interior (N : ℕ) (m : ℝ) (i : Fin d) (k : Site d (N + 3))
    (hk0 : 0 < (k i).val) (hkhalf : 2 * (k i).val ≠ N + 3) :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_massive_real N m (nuR N m k)]
  have hcoe : Nat.card {k' : Site d (N + 3) // nuR N m k' = nuR N m k}
      = Set.ncard {k' : Site d (N + 3) | nuR N m k' = nuR N m k} :=
    Nat.card_coe_set_eq _
  rw [hcoe]
  have hsub : ({k, reflectAxis i k} : Set (Site d (N + 3)))
      ⊆ {k' : Site d (N + 3) | nuR N m k' = nuR N m k} := by
    rintro x (rfl | rfl)
    · exact rfl
    · exact nuR_reflectAxis N m i k
  have hpair : Set.ncard ({k, reflectAxis i k} : Set (Site d (N + 3))) = 2 :=
    Set.ncard_pair (Ne.symm (ne_reflectAxis i k hk0 hkhalf))
  calc (2 : ℕ) = Set.ncard ({k, reflectAxis i k} : Set (Site d (N + 3))) := hpair.symm
    _ ≤ Set.ncard {k' : Site d (N + 3) | nuR N m k' = nuR N m k} :=
        Set.ncard_le_ncard hsub (Set.toFinite _)

end TorusReflectionMultiplicity
