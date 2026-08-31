import TorusReflectionCount

/-!
# Reflections are not all the collisions, and neither are signed permutations

Every multiplicity result in the torus chain has carried one fence, in these words
(`TorusReflectionCount`):

> Whether two frequencies that are **not** reflections of one another can share an eigenvalue at
> `d ≥ 2` is exactly the question the ring's biconditional settles in one dimension, and **nothing
> settles it in any other**.

**They can, and the reason is visible once it is looked for.** `νR` is a *sum over axes* of a
function of one coordinate, so it does not see the order of the axes at all.

> **`nuR_comp_perm`** — `νR (k ∘ σ) = νR k` for every permutation `σ` of the axes, in every
> dimension and at every side length. One reindexing of a finite sum; there is no analysis in it.
>
> **`swap_ne_reflectAxes` / `nuR_swap_eq`** — hence at `d = 2` and side at least four the
> frequencies `(1, 2)` and `(2, 1)` share an eigenvalue, and `(2, 1)` is **not** `reflectAxes S`
> applied to `(1, 2)` for any `S`. **The fence is answered: reflections are not all of them.**

## And signed permutations are not all of them either

Adjoining the permutations to the reflections gives the signed-permutation group, of order
`2^d · d!`, and the natural guess is that it is the whole story. **It is not**, and the smallest
witness is small enough to check by hand.

> **`sporadic_nuR_eq`** — at `d = 2` and side `12`, the frequencies `(2, 3)` and `(0, 4)` have the
> same eigenvalue: `cos(π/3) + cos(π/2) = ½ + 0` and `cos 0 + cos(2π/3) = 1 − ½`.
>
> **`sporadic_ne_signed_perm`** — and `(0, 4)` is not `reflectAxes S (2, 3) ∘ σ` for any `S` and any
> `σ`. The eight images all have first coordinate in `{2, 3, 9, 10}` and this one has `0`.

So the collision group at `d ≥ 2` strictly contains the signed permutations, and the arithmetic of
which cosine sums agree is not a symmetry question at all.

## What is NOT here

**No upper bound on any multiplicity, in any dimension above one.** This makes the fence's answer
negative; it does not replace it with a count. `TorusReflectionCount`'s `2^s` is still the only
lower bound and there is still no upper one, and **the cost of getting one is not estimated**
(`ERRATUM 194`, `ERRATUM 246`).

**No group is constructed.** `nuR_comp_perm` is an invariance statement about a function, not an
action on frequencies bundled as a `MulAction`; nothing in this estate consumes such a carrier,
which is `LovelockReduction` §1's reason for not building one.

**Nothing about which sporadic collisions exist.** One witness is exhibited at one side length. It
is not claimed to be the smallest, and no family is offered.

**The eigenvalues are `νR`'s, not a graph's.** Transporting to `torusGraph` is
`MassiveTorusSpectrum.spectrum_real_eq_range_nuR`, which is **not applied below**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusNonReflectionCollision

open Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusReflectionCount

variable {d : ℕ}

/-! ## 1. The eigenvalue does not see the order of the axes -/

/-- **`νR` IS INVARIANT UNDER PERMUTING THE AXES.** `νR` is a sum over `Fin d` of a function of one
coordinate, and a permutation reindexes that sum. No analysis, in any dimension. -/
theorem nuR_comp_perm (N : ℕ) (m : ℝ) (k : Site d (N + 3)) (σ : Equiv.Perm (Fin d)) :
    nuR N m (k ∘ σ) = nuR N m k := by
  simp only [nuR]
  congr 1
  exact Equiv.sum_comp σ (fun i => 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)))

/-! ## 2. So at `d = 2` there is a collision that is not a reflection -/

/-- The frequency `(1, 2)`, at any side length at least four. -/
def base (N : ℕ) : Site 2 (N + 1 + 3) := ![⟨1, by omega⟩, ⟨2, by omega⟩]

/-- **THE TRANSPOSED FREQUENCY HAS THE SAME EIGENVALUE.** `Equiv.swap 0 1` is a permutation. -/
theorem nuR_swap_eq (N : ℕ) (m : ℝ) :
    nuR (N + 1) m (base N ∘ Equiv.swap 0 1) = nuR (N + 1) m (base N) :=
  nuR_comp_perm (N + 1) m (base N) (Equiv.swap 0 1)

/-- **AND IT IS NOT A REFLECTION OF IT.** The first coordinate decides it on its own: the transposed
frequency has `2` there, and `reflectAxes S (1, 2)` has either `1` or `N + 3`, neither of which is
`2` at any side length at least four. -/
theorem swap_ne_reflectAxes (N : ℕ) (S : Finset (Fin 2)) :
    base N ∘ Equiv.swap 0 1 ≠ reflectAxes S (base N) := by
  intro h
  have hb0 : (base N (0 : Fin 2)).val = 1 := by simp [base]
  have h0 : ((base N ∘ Equiv.swap 0 1) (0 : Fin 2)).val
      = ((reflectAxes S (base N)) (0 : Fin 2)).val := congrArg Fin.val (congrFun h 0)
  have hval : ((base N ∘ Equiv.swap 0 1) (0 : Fin 2)).val = 2 := by
    simp [base, Function.comp, Equiv.swap_apply_left]
  rw [hval] at h0
  by_cases hS : (0 : Fin 2) ∈ S
  · rw [reflectAxes_val_of_mem hS, hb0, Nat.mod_eq_of_lt (by omega)] at h0
    omega
  · rw [reflectAxes_of_not_mem hS] at h0
    simp [base] at h0

/-! ## 3. And a collision outside the signed permutations -/

/-- The frequency `(2, 3)` at side `12`. -/
def spA : Site 2 (9 + 3) := ![⟨2, by omega⟩, ⟨3, by omega⟩]

/-- The frequency `(0, 4)` at side `12`. -/
def spB : Site 2 (9 + 3) := ![⟨0, by omega⟩, ⟨4, by omega⟩]

/-- **A COLLISION THE SIGNED PERMUTATIONS DO NOT EXPLAIN.** `cos(π/3) + cos(π/2) = ½ + 0` and
`cos 0 + cos(2π/3) = 1 − ½`. -/
theorem sporadic_nuR_eq (m : ℝ) : nuR 9 m spA = nuR 9 m spB := by
  have e2 : (2 : ℝ) * Real.pi * 2 / 12 = Real.pi / 3 := by ring
  have e3 : (2 : ℝ) * Real.pi * 3 / 12 = Real.pi / 2 := by ring
  have e4 : (2 : ℝ) * Real.pi * 4 / 12 = Real.pi - Real.pi / 3 := by ring
  simp only [nuR, Fin.sum_univ_two, spA, spB, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  rw [e2, e3, e4, Real.cos_pi_sub, Real.cos_pi_div_three, Real.cos_pi_div_two]
  ring

/-- **AND IT IS NOT A SIGNED PERMUTATION OF IT.** The first coordinate again: every
`reflectAxes S (2, 3) ∘ σ` has `2`, `3`, `9` or `10` there, and `(0, 4)` has `0`. -/
theorem sporadic_ne_signed_perm (S : Finset (Fin 2)) (σ : Equiv.Perm (Fin 2)) :
    spB ≠ reflectAxes S spA ∘ σ := by
  intro h
  have h0 := congrFun h 0
  have hB : (spB (0 : Fin 2)).val = 0 := by simp [spB]
  have hA : ∀ j : Fin 2, (spA j).val = 2 ∨ (spA j).val = 3 := by
    intro j; fin_cases j <;> simp [spA]
  have hval : ((reflectAxes S spA ∘ σ) (0 : Fin 2)).val ≠ 0 := by
    by_cases hS : σ (0 : Fin 2) ∈ S
    · have := reflectAxes_val_of_mem (N := 9) (S := S) (k := spA) hS
      simp only [Function.comp]
      rw [this]
      rcases hA (σ 0) with hh | hh <;> rw [hh] <;> decide
    · have := reflectAxes_of_not_mem (N := 9) (S := S) (k := spA) hS
      simp only [Function.comp]
      rw [this]
      rcases hA (σ 0) with hh | hh <;> omega
  rw [← h0, hB] at hval
  exact hval rfl

end TorusNonReflectionCollision
