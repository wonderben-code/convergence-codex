import CycleMultiplicity

/-!
# The count: every interior eigenvalue of the ring has multiplicity exactly two

`CycleMultiplicity` settled **which** frequencies of the ring share an eigenvalue — they agree or
they reflect — and drew its own fence around what that is not:

> **The count itself is not taken.** Turning the biconditional into
> `Nat.card {k' // νR k' = νR k} = 2` needs the reflected frequency exhibited as an object and shown
> distinct from `k`, and **that is not done below**.

`PROOF_STRATEGY` §3 — *the moment `B` lands, immediately re-attempt `B → C`* — and the fence was a
scoping decision for one unit rather than a refusal. The object and the distinctness are here, and
they are the whole of it.

> **`mirrorFreq`** — the reflected frequency `n − k`, as a `Site 1 n` rather than as an arithmetic
> condition.
>
> **`fibre_eq_pair`** — at an **interior** frequency (not `0`, not the halfway one) the set of
> frequencies sharing its eigenvalue is exactly `{k, mirrorFreq k}`, and the two are distinct.
>
> **`card_fibre_eq_two`, `finrank_eigenspace_interior_eq_two`** — so the fibre has two elements, and
> by `TorusRealMultiplicity.finrank_eigenspace_massive_real` **the real eigenspace of the massive
> Laplacian at an interior eigenvalue of the ring is two dimensional.** That is the first
> multiplicity *number* in this estate at an eigenvalue which is neither the least nor the greatest.

**WHY THE HYPOTHESES ARE THE RIGHT ONES AND NOT A CONVENIENCE.** `0 < k` fails exactly at the
constant character, whose eigenspace `TorusGroundState` shows is one dimensional; `2k ≠ n` fails
exactly at the alternating one, whose eigenspace `TorusTopSimple` shows is one dimensional at even
side length. **So the three cases together are the whole spectrum of the ring**, and the two
exceptions are not gaps but the two frequencies that are their own reflections.

## What is NOT here

**Still one dimension.** `d ≥ 2` is untouched, and the reason is unchanged: per-axis reflections are
*some* of the collisions there and nothing says they are all of them. **No cost is claimed**
(`ERRATUM 246`).

**^ SOMETHING SAYS IT NOW, 2026-08-31, AND WHAT IT SAYS IS THAT THEY ARE NOT; THE SENTENCE IS KEPT**
(`ERRATUM 94`, `ERRATUM 371`). `TorusNonReflectionCollision.nuR_comp_perm` makes `νR` invariant
under permuting the axes — `νR` is a sum over the axes and a sum does not see their order — so at
`d = 2` and side at least four `(1, 2)` and `(2, 1)` collide with the second outside every
`reflectAxes S`. **Nor do the signed permutations exhaust them**: at side `12`, `(2, 3)` and
`(0, 4)` collide and no reflection-and-permutation relates them. **This file's `d = 1` count is
untouched** — `2` at every interior frequency, exact — and no upper bound at `d ≥ 2` is proved or
costed.

**No list of eigenvectors.** The dimension is two; **no basis of that eigenspace is exhibited**, and
the two characters at `k` and `n − k` are the obvious candidates over `ℂ` — their real and imaginary
parts are **not** shown here to span the real eigenspace.

**Not transported to `cycleGraph`.** As in the previous unit, this is `νR` on `Site 1 (N+3)`, and
`TorusCycleGraph.torusGraph_one_iso` is not applied.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleMultiplicityCount

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity CycleMultiplicity

/-- **THE REFLECTED FREQUENCY, AS AN OBJECT.** `n − k` reduced mod `n`, which is total: at `k = 0`
the subtraction would leave `n` itself, outside `Fin n`, and the reduction sends it back to `0` —
which is right, since `0` is its own reflection. -/
def mirrorFreq {N : ℕ} (k : Site 1 (N + 3)) : Site 1 (N + 3) :=
  fun _ => ⟨(N + 3 - (k 0).val) % (N + 3), Nat.mod_lt _ (by omega)⟩

/-- Away from `0` the reduction does nothing and the value is the plain difference. -/
theorem mirrorFreq_val {N : ℕ} (k : Site 1 (N + 3)) (hk : 0 < (k 0).val) :
    ((mirrorFreq k) 0).val = N + 3 - (k 0).val := by
  have h1 : N + 3 - (k 0).val < N + 3 := by omega
  simpa [mirrorFreq] using Nat.mod_eq_of_lt h1

/-- Two frequencies of the ring are equal exactly when their single coordinates are. -/
theorem site_one_ext {N : ℕ} {k k' : Site 1 (N + 3)} (h : (k' 0).val = (k 0).val) : k' = k := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  exact Fin.ext h

/-- **THE FIBRE AT AN INTERIOR FREQUENCY IS A PAIR.** `0 < k` excludes the constant character and
`2k ≠ n` the alternating one; at every other frequency the eigenvalue is shared by exactly the
frequency and its reflection, and those two are different. -/
theorem fibre_eq_pair (N : ℕ) (m : ℝ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    {k' : Site 1 (N + 3) | nuR N m k' = nuR N m k} = {k, mirrorFreq k} := by
  ext k'
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [nuR_eq_iff_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (site_one_ext h)
    · refine Or.inr (site_one_ext ?_)
      rw [mirrorFreq_val k hk0]
      omega
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      rw [mirrorFreq_val k hk0]
      omega

/-- The two are distinct, which is where `2k ≠ n` is used. -/
theorem ne_mirrorFreq {N : ℕ} (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) : k ≠ mirrorFreq k := by
  intro h
  have h2 := congrArg (fun j : Site 1 (N + 3) => (j 0).val) h
  simp only at h2
  rw [mirrorFreq_val k hk0] at h2
  omega

/-- **SO THE FIBRE HAS TWO ELEMENTS.** -/
theorem card_fibre_eq_two (N : ℕ) (m : ℝ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    Nat.card {k' : Site 1 (N + 3) // nuR N m k' = nuR N m k} = 2 := by
  have hcoe : Nat.card {k' : Site 1 (N + 3) // nuR N m k' = nuR N m k}
      = Set.ncard {k' : Site 1 (N + 3) | nuR N m k' = nuR N m k} :=
    Nat.card_coe_set_eq _
  rw [hcoe, fibre_eq_pair N m k hk0 hkhalf, Set.ncard_pair (ne_mirrorFreq k hk0 hkhalf)]

/-- **THE INTERIOR EIGENSPACES OF THE RING ARE TWO DIMENSIONAL**, over `ℝ` and for the massive
Laplacian. The first multiplicity number in this estate at an eigenvalue that is neither the least
nor the greatest. -/
theorem finrank_eigenspace_interior_eq_two (N : ℕ) (m : ℝ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph 1 (N + 3)) m) - (nuR N m k) • LinearMap.id)) = 2 := by
  rw [finrank_eigenspace_massive_real N m (nuR N m k)]
  exact card_fibre_eq_two N m k hk0 hkhalf

end CycleMultiplicityCount
