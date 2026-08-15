import SL2Connected

/-!
# Properness of Λ, by the route the estate had to avoid

`LorentzGroup` §5 proves `det Λ(A) = 1` for `A ∈ SL₂(ℂ)` algebraically, by writing every element
of SL₂(ℂ) as a product of squares, and its section header explains why:

> The usual proof that the image is proper is topological: `det Λ` is continuous, valued in `{±1}`,
> and SL₂(ℂ) is connected. **That argument is not available here**, and it is not needed.

**Both missing ingredients arrived on 15 Aug 2026** — `LorentzConnectedReduction` proved `Λ`
continuous, `SL2Connected` proved SL₂(ℂ) connected — so the sentence is now false and this file is
the demonstration. `LorentzGroup` §5 carries a pointer here; the paragraph itself is left standing,
because it was true when written and because the algebraic proof it introduces is still the one
the estate depends on.

## What this is for, stated honestly

**It is a second route to a theorem the estate already has**, in the sense `SpinMeetsSL2`'s
`det_boost_block` is: a fact reached twice, by arguments sharing no lemma, is a fact whose proof
one need not read to believe. `LorentzGroup.det_lorentzMat` and
`det_lorentzMat_topological` here have **no lemma in common** — one runs on an explicit square-root
formula inside SL₂(ℂ), the other on continuity, the sign of a determinant and connectedness.

**It is not needed and nothing is rewired to use it.** Everything downstream still consumes
`LorentzGroup.det_lorentzMat`. Replacing that dependency would move a load-bearing fact from a
short algebraic proof onto three files' worth of topology, which is a worse trade even though the
topology is now available.

**And it retires an excuse rather than an obstacle.** The §5 sentence was not recording a gap in
the mathematics; it was recording what this estate could reach in July. What changed is the
estate, not the Lorentz group.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LorentzProperTopological

open Matrix LorentzGroup

/-- `det Λ` is continuous on SL₂(ℂ), which is the first of the two ingredients §5 lacked. -/
theorem continuous_det :
    Continuous fun A : SL2C => (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det :=
  (LorentzConnectedReduction.continuous_lorentzMat.comp
    (by fun_prop : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ))).matrix_det

/-- …and it never vanishes, because it squares to one. -/
theorem det_ne_zero (A : SL2C) : (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
  intro h
  have hsq := det_lorentzMat_sq (A : Matrix (Fin 2) (Fin 2) ℂ) A.2
  rw [h] at hsq
  norm_num at hsq

/-- **THE SIGN OF `det Λ` IS LOCALLY CONSTANT**, by the argument `LorentzIdentityComponent` uses
on O(1,3): a quantity that cannot vanish cuts its domain into two open pieces. -/
theorem isClopen_det_pos :
    IsClopen {A : SL2C | 0 < (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det} := by
  refine ⟨?_, isOpen_lt continuous_const continuous_det⟩
  rw [← isOpen_compl_iff]
  have hset : {A : SL2C | 0 < (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det}ᶜ
      = {A : SL2C | (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det < 0} := by
    ext A
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (det_ne_zero A), fun h => h.le⟩
  rw [hset]
  exact isOpen_lt continuous_det continuous_const

/-- **PROPERNESS, BY THE TOPOLOGICAL ROUTE.** The clopen set of §"isClopen" contains `1`, and
SL₂(ℂ) is connected, so it is everything; `det² = 1` then pins the value. -/
theorem det_lorentzMat_topological (A : SL2C) :
    (lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det = 1 := by
  have hmem : A ∈ {B : SL2C | 0 < (lorentzMat (B : Matrix (Fin 2) (Fin 2) ℂ)).det} := by
    rcases isClopen_iff.mp isClopen_det_pos with hempty | huniv
    · exfalso
      have h1 : (1 : SL2C) ∈ {B : SL2C | 0 < (lorentzMat (B : Matrix (Fin 2) (Fin 2) ℂ)).det} := by
        simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one, lorentzMat_one,
          Matrix.det_one]
        norm_num
      rw [hempty] at h1
      exact h1
    · rw [huniv]; trivial
  simp only [Set.mem_setOf_eq] at hmem
  have hsq := det_lorentzMat_sq (A : Matrix (Fin 2) (Fin 2) ℂ) A.2
  have hfac : ((lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det - 1)
      * ((lorentzMat (A : Matrix (Fin 2) (Fin 2) ℂ)).det + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h <;> linarith

/-- The two proofs agree, which is the only sense in which a second route can be checked. -/
theorem agrees_with_algebraic (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (lorentzMat A).det = 1 :=
  det_lorentzMat_topological ⟨A, hA⟩

end LorentzProperTopological
