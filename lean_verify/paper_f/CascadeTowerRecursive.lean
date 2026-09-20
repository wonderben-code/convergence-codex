/-
  CascadeTowerRecursive.lean — the cascade as a family DEFINED BY the recursion `D (k+1) := End
  (D k)`,
  with its algebra structure produced by the same recursion, and proved equivalent level by level to
  the matrix family `SpineSharpenings.D`.

  SPINE link L4 (the cascade `M₂ → M₄ → M₁₆ → …`), rated GENUINE — hardening unit 152, 2026-09-20.

  WHY. L4's row records the one residue its GENUINE rating still carries, in `SpineSharpenings`'
  own words: *"`D` is DEFINED as matrix algebras and the theorem says `End` of each is equivalent
  to the next; a family defined BY the recursion `D (k+1) := End (D k)` needs a `Module` instance
  produced by the same recursion and is a different, harder object, and is NOT built."* The title's
  `…` is that recursion. This file builds it. The obstacle was never mathematical: a type family
  defined by recursion has no ring structure until one is produced alongside it, so the recursion
  has to run on a BUNDLE (a type together with its `Ring` and `Algebra ℂ` instances). Once it does,
  `next B := ⟨Module.End ℂ B.carrier⟩` is a step that Lean can take at every level, and the
  equivalence with the matrix family is `SeedStarStructure.endAlgConj` (unit 150) composed with
  `SpineSharpenings.endTower` at each step.

  WHAT IS PROVED.
  * `AlgBundle` — a type with a `Ring` and an `Algebra ℂ` instance, carried as data.
  * `next B` — the bundle of `Module.End ℂ B.carrier`; `towerBundle : ℕ → AlgBundle` by
    recursion from `M₂(ℂ)`; `Dr k := (towerBundle k).carrier`, the recursively defined family,
    with its ring and algebra structure obtained BY that recursion and nothing else.
  * `Dr_succ : Dr (k + 1) = Module.End ℂ (Dr k)` — by `rfl`, which is the point: the family is the
    recursion, not a family of matrix algebras that a theorem compares to the recursion.
  * **`towerEquiv k : Dr k ≃ₐ[ℂ] SpineSharpenings.D k`** at every `k`, by induction — so the
    recursively defined level `k` IS `M_{2^{2^k}}(ℂ)` as an algebra; `finrank_Dr : finrank ℂ
  (Dr k) =
    towerSize k ^ 2`; `Dr_zero_equiv_m2`, `Dr_one_equiv_m4`.
  * `towerEquiv_succ` — the induction step is the conjugation of endomorphisms along the previous
    level's equivalence followed by `endTower`, stated as an equation of equivalences.

  WHAT IS **NOT** PROVED, said exactly.
  * The DEPTH of the cascade (why the tower stops at `M₂₅₆`, `ASSUMPTIONS_LEDGER` 5, 23) and WHICH
    tensor factor decomposes at each level (10, 30) are untouched; the tower here is infinite and
    says nothing about a preferred level.
  * `Dr 0` is `M₂(ℂ)` written down. The arrow from the seed THEOREM into level `1`
    (`SeedStarStructure.seedEndEquiv`) is the previous unit's and is not repeated; nothing here
  makes
    the seed derived rather than posited.
  * The equivalences are of `ℂ`-algebras; no ⋆-structure is carried up the tower (the seed's star,
    unit 150, is at level `0` only).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SeedStarStructure

namespace CascadeTowerRecursive

open Module SpineSharpenings SeedStarStructure

/-! ## 1. Bundles, so that the recursion can carry its own structure -/

/-- A type with the algebra structure the recursion needs, carried as data. -/
structure AlgBundle where
  /-- The underlying type. -/
  carrier : Type
  /-- Its ring structure. -/
  [ring : Ring carrier]
  /-- Its `ℂ`-algebra structure. -/
  [alg : Algebra ℂ carrier]

attribute [instance] AlgBundle.ring AlgBundle.alg

/-- One step: the endomorphism algebra of the previous level. -/
def next (B : AlgBundle) : AlgBundle := ⟨Module.End ℂ B.carrier⟩

/-- The tower, by recursion from `M₂(ℂ)`. -/
def towerBundle : ℕ → AlgBundle
  | 0 => ⟨Matrix (Fin 2) (Fin 2) ℂ⟩
  | k + 1 => next (towerBundle k)

/-- The recursively defined family `M₂, End M₂, End (End M₂), …`. -/
abbrev Dr (k : ℕ) : Type := (towerBundle k).carrier

theorem Dr_zero : Dr 0 = Matrix (Fin 2) (Fin 2) ℂ := rfl

/-- **THE RECURSION, AS AN EQUATION OF TYPES, BY `rfl`.** -/
theorem Dr_succ (k : ℕ) : Dr (k + 1) = Module.End ℂ (Dr k) := rfl

/-! ## 2. Level by level, the recursive family is the matrix family -/

/-- `Dr k ≃ₐ[ℂ] D k` at every `k`: the base is `M₂(ℂ) ≃ₐ D 0` (`m2ToD0`), the step conjugates
endomorphisms along the previous equivalence (`endAlgConj`) and applies `endTower`. -/
noncomputable def towerEquiv : (k : ℕ) → (Dr k ≃ₐ[ℂ] SpineSharpenings.D k)
  | 0 => m2ToD0
  | k + 1 => (endAlgConj (towerEquiv k).toLinearEquiv).trans (SpineSharpenings.endTower k)

theorem towerEquiv_zero : towerEquiv 0 = m2ToD0 := rfl

theorem towerEquiv_succ (k : ℕ) :
    towerEquiv (k + 1)
      = (endAlgConj (towerEquiv k).toLinearEquiv).trans (SpineSharpenings.endTower k) := rfl

/-- The recursively defined level `k` has the matrix family's dimension. -/
theorem finrank_Dr (k : ℕ) : finrank ℂ (Dr k) = towerSize k ^ 2 := by
  rw [(towerEquiv k).toLinearEquiv.finrank_eq]
  simp [SpineSharpenings.D, Module.finrank_matrix, sq]

theorem Dr_zero_equiv_m2 : Nonempty (Dr 0 ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨AlgEquiv.refl⟩

theorem Dr_one_equiv_m4 : Nonempty (Dr 1 ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨(towerEquiv 1).trans (Matrix.reindexAlgEquiv ℂ ℂ (finCongr SpineSharpenings.towerSize_one))⟩

theorem Dr_two_equiv_m16 : Nonempty (Dr 2 ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ) :=
  ⟨(towerEquiv 2).trans (Matrix.reindexAlgEquiv ℂ ℂ (finCongr SpineSharpenings.towerSize_two))⟩

theorem Dr_three_equiv_m256 : Nonempty (Dr 3 ≃ₐ[ℂ] Matrix (Fin 256) (Fin 256) ℂ) :=
  ⟨(towerEquiv 3).trans (Matrix.reindexAlgEquiv ℂ ℂ (finCongr SpineSharpenings.towerSize_three))⟩

end CascadeTowerRecursive
