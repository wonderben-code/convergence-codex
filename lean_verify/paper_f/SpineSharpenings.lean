/-
  SpineSharpenings: the four residues the recompute named for the four GENUINE links,
  each of which was one composition away

  SPINE LINKS L3, L4, L5, L8 — all four rated **GENUINE**, and all four carrying a residue
  the 14 September recompute described as *"one composition from a theorem"*, *"a
  three-line corollary, unwritten"*, *"a comment, one composition from a theorem"* or *"a
  composition of two theorems with no `IsLeast` wrapper"*. The Caesar order ranked them
  10 of 12 and labelled them **trivial**. This file is the composition, and the estimate
  was right: every declaration below closed on the first type-check.

  **WHY A GENUINE LINK STILL HAS A RESIDUE, AND WHY IT IS WORTH CLOSING.** The campaign's
  vocabulary rates a link GENUINE when its HEADLINE is a machine-checked theorem
  statement. It does not require that every sentence near the headline be a theorem — and
  in each of these four cases a real theorem existed a composition away and a *reader* had
  to do the composing. That is exactly the class of gap that turns into a false claim
  later: `ERRATUM 563` was an absence clause that this campaign's own work falsified
  fourteen hours after it was written, and `ERRATUM 565` was a claim whose cited evidence
  was true and about a different variable. **A sentence a reader has to compose is a
  sentence that will be misquoted.**

  WHAT IS PROVED, one per link.

  * **L5 — `end_finrank_injective`.** The recompute: *"The pre-image clause in its general
    `End` form for arbitrary `V, W` — a three-line corollary, unwritten."* The estate had
    `end_dim_strictly_increasing` (the arrow) and `CascadeEnd.size_eq_of_end_equiv` (the
    pre-image at matrix algebras); the general statement — `finrank (End V) = finrank (End W)`
    forces `finrank V = finrank W`, for any two free finite modules — is here, off
    `Module.finrank_linearMap` and `Nat.mul_self_inj`. **This is the irreversibility
    clause in the form the headline claims**: not just that dimension grows, but that the
    level is recoverable from `End` of it.

  * **L4 — `towerSize`, `D`, `endTower`.** The recompute: *"The title's `…`: no type family
    `D (k+1) = End (D k)` with `D k ≃ₐ M_{2^{2^k}}` for all `k` — the step exists at every
    `b`, the tower is unwritten."* `D k := M_{2^{2^k}}(ℂ)` and
    **`endTower k : End (D k) ≃ₐ[ℂ] D (k+1)`** at every `k`, off
    `CascadeEnd.endMatrixEquiv` and the arithmetic `(2^{2^k})² = 2^{2^{k+1}}`
    (`towerSize_succ`). `towerSize_zero`/`_one`/`_two`/`_three` pin the sizes at `2`, `4`,
    `16`, `256` — the cascade's own `D₁`, `D₂`, `D₃`, `D₄`.
    **STATED PLAINLY BECAUSE IT IS NOT THE STRONGEST READING**: `D` is *defined* as a
    family of matrix algebras and `endTower` says `End` of each is equivalent to the next.
    A family *defined* by the recursion `D (k+1) := End (D k)` is a different object, and
    building it needs a `Module` instance produced by the same recursion — that is
    genuinely harder and is **not** done here. What the title's `…` asks for is the
    equivalence at every level, and that is what this gives.
    ⚠ **DONE 2026-09-20 (hardening unit 152), KEPT AS WRITTEN PER `ERRATUM 94`:**
    `CascadeTowerRecursive.lean` runs the recursion on a bundle carrying its own `Ring`
    and `Algebra ℂ` instances, so `Dr (k + 1) = Module.End ℂ (Dr k)` is `rfl`, and
    `towerEquiv k : Dr k ≃ₐ[ℂ] D k` at every `k` off `endTower` and unit 150's
    `SeedStarStructure.endAlgConj`. The two readings of the title's `…` are now the same
    algebras, level by level.

  * **L8 — `clifford_finrank_four_of_iso`.** The recompute: *"the converse
    `≅ M₄(ℂ) only for dim 4` is a comment, one composition from a theorem."* It is now a
    theorem: for every complex quadratic form on a finite-dimensional space, an algebra
    equivalence `Cl(Q) ≃ₐ[ℂ] M₄(ℂ)` forces `finrank V = 4`, off
    `CliffordDimension.finrank_cliffordAlgebra_complex` (`dim Cl(Q) = 2^{dim V}`) and
    injectivity of `2 ^ ·`. With `CliffordEvenLadder.clifford_iso_of_nondegenerate` in the
    other direction, `clifford_iso_M4_iff_finrank_four` is the **iff** — so "four
    dimensions" and "the algebra is `M₄(ℂ)`" are interchangeable hypotheses, which is what
    L8's gloss needs and what the comment asserted.

  * **L3 — `seedDims`, `seed_four_isLeast`.** The recompute: *"`minimal` is a composition
    of two theorems with no `IsLeast` wrapper."* `seedDims` is the set of dimensions
    realised by non-commutative finite-dimensional semisimple `ℂ`-algebras, and
    **`seed_four_isLeast : IsLeast seedDims 4`** composes `SeedUniqueness.seed_dim_lower_bound`
    (the bound, over the whole class) with `m2_noncommutative` and `m2_finrank` (the
    witness). **STATED PLAINLY**: `seedDims` ranges over `Type` (universe 0), while
    `seed_dim_lower_bound` is universe-polymorphic — so this `IsLeast` is about the
    universe-0 slice of the class, which is where `M₂(ℂ)` lives and where the cascade's
    objects live. Making the set universe-polymorphic needs a `Set` in a higher universe
    and changes nothing mathematically.

  WHAT IS **NOT** CLAIMED. No rating moves: L3, L4, L5 and L8 were GENUINE before this
  file and are GENUINE after it, because a GENUINE rating is about the headline and these
  are residues beside it. The postulates those links rest on are untouched — L4's cascade
  DEPTH and which-factor-decomposes (`ASSUMPTIONS_LEDGER` 5, 10, 30), L8's reading of
  spacetime at `D₂` (22), L3's `IsSemisimpleRing` model of "trace-faithful" (4) and the
  unstated arrow from L2's `D` to an algebra (35), L5's "arrow of time" interpretation (2).
  And `SeedUniqueness` still has **no consumer** other than this file — queried:
  `grep -rln 'SeedUniqueness\|seed_dim_lower_bound\|seed_forced\|seed_unique_dim_four'`
  over the estate returns one other file, `StarRepSemisimple.lean`, and the hit there is a
  prose list in its header with no `import SeedUniqueness` anywhere. That is its own
  finding and is recorded in the L3 row rather than fixed here.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import SeedUniqueness
import CascadeEnd
import CliffordDimension
import CliffordEvenLadder

namespace SpineSharpenings

open Matrix Module

noncomputable section

/-! ## 1. L5 — irreversibility: the level is recoverable from `End` of it -/

/-- **L5's pre-image clause, in the general `End` form the headline claims.** If two free
finite modules have `End`s of the same dimension, they have the same dimension. So the
cascade step is not merely dimension-increasing (`end_dim_strictly_increasing`): the level
below is determined by `End` of it. -/
theorem end_finrank_injective (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] [AddCommGroup W] [Module ℂ W]
    [Module.Free ℂ W] [Module.Finite ℂ W]
    (h : finrank ℂ (Module.End ℂ V) = finrank ℂ (Module.End ℂ W)) :
    finrank ℂ V = finrank ℂ W := by
  rw [finrank_linearMap, finrank_linearMap] at h
  exact Nat.mul_self_inj.mp h

/-! ## 2. L4 — the tower, at every level -/

/-- The cascade's sizes: `2, 4, 16, 256, …`. -/
abbrev towerSize (k : ℕ) : ℕ := 2 ^ (2 ^ k)

/-- The cascade's levels as a family of algebras. **`D` is DEFINED as matrix algebras**;
see the header for what that does and does not say about the title's `…`. -/
abbrev D (k : ℕ) : Type := Matrix (Fin (towerSize k)) (Fin (towerSize k)) ℂ

/-- The arithmetic the tower runs on: `(2^{2^k})² = 2^{2^{k+1}}`. -/
theorem towerSize_succ (k : ℕ) : towerSize (k + 1) = towerSize k * towerSize k := by
  simp only [towerSize, pow_succ, ← pow_add]
  ring_nf

theorem towerSize_zero : towerSize 0 = 2 := by norm_num
theorem towerSize_one : towerSize 1 = 4 := by norm_num
theorem towerSize_two : towerSize 2 = 16 := by norm_num
theorem towerSize_three : towerSize 3 = 256 := by norm_num

/-- **L4's TOWER: `End` of each level is the next, at every `k`.** The step existed at
every `b` (`CascadeEnd.endMatrixEquiv`); this is the step indexed by the cascade. -/
def endTower (k : ℕ) : Module.End ℂ (D k) ≃ₐ[ℂ] D (k + 1) :=
  (CascadeEnd.endMatrixEquiv (towerSize k)).trans
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (towerSize_succ k).symm))

/-- The cascade's first three steps, read off the tower: `End(M₂) ≃ M₄`,
`End(M₄) ≃ M₁₆`, `End(M₁₆) ≃ M₂₅₆`. -/
theorem endTower_inhabited :
    Nonempty (Module.End ℂ (D 0) ≃ₐ[ℂ] D 1)
    ∧ Nonempty (Module.End ℂ (D 1) ≃ₐ[ℂ] D 2)
    ∧ Nonempty (Module.End ℂ (D 2) ≃ₐ[ℂ] D 3) :=
  ⟨⟨endTower 0⟩, ⟨endTower 1⟩, ⟨endTower 2⟩⟩

/-! ## 3. L8 — the converse, and the iff -/

/-- **L8's CONVERSE, which was a comment.** For every complex quadratic form on a
finite-dimensional space, `Cl(Q) ≃ₐ[ℂ] M₄(ℂ)` forces `dim V = 4`. Off
`CliffordDimension.finrank_cliffordAlgebra_complex` and injectivity of `2 ^ ·`. -/
theorem clifford_finrank_four_of_iso (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (Q : QuadraticForm ℂ V)
    (h : Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)) :
    finrank ℂ V = 4 := by
  obtain ⟨e⟩ := h
  have h1 : finrank ℂ (CliffordAlgebra Q) = 16 := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  rw [CliffordDimension.finrank_cliffordAlgebra_complex] at h1
  have h2 : (2 : ℕ) ^ finrank ℂ V = 2 ^ 4 := by simpa using h1
  exact Nat.pow_right_injective (by norm_num) h2

/-- **AND THE IFF.** "Four dimensions" and "the algebra is `M₄(ℂ)`" are interchangeable
hypotheses for a nondegenerate complex form — which is what L8's gloss needs. The forward
direction is `CliffordEvenLadder.clifford_iso_of_nondegenerate`. -/
theorem clifford_iso_M4_iff_finrank_four (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ) ↔ finrank ℂ V = 4 :=
  ⟨clifford_finrank_four_of_iso V Q, fun h => by
    have := CliffordEvenLadder.clifford_iso_of_nondegenerate 2 (by omega : finrank ℂ V = 2 * 2)
      Q hQ
    simpa using this⟩

/-! ## 4. L3 — minimality, with the wrapper -/

/-- The dimensions realised by a non-commutative finite-dimensional semisimple
`ℂ`-algebra. **Over `Type` (universe 0)**; see the header. -/
def seedDims : Set ℕ :=
  {d | ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A) (_ : FiniteDimensional ℂ A)
        (_ : IsSemisimpleRing A), (∃ a b : A, a * b ≠ b * a) ∧ finrank ℂ A = d}

theorem four_mem_seedDims : 4 ∈ seedDims :=
  ⟨Matrix (Fin 2) (Fin 2) ℂ, inferInstance, inferInstance, inferInstance, inferInstance,
    SeedUniqueness.m2_noncommutative, SeedUniqueness.m2_finrank⟩

/-- **L3's "minimal", as `IsLeast`.** The bound is
`SeedUniqueness.seed_dim_lower_bound` over the whole class; the witness is `M₂(ℂ)`. The
two existed and nothing composed them. -/
theorem seed_four_isLeast : IsLeast seedDims 4 := by
  refine ⟨four_mem_seedDims, ?_⟩
  rintro d ⟨A, _, _, _, _, hnc, hdim⟩
  rw [← hdim]
  exact SeedUniqueness.seed_dim_lower_bound A hnc

end

end SpineSharpenings
