import RealDivisionSmallCases
import Mathlib.Algebra.QuaternionBasis

/-!
# The last case, and Frobenius's theorem

`RealDivisionSmallCases` closed dimensions one and two and left one case: `dim D = 4 → ℍ ≃ₐ[ℝ] D`.
Its header first denied that a tool for it existed and then, because `ERRATUM 42` makes an absence
claim a probe rather than a memory, found one — `QuaternionAlgebra.Basis.liftHom`, whose four
hypotheses at `ℍ[ℝ] = ℍ[ℝ,-1,0,-1]` are

```
i * i = (-1) • 1 + 0 • i      j * j = (-1) • 1      i * j = k      j * i = 0 • j - k
```

**and every one of those is already a theorem in this chain.** `RealDivisionPureBasis` and
`RealDivisionPureDim` proved them about a normalised orthogonal pure pair and its product, for
reasons that had nothing to do with quaternions. **This file is the assembly.**

> **§1. The pair, at dimension four.** `exists_normalised_pair` — the pure part has dimension three
> there (`RealDivisionPureSpace.finrank_eq_succ`), so a normalised element exists, one direction
> cannot span it, and `RealDivisionPureBasis.exists_orthogonal_normalised` supplies the partner.
> The three facts it returns are exactly the structure's hypotheses in this project's vocabulary.
>
> **§2. The translation.** `pureQuatBasis` — a `QuaternionAlgebra.Basis D (-1) 0 (-1)` built from
> that pair. **Every field is a rewrite of a theorem already proved**: `pureSq_spec` twice for the
> two squares, `rfl` for the product, and `RealDivisionFormFun.orthogonal_iff_anticomm` for the
> sign flip. There is no new mathematics in this section, which is the point of it.
>
> **§3. The isomorphism.** `algEquivQuaternion` — `liftHom` at that basis, made bijective by
> `RealDivisionSmallCases.bijective_of_finrank_eq` and `Quaternion.finrank_eq_four`. **This is where
> the `[DivisionRing K]` in that lemma is spent**: `ℍ[ℝ]` is not a field, and a `[Field K]` version
> — which is what the first draft of that file carried — could not be used here at all.
>
> **§4. `frobenius`.** The trichotomy plus the three cases: every finite-dimensional real division
> algebra is `ℝ`, `ℂ` or `ℍ`.

**WHAT THIS IS.** Frobenius's theorem, as the `UNLOCK_WATCHLIST` item states it: *`ℝ`, `ℂ` and `ℍ`
are the **only** finite-dimensional real division algebras.* The item is closed.

**WHAT THIS IS NOT.** It is not a classification of real division algebras in general — finiteness
of dimension is a hypothesis on every theorem here, and dropping it is a different subject
(`ERRATUM 60`). It says nothing about associativity being droppable: the octonions are outside every
statement in this chain because `D` is a `DivisionRing` throughout, and **Hurwitz's theorem is not
here, not attempted, and not costed** (`ERRATUM 194`, `ERRATUM 246`). And the three algebras'
pairwise distinctness is `RealDivisionTrichotomy`'s, proved earlier and not restated. **No published
tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionQuaternionCase

open RealDivisionPure RealDivisionPureForm RealDivisionPureSpace
open RealDivisionFormFun RealDivisionPureBasis RealDivisionPureDim RealDivisionSmallCases
open Quaternion

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-! ### §1. At dimension four the pair exists -/

/-- **The pair.** At dimension four the pure part has dimension three, so one direction cannot span
it and `exists_orthogonal_normalised` supplies a partner. -/
theorem exists_normalised_pair (h : Module.finrank ℝ D = 4) :
    ∃ i j : pureSubmodule D, pureSq i = -1 ∧ pureSq j = -1 ∧ pureForm i j = 0 := by
  have hsucc := finrank_eq_succ (D := D)
  haveI : Nontrivial (pureSubmodule D) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : pureSubmodule D)
  obtain ⟨t, _, hti⟩ := exists_smul_sq_neg_one (mem_pureSubmodule.mp u.2)
    (fun hc => hu (Submodule.coe_eq_zero.mp hc))
  have hi : pureSq (t • u) = -1 := (pureSq_eq (D := D) (u := t • u) hti).symm
  have hlt : Submodule.span ℝ ({t • u} : Set (pureSubmodule D)) < ⊤ := by
    refine span_lt_top_of_card_lt_finrank ?_
    simp
    omega
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨j, hj, hij⟩ := exists_orthogonal_normalised hi hv
  exact ⟨t • u, j, hi, hj, hij⟩

/-! ### §2. The pair is a quaternion basis -/

/-- **The translation, and it contains no new mathematics.** Each field is a theorem this chain
already has, rewritten into `QuaternionAlgebra.Basis`'s vocabulary. -/
def pureQuatBasis {i j : pureSubmodule D} (hi : pureSq i = -1) (hj : pureSq j = -1)
    (hij : pureForm i j = 0) : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1) where
  i := (i : D)
  j := (j : D)
  k := (i : D) * (j : D)
  i_mul_i := by rw [pureSq_spec i, hi, zero_smul, add_zero]
  j_mul_j := by rw [pureSq_spec j, hj]
  i_mul_j := rfl
  j_mul_i := by
    have hanti : (i : D) * (j : D) + (j : D) * (i : D) = 0 :=
      (orthogonal_iff_anticomm i j).mp hij
    rw [zero_smul, zero_sub]
    linear_combination (norm := noncomm_ring) hanti

/-! ### §3. Dimension four is `ℍ` -/

/-- At dimension four, `liftHom` at that basis is the isomorphism. **This is where the shared
lemma's `[DivisionRing K]` is spent** — `ℍ[ℝ]` is not a field.

Stated as `Nonempty` first, and not because the `Prop` is what is wanted: `exists_normalised_pair`
returns an `∃`, which cannot be eliminated into a type, so the data version is `Classical.choice`
applied to this and says so rather than hiding a choice inside a `def`. -/
theorem algEquiv_quaternion (h : Module.finrank ℝ D = 4) : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) := by
  obtain ⟨i, j, hi, hj, hij⟩ := exists_normalised_pair h
  have hdim : Module.finrank ℝ ℍ[ℝ,(-1 : ℝ),0,(-1 : ℝ)] = Module.finrank ℝ D := by
    rw [QuaternionAlgebra.finrank_eq_four, h]
  exact ⟨AlgEquiv.ofBijective (pureQuatBasis hi hj hij).liftHom
    (bijective_of_finrank_eq _ hdim)⟩

/-- The data form, by choice. -/
noncomputable def algEquivQuaternion (h : Module.finrank ℝ D = 4) : ℍ[ℝ] ≃ₐ[ℝ] D :=
  (algEquiv_quaternion h).some

/-! ### §4. Frobenius's theorem -/

/-- **FROBENIUS'S THEOREM.** Every finite-dimensional real division algebra is `ℝ`, `ℂ` or `ℍ`.
The dimension is `1`, `2` or `4` by `RealDivisionPureDim.finrank_eq_one_two_or_four`, and each
dimension has its isomorphism. -/
theorem frobenius : Nonempty (ℝ ≃ₐ[ℝ] D) ∨ Nonempty (ℂ ≃ₐ[ℝ] D) ∨ Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) := by
  rcases finrank_eq_one_two_or_four (D := D) with h1 | h2 | h4
  · exact Or.inl (algEquiv_real h1)
  · exact Or.inr (Or.inl (algEquiv_complex h2))
  · exact Or.inr (Or.inr (algEquiv_quaternion h4))

end RealDivisionQuaternionCase
